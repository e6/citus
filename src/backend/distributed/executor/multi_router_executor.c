/*
 * multi_router_executor.c
 *
 * Routines for executing remote tasks as part of a distributed execution plan
 * with synchronous connections. The routines utilize the connection cache.
 * Therefore, only a single connection is opened for each worker. Also, router
 * executor does not require a master table and a master query. In other words,
 * the results that are fetched from a single worker is sent to the output console
 * directly. Lastly, router executor can only execute a single task.
 *
 * Copyright (c) 2012-2016, Citus Data, Inc.
 */

#include "postgres.h"
#include "c.h"
#include "fmgr.h"
#include "funcapi.h"
#include "libpq-fe.h"
#include "miscadmin.h"

#include "access/xact.h"
#include "distributed/citus_ruleutils.h"
#include "distributed/connection_cache.h"
#include "distributed/listutils.h"
#include "distributed/multi_executor.h"
#include "distributed/multi_physical_planner.h"
#include "distributed/multi_planner.h"
#include "distributed/multi_router_executor.h"
#include "distributed/resource_lock.h"
#include "executor/executor.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/pg_list.h"
#include "optimizer/planmain.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/elog.h"
#include "utils/errcodes.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/palloc.h"
#if (PG_VERSION_NUM >= 90500)
#include "utils/ruleutils.h"
#endif


/* controls use of locks to enforce safe commutativity */
bool AllModificationsCommutative = false;

/* used by PartiallyEvaluateExpressionWalker */
typedef struct ExpressionWalkerState
{
	bool isTopLevel; /* if there are no vars the entire expression can be evaluated */
	bool containsVar; /* the callee sets this to signal to the parent it has a Var */
	bool parentIsBranch; /* the caller sets this to signal to the children they should
							also set the below variables */
	List *subtreesWithVar; /* when parentIsBranch add yourself to one of these */
	List *subtreesWithoutVar;
	List *subtreeOrder;  /* A list of ints representing in which order the WithVar and
							WithoutVar lists should be reassembled */
} ExpressionWalkerState;


static LOCKMODE CommutativityRuleToLockMode(CmdType commandType, bool upsertQuery);
static void AcquireExecutorShardLock(Task *task, LOCKMODE lockMode);
static int32 ExecuteDistributedModify(Query *query, Task *task);
static void DeparseShardQuery(Query *query, Task *task, StringInfo queryString);
static void ExecuteSingleShardSelect(QueryDesc *queryDesc, uint64 tupleCount,
									 Task *task, EState *executorState,
									 TupleDesc tupleDescriptor,
									 DestReceiver *destination);
static bool SendQueryInSingleRowMode(PGconn *connection, char *query);
static bool StoreQueryResult(PGconn *connection, TupleDesc tupleDescriptor,
							 Tuplestorestate *tupleStore);
static void ExecuteFunctions(Query *query);
static Node * PartiallyEvaluateExpression(Node *expression);
static Node * PartiallyEvaluateExpressionWalker(Node *expression,
												ExpressionWalkerState *state);
static void InitializeWalkerState(ExpressionWalkerState *state);
static List * RewriteArgs(ExpressionWalkerState *state);
static Node * EvaluateExpression(Node *expression);

static Expr *citus_evaluate_expr(Expr *expr, Oid result_type, int32 result_typmod,
								 Oid result_collation);


/*
 * RouterExecutorStart sets up the executor state and queryDesc for router
 * execution.
 */
void
RouterExecutorStart(QueryDesc *queryDesc, int eflags, Task *task)
{
	LOCKMODE lockMode = NoLock;
	EState *executorState = NULL;
	CmdType commandType = queryDesc->operation;

	/* ensure that the task is not NULL */
	Assert(task != NULL);

	/* disallow transactions and triggers during distributed modify commands */
	if (commandType != CMD_SELECT)
	{
		bool topLevel = true;
		PreventTransactionChain(topLevel, "distributed commands");
		eflags |= EXEC_FLAG_SKIP_TRIGGERS;
	}

	/* signal that it is a router execution */
	eflags |= EXEC_FLAG_CITUS_ROUTER_EXECUTOR;

	/* build empty executor state to obtain per-query memory context */
	executorState = CreateExecutorState();
	executorState->es_top_eflags = eflags;
	executorState->es_instrument = queryDesc->instrument_options;

	queryDesc->estate = executorState;

	/*
	 * As it's similar to what we're doing, use a MaterialState node to store
	 * our state. This is used to store our tuplestore, so cursors etc. can
	 * work.
	 */
	queryDesc->planstate = (PlanState *) makeNode(MaterialState);

#if (PG_VERSION_NUM < 90500)

	/* make sure that upsertQuery is false for versions that UPSERT is not available */
	Assert(task->upsertQuery == false);
#endif

	lockMode = CommutativityRuleToLockMode(commandType, task->upsertQuery);

	if (lockMode != NoLock)
	{
		AcquireExecutorShardLock(task, lockMode);
	}
}


/*
 * CommutativityRuleToLockMode determines the commutativity rule for the given
 * command and returns the appropriate lock mode to enforce that rule. The
 * function assumes a SELECT doesn't modify state and therefore is commutative
 * with all other commands. The function also assumes that an INSERT commutes
 * with another INSERT, but not with an UPDATE/DELETE/UPSERT; and an
 * UPDATE/DELETE/UPSERT doesn't commute with an INSERT, UPDATE, DELETE or UPSERT.
 *
 * Note that the above comment defines INSERT INTO ... ON CONFLICT type of queries
 * as an UPSERT. Since UPSERT is not defined as a separate command type in postgres,
 * we have to pass it as a second parameter to the function.
 *
 * The above mapping is overridden entirely when all_modifications_commutative
 * is set to true. In that case, all commands just claim a shared lock. This
 * allows the shard repair logic to lock out modifications while permitting all
 * commands to otherwise commute.
 */
static LOCKMODE
CommutativityRuleToLockMode(CmdType commandType, bool upsertQuery)
{
	LOCKMODE lockMode = NoLock;

	/* bypass commutativity checks when flag enabled */
	if (AllModificationsCommutative)
	{
		return ShareLock;
	}

	if (commandType == CMD_SELECT)
	{
		lockMode = NoLock;
	}
	else if (upsertQuery)
	{
		lockMode = ExclusiveLock;
	}
	else if (commandType == CMD_INSERT)
	{
		lockMode = ShareLock;
	}
	else if (commandType == CMD_UPDATE || commandType == CMD_DELETE)
	{
		lockMode = ExclusiveLock;
	}
	else
	{
		ereport(ERROR, (errmsg("unrecognized operation code: %d", (int) commandType)));
	}

	return lockMode;
}


/*
 * AcquireExecutorShardLock: acquire shard lock needed for execution of
 * a single task within a distributed plan.
 */
static void
AcquireExecutorShardLock(Task *task, LOCKMODE lockMode)
{
	int64 shardId = task->anchorShardId;

	LockShardResource(shardId, lockMode);
}


/*
 * RouterExecutorRun actually executes a single task on a worker.
 */
void
RouterExecutorRun(QueryDesc *queryDesc, ScanDirection direction, long count)
{
	PlannedStmt *planStatement = queryDesc->plannedstmt;
	MultiPlan *multiPlan = GetMultiPlan(planStatement);
	List *taskList = multiPlan->workerJob->taskList;
	Task *task = NULL;
	EState *estate = queryDesc->estate;
	CmdType operation = queryDesc->operation;
	MemoryContext oldcontext = NULL;

	/* router executor can only execute distributed plans with a single task */
	Assert(list_length(taskList) == 1);
	task = (Task *) linitial(taskList);

	Assert(estate != NULL);
	Assert(!(estate->es_top_eflags & EXEC_FLAG_EXPLAIN_ONLY));
	Assert(task != NULL);

	/* we only support default scan direction and row fetch count */
	if (!ScanDirectionIsForward(direction))
	{
		ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						errmsg("scan directions other than forward scans "
							   "are unsupported")));
	}

	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	if (queryDesc->totaltime != NULL)
	{
		InstrStartNode(queryDesc->totaltime);
	}

	if (operation == CMD_INSERT || operation == CMD_UPDATE ||
		operation == CMD_DELETE)
	{
		Query *query = multiPlan->workerJob->jobQuery;
		int32 affectedRowCount = ExecuteDistributedModify(query, task);
		estate->es_processed = affectedRowCount;
	}
	else if (operation == CMD_SELECT)
	{
		DestReceiver *destination = queryDesc->dest;
		TupleDesc resultTupleDescriptor = queryDesc->tupDesc;

		ExecuteSingleShardSelect(queryDesc, count, task, estate,
								 resultTupleDescriptor, destination);
	}
	else
	{
		ereport(ERROR, (errmsg("unrecognized operation code: %d",
							   (int) operation)));
	}

	if (queryDesc->totaltime != NULL)
	{
		InstrStopNode(queryDesc->totaltime, estate->es_processed);
	}

	MemoryContextSwitchTo(oldcontext);
}


/*
 * ExecuteDistributedModify is the main entry point for modifying distributed
 * tables. A distributed modification is successful if any placement of the
 * distributed table is successful. ExecuteDistributedModify returns the number
 * of modified rows in that case and errors in all others. This function will
 * also generate warnings for individual placement failures.
 */
static int32
ExecuteDistributedModify(Query *query, Task *task)
{
	int32 affectedTupleCount = -1;
	ListCell *taskPlacementCell = NULL;
	List *failedPlacementList = NIL;
	ListCell *failedPlacementCell = NULL;
	StringInfo queryString = makeStringInfo();

	ExecuteFunctions(query);
	DeparseShardQuery(query, task, queryString);
	elog(DEBUG4, "old query: %s", task->queryString);
	elog(DEBUG4, "new query: %s", queryString->data);

	foreach(taskPlacementCell, task->taskPlacementList)
	{
		ShardPlacement *taskPlacement = (ShardPlacement *) lfirst(taskPlacementCell);
		char *nodeName = taskPlacement->nodeName;
		int32 nodePort = taskPlacement->nodePort;

		PGconn *connection = NULL;
		PGresult *result = NULL;
		char *currentAffectedTupleString = NULL;
		int32 currentAffectedTupleCount = -1;

		Assert(taskPlacement->shardState == FILE_FINALIZED);

		connection = GetOrEstablishConnection(nodeName, nodePort);
		if (connection == NULL)
		{
			failedPlacementList = lappend(failedPlacementList, taskPlacement);
			continue;
		}

		result = PQexec(connection, queryString->data);
		if (PQresultStatus(result) != PGRES_COMMAND_OK)
		{
			ReportRemoteError(connection, result);
			PQclear(result);

			failedPlacementList = lappend(failedPlacementList, taskPlacement);
			continue;
		}

		currentAffectedTupleString = PQcmdTuples(result);
		currentAffectedTupleCount = pg_atoi(currentAffectedTupleString, sizeof(int32), 0);

		if ((affectedTupleCount == -1) ||
			(affectedTupleCount == currentAffectedTupleCount))
		{
			affectedTupleCount = currentAffectedTupleCount;
		}
		else
		{
			ereport(WARNING, (errmsg("modified %d tuples, but expected to modify %d",
									 currentAffectedTupleCount, affectedTupleCount),
							  errdetail("modified placement on %s:%d",
										nodeName, nodePort)));
		}

		PQclear(result);
	}

	/* if all placements failed, error out */
	if (list_length(failedPlacementList) == list_length(task->taskPlacementList))
	{
		ereport(ERROR, (errmsg("could not modify any active placements")));
	}

	/* otherwise, mark failed placements as inactive: they're stale */
	foreach(failedPlacementCell, failedPlacementList)
	{
		ShardPlacement *failedPlacement = (ShardPlacement *) lfirst(failedPlacementCell);
		uint64 shardLength = 0;

		DeleteShardPlacementRow(failedPlacement->shardId, failedPlacement->nodeName,
								failedPlacement->nodePort);
		InsertShardPlacementRow(failedPlacement->shardId, FILE_INACTIVE, shardLength,
								failedPlacement->nodeName, failedPlacement->nodePort);
	}

	return affectedTupleCount;
}


static void
DeparseShardQuery(Query *query, Task *task, StringInfo queryString)
{
	uint64 shardId = task->anchorShardId;
	Oid relid = ((RangeTblEntry *) linitial(query->rtable))->relid;

	deparse_shard_query(query, relid, shardId, queryString);
}


/*
 * ExecuteSingleShardSelect executes, if not done already, the remote select query and
 * sends the resulting tuples to the given destination receiver. If the query fails on a
 * given placement, the function attempts it on its replica.
 */
static void
ExecuteSingleShardSelect(QueryDesc *queryDesc, uint64 tupleCount, Task *task,
						 EState *executorState, TupleDesc tupleDescriptor,
						 DestReceiver *destination)
{
	bool resultsOK = false;
	TupleTableSlot *tupleTableSlot = NULL;
	MaterialState *routerState = (MaterialState *) queryDesc->planstate;
	Tuplestorestate *tupleStore = routerState->tuplestorestate;
	uint64 currentTupleCount = 0;

	/* initialize tuplestore for the first call */
	if (routerState->tuplestorestate == NULL)
	{
		routerState->tuplestorestate = tuplestore_begin_heap(false, false, work_mem);
		tupleStore = routerState->tuplestorestate;

		resultsOK = ExecuteTaskAndStoreResults(task, tupleDescriptor, tupleStore);
		if (!resultsOK)
		{
			ereport(ERROR, (errmsg("could not receive query results")));
		}
	}

	tupleTableSlot = MakeSingleTupleTableSlot(tupleDescriptor);

	/* startup the tuple receiver */
	(*destination->rStartup)(destination, CMD_SELECT, tupleDescriptor);

	/* iterate over tuples in tuple store, and send them to destination */
	for (;;)
	{
		bool nextTuple = tuplestore_gettupleslot(tupleStore, true, false, tupleTableSlot);
		if (!nextTuple)
		{
			break;
		}

		(*destination->receiveSlot)(tupleTableSlot, destination);
		executorState->es_processed++;

		ExecClearTuple(tupleTableSlot);

		currentTupleCount++;

		/*
		 * If numberTuples is zero fetch all tuples, otherwise stop after
		 * count tuples.
		 */
		if (tupleCount > 0 && tupleCount == currentTupleCount)
		{
			break;
		}
	}

	/* shutdown the tuple receiver */
	(*destination->rShutdown)(destination);

	ExecDropSingleTupleTableSlot(tupleTableSlot);
}


/*
 * ExecuteTaskAndStoreResults executes the task on the remote node, retrieves
 * the results and stores them in the given tuple store. If the task fails on
 * one of the placements, the function retries it on other placements.
 */
bool
ExecuteTaskAndStoreResults(Task *task, TupleDesc tupleDescriptor,
						   Tuplestorestate *tupleStore)
{
	bool resultsOK = false;
	List *taskPlacementList = task->taskPlacementList;
	ListCell *taskPlacementCell = NULL;

	/*
	 * Try to run the query to completion on one placement. If the query fails
	 * attempt the query on the next placement.
	 */
	foreach(taskPlacementCell, taskPlacementList)
	{
		ShardPlacement *taskPlacement = (ShardPlacement *) lfirst(taskPlacementCell);
		char *nodeName = taskPlacement->nodeName;
		int32 nodePort = taskPlacement->nodePort;
		bool queryOK = false;
		bool storedOK = false;

		PGconn *connection = GetOrEstablishConnection(nodeName, nodePort);
		if (connection == NULL)
		{
			continue;
		}

		queryOK = SendQueryInSingleRowMode(connection, task->queryString);
		if (!queryOK)
		{
			PurgeConnection(connection);
			continue;
		}

		storedOK = StoreQueryResult(connection, tupleDescriptor, tupleStore);
		if (storedOK)
		{
			resultsOK = true;
			break;
		}
		else
		{
			tuplestore_clear(tupleStore);
			PurgeConnection(connection);
		}
	}

	return resultsOK;
}


/*
 * SendQueryInSingleRowMode sends the given query on the connection in an
 * asynchronous way. The function also sets the single-row mode on the
 * connection so that we receive results a row at a time.
 */
static bool
SendQueryInSingleRowMode(PGconn *connection, char *query)
{
	int querySent = 0;
	int singleRowMode = 0;

	querySent = PQsendQuery(connection, query);
	if (querySent == 0)
	{
		ReportRemoteError(connection, NULL);
		return false;
	}

	singleRowMode = PQsetSingleRowMode(connection);
	if (singleRowMode == 0)
	{
		ReportRemoteError(connection, NULL);
		return false;
	}

	return true;
}


/*
 * StoreQueryResult gets the query results from the given connection, builds
 * tuples from the results and stores them in the given tuple-store. If the
 * function can't receive query results, it returns false. Note that this
 * function assumes the query has already been sent on the connection and the
 * tuplestore has earlier been initialized.
 */
static bool
StoreQueryResult(PGconn *connection, TupleDesc tupleDescriptor,
				 Tuplestorestate *tupleStore)
{
	AttInMetadata *attributeInputMetadata = TupleDescGetAttInMetadata(tupleDescriptor);
	uint32 expectedColumnCount = tupleDescriptor->natts;
	char **columnArray = (char **) palloc0(expectedColumnCount * sizeof(char *));
	MemoryContext ioContext = AllocSetContextCreate(CurrentMemoryContext,
													"StoreQueryResult",
													ALLOCSET_DEFAULT_MINSIZE,
													ALLOCSET_DEFAULT_INITSIZE,
													ALLOCSET_DEFAULT_MAXSIZE);

	Assert(tupleStore != NULL);

	for (;;)
	{
		uint32 rowIndex = 0;
		uint32 columnIndex = 0;
		uint32 rowCount = 0;
		uint32 columnCount = 0;
		ExecStatusType resultStatus = 0;

		PGresult *result = PQgetResult(connection);
		if (result == NULL)
		{
			break;
		}

		resultStatus = PQresultStatus(result);
		if ((resultStatus != PGRES_SINGLE_TUPLE) && (resultStatus != PGRES_TUPLES_OK))
		{
			ReportRemoteError(connection, result);
			PQclear(result);

			return false;
		}

		rowCount = PQntuples(result);
		columnCount = PQnfields(result);
		Assert(columnCount == expectedColumnCount);

		for (rowIndex = 0; rowIndex < rowCount; rowIndex++)
		{
			HeapTuple heapTuple = NULL;
			MemoryContext oldContext = NULL;
			memset(columnArray, 0, columnCount * sizeof(char *));

			for (columnIndex = 0; columnIndex < columnCount; columnIndex++)
			{
				if (PQgetisnull(result, rowIndex, columnIndex))
				{
					columnArray[columnIndex] = NULL;
				}
				else
				{
					columnArray[columnIndex] = PQgetvalue(result, rowIndex, columnIndex);
				}
			}

			/*
			 * Switch to a temporary memory context that we reset after each tuple. This
			 * protects us from any memory leaks that might be present in I/O functions
			 * called by BuildTupleFromCStrings.
			 */
			oldContext = MemoryContextSwitchTo(ioContext);

			heapTuple = BuildTupleFromCStrings(attributeInputMetadata, columnArray);

			MemoryContextSwitchTo(oldContext);

			tuplestore_puttuple(tupleStore, heapTuple);
			MemoryContextReset(ioContext);
		}

		PQclear(result);
	}

	pfree(columnArray);

	return true;
}


/*
 * RouterExecutorFinish cleans up after a distributed execution.
 */
void
RouterExecutorFinish(QueryDesc *queryDesc)
{
	EState *estate = queryDesc->estate;
	Assert(estate != NULL);

	estate->es_finished = true;
}


/*
 * RouterExecutorEnd cleans up the executor state after a distributed
 * execution.
 */
void
RouterExecutorEnd(QueryDesc *queryDesc)
{
	EState *estate = queryDesc->estate;
	MaterialState *routerState = (MaterialState *) queryDesc->planstate;

	if (routerState->tuplestorestate)
	{
		tuplestore_end(routerState->tuplestorestate);
	}

	Assert(estate != NULL);

	FreeExecutorState(estate);
	queryDesc->estate = NULL;
	queryDesc->totaltime = NULL;
}


/*
 * Walks each TargetEntry of the query, evaluates sub-expressions without Vars.
 */
static void
ExecuteFunctions(Query *query)
{
	CmdType commandType = query->commandType;
	ListCell *targetEntryCell = NULL;
	Node *modifiedNode = NULL;

	/* DELETE has no targetList */
	if (!(commandType == CMD_INSERT) && !(commandType == CMD_UPDATE))
	{
		return;
	}

	foreach(targetEntryCell, query->targetList)
	{
		TargetEntry *targetEntry = (TargetEntry *) lfirst(targetEntryCell);

		/* performance optimization for the most common cases */
		if (IsA(targetEntry->expr, Const) || IsA(targetEntry->expr, Var))
		{
			continue;
		}

		modifiedNode = PartiallyEvaluateExpression((Node *) targetEntry->expr);

		targetEntry->expr = (Expr *) modifiedNode;
	}
}


/*
 * Walks the expression, evaluates sub-expressions which don't contain Vars.
 *
 * The flow of control is a little convoluted to prevent ourselves from needing to walk
 * parts of the tree multiple times. When we walk a node which contains multiple
 * sub-trees we recurse and remember which parts of the tree contained a Var. If some
 * did and some didn't we evaluate the parts of the tree which didn't. If none of the
 * sub-trees contained a Var we do nothing besides reporting that fact.
 *
 * At the top-level of the expression we evaluate everything if no Vars were found.
 */
static Node * PartiallyEvaluateExpression(Node *expression)
{
	ExpressionWalkerState unused;
	InitializeWalkerState(&unused);
	unused.isTopLevel = true;

	return PartiallyEvaluateExpressionWalker(expression, &unused);
}


static Node * PartiallyEvaluateExpressionWalker(Node *expression,
		ExpressionWalkerState *parentState)
{
	ExpressionWalkerState childState;
	Node *copy = NULL;
	bool isBranch = false;
	bool containsVar = false;

	if (expression == NULL)
	{
		return expression;
	}

	/* pass any argument lists back to the mutator to copy and recurse for us */
	if (IsA(expression, List))
	{
		return expression_tree_mutator(expression,
									   PartiallyEvaluateExpressionWalker,
									   parentState);
	}

	InitializeWalkerState(&childState);

	if (IsA(expression, Var))
	{
		containsVar = true;
	}

	if (IsA(expression, FuncExpr) || IsA(expression, OpExpr))
	{
		/* Tell the next step that it should add itself to one of the subtree lists */
		childState.parentIsBranch = true;
		isBranch = true;
	}

	copy = expression_tree_mutator(expression,
								   PartiallyEvaluateExpressionWalker,
								   &childState);

	containsVar |= childState.containsVar;

	if (parentState->parentIsBranch)
	{
		if (containsVar)
		{
			parentState->subtreesWithVar = lappend(parentState->subtreesWithVar, copy);
			parentState->subtreeOrder = lappend_int(parentState->subtreeOrder, 0);
		}
		else
		{
			parentState->subtreesWithoutVar = lappend(parentState->subtreesWithoutVar,
													  copy);
			parentState->subtreeOrder = lappend_int(parentState->subtreeOrder, 1);
		}
	}

	/* never set containsVar=false because parentState is shared between sibling trees */
	if (containsVar)
	{
		parentState->containsVar = true;
	}

	if (isBranch && parentState->isTopLevel &&
		list_length(childState.subtreesWithVar) == 0)
	{
		return EvaluateExpression(expression);
	}

	if ((list_length(childState.subtreesWithVar) != 0) &&
		(list_length(childState.subtreesWithoutVar) != 0))
	{
		if (IsA(expression, FuncExpr))
		{
			((FuncExpr *) copy)->args = RewriteArgs(&childState);
		}

		if (IsA(expression, OpExpr))
		{
			((OpExpr *) copy)->args = RewriteArgs(&childState);
		}
	}

	return copy;
}

/* evaluate every non-Var arg and return an argument list */
static List * RewriteArgs(ExpressionWalkerState *state)
{
	List *rewrittenArgs = NULL;
	ListCell *nextArgContainsVarCell = NULL;
	int nextArgContainsVar = 0;

	foreach(nextArgContainsVarCell, state->subtreeOrder)
	{
		nextArgContainsVar = lfirst_int(nextArgContainsVarCell);
		if (nextArgContainsVar)
		{
			Node *original = (Node *)linitial(state->subtreesWithoutVar);
			Node *evaluated = EvaluateExpression(original);
			rewrittenArgs = lappend(rewrittenArgs, evaluated);
			state->subtreesWithoutVar =
				list_delete_first(state->subtreesWithoutVar);
		}
		else
		{
			rewrittenArgs = lappend(rewrittenArgs,
									linitial(state->subtreesWithVar));
			state->subtreesWithVar = list_delete_first(state->subtreesWithVar);
		}
	}

	return rewrittenArgs;
}

static Node * EvaluateExpression(Node *expression)
{
	if(IsA(expression, FuncExpr))
	{
		FuncExpr *expr = (FuncExpr *)expression;

		return (Node *) citus_evaluate_expr((Expr *) expr,
									  expr->funcresulttype,
									  exprTypmod((Node *) expr),
									  expr->funccollid);
	}

	if(IsA(expression, OpExpr))
	{
		OpExpr *expr = (OpExpr *)expression;

		return (Node *) citus_evaluate_expr((Expr *) expr,
									  expr->opresulttype,
									  exprTypmod((Node *) expr),
									  expr->opcollid);
	}

	// TODO: What else should we evaluate here?
	// What else can contain a function call?
	return expression;
}


static void InitializeWalkerState(ExpressionWalkerState *state)
{
	state->isTopLevel = false;
	state->containsVar = false;
	state->parentIsBranch = false;
	state->subtreesWithVar = NULL;
	state->subtreesWithoutVar = NULL;
	state->subtreeOrder = NULL;
}

/*
 * pre-evaluate a constant expression, a copy of pg's evaluate_expr
 *
 * We use the executor's routine ExecEvalExpr() to avoid duplication of
 * code and ensure we get the same result as the executor would get.
 */
Expr *
citus_evaluate_expr(Expr *expr, Oid result_type, int32 result_typmod,
					Oid result_collation)
{
	EState	   *estate;
	ExprState  *exprstate;
	MemoryContext oldcontext;
	Datum		const_val;
	bool		const_is_null;
	int16		resultTypLen;
	bool		resultTypByVal;

	/*
	 * To use the executor, we need an EState.
	 */
	estate = CreateExecutorState();

	/* We can use the estate's working context to avoid memory leaks. */
	oldcontext = MemoryContextSwitchTo(estate->es_query_cxt);

	/* Make sure any opfuncids are filled in. */
	fix_opfuncids((Node *) expr);

	/*
	 * Prepare expr for execution.  (Note: we can't use ExecPrepareExpr
	 * because it'd result in recursively invoking eval_const_expressions.)
	 */
	exprstate = ExecInitExpr(expr, NULL);

	/*
	 * And evaluate it.
	 *
	 * It is OK to use a default econtext because none of the ExecEvalExpr()
	 * code used in this situation will use econtext.  That might seem
	 * fortuitous, but it's not so unreasonable --- a constant expression does
	 * not depend on context, by definition, n'est ce pas?
	 */
	const_val = ExecEvalExprSwitchContext(exprstate,
										  GetPerTupleExprContext(estate),
										  &const_is_null, NULL);

	/* Get info needed about result datatype */
	get_typlenbyval(result_type, &resultTypLen, &resultTypByVal);

	/* Get back to outer memory context */
	MemoryContextSwitchTo(oldcontext);

	/*
	 * Must copy result out of sub-context used by expression eval.
	 *
	 * Also, if it's varlena, forcibly detoast it.  This protects us against
	 * storing TOAST pointers into plans that might outlive the referenced
	 * data.  (makeConst would handle detoasting anyway, but it's worth a few
	 * extra lines here so that we can do the copy and detoast in one step.)
	 */
	if (!const_is_null)
	{
		if (resultTypLen == -1)
			const_val = PointerGetDatum(PG_DETOAST_DATUM_COPY(const_val));
		else
			const_val = datumCopy(const_val, resultTypByVal, resultTypLen);
	}

	/* Release all the junk we just created */
	FreeExecutorState(estate);

	/*
	 * Make the constant result node.
	 */
	return (Expr *) makeConst(result_type, result_typmod, result_collation,
							  resultTypLen,
							  const_val, const_is_null,
							  resultTypByVal);
}
