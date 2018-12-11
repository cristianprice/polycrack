#include "postgres.h"

#include "access/htup_details.h"
#include "access/sysattr.h"
#include "catalog/pg_class.h"
#include "commands/defrem.h"
#include "commands/explain.h"
#include "commands/vacuum.h"
#include "foreign/fdwapi.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/cost.h"
#include "optimizer/clauses.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/var.h"
#include "optimizer/tlist.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/sampling.h"
#include "utils/selfuncs.h"
#include "polycrack_fdw.h"
#include "parser/parsetree.h"

PG_MODULE_MAGIC
;

/* Default CPU cost to start up a foreign query. */
#define DEFAULT_FDW_STARTUP_COST	100.0

/* Default CPU cost to process 1 row (above and beyond cpu_tuple_cost). */
#define DEFAULT_FDW_TUPLE_COST		0.01

/* If no remote estimates, assume a sort costs 20% extra */
#define DEFAULT_FDW_SORT_MULTIPLIER 1.2

/*
 * SQL functions
 */
extern Datum polycrack_fdw_handler(PG_FUNCTION_ARGS);
extern Datum polycrack_fdw_validator(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(polycrack_fdw_handler);
PG_FUNCTION_INFO_V1(polycrack_fdw_validator);

static bool ec_member_matches_foreign(PlannerInfo *root, RelOptInfo *rel, EquivalenceClass *ec, EquivalenceMember *em,
		void *arg);
static void add_paths_with_pathkeys_for_rel(PlannerInfo *root, RelOptInfo *rel, Path *epq_path);

/* callback functions */
#if (PG_VERSION_NUM >= 90200)
static void polycrackGetForeignRelSize(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid);

static void polycrackGetForeignPaths(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid);

#if (PG_VERSION_NUM < 90500)
static ForeignScan *polycrackGetForeignPlan(PlannerInfo *root,
		RelOptInfo *baserel,
		Oid foreigntableid,
		ForeignPath *best_path,
		List *tlist,
		List *scan_clauses);
#else
static ForeignScan *polycrackGetForeignPlan(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid,
		ForeignPath *best_path, List *tlist, List *scan_clauses, Plan *outer_plan);
#endif

#else /* 9.1 only */
static FdwPlan *polycrackPlanForeignScan(Oid foreigntableid, PlannerInfo *root, RelOptInfo *baserel);
#endif

static void polycrackBeginForeignScan(ForeignScanState *node, int eflags);

static TupleTableSlot *polycrackIterateForeignScan(ForeignScanState *node);

static void polycrackReScanForeignScan(ForeignScanState *node);

static void polycrackEndForeignScan(ForeignScanState *node);

#if (PG_VERSION_NUM >= 90300)
static void polycrackAddForeignUpdateTargets(Query *parsetree, RangeTblEntry *target_rte, Relation target_relation);

static List *polycrackPlanForeignModify(PlannerInfo *root, ModifyTable *plan, Index resultRelation, int subplan_index);

static void polycrackBeginForeignModify(ModifyTableState *mtstate, ResultRelInfo *rinfo, List *fdw_private,
		int subplan_index, int eflags);

static TupleTableSlot *polycrackExecForeignInsert(EState *estate, ResultRelInfo *rinfo, TupleTableSlot *slot,
		TupleTableSlot *planSlot);

static TupleTableSlot *polycrackExecForeignUpdate(EState *estate, ResultRelInfo *rinfo, TupleTableSlot *slot,
		TupleTableSlot *planSlot);

static TupleTableSlot *polycrackExecForeignDelete(EState *estate, ResultRelInfo *rinfo, TupleTableSlot *slot,
		TupleTableSlot *planSlot);

static void polycrackEndForeignModify(EState *estate, ResultRelInfo *rinfo);

static int polycrackIsForeignRelUpdatable(Relation rel);

#endif

static void polycrackExplainForeignScan(ForeignScanState *node, struct ExplainState * es);

#if (PG_VERSION_NUM >= 90300)
static void polycrackExplainForeignModify(ModifyTableState *mtstate, ResultRelInfo *rinfo, List *fdw_private,
		int subplan_index, struct ExplainState * es);
#endif

#if (PG_VERSION_NUM >= 90200)
static bool polycrackAnalyzeForeignTable(Relation relation, AcquireSampleRowsFunc *func, BlockNumber *totalpages);
#endif

#if (PG_VERSION_NUM >= 90500)

static void polycrackGetForeignJoinPaths(PlannerInfo *root, RelOptInfo *joinrel, RelOptInfo *outerrel,
		RelOptInfo *innerrel, JoinType jointype, JoinPathExtraData *extra);

static RowMarkType polycrackGetForeignRowMarkType(RangeTblEntry *rte, LockClauseStrength strength);

static HeapTuple polycrackRefetchForeignRow(EState *estate, ExecRowMark *erm, Datum rowid,
bool *updated);

static List *polycrackImportForeignSchema(ImportForeignSchemaStmt *stmt, Oid serverOid);

#endif

/*
 * structures used by the FDW
 *
 * These next structures are not actually used by polycrack,but something like
 * them will be needed by anything more complicated that does actual work.
 */

/*
 * Describes the valid options for objects that use this wrapper.
 */
struct polycrackFdwOption {
	const char *optname;
	Oid optcontext; /* Oid of catalog in which option may appear */
};

typedef struct {
	Expr *current; /* current expr, or NULL if not yet found */
	List *already_used; /* expressions already dealt with */
} ec_member_foreign_arg;

/*
 * The plan state is set up in polycrackGetForeignRelSize and stashed away in
 * baserel->fdw_private and fetched in polycrackGetForeignPaths.
 */
typedef struct {
	char *foo;
	int bar;
} PolycrackFdwPlanState;

/*
 * The scan state is for maintaining state for a scan, eiher for a
 * SELECT or UPDATE or DELETE.
 *
 * It is set up in polycrackBeginForeignScan and stashed in node->fdw_state
 * and subsequently used in polycrackIterateForeignScan,
 * polycrackEndForeignScan and polycrackReScanForeignScan.
 */
typedef struct {
	char *baz;
	int blurfl;
} PolycrackFdwScanState;

/*
 * The modify state is for maintaining state of modify operations.
 *
 * It is set up in polycrackBeginForeignModify and stashed in
 * rinfo->ri_FdwState and subsequently used in polycrackExecForeignInsert,
 * polycrackExecForeignUpdate, polycrackExecForeignDelete and
 * polycrackEndForeignModify.
 */
typedef struct {
	char *chimp;
	int chump;
} PolycrackFdwModifyState;

Datum polycrack_fdw_handler(PG_FUNCTION_ARGS) {
	FdwRoutine *fdwroutine = makeNode(FdwRoutine);

	elog(DEBUG1, "entering function %s", __func__);

	/*
	 * assign the handlers for the FDW
	 *
	 * This function might be called a number of times. In particular, it is
	 * likely to be called for each INSERT statement. For an explanation, see
	 * core postgres file src/optimizer/plan/createplan.c where it calls
	 * GetFdwRoutineByRelId(().
	 */

	/* Required by notations: S=SELECT I=INSERT U=UPDATE D=DELETE */

	/* these are required */
#if (PG_VERSION_NUM >= 90200)
	fdwroutine->GetForeignRelSize = polycrackGetForeignRelSize; /* S U D */
	fdwroutine->GetForeignPaths = polycrackGetForeignPaths; /* S U D */
	fdwroutine->GetForeignPlan = polycrackGetForeignPlan; /* S U D */
#else
	fdwroutine->PlanForeignScan = polycrackPlanForeignScan; /* S */
#endif
	fdwroutine->BeginForeignScan = polycrackBeginForeignScan; /* S U D */
	fdwroutine->IterateForeignScan = polycrackIterateForeignScan; /* S */
	fdwroutine->ReScanForeignScan = polycrackReScanForeignScan; /* S */
	fdwroutine->EndForeignScan = polycrackEndForeignScan; /* S U D */

	/* remainder are optional - use NULL if not required */
	/* support for insert / update / delete */
#if (PG_VERSION_NUM >= 90300)
	fdwroutine->IsForeignRelUpdatable = polycrackIsForeignRelUpdatable;
	fdwroutine->AddForeignUpdateTargets = polycrackAddForeignUpdateTargets; /* U D */
	fdwroutine->PlanForeignModify = polycrackPlanForeignModify; /* I U D */
	fdwroutine->BeginForeignModify = polycrackBeginForeignModify; /* I U D */
	fdwroutine->ExecForeignInsert = polycrackExecForeignInsert; /* I */
	fdwroutine->ExecForeignUpdate = polycrackExecForeignUpdate; /* U */
	fdwroutine->ExecForeignDelete = polycrackExecForeignDelete; /* D */
	fdwroutine->EndForeignModify = polycrackEndForeignModify; /* I U D */
#endif

	/* support for EXPLAIN */
	fdwroutine->ExplainForeignScan = polycrackExplainForeignScan; /* EXPLAIN S U D */
#if (PG_VERSION_NUM >= 90300)
	fdwroutine->ExplainForeignModify = polycrackExplainForeignModify; /* EXPLAIN I U D */
#endif

#if (PG_VERSION_NUM >= 90200)
	/* support for ANALYSE */
	fdwroutine->AnalyzeForeignTable = polycrackAnalyzeForeignTable; /* ANALYZE only */
#endif

#if (PG_VERSION_NUM >= 90500)
	/* Support functions for IMPORT FOREIGN SCHEMA */
	fdwroutine->ImportForeignSchema = polycrackImportForeignSchema;

	/* Support for scanning foreign joins */
	fdwroutine->GetForeignJoinPaths = polycrackGetForeignJoinPaths;

	/* Support for locking foreign rows */
	fdwroutine->GetForeignRowMarkType = polycrackGetForeignRowMarkType;
	fdwroutine->RefetchForeignRow = polycrackRefetchForeignRow;

#endif

	PG_RETURN_POINTER(fdwroutine);
}

Datum polycrack_fdw_validator(PG_FUNCTION_ARGS) {
	List *options_list = untransformRelOptions(PG_GETARG_DATUM(0));

	elog(DEBUG1, "entering function %s", __func__);

	/* make sure the options are valid */

	/* no options are supported */

	if (list_length(options_list) > 0)
		ereport(ERROR, (errcode(ERRCODE_FDW_INVALID_OPTION_NAME), errmsg("invalid options"), errhint("Polycrack FDW does not support any options")));

	PG_RETURN_VOID() ;
}

/*
 * get_useful_ecs_for_relation
 *		Determine which EquivalenceClasses might be involved in useful
 *		orderings of this relation.
 *
 * This function is in some respects a mirror image of the core function
 * pathkeys_useful_for_merging: for a regular table, we know what indexes
 * we have and want to test whether any of them are useful.  For a foreign
 * table, we don't know what indexes are present on the remote side but
 * want to speculate about which ones we'd like to use if they existed.
 *
 * This function returns a list of potentially-useful equivalence classes,
 * but it does not guarantee that an EquivalenceMember exists which contains
 * Vars only from the given relation.  For example, given ft1 JOIN t1 ON
 * ft1.x + t1.x = 0, this function will say that the equivalence class
 * containing ft1.x + t1.x is potentially useful.  Supposing ft1 is remote and
 * t1 is local (or on a different server), it will turn out that no useful
 * ORDER BY clause can be generated.  It's not our job to figure that out
 * here; we're only interested in identifying relevant ECs.
 */
static List* get_useful_ecs_for_relation(PlannerInfo *root, RelOptInfo *rel) {
	List *useful_eclass_list = NIL;
	ListCell *lc;
	Relids relids;

	/*
	 * First, consider whether any active EC is potentially useful for a merge
	 * join against this relation.
	 */
	if (rel->has_eclass_joins) {
		foreach(lc, root->eq_classes)
		{
			EquivalenceClass *cur_ec = (EquivalenceClass *) lfirst(lc);

			if (eclass_useful_for_merging(root, cur_ec, rel))
				useful_eclass_list = lappend(useful_eclass_list, cur_ec);
		}
	}

	/*
	 * Next, consider whether there are any non-EC derivable join clauses that
	 * are merge-joinable.  If the joininfo list is empty, we can exit
	 * quickly.
	 */
	if (rel->joininfo == NIL)
		return useful_eclass_list;

	/* If this is a child rel, we must use the topmost parent rel to search. */
	if (IS_OTHER_REL(rel)) {
		Assert(!bms_is_empty(rel->top_parent_relids));
		relids = rel->top_parent_relids;
	} else
		relids = rel->relids;

	/* Check each join clause in turn. */
	foreach(lc, rel->joininfo)
	{
		RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(lc);

		/* Consider only mergejoinable clauses */
		if (restrictinfo->mergeopfamilies == NIL)
			continue;

		/* Make sure we've got canonical ECs. */
		update_mergeclause_eclasses(root, restrictinfo);

		/*
		 * restrictinfo->mergeopfamilies != NIL is sufficient to guarantee
		 * that left_ec and right_ec will be initialized, per comments in
		 * distribute_qual_to_rels.
		 *
		 * We want to identify which side of this merge-joinable clause
		 * contains columns from the relation produced by this RelOptInfo. We
		 * test for overlap, not containment, because there could be extra
		 * relations on either side.  For example, suppose we've got something
		 * like ((A JOIN B ON A.x = B.x) JOIN C ON A.y = C.y) LEFT JOIN D ON
		 * A.y = D.y.  The input rel might be the joinrel between A and B, and
		 * we'll consider the join clause A.y = D.y. relids contains a
		 * relation not involved in the join class (B) and the equivalence
		 * class for the left-hand side of the clause contains a relation not
		 * involved in the input rel (C).  Despite the fact that we have only
		 * overlap and not containment in either direction, A.y is potentially
		 * useful as a sort column.
		 *
		 * Note that it's even possible that relids overlaps neither side of
		 * the join clause.  For example, consider A LEFT JOIN B ON A.x = B.x
		 * AND A.x = 1.  The clause A.x = 1 will appear in B's joininfo list,
		 * but overlaps neither side of B.  In that case, we just skip this
		 * join clause, since it doesn't suggest a useful sort order for this
		 * relation.
		 */
		if (bms_overlap(relids, restrictinfo->right_ec->ec_relids))
			useful_eclass_list = list_append_unique_ptr(useful_eclass_list, restrictinfo->right_ec);
		else if (bms_overlap(relids, restrictinfo->left_ec->ec_relids))
			useful_eclass_list = list_append_unique_ptr(useful_eclass_list, restrictinfo->left_ec);
	}

	return useful_eclass_list;
}

/*
 * get_useful_pathkeys_for_relation
 *		Determine which orderings of a relation might be useful.
 *
 * Getting data in sorted order can be useful either because the requested
 * order matches the final output ordering for the overall query we're
 * planning, or because it enables an efficient merge join.  Here, we try
 * to figure out which pathkeys to consider.
 */
static List* get_useful_pathkeys_for_relation(PlannerInfo *root, RelOptInfo *rel) {
	List *useful_pathkeys_list = NIL;
	List *useful_eclass_list;
	PgFdwRelationInfo *fpinfo = (PgFdwRelationInfo *) rel->fdw_private;
	EquivalenceClass *query_ec = NULL;
	ListCell *lc;

	/*
	 * Pushing the query_pathkeys to the remote server is always worth
	 * considering, because it might let us avoid a local sort.
	 */
	if (root->query_pathkeys) {
		bool query_pathkeys_ok = true;

		foreach(lc, root->query_pathkeys)
		{
			PathKey *pathkey = (PathKey *) lfirst(lc);
			EquivalenceClass *pathkey_ec = pathkey->pk_eclass;
			Expr *em_expr;

			/*
			 * The planner and executor don't have any clever strategy for
			 * taking data sorted by a prefix of the query's pathkeys and
			 * getting it to be sorted by all of those pathkeys. We'll just
			 * end up resorting the entire data set.  So, unless we can push
			 * down all of the query pathkeys, forget it.
			 *
			 * is_foreign_expr would detect volatile expressions as well, but
			 * checking ec_has_volatile here saves some cycles.
			 */
			if (pathkey_ec->ec_has_volatile || !(em_expr = find_em_expr_for_rel(pathkey_ec, rel))
					|| !is_foreign_expr(root, rel, em_expr)) {
				query_pathkeys_ok = false;
				break;
			}
		}

		if (query_pathkeys_ok)
			useful_pathkeys_list = list_make1(list_copy(root->query_pathkeys));
	}

	/*
	 * Even if we're not using remote estimates, having the remote side do the
	 * sort generally won't be any worse than doing it locally, and it might
	 * be much better if the remote side can generate data in the right order
	 * without needing a sort at all.  However, what we're going to do next is
	 * try to generate pathkeys that seem promising for possible merge joins,
	 * and that's more speculative.  A wrong choice might hurt quite a bit, so
	 * bail out if we can't use remote estimates.
	 */
	if (!fpinfo->use_remote_estimate)
		return useful_pathkeys_list;

	/* Get the list of interesting EquivalenceClasses. */
	useful_eclass_list = get_useful_ecs_for_relation(root, rel);

	/* Extract unique EC for query, if any, so we don't consider it again. */
	if (list_length(root->query_pathkeys) == 1) {
		PathKey *query_pathkey = linitial(root->query_pathkeys);

		query_ec = query_pathkey->pk_eclass;
	}

	/*
	 * As a heuristic, the only pathkeys we consider here are those of length
	 * one.  It's surely possible to consider more, but since each one we
	 * choose to consider will generate a round-trip to the remote side, we
	 * need to be a bit cautious here.  It would sure be nice to have a local
	 * cache of information about remote index definitions...
	 */
	foreach(lc, useful_eclass_list)
	{
		EquivalenceClass *cur_ec = lfirst(lc);
		Expr *em_expr;
		PathKey *pathkey;

		/* If redundant with what we did above, skip it. */
		if (cur_ec == query_ec)
			continue;

		/* If no pushable expression for this rel, skip it. */
		em_expr = find_em_expr_for_rel(cur_ec, rel);
		if (em_expr == NULL || !is_foreign_expr(root, rel, em_expr))
			continue;

		/* Looks like we can generate a pathkey, so let's do it. */
		pathkey = make_canonical_pathkey(root, cur_ec, linitial_oid(cur_ec->ec_opfamilies),
		BTLessStrategyNumber,
		false);
		useful_pathkeys_list = lappend(useful_pathkeys_list, list_make1(pathkey));
	}

	return useful_pathkeys_list;
}

void estimate_path_cost_size(PlannerInfo *root, RelOptInfo *foreignrel, List *param_join_conds, List *pathkeys,
		double *p_rows, int *p_width, Cost *p_startup_cost, Cost *p_total_cost) {
	PgFdwRelationInfo *fpinfo = (PgFdwRelationInfo *) foreignrel->fdw_private;
	double rows;
	double retrieved_rows;
	int width;
	Cost startup_cost;
	Cost total_cost;
	Cost cpu_per_tuple;

	/*
	 * If the table or the server is configured to use remote estimates,
	 * connect to the foreign server and execute EXPLAIN to estimate the
	 * number of rows selected by the restriction+join clauses.  Otherwise,
	 * estimate rows using whatever statistics we have locally, in a way
	 * similar to ordinary tables.
	 */
	if (fpinfo->use_remote_estimate) {
		List *remote_param_join_conds;
		List *local_param_join_conds;
		StringInfoData sql;
		Selectivity local_sel;
		QualCost local_cost;
		List *fdw_scan_tlist = NIL;
		List *remote_conds;

		/* Required only to be passed to deparseSelectStmtForRel */
		List *retrieved_attrs;

		/*
		 * param_join_conds might contain both clauses that are safe to send
		 * across, and clauses that aren't.
		 */
		classifyConditions(root, foreignrel, param_join_conds, &remote_param_join_conds, &local_param_join_conds);

		/* Build the list of columns to be fetched from the foreign server. */
		if (IS_JOIN_REL(foreignrel) || IS_UPPER_REL(foreignrel))
			fdw_scan_tlist = build_tlist_to_deparse(foreignrel);
		else
			fdw_scan_tlist = NIL;

		/*
		 * The complete list of remote conditions includes everything from
		 * baserestrictinfo plus any extra join_conds relevant to this
		 * particular path.
		 */
		remote_conds = list_concat(list_copy(remote_param_join_conds), fpinfo->remote_conds);

		/*
		 * Construct EXPLAIN query including the desired SELECT, FROM, and
		 * WHERE clauses. Params and other-relation Vars are replaced by dummy
		 * values, so don't request params_list.
		 */
		initStringInfo(&sql);
		appendStringInfoString(&sql, "EXPLAIN ");
		deparseSelectStmtForRel(&sql, root, foreignrel, fdw_scan_tlist, remote_conds, pathkeys, false, &retrieved_attrs, NULL);

		/* Get the remote estimate */
//		conn = GetConnection(fpinfo->user, false);
//		get_remote_estimate(sql.data, conn, &rows, &width, &startup_cost, &total_cost);
//		ReleaseConnection(conn);
		retrieved_rows = rows;

		/* Factor in the selectivity of the locally-checked quals */
		local_sel = clauselist_selectivity(root, local_param_join_conds, foreignrel->relid, JOIN_INNER,
		NULL);
		local_sel *= fpinfo->local_conds_sel;

		rows = clamp_row_est(rows * local_sel);

		/* Add in the eval cost of the locally-checked quals */
		startup_cost += fpinfo->local_conds_cost.startup;
		total_cost += fpinfo->local_conds_cost.per_tuple * retrieved_rows;
		cost_qual_eval(&local_cost, local_param_join_conds, root);
		startup_cost += local_cost.startup;
		total_cost += local_cost.per_tuple * retrieved_rows;
	} else {
		Cost run_cost = 0;

		/*
		 * We don't support join conditions in this mode (hence, no
		 * parameterized paths can be made).
		 */
		Assert(param_join_conds == NIL);

		/*
		 * Use rows/width estimates made by set_baserel_size_estimates() for
		 * base foreign relations and set_joinrel_size_estimates() for join
		 * between foreign relations.
		 */
		rows = foreignrel->rows;
		width = foreignrel->reltarget->width;

		/* Back into an estimate of the number of retrieved rows. */
		retrieved_rows = clamp_row_est(rows / fpinfo->local_conds_sel);

		/*
		 * We will come here again and again with different set of pathkeys
		 * that caller wants to cost. We don't need to calculate the cost of
		 * bare scan each time. Instead, use the costs if we have cached them
		 * already.
		 */
		if (fpinfo->rel_startup_cost > 0 && fpinfo->rel_total_cost > 0) {
			startup_cost = fpinfo->rel_startup_cost;
			run_cost = fpinfo->rel_total_cost - fpinfo->rel_startup_cost;
		} else if (IS_JOIN_REL(foreignrel)) {
			PgFdwRelationInfo *fpinfo_i;
			PgFdwRelationInfo *fpinfo_o;
			QualCost join_cost;
			QualCost remote_conds_cost;
			double nrows;

			/* For join we expect inner and outer relations set */
			Assert(fpinfo->innerrel && fpinfo->outerrel);

			fpinfo_i = (PgFdwRelationInfo *) fpinfo->innerrel->fdw_private;
			fpinfo_o = (PgFdwRelationInfo *) fpinfo->outerrel->fdw_private;

			/* Estimate of number of rows in cross product */
			nrows = fpinfo_i->rows * fpinfo_o->rows;
			/* Clamp retrieved rows estimate to at most size of cross product */
			retrieved_rows = Min(retrieved_rows, nrows);

			/*
			 * The cost of foreign join is estimated as cost of generating
			 * rows for the joining relations + cost for applying quals on the
			 * rows.
			 */

			/*
			 * Calculate the cost of clauses pushed down to the foreign server
			 */
			cost_qual_eval(&remote_conds_cost, fpinfo->remote_conds, root);
			/* Calculate the cost of applying join clauses */
			cost_qual_eval(&join_cost, fpinfo->joinclauses, root);

			/*
			 * Startup cost includes startup cost of joining relations and the
			 * startup cost for join and other clauses. We do not include the
			 * startup cost specific to join strategy (e.g. setting up hash
			 * tables) since we do not know what strategy the foreign server
			 * is going to use.
			 */
			startup_cost = fpinfo_i->rel_startup_cost + fpinfo_o->rel_startup_cost;
			startup_cost += join_cost.startup;
			startup_cost += remote_conds_cost.startup;
			startup_cost += fpinfo->local_conds_cost.startup;

			/*
			 * Run time cost includes:
			 *
			 * 1. Run time cost (total_cost - startup_cost) of relations being
			 * joined
			 *
			 * 2. Run time cost of applying join clauses on the cross product
			 * of the joining relations.
			 *
			 * 3. Run time cost of applying pushed down other clauses on the
			 * result of join
			 *
			 * 4. Run time cost of applying nonpushable other clauses locally
			 * on the result fetched from the foreign server.
			 */
			run_cost = fpinfo_i->rel_total_cost - fpinfo_i->rel_startup_cost;
			run_cost += fpinfo_o->rel_total_cost - fpinfo_o->rel_startup_cost;
			run_cost += nrows * join_cost.per_tuple;
			nrows = clamp_row_est(nrows * fpinfo->joinclause_sel);
			run_cost += nrows * remote_conds_cost.per_tuple;
			run_cost += fpinfo->local_conds_cost.per_tuple * retrieved_rows;
		} else if (IS_UPPER_REL(foreignrel)) {
			PgFdwRelationInfo *ofpinfo;
			PathTarget *ptarget = foreignrel->reltarget;
			AggClauseCosts aggcosts;
			double input_rows;
			int numGroupCols;
			double numGroups = 1;

			/* Make sure the core code set the pathtarget. */
			Assert(ptarget != NULL);

			/*
			 * This cost model is mixture of costing done for sorted and
			 * hashed aggregates in cost_agg().  We are not sure which
			 * strategy will be considered at remote side, thus for
			 * simplicity, we put all startup related costs in startup_cost
			 * and all finalization and run cost are added in total_cost.
			 *
			 * Also, core does not care about costing HAVING expressions and
			 * adding that to the costs.  So similarly, here too we are not
			 * considering remote and local conditions for costing.
			 */

			ofpinfo = (PgFdwRelationInfo *) fpinfo->outerrel->fdw_private;

			/* Get rows and width from input rel */
			input_rows = ofpinfo->rows;
			width = ofpinfo->width;

			/* Collect statistics about aggregates for estimating costs. */
			MemSet(&aggcosts, 0, sizeof(AggClauseCosts));
			if (root->parse->hasAggs) {
				get_agg_clause_costs(root, (Node *) fpinfo->grouped_tlist, AGGSPLIT_SIMPLE, &aggcosts);

				/*
				 * The cost of aggregates in the HAVING qual will be the same
				 * for each child as it is for the parent, so there's no need
				 * to use a translated version of havingQual.
				 */
				get_agg_clause_costs(root, (Node *) root->parse->havingQual, AGGSPLIT_SIMPLE, &aggcosts);
			}

			/* Get number of grouping columns and possible number of groups */
			numGroupCols = list_length(root->parse->groupClause);
			numGroups =
					estimate_num_groups(root, get_sortgrouplist_exprs(root->parse->groupClause, fpinfo->grouped_tlist), input_rows, NULL);

			/*
			 * Number of rows expected from foreign server will be same as
			 * that of number of groups.
			 */
			rows = retrieved_rows = numGroups;

			/*-----
			 * Startup cost includes:
			 *	  1. Startup cost for underneath input relation
			 *	  2. Cost of performing aggregation, per cost_agg()
			 *	  3. Startup cost for PathTarget eval
			 *-----
			 */
			startup_cost = ofpinfo->rel_startup_cost;
			startup_cost += aggcosts.transCost.startup;
			startup_cost += aggcosts.transCost.per_tuple * input_rows;
			startup_cost += (cpu_operator_cost * numGroupCols) * input_rows;
			startup_cost += ptarget->cost.startup;

			/*-----
			 * Run time cost includes:
			 *	  1. Run time cost of underneath input relation
			 *	  2. Run time cost of performing aggregation, per cost_agg()
			 *	  3. PathTarget eval cost for each output row
			 *-----
			 */
			run_cost = ofpinfo->rel_total_cost - ofpinfo->rel_startup_cost;
			run_cost += aggcosts.finalCost * numGroups;
			run_cost += cpu_tuple_cost * numGroups;
			run_cost += ptarget->cost.per_tuple * numGroups;
		} else {
			/* Clamp retrieved rows estimates to at most foreignrel->tuples. */
			retrieved_rows = Min(retrieved_rows, foreignrel->tuples);

			/*
			 * Cost as though this were a seqscan, which is pessimistic.  We
			 * effectively imagine the local_conds are being evaluated
			 * remotely, too.
			 */
			startup_cost = 0;
			run_cost = 0;
			run_cost += seq_page_cost * foreignrel->pages;

			startup_cost += foreignrel->baserestrictcost.startup;
			cpu_per_tuple = cpu_tuple_cost + foreignrel->baserestrictcost.per_tuple;
			run_cost += cpu_per_tuple * foreignrel->tuples;
		}

		/*
		 * Without remote estimates, we have no real way to estimate the cost
		 * of generating sorted output.  It could be free if the query plan
		 * the remote side would have chosen generates properly-sorted output
		 * anyway, but in most cases it will cost something.  Estimate a value
		 * high enough that we won't pick the sorted path when the ordering
		 * isn't locally useful, but low enough that we'll err on the side of
		 * pushing down the ORDER BY clause when it's useful to do so.
		 */
		if (pathkeys != NIL) {
			startup_cost *= DEFAULT_FDW_SORT_MULTIPLIER;
			run_cost *= DEFAULT_FDW_SORT_MULTIPLIER;
		}

		total_cost = startup_cost + run_cost;
	}

	/*
	 * Cache the costs for scans without any pathkeys or parameterization
	 * before adding the costs for transferring data from the foreign server.
	 * These costs are useful for costing the join between this relation and
	 * another foreign relation or to calculate the costs of paths with
	 * pathkeys for this relation, when the costs can not be obtained from the
	 * foreign server. This function will be called at least once for every
	 * foreign relation without pathkeys and parameterization.
	 */
	if (pathkeys == NIL && param_join_conds == NIL) {
		fpinfo->rel_startup_cost = startup_cost;
		fpinfo->rel_total_cost = total_cost;
	}

	/*
	 * Add some additional cost factors to account for connection overhead
	 * (fdw_startup_cost), transferring data across the network
	 * (fdw_tuple_cost per retrieved row), and local manipulation of the data
	 * (cpu_tuple_cost per retrieved row).
	 */
	startup_cost += fpinfo->fdw_startup_cost;
	total_cost += fpinfo->fdw_startup_cost;
	total_cost += fpinfo->fdw_tuple_cost * retrieved_rows;
	total_cost += cpu_tuple_cost * retrieved_rows;

	/* Return results. */
	*p_rows = rows;
	*p_width = width;
	*p_startup_cost = startup_cost;
	*p_total_cost = total_cost;
}

Expr* find_em_expr_for_rel(EquivalenceClass *ec, RelOptInfo *rel) {
	ListCell *lc_em;

	foreach(lc_em, ec->ec_members)
	{
		EquivalenceMember *em = lfirst(lc_em);

		if (bms_is_subset(em->em_relids, rel->relids) && !bms_is_empty(em->em_relids)) {
			/*
			 * If there is more than one equivalence member whose Vars are
			 * taken entirely from this relation, we'll be content to choose
			 * any one of those.
			 */
			return em->em_expr;
		}
	}

	/* We didn't find any suitable equivalence class expression */
	return NULL;
}

#if (PG_VERSION_NUM >= 90200)
static void polycrackGetForeignRelSize(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid) {
	/*
	 * Obtain relation size estimates for a foreign table. This is called at
	 * the beginning of planning for a query that scans a foreign table. root
	 * is the planner's global information about the query; baserel is the
	 * planner's information about this table; and foreigntableid is the
	 * pg_class OID of the foreign table. (foreigntableid could be obtained
	 * from the planner data structures, but it's passed explicitly to save
	 * effort.)
	 *
	 * This function should update baserel->rows to be the expected number of
	 * rows returned by the table scan, after accounting for the filtering
	 * done by the restriction quals. The initial value of baserel->rows is
	 * just a constant default estimate, which should be replaced if at all
	 * possible. The function may also choose to update baserel->width if it
	 * can compute a better estimate of the average result row width.
	 */

	PgFdwRelationInfo *fpinfo;
	ListCell *lc;
	RangeTblEntry *rte = planner_rt_fetch(baserel->relid, root);
	const char *namespace;
	const char *relname;
	const char *refname;

	/*
	 * We use PgFdwRelationInfo to pass various information to subsequent
	 * functions.
	 */
	fpinfo = (PgFdwRelationInfo *) palloc0(sizeof(PgFdwRelationInfo));
	baserel->fdw_private = (void *) fpinfo;

	/* Base foreign tables need to be pushed down always. */
	fpinfo->pushdown_safe = true;

	/* Look up foreign-table catalog info. */
	fpinfo->table = GetForeignTable(foreigntableid);
	fpinfo->server = GetForeignServer(fpinfo->table->serverid);

	/*
	 * Extract user-settable option values.  Note that per-table setting of
	 * use_remote_estimate overrides per-server setting.
	 */
	fpinfo->use_remote_estimate = false;
	fpinfo->fdw_startup_cost = DEFAULT_FDW_STARTUP_COST;
	fpinfo->fdw_tuple_cost = DEFAULT_FDW_TUPLE_COST;
	fpinfo->shippable_extensions = NIL;
	fpinfo->fetch_size = 100;

	//apply_server_options(fpinfo);
	//apply_table_options(fpinfo);

	/*
	 * If the table or the server is configured to use remote estimates,
	 * identify which user to do remote access as during planning.  This
	 * should match what ExecCheckRTEPerms() does.  If we fail due to lack of
	 * permissions, the query would have failed at runtime anyway.
	 */
	if (fpinfo->use_remote_estimate) {
		Oid userid = rte->checkAsUser ? rte->checkAsUser : GetUserId();

		fpinfo->user = GetUserMapping(userid, fpinfo->server->serverid);
	} else
		fpinfo->user = NULL;

	/*
	 * Identify which baserestrictinfo clauses can be sent to the remote
	 * server and which can't.
	 */
	classifyConditions(root, baserel, baserel->baserestrictinfo, &fpinfo->remote_conds, &fpinfo->local_conds);

	/*
	 * Identify which attributes will need to be retrieved from the remote
	 * server.  These include all attrs needed for joins or final output, plus
	 * all attrs used in the local_conds.  (Note: if we end up using a
	 * parameterized scan, it's possible that some of the join clauses will be
	 * sent to the remote and thus we wouldn't really need to retrieve the
	 * columns used in them.  Doesn't seem worth detecting that case though.)
	 */
	fpinfo->attrs_used = NULL;
	pull_varattnos((Node *) baserel->reltarget->exprs, baserel->relid, &fpinfo->attrs_used);
	foreach(lc, fpinfo->local_conds)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);

		pull_varattnos((Node *) rinfo->clause, baserel->relid, &fpinfo->attrs_used);
	}

	/*
	 * Compute the selectivity and cost of the local_conds, so we don't have
	 * to do it over again for each path.  The best we can do for these
	 * conditions is to estimate selectivity on the basis of local statistics.
	 */
	fpinfo->local_conds_sel = clauselist_selectivity(root, fpinfo->local_conds, baserel->relid, JOIN_INNER,
	NULL);

	cost_qual_eval(&fpinfo->local_conds_cost, fpinfo->local_conds, root);

	/*
	 * Set cached relation costs to some negative value, so that we can detect
	 * when they are set to some sensible costs during one (usually the first)
	 * of the calls to estimate_path_cost_size().
	 */
	fpinfo->rel_startup_cost = -1;
	fpinfo->rel_total_cost = -1;

	/*
	 * If the table or the server is configured to use remote estimates,
	 * connect to the foreign server and execute EXPLAIN to estimate the
	 * number of rows selected by the restriction clauses, as well as the
	 * average row width.  Otherwise, estimate using whatever statistics we
	 * have locally, in a way similar to ordinary tables.
	 */
	if (fpinfo->use_remote_estimate) {
		/*
		 * Get cost/size estimates with help of remote server.  Save the
		 * values in fpinfo so we don't need to do it again to generate the
		 * basic foreign path.
		 */
		estimate_path_cost_size(root, baserel, NIL, NIL, &fpinfo->rows, &fpinfo->width, &fpinfo->startup_cost, &fpinfo->total_cost);

		/* Report estimated baserel size to planner. */
		baserel->rows = fpinfo->rows;
		baserel->reltarget->width = fpinfo->width;
	} else {
		/*
		 * If the foreign table has never been ANALYZEd, it will have relpages
		 * and reltuples equal to zero, which most likely has nothing to do
		 * with reality.  We can't do a whole lot about that if we're not
		 * allowed to consult the remote server, but we can use a hack similar
		 * to plancat.c's treatment of empty relations: use a minimum size
		 * estimate of 10 pages, and divide by the column-datatype-based width
		 * estimate to get the corresponding number of tuples.
		 */
		if (baserel->pages == 0 && baserel->tuples == 0) {
			baserel->pages = 10;
			baserel->tuples = (10 * BLCKSZ) / (baserel->reltarget->width + MAXALIGN(SizeofHeapTupleHeader));
		}

		/* Estimate baserel size as best we can with local statistics. */
		set_baserel_size_estimates(root, baserel);

		/* Fill in basically-bogus cost estimates for use later. */
		estimate_path_cost_size(root, baserel, NIL, NIL, &fpinfo->rows, &fpinfo->width, &fpinfo->startup_cost, &fpinfo->total_cost);
	}

	/*
	 * Set the name of relation in fpinfo, while we are constructing it here.
	 * It will be used to build the string describing the join relation in
	 * EXPLAIN output. We can't know whether VERBOSE option is specified or
	 * not, so always schema-qualify the foreign table name.
	 */
	fpinfo->relation_name = makeStringInfo();
	namespace = get_namespace_name(get_rel_namespace(foreigntableid));
	relname = get_rel_name(foreigntableid);
	refname = rte->eref->aliasname;
	appendStringInfo(fpinfo->relation_name, "%s.%s", quote_identifier(namespace), quote_identifier(relname));
	if (*refname && strcmp(refname, relname) != 0)
		appendStringInfo(fpinfo->relation_name, " %s", quote_identifier(rte->eref->aliasname));

	/* No outer and inner relations. */
	fpinfo->make_outerrel_subquery = false;
	fpinfo->make_innerrel_subquery = false;
	fpinfo->lower_subquery_rels = NULL;
	/* Set the relation index. */
	fpinfo->relation_index = baserel->relid;

}

static bool ec_member_matches_foreign(PlannerInfo *root, RelOptInfo *rel, EquivalenceClass *ec, EquivalenceMember *em,
		void *arg) {
	ec_member_foreign_arg *state = (ec_member_foreign_arg *) arg;
	Expr *expr = em->em_expr;

	/*
	 * If we've identified what we're processing in the current scan, we only
	 * want to match that expression.
	 */
	if (state->current != NULL)
		return equal(expr, state->current);

	/*
	 * Otherwise, ignore anything we've already processed.
	 */
	if (list_member(state->already_used, expr))
		return false;

	/* This is the new target to process. */
	state->current = expr;
	return true;
}

static void add_paths_with_pathkeys_for_rel(PlannerInfo *root, RelOptInfo *rel, Path *epq_path) {
	List *useful_pathkeys_list = NIL; /* List of all pathkeys */
	ListCell *lc;

	useful_pathkeys_list = get_useful_pathkeys_for_relation(root, rel);

	/* Create one path for each set of pathkeys we found above. */
	foreach(lc, useful_pathkeys_list)
	{
		double rows;
		int width;
		Cost startup_cost;
		Cost total_cost;
		List *useful_pathkeys = lfirst(lc);
		Path *sorted_epq_path;

		estimate_path_cost_size(root, rel, NIL, useful_pathkeys, &rows, &width, &startup_cost, &total_cost);

		/*
		 * The EPQ path must be at least as well sorted as the path itself, in
		 * case it gets used as input to a mergejoin.
		 */
		sorted_epq_path = epq_path;
		if (sorted_epq_path != NULL && !pathkeys_contained_in(useful_pathkeys, sorted_epq_path->pathkeys))
			sorted_epq_path = (Path *) create_sort_path(root, rel, sorted_epq_path, useful_pathkeys, -1.0);

		add_path(rel, (Path *) create_foreignscan_path(root, rel,
		NULL, rows, startup_cost, total_cost, useful_pathkeys,
		NULL, sorted_epq_path,
		NIL));
	}
}

static void polycrackGetForeignPaths(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid) {
	/*
	 * Create possible access paths for a scan on a foreign table. This is
	 * called during query planning. The parameters are the same as for
	 * GetForeignRelSize, which has already been called.
	 *
	 * This function must generate at least one access path (ForeignPath node)
	 * for a scan on the foreign table and must call add_path to add each such
	 * path to baserel->pathlist. It's recommended to use
	 * create_foreignscan_path to build the ForeignPath nodes. The function
	 * can generate multiple access paths, e.g., a path which has valid
	 * pathkeys to represent a pre-sorted result. Each access path must
	 * contain cost estimates, and can contain any FDW-private information
	 * that is needed to identify the specific scan method intended.
	 */

	/*
	 * PolycrackFdwPlanState *plan_state = baserel->fdw_private;
	 */

	PgFdwRelationInfo *fpinfo = (PgFdwRelationInfo *) baserel->fdw_private;
	ForeignPath *path;
	List *ppi_list;
	ListCell *lc;

	/*
	 * Create simplest ForeignScan path node and add it to baserel.  This path
	 * corresponds to SeqScan path of regular tables (though depending on what
	 * baserestrict conditions we were able to send to remote, there might
	 * actually be an indexscan happening there).  We already did all the work
	 * to estimate cost and size of this path.
	 */
	path = create_foreignscan_path(root, baserel,
	NULL, /* default pathtarget */
	fpinfo->rows, fpinfo->startup_cost, fpinfo->total_cost,
	NIL, /* no pathkeys */
	NULL, /* no outer rel either */
	NULL, /* no extra plan */
	NIL); /* no fdw_private list */

	add_path(baserel, (Path *) path);

	/* Add paths with pathkeys */
	add_paths_with_pathkeys_for_rel(root, baserel, NULL);

	/*
	 * If we're not using remote estimates, stop here.  We have no way to
	 * estimate whether any join clauses would be worth sending across, so
	 * don't bother building parameterized paths.
	 */
	if (!fpinfo->use_remote_estimate)
		return;

	/*
	 * Thumb through all join clauses for the rel to identify which outer
	 * relations could supply one or more safe-to-send-to-remote join clauses.
	 * We'll build a parameterized path for each such outer relation.
	 *
	 * It's convenient to manage this by representing each candidate outer
	 * relation by the ParamPathInfo node for it.  We can then use the
	 * ppi_clauses list in the ParamPathInfo node directly as a list of the
	 * interesting join clauses for that rel.  This takes care of the
	 * possibility that there are multiple safe join clauses for such a rel,
	 * and also ensures that we account for unsafe join clauses that we'll
	 * still have to enforce locally (since the parameterized-path machinery
	 * insists that we handle all movable clauses).
	 */
	ppi_list = NIL;
	foreach(lc, baserel->joininfo)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
		Relids required_outer;
		ParamPathInfo *param_info;

		/* Check if clause can be moved to this rel */
		if (!join_clause_is_movable_to(rinfo, baserel))
			continue;

		/* See if it is safe to send to remote */
		if (!is_foreign_expr(root, baserel, rinfo->clause))
			continue;

		/* Calculate required outer rels for the resulting path */
		required_outer = bms_union(rinfo->clause_relids, baserel->lateral_relids);
		/* We do not want the foreign rel itself listed in required_outer */
		required_outer = bms_del_member(required_outer, baserel->relid);

		/*
		 * required_outer probably can't be empty here, but if it were, we
		 * couldn't make a parameterized path.
		 */
		if (bms_is_empty(required_outer))
			continue;

		/* Get the ParamPathInfo */
		param_info = get_baserel_parampathinfo(root, baserel, required_outer);
		Assert(param_info != NULL);

		/*
		 * Add it to list unless we already have it.  Testing pointer equality
		 * is OK since get_baserel_parampathinfo won't make duplicates.
		 */
		ppi_list = list_append_unique_ptr(ppi_list, param_info);
	}

	/*
	 * The above scan examined only "generic" join clauses, not those that
	 * were absorbed into EquivalenceClauses.  See if we can make anything out
	 * of EquivalenceClauses.
	 */
	if (baserel->has_eclass_joins) {
		/*
		 * We repeatedly scan the eclass list looking for column references
		 * (or expressions) belonging to the foreign rel.  Each time we find
		 * one, we generate a list of equivalence joinclauses for it, and then
		 * see if any are safe to send to the remote.  Repeat till there are
		 * no more candidate EC members.
		 */
		ec_member_foreign_arg arg;

		arg.already_used = NIL;
		for (;;) {
			List *clauses;

			/* Make clauses, skipping any that join to lateral_referencers */
			arg.current = NULL;
			clauses =
					generate_implied_equalities_for_column(root, baserel, ec_member_matches_foreign, (void *) &arg, baserel->lateral_referencers);

			/* Done if there are no more expressions in the foreign rel */
			if (arg.current == NULL) {
				Assert(clauses == NIL);
				break;
			}

			/* Scan the extracted join clauses */
			foreach(lc, clauses)
			{
				RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);
				Relids required_outer;
				ParamPathInfo *param_info;

				/* Check if clause can be moved to this rel */
				if (!join_clause_is_movable_to(rinfo, baserel))
					continue;

				/* See if it is safe to send to remote */
				if (!is_foreign_expr(root, baserel, rinfo->clause))
					continue;

				/* Calculate required outer rels for the resulting path */
				required_outer = bms_union(rinfo->clause_relids, baserel->lateral_relids);
				required_outer = bms_del_member(required_outer, baserel->relid);
				if (bms_is_empty(required_outer))
					continue;

				/* Get the ParamPathInfo */
				param_info = get_baserel_parampathinfo(root, baserel, required_outer);
				Assert(param_info != NULL);

				/* Add it to list unless we already have it */
				ppi_list = list_append_unique_ptr(ppi_list, param_info);
			}

			/* Try again, now ignoring the expression we found this time */
			arg.already_used = lappend(arg.already_used, arg.current);
		}
	}

	/*
	 * Now build a path for each useful outer relation.
	 */
	foreach(lc, ppi_list)
	{
		ParamPathInfo *param_info = (ParamPathInfo *) lfirst(lc);
		double rows;
		int width;
		Cost startup_cost;
		Cost total_cost;

		/* Get a cost estimate from the remote */
		estimate_path_cost_size(root, baserel, param_info->ppi_clauses, NIL, &rows, &width, &startup_cost, &total_cost);

		/*
		 * ppi_rows currently won't get looked at by anything, but still we
		 * may as well ensure that it matches our idea of the rowcount.
		 */
		param_info->ppi_rows = rows;

		/* Make the path */
		path = create_foreignscan_path(root, baserel,
		NULL, /* default pathtarget */
		rows, startup_cost, total_cost,
		NIL, /* no pathkeys */
		param_info->ppi_req_outer,
		NULL,
		NIL); /* no fdw_private list */
		add_path(baserel, (Path *) path);
	}
}

#if (PG_VERSION_NUM < 90500)
static ForeignScan *
polycrackGetForeignPlan(PlannerInfo *root,
		RelOptInfo *baserel,
		Oid foreigntableid,
		ForeignPath *best_path,
		List *tlist,
		List *scan_clauses)
#else
static ForeignScan *
polycrackGetForeignPlan(PlannerInfo *root, RelOptInfo *baserel, Oid foreigntableid, ForeignPath *best_path, List *tlist,
		List *scan_clauses, Plan *outer_plan)
#endif
{
	/*
	 * Create a ForeignScan plan node from the selected foreign access path.
	 * This is called at the end of query planning. The parameters are as for
	 * GetForeignRelSize, plus the selected ForeignPath (previously produced
	 * by GetForeignPaths), the target list to be emitted by the plan node,
	 * and the restriction clauses to be enforced by the plan node.
	 *
	 * This function must create and return a ForeignScan plan node; it's
	 * recommended to use make_foreignscan to build the ForeignScan node.
	 *
	 */

	/*
	 * PolycrackFdwPlanState *plan_state = baserel->fdw_private;
	 */

	Index scan_relid = baserel->relid;

	/*
	 * We have no native ability to evaluate restriction clauses, so we just
	 * put all the scan_clauses into the plan node's qual list for the
	 * executor to check. So all we have to do here is strip RestrictInfo
	 * nodes from the clauses and ignore pseudoconstants (which will be
	 * handled elsewhere).
	 */

	elog(DEBUG1, "entering function %s", __func__);

	scan_clauses = extract_actual_clauses(scan_clauses, false);

	/* Create the ForeignScan node */
#if(PG_VERSION_NUM < 90500)
	return make_foreignscan(tlist,
			scan_clauses,
			scan_relid,
			NIL, /* no expressions to evaluate */
			NIL); /* no private state either */
#else
	return make_foreignscan(tlist, scan_clauses, scan_relid,
	NIL, /* no expressions to evaluate */
	NIL, /* no private state either */
	NIL, /* no custom tlist */
	NIL, /* no remote quals */
	outer_plan);
#endif

}

#else

static FdwPlan *
polycrackPlanForeignScan(Oid foreigntableid, PlannerInfo *root, RelOptInfo *baserel)
{
	FdwPlan *fdwplan;
	fdwplan = makeNode(FdwPlan);
	fdwplan->fdw_private = NIL;
	fdwplan->startup_cost = 0;
	fdwplan->total_cost = 0;
	return fdwplan;
}

#endif

static void polycrackBeginForeignScan(ForeignScanState *node, int eflags) {
	/*
	 * Begin executing a foreign scan. This is called during executor startup.
	 * It should perform any initialization needed before the scan can start,
	 * but not start executing the actual scan (that should be done upon the
	 * first call to IterateForeignScan). The ForeignScanState node has
	 * already been created, but its fdw_state field is still NULL.
	 * Information about the table to scan is accessible through the
	 * ForeignScanState node (in particular, from the underlying ForeignScan
	 * plan node, which contains any FDW-private information provided by
	 * GetForeignPlan). eflags contains flag bits describing the executor's
	 * operating mode for this plan node.
	 *
	 * Note that when (eflags & EXEC_FLAG_EXPLAIN_ONLY) is true, this function
	 * should not perform any externally-visible actions; it should only do
	 * the minimum required to make the node state valid for
	 * ExplainForeignScan and EndForeignScan.
	 *
	 */

	PolycrackFdwScanState * scan_state = palloc0(sizeof(PolycrackFdwScanState));
	node->fdw_state = scan_state;

	elog(DEBUG1, "entering function %s", __func__);

}

static TupleTableSlot *
polycrackIterateForeignScan(ForeignScanState *node) {
	/*
	 * Fetch one row from the foreign source, returning it in a tuple table
	 * slot (the node's ScanTupleSlot should be used for this purpose). Return
	 * NULL if no more rows are available. The tuple table slot infrastructure
	 * allows either a physical or virtual tuple to be returned; in most cases
	 * the latter choice is preferable from a performance standpoint. Note
	 * that this is called in a short-lived memory context that will be reset
	 * between invocations. Create a memory context in BeginForeignScan if you
	 * need longer-lived storage, or use the es_query_cxt of the node's
	 * EState.
	 *
	 * The rows returned must match the column signature of the foreign table
	 * being scanned. If you choose to optimize away fetching columns that are
	 * not needed, you should insert nulls in those column positions.
	 *
	 * Note that PostgreSQL's executor doesn't care whether the rows returned
	 * violate any NOT NULL constraints that were defined on the foreign table
	 * columns — but the planner does care, and may optimize queries
	 * incorrectly if NULL values are present in a column declared not to
	 * contain them. If a NULL value is encountered when the user has declared
	 * that none should be present, it may be appropriate to raise an error
	 * (just as you would need to do in the case of a data type mismatch).
	 */

	/* ----
	 * PolycrackFdwScanState *scan_state =
	 *	 (PolycrackFdwScanState *) node->fdw_state;
	 * ----
	 */

	TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;

	elog(DEBUG1, "entering function %s", __func__);

	ExecClearTuple(slot);

	/* get the next record, if any, and fill in the slot */

	/* then return the slot */
	return slot;
}

static void polycrackReScanForeignScan(ForeignScanState *node) {
	/*
	 * Restart the scan from the beginning. Note that any parameters the scan
	 * depends on may have changed value, so the new scan does not necessarily
	 * return exactly the same rows.
	 */

	/* ----
	 * PolycrackFdwScanState *scan_state =
	 *	 (PolycrackFdwScanState *) node->fdw_state;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

}

static void polycrackEndForeignScan(ForeignScanState *node) {
	/*
	 * End the scan and release resources. It is normally not important to
	 * release palloc'd memory, but for example open files and connections to
	 * remote servers should be cleaned up.
	 */

	/* ----
	 * PolycrackFdwScanState *scan_state =
	 *	 (PolycrackFdwScanState *) node->fdw_state;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

}

#if (PG_VERSION_NUM >= 90300)
static void polycrackAddForeignUpdateTargets(Query *parsetree, RangeTblEntry *target_rte, Relation target_relation) {
	/*
	 * UPDATE and DELETE operations are performed against rows previously
	 * fetched by the table-scanning functions. The FDW may need extra
	 * information, such as a row ID or the values of primary-key columns, to
	 * ensure that it can identify the exact row to update or delete. To
	 * support that, this function can add extra hidden, or "junk", target
	 * columns to the list of columns that are to be retrieved from the
	 * foreign table during an UPDATE or DELETE.
	 *
	 * To do that, add TargetEntry items to parsetree->targetList, containing
	 * expressions for the extra values to be fetched. Each such entry must be
	 * marked resjunk = true, and must have a distinct resname that will
	 * identify it at execution time. Avoid using names matching ctidN or
	 * wholerowN, as the core system can generate junk columns of these names.
	 *
	 * This function is called in the rewriter, not the planner, so the
	 * information available is a bit different from that available to the
	 * planning routines. parsetree is the parse tree for the UPDATE or DELETE
	 * command, while target_rte and target_relation describe the target
	 * foreign table.
	 *
	 * If the AddForeignUpdateTargets pointer is set to NULL, no extra target
	 * expressions are added. (This will make it impossible to implement
	 * DELETE operations, though UPDATE may still be feasible if the FDW
	 * relies on an unchanging primary key to identify rows.)
	 */

	elog(DEBUG1, "entering function %s", __func__);

}

static List *
polycrackPlanForeignModify(PlannerInfo *root, ModifyTable *plan, Index resultRelation, int subplan_index) {
	/*
	 * Perform any additional planning actions needed for an insert, update,
	 * or delete on a foreign table. This function generates the FDW-private
	 * information that will be attached to the ModifyTable plan node that
	 * performs the update action. This private information must have the form
	 * of a List, and will be delivered to BeginForeignModify during the
	 * execution stage.
	 *
	 * root is the planner's global information about the query. plan is the
	 * ModifyTable plan node, which is complete except for the fdwPrivLists
	 * field. resultRelation identifies the target foreign table by its
	 * rangetable index. subplan_index identifies which target of the
	 * ModifyTable plan node this is, counting from zero; use this if you want
	 * to index into plan->plans or other substructure of the plan node.
	 *
	 * If the PlanForeignModify pointer is set to NULL, no additional
	 * plan-time actions are taken, and the fdw_private list delivered to
	 * BeginForeignModify will be NIL.
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return NULL;
}

static void polycrackBeginForeignModify(ModifyTableState *mtstate, ResultRelInfo *rinfo, List *fdw_private,
		int subplan_index, int eflags) {
	/*
	 * Begin executing a foreign table modification operation. This routine is
	 * called during executor startup. It should perform any initialization
	 * needed prior to the actual table modifications. Subsequently,
	 * ExecForeignInsert, ExecForeignUpdate or ExecForeignDelete will be
	 * called for each tuple to be inserted, updated, or deleted.
	 *
	 * mtstate is the overall state of the ModifyTable plan node being
	 * executed; global data about the plan and execution state is available
	 * via this structure. rinfo is the ResultRelInfo struct describing the
	 * target foreign table. (The ri_FdwState field of ResultRelInfo is
	 * available for the FDW to store any private state it needs for this
	 * operation.) fdw_private contains the private data generated by
	 * PlanForeignModify, if any. subplan_index identifies which target of the
	 * ModifyTable plan node this is. eflags contains flag bits describing the
	 * executor's operating mode for this plan node.
	 *
	 * Note that when (eflags & EXEC_FLAG_EXPLAIN_ONLY) is true, this function
	 * should not perform any externally-visible actions; it should only do
	 * the minimum required to make the node state valid for
	 * ExplainForeignModify and EndForeignModify.
	 *
	 * If the BeginForeignModify pointer is set to NULL, no action is taken
	 * during executor startup.
	 */

	PolycrackFdwModifyState *modify_state = palloc0(sizeof(PolycrackFdwModifyState));
	rinfo->ri_FdwState = modify_state;

	elog(DEBUG1, "entering function %s", __func__);

}

static TupleTableSlot *
polycrackExecForeignInsert(EState *estate, ResultRelInfo *rinfo, TupleTableSlot *slot, TupleTableSlot *planSlot) {
	/*
	 * Insert one tuple into the foreign table. estate is global execution
	 * state for the query. rinfo is the ResultRelInfo struct describing the
	 * target foreign table. slot contains the tuple to be inserted; it will
	 * match the rowtype definition of the foreign table. planSlot contains
	 * the tuple that was generated by the ModifyTable plan node's subplan; it
	 * differs from slot in possibly containing additional "junk" columns.
	 * (The planSlot is typically of little interest for INSERT cases, but is
	 * provided for completeness.)
	 *
	 * The return value is either a slot containing the data that was actually
	 * inserted (this might differ from the data supplied, for example as a
	 * result of trigger actions), or NULL if no row was actually inserted
	 * (again, typically as a result of triggers). The passed-in slot can be
	 * re-used for this purpose.
	 *
	 * The data in the returned slot is used only if the INSERT query has a
	 * RETURNING clause. Hence, the FDW could choose to optimize away
	 * returning some or all columns depending on the contents of the
	 * RETURNING clause. However, some slot must be returned to indicate
	 * success, or the query's reported rowcount will be wrong.
	 *
	 * If the ExecForeignInsert pointer is set to NULL, attempts to insert
	 * into the foreign table will fail with an error message.
	 *
	 */

	/* ----
	 * PolycrackFdwModifyState *modify_state =
	 *	 (PolycrackFdwModifyState *) rinfo->ri_FdwState;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return slot;
}

static TupleTableSlot *
polycrackExecForeignUpdate(EState *estate, ResultRelInfo *rinfo, TupleTableSlot *slot, TupleTableSlot *planSlot) {
	/*
	 * Update one tuple in the foreign table. estate is global execution state
	 * for the query. rinfo is the ResultRelInfo struct describing the target
	 * foreign table. slot contains the new data for the tuple; it will match
	 * the rowtype definition of the foreign table. planSlot contains the
	 * tuple that was generated by the ModifyTable plan node's subplan; it
	 * differs from slot in possibly containing additional "junk" columns. In
	 * particular, any junk columns that were requested by
	 * AddForeignUpdateTargets will be available from this slot.
	 *
	 * The return value is either a slot containing the row as it was actually
	 * updated (this might differ from the data supplied, for example as a
	 * result of trigger actions), or NULL if no row was actually updated
	 * (again, typically as a result of triggers). The passed-in slot can be
	 * re-used for this purpose.
	 *
	 * The data in the returned slot is used only if the UPDATE query has a
	 * RETURNING clause. Hence, the FDW could choose to optimize away
	 * returning some or all columns depending on the contents of the
	 * RETURNING clause. However, some slot must be returned to indicate
	 * success, or the query's reported rowcount will be wrong.
	 *
	 * If the ExecForeignUpdate pointer is set to NULL, attempts to update the
	 * foreign table will fail with an error message.
	 *
	 */

	/* ----
	 * PolycrackFdwModifyState *modify_state =
	 *	 (PolycrackFdwModifyState *) rinfo->ri_FdwState;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return slot;
}

static TupleTableSlot *
polycrackExecForeignDelete(EState *estate, ResultRelInfo *rinfo, TupleTableSlot *slot, TupleTableSlot *planSlot) {
	/*
	 * Delete one tuple from the foreign table. estate is global execution
	 * state for the query. rinfo is the ResultRelInfo struct describing the
	 * target foreign table. slot contains nothing useful upon call, but can
	 * be used to hold the returned tuple. planSlot contains the tuple that
	 * was generated by the ModifyTable plan node's subplan; in particular, it
	 * will carry any junk columns that were requested by
	 * AddForeignUpdateTargets. The junk column(s) must be used to identify
	 * the tuple to be deleted.
	 *
	 * The return value is either a slot containing the row that was deleted,
	 * or NULL if no row was deleted (typically as a result of triggers). The
	 * passed-in slot can be used to hold the tuple to be returned.
	 *
	 * The data in the returned slot is used only if the DELETE query has a
	 * RETURNING clause. Hence, the FDW could choose to optimize away
	 * returning some or all columns depending on the contents of the
	 * RETURNING clause. However, some slot must be returned to indicate
	 * success, or the query's reported rowcount will be wrong.
	 *
	 * If the ExecForeignDelete pointer is set to NULL, attempts to delete
	 * from the foreign table will fail with an error message.
	 */

	/* ----
	 * PolycrackFdwModifyState *modify_state =
	 *	 (PolycrackFdwModifyState *) rinfo->ri_FdwState;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return slot;
}

static void polycrackEndForeignModify(EState *estate, ResultRelInfo *rinfo) {
	/*
	 * End the table update and release resources. It is normally not
	 * important to release palloc'd memory, but for example open files and
	 * connections to remote servers should be cleaned up.
	 *
	 * If the EndForeignModify pointer is set to NULL, no action is taken
	 * during executor shutdown.
	 */

	/* ----
	 * PolycrackFdwModifyState *modify_state =
	 *	 (PolycrackFdwModifyState *) rinfo->ri_FdwState;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

}

static int polycrackIsForeignRelUpdatable(Relation rel) {
	/*
	 * Report which update operations the specified foreign table supports.
	 * The return value should be a bit mask of rule event numbers indicating
	 * which operations are supported by the foreign table, using the CmdType
	 * enumeration; that is, (1 << CMD_UPDATE) = 4 for UPDATE, (1 <<
	 * CMD_INSERT) = 8 for INSERT, and (1 << CMD_DELETE) = 16 for DELETE.
	 *
	 * If the IsForeignRelUpdatable pointer is set to NULL, foreign tables are
	 * assumed to be insertable, updatable, or deletable if the FDW provides
	 * ExecForeignInsert, ExecForeignUpdate, or ExecForeignDelete
	 * respectively. This function is only needed if the FDW supports some
	 * tables that are updatable and some that are not. (Even then, it's
	 * permissible to throw an error in the execution routine instead of
	 * checking in this function. However, this function is used to determine
	 * updatability for display in the information_schema views.)
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return (1 << CMD_UPDATE) | (1 << CMD_INSERT) | (1 << CMD_DELETE);
}
#endif

static void polycrackExplainForeignScan(ForeignScanState *node, struct ExplainState * es) {
	/*
	 * Print additional EXPLAIN output for a foreign table scan. This function
	 * can call ExplainPropertyText and related functions to add fields to the
	 * EXPLAIN output. The flag fields in es can be used to determine what to
	 * print, and the state of the ForeignScanState node can be inspected to
	 * provide run-time statistics in the EXPLAIN ANALYZE case.
	 *
	 * If the ExplainForeignScan pointer is set to NULL, no additional
	 * information is printed during EXPLAIN.
	 */

	elog(DEBUG1, "entering function %s", __func__);

}

#if (PG_VERSION_NUM >= 90300)
static void polycrackExplainForeignModify(ModifyTableState *mtstate, ResultRelInfo *rinfo, List *fdw_private,
		int subplan_index, struct ExplainState * es) {
	/*
	 * Print additional EXPLAIN output for a foreign table update. This
	 * function can call ExplainPropertyText and related functions to add
	 * fields to the EXPLAIN output. The flag fields in es can be used to
	 * determine what to print, and the state of the ModifyTableState node can
	 * be inspected to provide run-time statistics in the EXPLAIN ANALYZE
	 * case. The first four arguments are the same as for BeginForeignModify.
	 *
	 * If the ExplainForeignModify pointer is set to NULL, no additional
	 * information is printed during EXPLAIN.
	 */

	/* ----
	 * PolycrackFdwModifyState *modify_state =
	 *	 (PolycrackFdwModifyState *) rinfo->ri_FdwState;
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

}
#endif

#if (PG_VERSION_NUM >= 90200)
static bool polycrackAnalyzeForeignTable(Relation relation, AcquireSampleRowsFunc *func, BlockNumber *totalpages) {
	/* ----
	 * This function is called when ANALYZE is executed on a foreign table. If
	 * the FDW can collect statistics for this foreign table, it should return
	 * true, and provide a pointer to a function that will collect sample rows
	 * from the table in func, plus the estimated size of the table in pages
	 * in totalpages. Otherwise, return false.
	 *
	 * If the FDW does not support collecting statistics for any tables, the
	 * AnalyzeForeignTable pointer can be set to NULL.
	 *
	 * If provided, the sample collection function must have the signature:
	 *
	 *	  int
	 *	  AcquireSampleRowsFunc (Relation relation, int elevel,
	 *							 HeapTuple *rows, int targrows,
	 *							 double *totalrows,
	 *							 double *totaldeadrows);
	 *
	 * A random sample of up to targrows rows should be collected from the
	 * table and stored into the caller-provided rows array. The actual number
	 * of rows collected must be returned. In addition, store estimates of the
	 * total numbers of live and dead rows in the table into the output
	 * parameters totalrows and totaldeadrows. (Set totaldeadrows to zero if
	 * the FDW does not have any concept of dead rows.)
	 * ----
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return false;
}
#endif

#if (PG_VERSION_NUM >= 90500)
static void polycrackGetForeignJoinPaths(PlannerInfo *root, RelOptInfo *joinrel, RelOptInfo *outerrel,
		RelOptInfo *innerrel, JoinType jointype, JoinPathExtraData *extra) {
	/*
	 * Create possible access paths for a join of two (or more) foreign tables
	 * that all belong to the same foreign server. This optional function is
	 * called during query planning. As with GetForeignPaths, this function
	 * should generate ForeignPath path(s) for the supplied joinrel, and call
	 * add_path to add these paths to the set of paths considered for the
	 * join. But unlike GetForeignPaths, it is not necessary that this
	 * function succeed in creating at least one path, since paths involving
	 * local joining are always possible.
	 *
	 * Note that this function will be invoked repeatedly for the same join
	 * relation, with different combinations of inner and outer relations; it
	 * is the responsibility of the FDW to minimize duplicated work.
	 *
	 * If a ForeignPath path is chosen for the join, it will represent the
	 * entire join process; paths generated for the component tables and
	 * subsidiary joins will not be used. Subsequent processing of the join
	 * path proceeds much as it does for a path scanning a single foreign
	 * table. One difference is that the scanrelid of the resulting
	 * ForeignScan plan node should be set to zero, since there is no single
	 * relation that it represents; instead, the fs_relids field of the
	 * ForeignScan node represents the set of relations that were joined. (The
	 * latter field is set up automatically by the core planner code, and need
	 * not be filled by the FDW.) Another difference is that, because the
	 * column list for a remote join cannot be found from the system catalogs,
	 * the FDW must fill fdw_scan_tlist with an appropriate list of
	 * TargetEntry nodes, representing the set of columns it will supply at
	 * runtime in the tuples it returns.
	 */

	elog(DEBUG1, "entering function %s", __func__);

}

static RowMarkType polycrackGetForeignRowMarkType(RangeTblEntry *rte, LockClauseStrength strength) {
	/*
	 * Report which row-marking option to use for a foreign table. rte is the
	 * RangeTblEntry node for the table and strength describes the lock
	 * strength requested by the relevant FOR UPDATE/SHARE clause, if any. The
	 * result must be a member of the RowMarkType enum type.
	 *
	 * This function is called during query planning for each foreign table
	 * that appears in an UPDATE, DELETE, or SELECT FOR UPDATE/SHARE query and
	 * is not the target of UPDATE or DELETE.
	 *
	 * If the GetForeignRowMarkType pointer is set to NULL, the ROW_MARK_COPY
	 * option is always used. (This implies that RefetchForeignRow will never
	 * be called, so it need not be provided either.)
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return ROW_MARK_COPY;

}

static HeapTuple polycrackRefetchForeignRow(EState *estate, ExecRowMark *erm, Datum rowid,
bool *updated) {
	/*
	 * Re-fetch one tuple from the foreign table, after locking it if
	 * required. estate is global execution state for the query. erm is the
	 * ExecRowMark struct describing the target foreign table and the row lock
	 * type (if any) to acquire. rowid identifies the tuple to be fetched.
	 * updated is an output parameter.
	 *
	 * This function should return a palloc'ed copy of the fetched tuple, or
	 * NULL if the row lock couldn't be obtained. The row lock type to acquire
	 * is defined by erm->markType, which is the value previously returned by
	 * GetForeignRowMarkType. (ROW_MARK_REFERENCE means to just re-fetch the
	 * tuple without acquiring any lock, and ROW_MARK_COPY will never be seen
	 * by this routine.)
	 *
	 * In addition, *updated should be set to true if what was fetched was an
	 * updated version of the tuple rather than the same version previously
	 * obtained. (If the FDW cannot be sure about this, always returning true
	 * is recommended.)
	 *
	 * Note that by default, failure to acquire a row lock should result in
	 * raising an error; a NULL return is only appropriate if the SKIP LOCKED
	 * option is specified by erm->waitPolicy.
	 *
	 * The rowid is the ctid value previously read for the row to be
	 * re-fetched. Although the rowid value is passed as a Datum, it can
	 * currently only be a tid. The function API is chosen in hopes that it
	 * may be possible to allow other datatypes for row IDs in future.
	 *
	 * If the RefetchForeignRow pointer is set to NULL, attempts to re-fetch
	 * rows will fail with an error message.
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return NULL;

}

static List *
polycrackImportForeignSchema(ImportForeignSchemaStmt *stmt, Oid serverOid) {
	/*
	 * Obtain a list of foreign table creation commands. This function is
	 * called when executing IMPORT FOREIGN SCHEMA, and is passed the parse
	 * tree for that statement, as well as the OID of the foreign server to
	 * use. It should return a list of C strings, each of which must contain a
	 * CREATE FOREIGN TABLE command. These strings will be parsed and executed
	 * by the core server.
	 *
	 * Within the ImportForeignSchemaStmt struct, remote_schema is the name of
	 * the remote schema from which tables are to be imported. list_type
	 * identifies how to filter table names: FDW_IMPORT_SCHEMA_ALL means that
	 * all tables in the remote schema should be imported (in this case
	 * table_list is empty), FDW_IMPORT_SCHEMA_LIMIT_TO means to include only
	 * tables listed in table_list, and FDW_IMPORT_SCHEMA_EXCEPT means to
	 * exclude the tables listed in table_list. options is a list of options
	 * used for the import process. The meanings of the options are up to the
	 * FDW. For example, an FDW could use an option to define whether the NOT
	 * NULL attributes of columns should be imported. These options need not
	 * have anything to do with those supported by the FDW as database object
	 * options.
	 *
	 * The FDW may ignore the local_schema field of the
	 * ImportForeignSchemaStmt, because the core server will automatically
	 * insert that name into the parsed CREATE FOREIGN TABLE commands.
	 *
	 * The FDW does not have to concern itself with implementing the filtering
	 * specified by list_type and table_list, either, as the core server will
	 * automatically skip any returned commands for tables excluded according
	 * to those options. However, it's often useful to avoid the work of
	 * creating commands for excluded tables in the first place. The function
	 * IsImportableForeignTable() may be useful to test whether a given
	 * foreign-table name will pass the filter.
	 */

	elog(DEBUG1, "entering function %s", __func__);

	return NULL;
}

#endif
