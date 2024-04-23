(ns xtdb.sql.plan2
  (:require [clojure.string :as str]
            [xtdb.error :as err]
            [xtdb.logical-plan :as lp]
            [xtdb.types :as types]
            [xtdb.util :as util])
  (:import clojure.lang.MapEntry
           (java.util Collection HashMap LinkedHashSet Map)
           java.util.function.Function
           (org.antlr.v4.runtime CharStreams CommonTokenStream ParserRuleContext)
           (xtdb.antlr SqlLexer SqlParser SqlParser$BaseTableContext SqlParser$DirectSqlStatementContext SqlParser$JoinSpecificationContext SqlParser$JoinTypeContext SqlVisitor)))

(defn- add-err! [{:keys [!errors]} err]
  (swap! !errors conj err)
  nil)

(declare ->ExprPlanVisitor ->QueryPlanVisitor)

(defn identifier-sym [^ParserRuleContext ctx]
  (some-> ctx
          (.accept (reify SqlVisitor
                     (visitSchemaName [_ ctx] (.getText ctx))
                     (visitAsClause [this ctx] (-> (.columnName ctx) (.accept this)))
                     (visitTableName [this ctx] (-> (.identifier ctx) (.accept this)))
                     (visitTableAlias [this ctx] (-> (.correlationName ctx) (.accept this)))
                     (visitColumnName [this ctx] (-> (.identifier ctx) (.accept this)))
                     (visitCorrelationName [this ctx] (-> (.identifier ctx) (.accept this)))

                     (visitRegularIdentifier [_ ctx] (symbol (util/str->normal-form-str (.getText ctx))))
                     (visitDelimitedIdentifier [_ ctx]
                       (let [di-str (.getText ctx)]
                         (symbol (subs di-str 1 (dec (count di-str))))))))))

(defprotocol Scope
  (available-cols [scope chain])
  (find-decl [scope chain])
  (plan-scope [scope]))

(defrecord AmbiguousColumnReference [chain])
(defrecord ColumnNotFound [chain])

(defrecord TableTimePeriodSpecificationVisitor [expr-visitor]
  SqlVisitor
  (visitQueryValidTimePeriodSpecification [this ctx]
    (if (.ALL ctx)
      :all-time
      (-> (.tableTimePeriodSpecification ctx)
          (.accept this))))

  (visitQuerySystemTimePeriodSpecification [this ctx]
    (if (.ALL ctx)
      :all-time
      (-> (.tableTimePeriodSpecification ctx)
          (.accept this))))

  (visitTableAllTime [_ _] :all-time)

  (visitTableAsOf [_ ctx]
    [:at (-> ctx (.expr) (.accept expr-visitor))])

  (visitTableBetween [_ ctx]
    [:between
     (-> ctx (.expr 0) (.accept expr-visitor))
     (-> ctx (.expr 1) (.accept expr-visitor))])

  (visitTableFromTo [_ ctx]
    [:in
     (-> ctx (.expr 0) (.accept expr-visitor))
     (-> ctx (.expr 1) (.accept expr-visitor))]))

(defrecord BaseTable [env, ^SqlParser$BaseTableContext ctx
                      schema-name table-name table-alias unique-table-alias cols
                      ^Map !reqd-cols]
  Scope
  (available-cols [_ chain]
    (when-not (and chain (not= chain [table-alias]))
      cols))

  (find-decl [_ [col-name table-name]]
    (when (or (nil? table-name) (= table-name table-alias))
      (if (or (contains? cols col-name) (types/temporal-column? col-name))
        (.computeIfAbsent !reqd-cols col-name
                          (reify Function
                            (apply [_ col]
                              (symbol (str unique-table-alias) (str col)))))
        (add-err! env (->ColumnNotFound col-name)))))

  (plan-scope [{{:keys [default-all-valid-time?]} :env, :as this}]
    (let [expr-visitor (->ExprPlanVisitor env this)]
      (letfn [(<-table-time-period-specification [specs]
                (case (count specs)
                  0 nil
                  1 (.accept ^ParserRuleContext (first specs) (->TableTimePeriodSpecificationVisitor expr-visitor))
                  (throw (UnsupportedOperationException. "multiple time period specifications"))))]
        (let [for-vt (or (<-table-time-period-specification (.queryValidTimePeriodSpecification ctx))
                         (when default-all-valid-time? :all-time))
              for-st (<-table-time-period-specification (.querySystemTimePeriodSpecification ctx))]

          [:rename unique-table-alias
           [:scan (cond-> {:table table-name}
                    for-vt (assoc :for-valid-time for-vt)
                    for-st (assoc :for-system-time for-st))
            (vec (.keySet !reqd-cols))]])))))

(defrecord JoinTable [env l r
                      ^SqlParser$JoinTypeContext join-type-ctx
                      ^SqlParser$JoinSpecificationContext join-spec-ctx]
  Scope
  (available-cols [_ chain]
    (->> [l r]
         (into [] (comp (mapcat #(available-cols % chain))
                        (distinct)))))

  (find-decl [_ chain]
    (let [matches (->> [l r]
                       (keep (fn [scope]
                               (find-decl scope chain))))]
      (when (> (count matches) 1)
        (add-err! env (->AmbiguousColumnReference chain)))

      (first matches)))

  (plan-scope [this-scope]
    (let [join-type (case (some-> join-type-ctx
                                  (.outerJoinType)
                                  (.getText)
                                  (str/upper-case))
                      "LEFT" :left-outer-join
                      "RIGHT" :right-outer-join
                      "FULL" :full-outer-join
                      :join)

          join-cond (or (some-> join-spec-ctx
                                (.accept
                                 (reify SqlVisitor
                                   (visitJoinCondition [_ ctx]
                                     (let [expr-visitor (->ExprPlanVisitor env this-scope)]
                                       [(-> (.expr ctx)
                                            (.accept expr-visitor))])))))
                        [])
          planned-l (plan-scope l)
          planned-r (plan-scope r)]
      (if (= :right-outer-join join-type)
        [:left-outer-join join-cond planned-r planned-l]
        [join-type join-cond planned-l planned-r]))))

(defrecord DerivedTable [plan table-alias unique-table-alias available-cols col-syms]
  Scope
  (available-cols [_ chain]
    (when-not (and chain (not= chain [table-alias]))
      available-cols))

  (find-decl [_ [col-name table-name]]
    (when (or (nil? table-name) (= table-name table-alias))
      (when-let [col (get available-cols col-name)]
        (symbol (str unique-table-alias) (str col)))))

  (plan-scope [_]
    [:rename unique-table-alias
     plan]))

(defrecord FromClauseScope [env table-ref-scopes]
  Scope
  (available-cols [_ chain]
    (->> table-ref-scopes
         (into [] (comp (mapcat #(available-cols % chain)) (distinct)))))

  (find-decl [_ chain]
    (let [matches (->> table-ref-scopes
                       (keep (fn [scope]
                               (find-decl scope chain))))]
      (when (> (count matches) 1)
        (add-err! env (->AmbiguousColumnReference chain)))

      (first matches)))

  (plan-scope [_]
    (case (count table-ref-scopes)
      0 [:table [{}]]
      1 (plan-scope (first table-ref-scopes))
      [:mega-join [] (mapv plan-scope table-ref-scopes)])))

(defn- ->table-projection [^ParserRuleContext ctx]
  (some-> ctx
          (.accept
           (reify SqlVisitor
             (visitTableProjection [_ ctx]
               (some->> (.columnNameList ctx) (.columnName)
                        (mapv identifier-sym)))))))

(defn- ->insertion-ordered-set [coll]
  (LinkedHashSet. ^Collection (vec coll)))

(defrecord ProjectedCol [projection col-sym])

(defrecord ScopeVisitor [env scope]
  SqlVisitor
  (visitFromClause [this ctx]
    (->FromClauseScope env (->> (.tableReference ctx)
                                (mapv #(.accept ^ParserRuleContext % this)))))

  (visitBaseTable [{{:keys [!id-count table-info]} :env} ctx]
    (let [tn (some-> (.tableOrQueryName ctx) (.tableName))
          sn (identifier-sym (.schemaName tn))
          tn (identifier-sym (.identifier tn))
          table-alias (or (identifier-sym (.tableAlias ctx)) tn)
          unique-table-alias (symbol (str table-alias "." (swap! !id-count inc)))
          cols (some-> (.tableProjection ctx) (->table-projection))]
      (->BaseTable env ctx sn tn table-alias unique-table-alias
                   (->insertion-ordered-set (or cols (get table-info tn)))
                   (HashMap.))))

  (visitJoinTable [this ctx]
    (let [l (-> (.tableReference ctx 0) (.accept this))
          r (-> (.tableReference ctx 1) (.accept this))]
      (->JoinTable env l r (.joinType ctx) (.joinSpecification ctx))))

  (visitDerivedTable [{{:keys [!id-count]} :env} ctx]
    (let [{:keys [plan col-syms]} (-> (.subquery ctx) (.queryExpression)
                                      (.accept (-> (->QueryPlanVisitor env scope)
                                                   (assoc :out-col-syms (->table-projection (.tableProjection ctx))))))

          table-alias (identifier-sym (.tableAlias ctx))]

      (->DerivedTable plan table-alias
                      (symbol (str table-alias "." (swap! !id-count inc)))
                      (into #{} (map str) col-syms)
                      col-syms)))

  (visitWrappedTableReference [this ctx] (-> (.tableReference ctx) (.accept this))))

(defrecord SelectClauseProjectedCols [env scope]
  SqlVisitor
  (visitSelectClause [_ ctx]
    (let [sl-ctx (.selectList ctx)]
      (if (.ASTERISK sl-ctx)
        (vec (for [col-name (available-cols scope nil)
                   :let [sym (find-decl scope [col-name])]]
               (->ProjectedCol sym sym)))

        (->> (.selectSublist sl-ctx)
             (into [] (comp (map-indexed
                             (fn [col-idx ^ParserRuleContext sl-elem]
                               (.accept (.getChild sl-elem 0)
                                        (reify SqlVisitor
                                          (visitDerivedColumn [_ ctx]
                                            [(let [expr (.accept (.expr ctx) (->ExprPlanVisitor env scope))]
                                               (if-let [as-clause (.asClause ctx)]
                                                 (let [col-name (identifier-sym as-clause)]
                                                   (->ProjectedCol {col-name expr} col-name))

                                                 (if (symbol? expr)
                                                   (->ProjectedCol expr expr)
                                                   (let [col-name (symbol (str "xt$column_" (inc col-idx)))]
                                                     (->ProjectedCol {col-name expr} col-name)))))])

                                          (visitQualifiedAsterisk [_ ctx]
                                            (let [[table-name schema-name] (rseq (mapv identifier-sym (.identifier (.identifierChain ctx))))]
                                              (when schema-name
                                                (throw (UnsupportedOperationException. "schema not supported")))

                                              (if-let [table-cols (available-cols scope [table-name])]
                                                (for [col-name table-cols
                                                      :let [sym (find-decl scope [col-name table-name])]]
                                                  (->ProjectedCol sym sym))
                                                (throw (UnsupportedOperationException. (str "Table not found: " table-name))))))))))
                            cat)))))))

(defn- project-all-cols [scope]
  ;; duplicated from the ASTERISK case above
  (vec (for [col-name (available-cols scope nil)
             :let [sym (find-decl scope [col-name])]]
         (->ProjectedCol sym sym))))

(defrecord ExprPlanVisitor [env scope]
  SqlVisitor
  (visitSearchCondition [this ctx] (-> (.expr ctx) (.accept this)))
  (visitWrappedExpr [this ctx] (-> (.expr ctx) (.accept this)))

  (visitLiteralExpr [this ctx] (-> (.literal ctx) (.accept this)))
  (visitFloatLiteral [_ ctx] (parse-double (.getText ctx)))
  (visitIntegerLiteral [_ ctx] (parse-long (.getText ctx)))

  (visitCharacterStringLiteral [this ctx] (-> (.characterString ctx) (.accept this)))

  (visitCharacterString [_ ctx]
    (let [str (.getText ctx)]
      (subs str 1 (dec (count str)))))

  (visitBooleanLiteral [_ ctx]
    (case (-> (.getText ctx) str/lower-case)
      "true" true
      "false" false
      "unknown" nil))

  (visitNullLiteral [_ _ctx] nil)

  (visitColumnExpr [this ctx] (-> (.columnReference ctx) (.accept this)))

  (visitColumnReference [_ ctx]
    (let [chain (rseq (mapv identifier-sym (.identifier (.identifierChain ctx))))]
      (or (find-decl scope chain)
          (add-err! env (->ColumnNotFound chain)))))

  (visitParamExpr [this ctx] (-> (.parameterSpecification ctx) (.accept this)))

  (visitDynamicParameter [{{:keys [!param-count]} :env} _]
    (-> (symbol (str "?_" (dec (swap! !param-count inc))))
        (vary-meta assoc :param? true)))

  (visitPostgresParameter [{{:keys [!param-count]} :env} ctx]
    (-> (symbol (str "?_" (let [param-idx (dec (parse-long (subs (.getText ctx) 1)))]
                            (swap! !param-count min param-idx)
                            param-idx)))
        (vary-meta assoc :param? true)))

  (visitUnaryPlusExpr [this ctx] (-> (.expr ctx) (.accept this)))
  (visitUnaryMinusExpr [this ctx] (list '- (-> (.expr ctx) (.accept this))))

  (visitAddExpr [this ctx]
    (list '+
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitSubtractExpr [this ctx]
    (list '-
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitMultiplyExpr [this ctx]
    (list '*
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitDivideExpr [this ctx]
    (list '/
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitOrExpr [this ctx]
    (list 'or
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitAndExpr [this ctx]
    (list 'and
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitUnaryNotExpr [this ctx] (list 'not (-> (.expr ctx) (.accept this))))

  (visitComparisonPredicate [this ctx]
    (list (symbol (.getText (.compOp ctx)))
          (-> (.expr ctx 0) (.accept this))
          (-> (.expr ctx 1) (.accept this))))

  (visitNullPredicate [this ctx]
    (as-> (list 'nil? (-> (.expr ctx) (.accept this))) expr
       (if (.NOT ctx)
        (list 'not expr)
        expr))))

(defrecord ColumnCountMismatch [expected given])

(defprotocol OptimiseStatement
  (optimise-stmt [stmt]))

(defrecord QueryExpr [plan col-syms]
  OptimiseStatement (optimise-stmt [this] (update this :plan lp/rewrite-plan)))

(defn- remove-ns-qualifiers [{:keys [plan col-syms]}]
  (let [out-projections (->> col-syms
                             (into [] (map (fn [col-sym]
                                             (if (namespace col-sym)
                                               (let [out-sym (symbol (name col-sym))]
                                                 (->ProjectedCol {out-sym col-sym}
                                                                 out-sym))
                                               (->ProjectedCol col-sym col-sym))))))]
    (->QueryExpr [:project (mapv :projection out-projections)
                  plan]
                 (mapv :col-sym out-projections))))

(defrecord QueryPlanVisitor [env scope]
  SqlVisitor
  (visitWrappedQuery [this ctx] (-> (.queryExpressionBody ctx) (.accept this)))

  (visitQueryExpression [this ctx]
    (as-> (.accept (.queryExpressionBody ctx) this)
        {:keys [plan col-syms]}

      (let [out-projections (->> col-syms
                                 (into [] (map (fn [col-sym]
                                                 (if (namespace col-sym)
                                                   (let [out-sym (symbol (name col-sym))]
                                                     (->ProjectedCol {out-sym col-sym}
                                                                     out-sym))
                                                   (->ProjectedCol col-sym col-sym))))))]

        (->QueryExpr [:project (mapv :projection out-projections)
                      plan]
                     (mapv :col-sym out-projections)))))

  (visitUnionQuery [this ctx]
    (let [{l-plan :plan, :keys [col-syms]} (-> (.queryExpressionBody ctx 0) (.accept this)
                                               (remove-ns-qualifiers))
          {r-plan :plan} (-> (.queryExpressionBody ctx 1) (.accept this)
                             (remove-ns-qualifiers))
          plan [:union-all l-plan r-plan]]
      ;; TODO column matching

      (->QueryExpr (if-not (.ALL ctx)
                     [:distinct plan]
                     plan)
                   col-syms)))

  (visitExceptQuery [this ctx]
    (let [{l-plan :plan, :keys [col-syms]} (-> (.queryExpressionBody ctx 0) (.accept this)
                                               (remove-ns-qualifiers))
          {r-plan :plan} (-> (.queryExpressionBody ctx 1) (.accept this)
                             (remove-ns-qualifiers))
          distinct? (not (.ALL ctx))]
      ;; TODO column matching

      (->QueryExpr [:difference
                    (if distinct? [:distinct l-plan] l-plan)
                    (if distinct? [:distinct r-plan] r-plan)]
                   col-syms)))

  (visitIntersectQuery [this ctx]
    (let [{l-plan :plan, :keys [col-syms]} (-> (.queryExpressionBody ctx 0) (.accept this)
                                               (remove-ns-qualifiers))
          {r-plan :plan} (-> (.queryExpressionBody ctx 1) (.accept this)
                             (remove-ns-qualifiers))
          plan [:intersect l-plan r-plan]]
      ;; TODO column matching

      (->QueryExpr (if-not (.ALL ctx)
                     [:distinct plan]
                     plan)
                   col-syms)))

  (visitQuerySpecification [{:keys [out-col-syms]} ctx]
    (let [qs-scope (if-let [from (.fromClause ctx)]
                     (.accept from (->ScopeVisitor env scope))
                     scope)

          where-pred (when-let [where-clause (.whereClause ctx)]
                       (.accept (.expr where-clause) (->ExprPlanVisitor env qs-scope)))

          select-clause (.selectClause ctx)

          select-projected-cols (if select-clause
                                  (.accept select-clause (->SelectClauseProjectedCols env qs-scope))
                                  (project-all-cols qs-scope))

          plan (as-> (plan-scope qs-scope) plan
                 (if where-pred
                   [:select where-pred
                    plan]
                   plan)

                 [:project (mapv :projection select-projected-cols)
                  plan])]

      (as-> (->QueryExpr plan (mapv :col-sym select-projected-cols))
          {:keys [plan col-syms] :as query-expr}

        (if out-col-syms
          (->QueryExpr [:rename (zipmap out-col-syms col-syms)
                        plan]
                       out-col-syms)
          query-expr)

        (if (some-> select-clause .setQuantifier (.getText) (str/upper-case) (= "DISTINCT"))
          (->QueryExpr [:distinct plan]
                       col-syms)
          query-expr))))

  (visitValuesQuery [this ctx] (-> (.tableValueConstructor ctx) (.accept this)))
  (visitTableValueConstructor [this ctx] (-> (.rowValueList ctx) (.accept this)))

  (visitRowValueList [{{:keys [!id-count]} :env, :keys [out-col-syms]} ctx]
    (let [expr-plan-visitor (->ExprPlanVisitor env scope)
          col-syms (or out-col-syms
                       (-> (.rowValueConstructor ctx 0)
                           (.accept
                            (reify SqlVisitor
                              (visitSingleExprRowConstructor [_ ctx]
                                '[xt$column_1])

                              (visitMultiExprRowConstructor [_ ctx]
                                (->> (.expr ctx)
                                     (into [] (map-indexed (fn [idx _]
                                                             (symbol (str "xt$column_" (inc idx))))))))))))

          col-keys (mapv keyword col-syms)

          unique-table-alias (symbol (str "xt.values." (swap! !id-count inc)))

          col-count (count col-keys)

          row-visitor (reify SqlVisitor
                        (visitSingleExprRowConstructor [_ ctx]
                          (let [expr (.expr ctx)]
                            (if (not= 1 col-count)
                              (add-err! env (->ColumnCountMismatch col-count 1))
                              {(first col-keys) (.accept expr expr-plan-visitor)})))

                        (visitMultiExprRowConstructor [_ ctx]
                          (let [exprs (.expr ctx)]
                            (if (not= (count exprs) col-count)
                              (add-err! env (->ColumnCountMismatch col-count (count exprs)))
                              (->> (map (fn [col ^ParserRuleContext expr]
                                          (MapEntry/create col
                                                           (.accept expr expr-plan-visitor)))
                                        col-keys
                                        exprs)
                                   (into {}))))))]

      (->QueryExpr [:rename unique-table-alias
                    [:table col-syms
                     (->> (.rowValueConstructor ctx)
                          (mapv #(.accept ^ParserRuleContext % row-visitor)))]]

                   (->> col-syms
                        (mapv #(symbol (str unique-table-alias) (str %))))))))

(defrecord StmtVisitor [env scope]
  SqlVisitor
  (visitDirectSqlStatement [this ctx] (-> (.directlyExecutableStatement ctx) (.accept this)))
  (visitDirectlyExecutableStatement [this ctx] (-> (.getChild ctx 0) (.accept this)))

  (visitQueryExpression [_ ctx] (-> ctx (.accept (->QueryPlanVisitor env scope)))))

(defn ->parser ^xtdb.antlr.SqlParser [sql]
  (-> (CharStreams/fromString sql)
      (SqlLexer.)
      (CommonTokenStream.)
      (SqlParser.)))

(defn- xform-table-info [table-info]
  (->> (for [[tn cns] table-info]
         [(symbol tn) (->> cns
                           (map symbol)
                           ^Collection
                           (sort-by identity (fn [s1 s2]
                                               (cond
                                                 (= 'xt$id s1) -1
                                                 (= 'xt$id s2) 1
                                                 :else (compare s1 s2))))
                           ->insertion-ordered-set)])
       (into {})))

(defn plan-expr
  ([sql] (plan-expr sql {}))

  ([sql {:keys [scope table-info default-all-valid-time?]}]
   (let [!errors (atom [])
         env {:scope scope
              :!errors !errors
              :!id-count (atom 0)
              :!param-count (atom 0)
              :table-info (xform-table-info table-info)
              :default-all-valid-time? (boolean default-all-valid-time?)}
         parser (->parser sql)
         plan (-> (.expr parser)
                  #_(doto (-> (.toStringTree parser) read-string (clojure.pprint/pprint))) ; <<no-commit>>
                  (.accept (->ExprPlanVisitor env scope)))]

     (if-let [errs (not-empty @!errors)]
       (throw (err/illegal-arg :xtdb/sql-error {:errors errs}))
       plan))))

;; eventually these data structures will be used as logical plans,
;; we won't need an adapter
(defprotocol AdaptPlan
  (->logical-plan [stmt]))

(extend-protocol AdaptPlan
  QueryExpr (->logical-plan [{:keys [plan]}] plan))

(defn parse-statement ^SqlParser$DirectSqlStatementContext [sql]
  (let [parser (->parser sql)]
    (-> (.directSqlStatement parser)
        #_(doto (-> (.toStringTree parser) read-string (clojure.pprint/pprint))) ; <<no-commit>>
        )))

(defn plan-statement
  ([sql] (plan-statement sql {}))

  ([sql {:keys [scope table-info default-all-valid-time?]}]
   (let [!errors (atom [])
         !param-count (atom 0)
         env {:!errors !errors
              :!id-count (atom 0)
              :!param-count !param-count
              :table-info (xform-table-info table-info)
              :default-all-valid-time? (boolean default-all-valid-time?)}
         stmt (-> (parse-statement sql)
                  (.accept (->StmtVisitor env scope)))]
     (-> (if-let [errs (not-empty @!errors)]
           (throw (err/illegal-arg :xtdb/sql-error {:errors errs}))
           (-> stmt
               #_(doto clojure.pprint/pprint) ;; <<no-commit>>
               (optimise-stmt) ;; <<no-commit>>
               #_(doto clojure.pprint/pprint) ;; <<no-commit>>
               ))
         (vary-meta assoc :param-count @!param-count)))))

(comment
  (plan-statement "SELECT * FROM foo WHERE bar + baz = 3"
                  {:table-info {"foo" #{"bar" "baz" "xt$id"}
                                "bar" #{"baz" "quux"}}}))
