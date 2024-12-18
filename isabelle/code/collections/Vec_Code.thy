theory Vec_Code
  imports Set_Code
begin

section \<open>Util\<close>

lemma restrict_map_eq_iff: \<open>m |` I = m' |` I \<longleftrightarrow> (\<forall>i \<in> I. m i = m' i)\<close>
  by (auto simp: restrict_map_def) metis

lemma map_restr_same_eqI[intro!]:
  assumes \<open>\<And>i. i \<in> I \<Longrightarrow> m i = m' i\<close>
  shows \<open>m |` I = m' |` I\<close>
  using assms restrict_map_eq_iff
  by blast

lemma map_restr_same_eqE[elim]:
  assumes \<open>m |` I = m' |` I\<close>
  obtains \<open>\<And>i. i \<in> I \<Longrightarrow> m i = m' i\<close>
  using assms restrict_map_eq_iff
  by metis

section \<open>Vectors\<close>

record ('v,'x,'natset) vec_ops =
  vec_op_\<alpha> :: "'v \<Rightarrow> (nat \<rightharpoonup> 'x)"
  vec_op_scope :: \<open>'v \<Rightarrow> 'natset\<close>
  vec_op_idx :: \<open>'v \<Rightarrow> nat \<Rightarrow> 'x\<close>
  vec_op_invar :: \<open>'v \<Rightarrow> bool\<close>
  vec_op_empty :: \<open>'v\<close>
  vec_op_update :: \<open>'v \<Rightarrow> nat \<Rightarrow> 'x \<Rightarrow> 'v\<close>
  vec_op_restr :: \<open>'v \<Rightarrow> 'natset \<Rightarrow> 'v\<close>

locale VecDefs =
  fixes 
    vec_ops :: "('v,'x,'natset) vec_ops" and
    set_ops :: \<open>(nat, 'natset) oset_ops\<close> and
    dims :: nat and
    doms :: \<open>nat \<Rightarrow> 'x set\<close>
begin

  abbreviation \<alpha> where "\<alpha> \<equiv> vec_op_\<alpha> vec_ops"
  abbreviation scope where "scope \<equiv> vec_op_scope vec_ops"
  abbreviation idx where "idx \<equiv> vec_op_idx vec_ops"
  abbreviation invar where "invar \<equiv> vec_op_invar vec_ops"
  abbreviation empty where "empty \<equiv> vec_op_empty vec_ops"
  abbreviation update where "update \<equiv> vec_op_update vec_ops"
  abbreviation scope_ops where "scope_ops \<equiv> set_ops"
  abbreviation restr where "restr \<equiv> vec_op_restr vec_ops"

subsection \<open>Additional Operations on vectors\<close>

definition \<open>insert_list v xs = fold (\<lambda>(k, x) m. update m k x) xs v\<close>

definition \<open>vec_eq_on v v' I \<longleftrightarrow> (\<forall>i \<in> I. idx v i = idx v' i)\<close>

definition \<open>vec_to_list v = map (\<alpha> v) [0..<dims]\<close>

subsection \<open>Scopes of vectors are sets\<close>

sublocale Scope: NatSetDefs scope_ops .

abbreviation "scope_\<alpha> v \<equiv> Scope.\<alpha> (scope v)"

definition \<open>vec_on v s \<longleftrightarrow> invar v \<and> s \<subseteq> scope_\<alpha> v\<close>

lemma vec_onE[elim]:
  assumes \<open>vec_on v s\<close>
  obtains \<open>invar v\<close> \<open>s \<subseteq> scope_\<alpha> v\<close>
  using assms
  unfolding vec_on_def 
  by auto

lemma vec_onD[dest]: 
  assumes \<open>vec_on v s\<close>
  shows \<open>invar v\<close> \<open>s \<subseteq> scope_\<alpha> v\<close>
  using assms by auto

lemma vec_onI[intro]: 
  assumes \<open>invar v\<close> \<open>s \<subseteq> scope_\<alpha> v\<close>
  shows \<open>vec_on v s\<close>
  using assms 
  unfolding vec_on_def
  by auto

end

locale Vec =
  VecDefs +
  assumes
    Scope: \<open>NatSet scope_ops\<close> and
    
    empty[simp]: \<open>\<alpha> empty = Map.empty\<close> and
    invar_empty[intro, simp]: \<open>invar empty\<close> and

    invar_update[intro!, simp]: \<open>\<And>v k x. invar v \<Longrightarrow> k < dims \<Longrightarrow> x \<in> doms k \<Longrightarrow> invar (update v k x)\<close> and
    idx_update[simp]: \<open>\<And>v k x. invar v \<Longrightarrow> k < dims \<Longrightarrow> x \<in> doms k \<Longrightarrow> \<alpha> (update v k x) = (\<alpha> v)(k \<mapsto> x)\<close> and

    scope_invar[intro!, simp]: \<open>\<And>v. invar v \<Longrightarrow> Scope.invar (scope v)\<close> and
    scope_invar_subs[dest]: \<open>\<And>v. invar v \<Longrightarrow> dom (\<alpha> v) \<subseteq> {0..<dims}\<close> and
    invar_subs_doms[dest, intro!]: \<open>\<And>v i. invar v \<Longrightarrow> i < dims \<Longrightarrow> i \<in> dom (\<alpha> v) \<Longrightarrow> the (\<alpha> v i) \<in> doms i\<close> and

    invar_restr[simp, intro!]: \<open>\<And>v s. invar v \<Longrightarrow> Scope.invar s \<Longrightarrow> invar (restr v s)\<close> and
    idx_restr[simp]: \<open>\<And>v s. invar v \<Longrightarrow> Scope.invar s \<Longrightarrow> 
      \<alpha> (restr v s) = restrict_map (\<alpha> v) (Scope.\<alpha> s)\<close> and

    scope_correct[simp]: \<open>\<And>v. invar v \<Longrightarrow> scope_\<alpha> v = dom (\<alpha> v)\<close> and
    \<alpha>_correct: \<open>\<And>v i. invar v \<Longrightarrow> \<alpha> v i = (if i \<in> scope_\<alpha> v then Some (idx v i) else None)\<close>

begin

sublocale Scope: NatSet scope_ops
  using Scope .

subsection \<open>@{const vec_on}\<close>
lemma vec_on_iff[simp]: \<open>vec_on v X \<longleftrightarrow> invar v \<and> X \<subseteq> dom (\<alpha> v)\<close>
  by fastforce

lemma vec_on_diff[intro]: \<open>vec_on v X \<Longrightarrow> vec_on v (X - Y)\<close>
  by auto

subsection \<open>@{const update}\<close>
lemma scope_update[simp]: 
  assumes \<open>invar v\<close> \<open>k < dims\<close> \<open>x \<in> doms k\<close> 
  shows \<open>Scope.\<alpha> (scope (update v k x)) = Set.insert k (Scope.\<alpha> (scope v))\<close>
  using assms
  by auto

subsection \<open>@{const idx}\<close>
lemma idx_\<alpha>[simp]: \<open>invar v \<Longrightarrow> i \<in> dom (\<alpha> v) \<Longrightarrow> idx v i = the (\<alpha> v i)\<close>
  using \<alpha>_correct by auto

lemma idx_in_doms[simp, intro!]: \<open>invar v \<Longrightarrow> i < dims \<Longrightarrow> i \<in> dom (\<alpha> v) \<Longrightarrow> idx v i \<in> doms i\<close>
  by (simp add: invar_subs_doms)

lemma the_\<alpha>_in_doms[simp, intro!]: \<open>invar v \<Longrightarrow> i < dims \<Longrightarrow> i \<in> dom (\<alpha> v) \<Longrightarrow> the (\<alpha> v i) \<in> doms i\<close>
  using invar_subs_doms .

lemma scope_le_dims[dest]: \<open>invar v \<Longrightarrow> i \<in> dom (\<alpha> v) \<Longrightarrow> i < dims\<close>
  using scope_invar_subs 
  by force

lemma some_idx[simp]: \<open>invar v \<Longrightarrow> i \<in> dom (\<alpha> v) \<Longrightarrow> Some (idx v i) = \<alpha> v i\<close>
  by auto

lemma \<alpha>_some_in_dims[dest]: \<open>\<alpha> v i = Some y \<Longrightarrow> invar v \<Longrightarrow> i < dims\<close>
  by blast

lemma \<alpha>_some_in_doms[dest]: \<open>\<alpha> v i = Some y \<Longrightarrow> invar v \<Longrightarrow> y \<in> doms i\<close>
  by (metis \<alpha>_some_in_dims domI option.sel the_\<alpha>_in_doms)

subsection \<open>@{const vec_eq_on}\<close>
lemma vec_eq_onE[elim]:
  assumes \<open>vec_eq_on v v' X\<close> \<open>i \<in> X\<close>
  shows \<open>idx v i = idx v' i\<close>
  using assms 
  unfolding vec_eq_on_def 
  by auto

lemma vec_eq_onD[dest]:
  assumes \<open>vec_eq_on v v' X\<close>
  shows \<open>\<And>i. i \<in> X \<Longrightarrow> idx v i = idx v' i\<close>
  using assms vec_eq_onE
  by blast

lemma vec_eq_on_iff[simp]: \<open>invar v \<Longrightarrow> invar v' \<Longrightarrow> I \<subseteq> dom (\<alpha> v) \<Longrightarrow> I \<subseteq> dom (\<alpha> v') \<Longrightarrow>
  vec_eq_on v v' I \<longleftrightarrow> (\<alpha> v) |` I = (\<alpha> v') |` I\<close>
  unfolding vec_eq_on_def
  by (fastforce simp: subset_iff)

lemma vec_eq_on_subs: \<open>Y \<subseteq> X \<Longrightarrow> vec_eq_on v v' X \<Longrightarrow> vec_eq_on v v' Y\<close>
  unfolding vec_eq_on_def
  by auto

lemma vec_eq_on_diff[intro]: \<open>vec_eq_on v v' X \<Longrightarrow> vec_eq_on v v' (X - Y)\<close>
  using vec_eq_on_subs
  by blast

lemma vec_eq_on_int[intro]: \<open>vec_eq_on v v' X \<Longrightarrow> vec_eq_on v v' Y \<Longrightarrow> vec_eq_on v v' (X \<inter> Y)\<close>
  using vec_eq_on_subs 
  by blast

lemma vec_eq_on_sym[simp]: \<open>vec_eq_on v v' X \<longleftrightarrow> vec_eq_on v' v X\<close>
  using vec_eq_on_def 
  by auto

lemma vec_eq_on_same[simp]: \<open>vec_eq_on v v X\<close>
  using vec_eq_on_def by auto

lemma vec_eq_onI[intro]:
  assumes \<open>\<And>i. i \<in> X \<Longrightarrow> idx v i = idx v' i\<close>
  shows \<open>vec_eq_on v v' X\<close>
  using assms 
  unfolding vec_eq_on_def
  by blast

subsection \<open>@{const restr}\<close>
lemma scope_restr[simp]: \<open>invar v \<Longrightarrow> Scope.invar s \<Longrightarrow> 
      scope_\<alpha> (restr v s) = Scope.\<alpha> s \<inter> Scope.\<alpha> (scope v)\<close>
  by auto

subsection \<open>@{const vec_to_list}\<close>
lemma vec_to_list_length[simp]: \<open>invar v \<Longrightarrow> length (vec_to_list v) = dims\<close>
  unfolding vec_to_list_def 
  by auto

lemma vec_to_list_idx_in[simp]: 
  \<open>invar v \<Longrightarrow> i < dims \<Longrightarrow> i \<in> Scope.\<alpha> (scope v) \<Longrightarrow> nth (vec_to_list v) i = Some (idx v i)\<close>
  unfolding vec_to_list_def 
  by auto

lemma vec_to_list_idx_notin[simp]:
  \<open>invar v \<Longrightarrow> i < dims \<Longrightarrow> i \<notin> Scope.\<alpha> (scope v) \<Longrightarrow> nth (vec_to_list v) i = None\<close>
  unfolding vec_to_list_def 
  using \<alpha>_correct 
  by auto

lemma vec_to_list_idx[simp]: 
  \<open>invar v \<Longrightarrow> i < dims \<Longrightarrow> nth (vec_to_list v) i = 
    (if i \<in> Scope.\<alpha> (scope v) then Some (idx v i) else None)\<close>
  by auto

subsection \<open>@{const insert_list}\<close>
lemma set_insert_list:
  assumes \<open>invar v\<close> \<open>List.set xs \<subseteq> {(k, v). v \<in> doms k \<and> k < dims}\<close>
  shows \<open>Scope.\<alpha> (scope (insert_list v xs)) = (Scope.\<alpha> (scope v)) \<union> List.set (map fst xs)\<close>
  using assms
  by (induction xs arbitrary: v) (fastforce simp: image_iff insert_list_def)+

lemma insert_list_cons[simp]: \<open>insert_list v (x#xs) = insert_list (update v (fst x) (snd x)) xs\<close>
  unfolding insert_list_def
  by (auto simp: case_prod_beta)

lemma insert_list_empty[simp]: \<open>insert_list v [] = v\<close>
  unfolding insert_list_def 
  by auto

lemma idx_insert_list[simp]:
  assumes \<open>invar v\<close> \<open>distinct (map fst xs)\<close> \<open>List.set xs \<subseteq> {(k, v). v \<in> doms k \<and> k < dims}\<close>
  shows \<open>\<alpha> (insert_list v xs) = map_upds (\<alpha> v) (map fst xs) (map snd xs)\<close>
  using assms
  by (induction xs arbitrary: v) auto

lemma vec_invar_insert_list[intro!]:
  assumes \<open>invar v\<close> \<open>List.set xs \<subseteq> {(k, v). v \<in> doms k \<and> k < dims}\<close>
  shows \<open>invar (insert_list v xs)\<close>
  using assms
  by (induction xs arbitrary: v) auto

lemma vec_scope_insert_list[simp]:
  assumes \<open>invar v\<close> \<open>List.set xs \<subseteq> {(k, v). v \<in> doms k \<and> k < dims}\<close>
  shows \<open>Scope.\<alpha> (scope (insert_list v xs)) = Scope.\<alpha> (scope v) \<union> fst ` List.set xs\<close> 
  using assms 
  by (induction xs arbitrary: v) fastforce+

subsection \<open>@{term vec_inst}\<close>
definition \<open>vec_inst v v' s = (Scope.iterate s (\<lambda>i v'. update v' i (idx v i)) v')\<close>

lemma invar_vec_instI[intro!, simp]: 
  \<open>invar v \<Longrightarrow> invar v' \<Longrightarrow> Scope.invar s \<Longrightarrow> Scope.\<alpha> s \<subseteq> dom (\<alpha> v) \<Longrightarrow> invar (vec_inst v v' s)\<close>
  unfolding vec_inst_def
  by (rule Scope.iterate_rule_P) (auto simp: subset_iff)

lemma vec_inst_correct[simp]: 
  \<open>Scope.invar s \<Longrightarrow> Scope.\<alpha> s \<subseteq> dom (\<alpha> v) \<Longrightarrow> invar x \<Longrightarrow> invar v \<Longrightarrow>
    \<alpha> (vec_inst v x s) = \<alpha> x ++ (\<alpha> v |` Scope.\<alpha> s)\<close>
    unfolding vec_inst_def
  by (rule Scope.iterate_rule_P[where I = \<open>\<lambda>X v'. invar v' \<and> \<alpha> v' = \<alpha> x ++ (\<alpha> v |` (Scope.\<alpha> s - X))\<close>])
     (auto simp: subset_iff scope_le_dims it_step_insert_iff restrict_map_insert simp flip: map_add_upd)

lemma scope_vec_inst[simp]:
  assumes \<open>Scope.invar s\<close> \<open>invar v\<close> \<open>invar v'\<close> \<open>Scope.\<alpha> s \<subseteq> dom (\<alpha> v)\<close>
  shows \<open>scope_\<alpha> (vec_inst v v' s) = scope_\<alpha> v' \<union> Scope.\<alpha> s\<close>
  using assms 
  by auto

end

section \<open>Relations between vectors\<close>
context Vec
begin

definition \<open>vec_rel R_elem v_code v \<longleftrightarrow>
  (invar v_code) \<and>
  (Scope.set_rel (scope v_code) (dom v)) \<and>
  (\<forall>i \<in> dom v. R_elem (idx v_code i) (the (v i)))\<close>

lemma vec_relE[elim]: 
  assumes \<open>vec_rel R_elem v_code v\<close>
  obtains \<open>invar v_code\<close>
  \<open>Scope.set_rel (scope v_code) (dom v)\<close>
  \<open>\<And>i. i \<in> dom v \<Longrightarrow> R_elem (idx v_code i) (the (v i))\<close>
  using assms unfolding vec_rel_def by auto

lemma vec_relI[intro]:
  assumes \<open>invar v_code\<close>
  \<open>Scope.set_rel (scope v_code) (dom v)\<close>
  \<open>\<And>i. i \<in> dom v \<Longrightarrow> R_elem (idx v_code i) (the (v i))\<close>
  shows \<open>vec_rel R_elem v_code v\<close>
  using assms unfolding vec_rel_def by auto

lemma vec_rel_eqD:
  assumes \<open>vec_rel (=) v_code v\<close> 
  shows \<open>\<alpha> v_code = v\<close>
proof -
  have \<open>\<alpha> v_code i = v i\<close> for i
    using assms
    by (cases \<open>v i\<close>; cases \<open>\<alpha> v_code i\<close>) (auto elim!: vec_relE | blast)+
  thus ?thesis
    using assms 
    by auto
qed

lemma vec_rel_in_vars[simp]: \<open>vec_rel (=) x_code x \<Longrightarrow> x i = Some y \<Longrightarrow> i < dims\<close>
  using scope_invar_subs[of x_code] by (elim vec_relE) force

lemma vec_rel_in_doms[simp]: \<open>vec_rel (=) x_code x \<Longrightarrow> x i = Some y \<Longrightarrow> y \<in> doms i\<close>
  using scope_invar_subs[of x_code] 
  by (auto elim!: vec_relE) (metis \<alpha>_some_in_doms domIff option.exhaust_sel)

lemma vec_rel_empty[simp, intro]: \<open>vec_rel R empty Map.empty\<close>
  by auto

end

end