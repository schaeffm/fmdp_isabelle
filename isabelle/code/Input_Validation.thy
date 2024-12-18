theory Input_Validation
  imports 
    Code_Setup 
    API_Code 
    API_Code_Rel
    Code_Inst
    "collections/Scoped_Fn_Inst"
begin

text \<open>
High-Level Idea:
1.  within the locale for code definitions only, define functions to check the input. If the input 
  checking is successful, we obtain the guarantees from the locale with assumptions.
2. We also have to define abstraction functions that lift an MDP to its abstract version + 
  instantiate Relation Locales from within Code locales.
\<close>

record ('s, 'pmf) api_input = 
  api_input_dims :: nat
  api_input_doms :: \<open>nat \<Rightarrow> nat\<close>

    api_input_t_max_code :: nat
    api_input_\<epsilon>_code :: "real"
    api_input_rewards_code_fn :: "nat \<Rightarrow> nat \<Rightarrow> real Scoped_Tree"
    api_input_rewards_scope_code :: "nat \<Rightarrow> nat \<Rightarrow> 's"
    api_input_reward_dim_code :: "nat \<Rightarrow> nat"

    api_input_actions_code :: "nat"
    api_input_d_code :: "nat"

    api_input_transitions_code_fn :: "nat \<Rightarrow> nat \<Rightarrow> 'pmf Scoped_Tree"
    api_input_transitions_scopes_code :: "nat \<Rightarrow> nat \<Rightarrow> 's"

    api_input_l_code :: "real"

    api_input_h_code_fn :: "nat \<Rightarrow> real Scoped_Tree" 
    api_input_h_scope_code :: "nat \<Rightarrow> 's"
    api_input_h_dim_code :: "nat"
    api_input_effects_code :: "nat \<Rightarrow> 's"

locale MDP_Code_DS =
  Scope: NatSet set_ops +
  Vec: Vec vec_ops set_ops dims doms +
  SR: ScopedStateReal sr_ops vec_ops set_ops dims doms +
  SE: ScopedStateEReal er_ops vec_ops set_ops dims doms +
  SP: ScopedStatePmf sp_ops sp_pmf_ops vec_ops set_ops pmf_set_ops dims doms +
  STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops dims doms +
    Coeffs: Coeffs constr_map_ops
  for 
    sr_ops :: \<open>('f, 'state, 'nat_set) scoped_fn_real_ops\<close> and
    ste_ops :: \<open>('f, 'ef) scoped_fn_to_ereal_ops\<close> and
    er_ops :: \<open>('ef, 'state, 'nat_set) scoped_fn_ereal_ops\<close> and
    sp_ops :: \<open>('pf, 'state, 'natpmf, 'nat_set) scoped_fn_basic_ops\<close> and
    constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close>
and vec_ops :: \<open>('state, nat,  'nat_set) vec_ops\<close>
and set_ops :: \<open>(nat, 'nat_set) oset_ops\<close> 
and sp_pmf_ops :: \<open>('natpmf, nat, 'pmf_set) pmf_ops\<close>
and pmf_set_ops :: \<open>(nat, 'pmf_set) oset_ops\<close> 
and dims doms
and lp_oracle :: \<open>nat \<Rightarrow> sparse_vec_ty \<Rightarrow> sparse_mat_ty \<Rightarrow> sparse_vec_ty \<Rightarrow> sparse_vec_ty LP_Cert option\<close>

text \<open>
We need a system description for which one may efficiently check that the claimed scopes are in fact
respected. Therefore, the system is described as nested arrays, each level tagged with a system 
dimension.
\<close>

locale Factored_API_Input_Defs =
  MDP_Code_DS +
  fixes
    api_input :: \<open>('c, 'f) api_input\<close>
  assumes
    dims: \<open>dims = api_input_dims api_input\<close> and
    doms: \<open>\<And>i. i < dims \<Longrightarrow> doms i = {..<api_input_doms api_input i}\<close>
begin

abbreviation \<open>t_max_code \<equiv> api_input_t_max_code api_input\<close>
abbreviation \<open>\<epsilon>_code \<equiv> api_input_\<epsilon>_code api_input\<close>
abbreviation \<open>rewards_code_fn \<equiv> api_input_rewards_code_fn api_input\<close>
abbreviation \<open>d_code \<equiv> api_input_d_code api_input\<close>
abbreviation \<open>reward_dim_code' a \<equiv> api_input_reward_dim_code api_input a\<close>
abbreviation \<open>rewards_scope_code' a i \<equiv> api_input_rewards_scope_code api_input a i\<close>
abbreviation \<open>rewards_scope_code a i \<equiv>
  rewards_scope_code' a (i - (if a = d_code then 0 else reward_dim_code' d_code))\<close>
abbreviation \<open>actions_code \<equiv> api_input_actions_code api_input\<close>
abbreviation \<open>reward_dim_code a \<equiv> reward_dim_code' a +
  (if a = d_code then 0 else reward_dim_code' d_code)\<close>
abbreviation \<open>transitions_code_fn \<equiv> api_input_transitions_code_fn api_input\<close>
abbreviation \<open>transitions_scopes_code \<equiv> api_input_transitions_scopes_code api_input\<close>
abbreviation \<open>l_code \<equiv> api_input_l_code api_input\<close>
abbreviation \<open>h_code_fn \<equiv> api_input_h_code_fn api_input\<close>
abbreviation \<open>h_scope_code \<equiv> api_input_h_scope_code api_input\<close>
abbreviation \<open>h_dim_code \<equiv> api_input_h_dim_code api_input\<close>
abbreviation \<open>effects_code \<equiv> api_input_effects_code api_input\<close>
abbreviation \<open>dims_code \<equiv> api_input_dims api_input\<close>
abbreviation \<open>doms_code \<equiv> api_input_doms api_input\<close>

fun scoped_tree_eval :: "'y Scoped_Tree \<Rightarrow> 'b \<Rightarrow> 'y"  where
  \<open>scoped_tree_eval (Scoped_Leaf x) v = x\<close>
| \<open>scoped_tree_eval (Scoped_Node i arr) v =
  (let j = Vec.idx v i in
    if j < IArray.length arr then
      scoped_tree_eval (IArray.sub arr j) v else undefined)\<close>
lemmas refl[of scoped_tree_eval, cong]

fun scoped_fold_left :: "'y Scoped_Tree \<Rightarrow> ('acc \<Rightarrow> 'y \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc"  where
  \<open>scoped_fold_left (Scoped_Leaf x) f acc = f acc x\<close>
| \<open>scoped_fold_left (Scoped_Node i arr) f acc =
    foldl (\<lambda>acc st. scoped_fold_left st f acc) acc  (IArray.list_of arr)\<close>

definition \<open>scoped_fold_all st p \<longleftrightarrow> scoped_fold_left st (\<lambda>acc y. acc \<and> p y) True\<close>
lemmas refl[of scoped_fold_all, cong]

fun scoped_tree_lengths :: \<open>'y Scoped_Tree \<Rightarrow> bool\<close> where
\<open>scoped_tree_lengths (Scoped_Leaf x) = True\<close> |
\<open>scoped_tree_lengths (Scoped_Node i arr) \<longleftrightarrow> 
  IArray.length arr = doms_code i \<and>
  (\<forall>a  \<in> set (IArray.list_of arr). scoped_tree_lengths a)\<close>
lemmas refl[of scoped_tree_lengths, cong]

lemmas scoped_tree_lengths.simps(2)[code del]
lemmas scoped_tree_lengths.simps(2)[unfolded IArray.all_def[symmetric], code]

fun scoped_tree_scopes :: \<open>'y Scoped_Tree \<Rightarrow> 'c \<Rightarrow> bool\<close> where
\<open>scoped_tree_scopes (Scoped_Leaf x) s = True\<close> |
\<open>scoped_tree_scopes (Scoped_Node i arr) s \<longleftrightarrow> 
    Scope.memb i s \<and> (\<forall>a  \<in> set (IArray.list_of arr). scoped_tree_scopes a s)\<close>
lemmas refl[of scoped_tree_scopes, cong]

lemmas scoped_tree_scopes.simps(2)[code del]
lemmas scoped_tree_scopes.simps(2)[unfolded IArray.all_def[symmetric], code]

definition \<open>check_scoped_tree f s \<longleftrightarrow> scoped_tree_lengths f \<and> scoped_tree_scopes f s\<close>
lemmas refl[of check_scoped_tree, cong]

lemma set_iarray_iff: \<open>x \<in> set_iarray arr \<longleftrightarrow> x \<in> set (IArray.list_of arr)\<close>
  by (cases arr) auto

lemma check_scoped_tree_eval:
  assumes 
    \<open>Scope.invar s\<close>
    \<open>check_scoped_tree f s\<close>
    \<open>Vec.invar v\<close>
    \<open>Vec.invar v'\<close>
    \<open>Scope.\<alpha> s \<subseteq> dom (Vec.\<alpha> v)\<close>
    \<open>Scope.\<alpha> s \<subseteq> dom (Vec.\<alpha> v')\<close>
    \<open>Vec.\<alpha> v |` Scope.\<alpha> s = Vec.\<alpha> v' |` Scope.\<alpha> s\<close>
  shows
    \<open>scoped_tree_eval f v = scoped_tree_eval f v'\<close>
proof -

  have the_v_eq_v'[simp]: \<open>the (Vec.\<alpha> v i) = the (Vec.\<alpha> v' i)\<close> if \<open>i \<in> Scope.\<alpha> s\<close> for i
    using assms that
    by auto

  show ?thesis
 using assms(2)
proof (induction f)
  case (Scoped_Node x1a x2)
  show ?case
    using assms dims doms Scoped_Node.prems
    by (auto simp add: check_scoped_tree_def subset_iff set_iarray_iff intro!: Scoped_Node.IH)
qed auto
qed

lemma check_scoped_tree_valid: \<open>Scope.invar s \<Longrightarrow> check_scoped_tree f s \<Longrightarrow> SR.valid_input_fn s (scoped_tree_eval f)\<close>
  unfolding SR.valid_input_fn_def
  using check_scoped_tree_eval
  by auto

definition \<open>set_to_code_set s = Scope.from_list (sorted_list_of_set s)\<close>
lemmas refl[of set_to_code_set, cong]

definition \<open>SR_scoped_tree_to_scoped_fn f s = SR.from_fn s (scoped_tree_eval f)\<close>
lemmas refl[of SR_scoped_tree_to_scoped_fn, cong]

definition \<open>SP_scoped_tree_to_scoped_fn f s = SP.from_fn s (scoped_tree_eval f)\<close>
lemmas refl[of SP_scoped_tree_to_scoped_fn, cong]

text \<open>We now build the system as expected by the locale: we transform the nested arrays to 
scoped functions\<close>

definition \<open>rewards_code =
  (let 
    drs = 
      IArray.of_fun (\<lambda>i. SR_scoped_tree_to_scoped_fn (rewards_code_fn d_code i) ((rewards_scope_code d_code i))) (reward_dim_code d_code);
    rs =
    IArray.of_fun (\<lambda>a.
      IArray.of_fun (\<lambda>i. if i < reward_dim_code d_code then IArray.sub drs i else
        let i' = i - reward_dim_code d_code in
        SR_scoped_tree_to_scoped_fn (rewards_code_fn a i') ((rewards_scope_code' a i')))
        (reward_dim_code a)) actions_code in
  (\<lambda>a i. IArray.sub (IArray.sub rs a) i))\<close>
lemmas refl[of rewards_code, cong]

lemma rewards_code_lt_d_dim: \<open>a < actions_code \<Longrightarrow> i < reward_dim_code d_code \<Longrightarrow> 
  (rewards_code a i = SR_scoped_tree_to_scoped_fn (rewards_code_fn d_code i) (rewards_scope_code d_code i))\<close>
  unfolding rewards_code_def
  by auto

lemma rewards_code_ge_d_dim: \<open>a < actions_code \<Longrightarrow> i \<ge> reward_dim_code d_code \<Longrightarrow> i < reward_dim_code a \<Longrightarrow> 
  (rewards_code a i = SR_scoped_tree_to_scoped_fn (rewards_code_fn a (i - reward_dim_code d_code)) (rewards_scope_code' a (i - reward_dim_code d_code)))\<close>
  unfolding rewards_code_def
  by auto

definition \<open>transitions_code =
  (let rs =
    IArray.of_fun (\<lambda>a.
      IArray.of_fun (\<lambda>i.
        let act = if Scope.memb i (effects_code a) then a else d_code in
        SP_scoped_tree_to_scoped_fn (transitions_code_fn act i) ((transitions_scopes_code act i)))
        dims_code) actions_code in
  (\<lambda>a. IArray.sub (IArray.sub rs a)))\<close>
lemmas refl[of transitions_code, cong]

definition \<open>h_code = 
  (let hs =
      IArray.of_fun (\<lambda>i. SR_scoped_tree_to_scoped_fn (h_code_fn i) (h_scope_code i)) h_dim_code in
  IArray.sub hs)\<close>
lemmas refl[of h_code, cong]

definition \<open>check_scope_fn f s \<longleftrightarrow> 
  Scope.invar s \<and> Scope.ball s (\<lambda>i. i <dims) \<and> check_scoped_tree f s\<close>
lemmas refl[of check_scope_fn, cong]

section \<open>Input validation\<close>

definition \<open>\<epsilon>_code_valid \<longleftrightarrow> \<epsilon>_code > 0\<close>
lemmas refl[of \<epsilon>_code_valid, cong]

definition \<open>dims_valid \<longleftrightarrow> dims > 0\<close>
lemmas refl[of dims_valid, cong]

definition \<open>doms_valid \<longleftrightarrow> (\<forall>i < dims. doms i > 0)\<close>
lemmas refl[of doms_valid, cong]

definition \<open>h_code_valid \<longleftrightarrow> (\<forall>i < h_dim_code. 
  check_scope_fn (h_code_fn i) (h_scope_code i))\<close>
lemmas refl[of h_code_valid, cong]

definition \<open>reward_code_valid \<longleftrightarrow> (\<forall>a < actions_code. \<forall>i < reward_dim_code' a.
  check_scope_fn (rewards_code_fn a i) (rewards_scope_code' a i))\<close>
lemmas refl[of reward_code_valid, cong]

definition \<open>valid_pmfs f i \<longleftrightarrow>
    scoped_fold_all f (\<lambda>pmf. SP.Pmf.invar pmf \<and> 
  SP.Pmf.Set.ball (SP.Pmf.supp pmf) (\<lambda>y. y < doms_code i))\<close>
lemmas refl[of valid_pmfs, cong]

definition \<open>transitions_code_valid \<longleftrightarrow> (\<forall>a < actions_code. \<forall>i < dims.
        let act = if Scope.memb i (effects_code a) then a else d_code in
  check_scope_fn (transitions_code_fn act i) (transitions_scopes_code act i) \<and>
  valid_pmfs (transitions_code_fn act i) i)\<close>
lemmas refl[of transitions_code_valid, cong]

definition \<open>l_valid \<longleftrightarrow> 0 \<le> l_code \<and> l_code < 1\<close>
lemmas refl[of l_valid, cong]

definition \<open>effects_valid \<longleftrightarrow>
  d_code < actions_code \<and> (\<forall>a < actions_code. 
    Scope.invar (effects_code a) \<and> Scope.ball (effects_code a) (\<lambda>i. i <dims)) \<and>
  Scope.isEmpty (effects_code d_code)\<close>
lemmas refl[of effects_valid, cong]

definition \<open>input_valid \<longleftrightarrow>
  l_valid \<and> \<epsilon>_code_valid \<and> dims_valid \<and> doms_valid \<and> effects_valid \<and>
  h_code_valid \<and> reward_code_valid \<and> transitions_code_valid
  \<close>
lemmas refl[of input_valid, cong]

print_locale MDPCodeDefs
sublocale Code_Inst: MDPCodeDefs where
  rewards_code = rewards_code and
  reward_dim_code = reward_dim_code and
  actions_code = actions_code and
  d_code = d_code and
  transitions_code = transitions_code and
  l_code = l_code and
  h_code = h_code and
  h_dim_code = h_dim_code and
  effects_code = effects_code and
  dims_code = dims_code and
  doms_code = doms_code 
  by unfold_locales

print_locale APIInstDefs
sublocale Code_Inst: APIInstDefs where
  rewards_code = rewards_code and
  reward_dim_code = reward_dim_code and
  actions_code = actions_code and
  d_code = d_code and
  transitions_code = transitions_code and
  l_code = l_code and
  h_code = h_code and
  h_dim_code = h_dim_code and
  effects_code = effects_code and
  constr_map_ops = constr_map_ops and
  lp_oracle = lp_oracle and
  dims_code = dims_code and
  doms_code = doms_code and
  \<epsilon>_code = \<epsilon>_code and
  t_max_code = t_max_code
  by unfold_locales

definition \<open>solver_checked = (if input_valid then Some Code_Inst.api_code else None)\<close>

end

locale Factored_API_Input = 
    Factored_API_Input_Defs +
    assumes 
      input_valid: \<open>input_valid\<close>
begin

lemma 
  dims_valid: \<open>Code_Inst.dims_valid\<close> and
  doms_valid: \<open>Code_Inst.doms_valid\<close> 
  using input_valid dims doms
  unfolding input_valid_def dims_valid_def doms_valid_def
  unfolding Code_Inst.dims_valid_def Code_Inst.doms_valid_def
  by auto

lemma check_scope_valid_input_fn[intro]:
  assumes \<open>check_scope_fn f X\<close>
  shows \<open>SP.valid_input_fn X (scoped_tree_eval f)\<close>
  using assms check_scoped_tree_valid
  unfolding check_scope_fn_def
  by auto

lemmas dims[symmetric, simp]

lemma check_scope_fnD[dest]:
  assumes \<open>check_scope_fn f s\<close>
   shows \<open>Scope.\<alpha> s \<subseteq> {..<dims}\<close>
  \<open>Scope.invar s\<close>
  \<open>check_scoped_tree f s\<close>
  using assms
  unfolding check_scope_fn_def
  by auto

lemma check_scope_fnE[elim]:
  assumes \<open>check_scope_fn f s\<close>
  obtains \<open>Scope.\<alpha> s \<subseteq> {..<dims}\<close>
  \<open>Scope.invar s\<close>
  \<open>check_scoped_tree f s\<close>
  using assms
  unfolding check_scope_fn_def
  by fastforce

lemma reward_valid: \<open>reward_code_valid\<close>
  using input_valid unfolding input_valid_def
  by auto

lemma d_code_in_actions: \<open>d_code < actions_code\<close>
  using input_valid unfolding input_valid_def effects_valid_def
  by auto

lemma invar_SR_scoped_treeI[intro!]: \<open>check_scope_fn f X \<Longrightarrow>  SR.invar (SR_scoped_tree_to_scoped_fn f X)\<close>
  using SR_scoped_tree_to_scoped_fn_def by auto

lemma SR_scoped_tree_scope[simp]: \<open>check_scope_fn f X \<Longrightarrow> SR.scoped_scope_\<alpha> (SR_scoped_tree_to_scoped_fn f X) = Scope.\<alpha> X\<close>
  unfolding SR_scoped_tree_to_scoped_fn_def
  using SR.from_dims_scope
  by blast

lemma invar_rewards_code[simp, intro!]: \<open>a < actions_code \<Longrightarrow> i < reward_dim_code a \<Longrightarrow> SR.invar (rewards_code a i)\<close>
  using reward_valid d_code_in_actions
  unfolding reward_code_valid_def
  unfolding rewards_code_def
  by (auto split: if_splits)

lemma check_scope_scope_in_dims: \<open>check_scope_fn f X \<Longrightarrow> x \<in> Scope.\<alpha> X \<Longrightarrow> x < dims\<close>
  unfolding SR_scoped_tree_to_scoped_fn_def
  by blast

lemma scope_rewards_code_in_dims: \<open>a < actions_code \<Longrightarrow> i < reward_dim_code a \<Longrightarrow> SR.scoped_scope_\<alpha> (rewards_code a i) \<subseteq> {..<dims}\<close>
   using reward_valid d_code_in_actions check_scope_scope_in_dims
  unfolding reward_code_valid_def
  unfolding rewards_code_def
  apply (auto split: if_splits simp:  SR_scoped_tree_scope Scope.ball_correct algebra_simps)
  by (smt (verit, del_insts) add.commute add_diff_inverse_nat add_less_imp_less_left check_scope_scope_in_dims)

lemma rewards_valid: \<open>Code_Inst.rewards_valid\<close>
  using reward_valid
  unfolding reward_code_valid_def
  unfolding Code_Inst.rewards_valid_def
  apply safe
  subgoal
    using scope_rewards_code_in_dims
    by blast
    using reward_valid d_code_in_actions check_scope_valid_input_fn
    unfolding reward_code_valid_def  SR_scoped_tree_to_scoped_fn_def
    by (auto split: if_splits simp: rewards_code_ge_d_dim rewards_code_lt_d_dim)

lemma effects_valid: \<open>Code_Inst.effects_valid\<close>
  unfolding Code_Inst.effects_valid_def
  using input_valid doms
  unfolding input_valid_def dims_valid_def doms_valid_def effects_valid_def transitions_code_valid_def
  unfolding Code_Inst.effects_valid_def 
  unfolding transitions_code_def
  by simp

lemma h_valid: \<open>Code_Inst.h_valid\<close>
  using input_valid doms
  unfolding input_valid_def h_code_valid_def
  unfolding Code_Inst.h_valid_def
  unfolding h_code_def
  unfolding SR_scoped_tree_to_scoped_fn_def
  using SR.from_dims_scope[OF check_scope_valid_input_fn]
  by auto blast


lemma scoped_fold_left_False: \<open>scoped_fold_left st (\<lambda>acc y. acc \<and> p y) False = False\<close>
proof (induction st)
  case (Scoped_Leaf x)
  then show ?case by auto
next
  case (Scoped_Node x1a x2)
  have \<open>\<not>foldl (\<lambda>acc st. scoped_fold_left st (\<lambda>acc y. acc \<and> p y) acc) False xs\<close>
    if \<open>set xs \<subseteq> set (IArray.list_of x2)\<close> for xs
    using that Scoped_Node
    by (induction xs rule: rev_induct) (auto simp: set_iarray_iff)
  then show ?case
    by auto
qed

lemma fold_scoped_fold_left_iff: \<open>foldl (\<lambda>acc st. scoped_fold_left st (\<lambda>acc y. acc \<and> p y) acc) init xs
  \<longleftrightarrow> init \<and> (\<forall>x \<in> set xs.  scoped_fold_left x (\<lambda>acc y. acc \<and> p y) init)\<close>
proof (induction xs arbitrary: init rule: rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    apply (cases init)
    subgoal
      apply (cases \<open> (\<forall>x \<in> set xs.  scoped_fold_left x (\<lambda>acc y. acc \<and> p y) True)\<close>)
      subgoal
        by auto
      subgoal
        using scoped_fold_left_False[of _ p]
        apply simp
        by (smt (verit, best))
      done
    subgoal using scoped_fold_left_False
      by auto
    done
qed


lemma check_scope_fn_children: \<open>check_scope_fn (Scoped_Node i a) s \<Longrightarrow> j < doms_code i \<Longrightarrow> check_scope_fn (IArray.list_of a ! j) s\<close>
  unfolding check_scope_fn_def check_scoped_tree_def
  by auto

lemma check_scope_fn_node_len[simp]: 
  \<open>check_scope_fn (Scoped_Node i a) s \<Longrightarrow> length (IArray.list_of a) = doms_code i\<close>
  unfolding check_scope_fn_def check_scoped_tree_def
  by auto

lemma check_scope_fn_in_scope: \<open>check_scope_fn (Scoped_Node i a) s \<Longrightarrow> i \<in> Scope.\<alpha> s\<close>
  unfolding check_scope_fn_def check_scoped_tree_def
  by auto

lemma scoped_fold_all_eval: 
  assumes \<open>scoped_fold_all t p\<close> \<open>check_scope_fn t s\<close> \<open>Vec.vec_on v (Scope.\<alpha> s)\<close>
  shows \<open>p (scoped_tree_eval t v)\<close>
  using assms
proof (induction t)
  case (Scoped_Leaf x)
  then show ?case
    by (auto simp: scoped_fold_all_def)
next
  case (Scoped_Node i x2)
  have \<open>i < dims\<close>
    using assms Scoped_Node
    by (metis Scope.correct(14) check_scope_fn_def check_scope_fn_in_scope)
  show ?case
    using Scoped_Node.prems
    apply (auto simp: scoped_fold_all_def fold_scoped_fold_left_iff set_iarray_iff intro!: Scoped_Node.IH)
    subgoal
      by (auto intro!: check_scope_fn_children)
    subgoal 
      apply (auto dest!: check_scope_fn_in_scope Vec.idx_in_doms[of _ i])
      using assms(2)  \<open>i < dims\<close>
      by (auto simp: doms)
    done
qed

lemma scoped_fold_all_from_fn_eval:
  assumes \<open>scoped_fold_all t p\<close> \<open>check_scope_fn t s\<close> \<open>Vec.vec_on v (Scope.\<alpha> s)\<close>
  shows \<open>p (SP.scoped_\<alpha> (SP.from_fn s (scoped_tree_eval t)) v)\<close>
  using scoped_fold_all_eval assms
  by (metis SP.scoped_from_dims_apply check_scope_valid_input_fn)
  
lemma valid_pmfs:
  assumes 
    \<open>valid_pmfs p i\<close> 
    \<open>check_scope_fn p (transitions_scopes_code a i)\<close> 
    \<open>Vec.vec_on v (Scope.\<alpha> (transitions_scopes_code a i))\<close>
    \<open>i < dims\<close>
  shows \<open>Code_Inst.valid_pmf (SP.scoped_\<alpha> (SP.from_fn (transitions_scopes_code a i) (scoped_tree_eval p)) v) i\<close>
  using assms
  unfolding valid_pmfs_def Code_Inst.valid_pmf_def
  by (auto dest!: scoped_fold_all_from_fn_eval simp: doms SP.Pmf.Set.ball_correct SP.Pmf.supp_invar)

lemma transitions_valid: \<open>Code_Inst.transitions_valid\<close>
  using input_valid doms
  unfolding input_valid_def transitions_code_valid_def
  unfolding Code_Inst.transitions_valid_def
  unfolding transitions_code_def
  unfolding SP_scoped_tree_to_scoped_fn_def
  unfolding Let_def
  apply simp
  apply safe
  subgoal by (auto simp: dest:check_scoped_tree_valid  split: if_splits intro!: valid_pmfs)
  subgoal by (auto simp: dest:check_scoped_tree_valid  split: if_splits intro!: valid_pmfs) 
      (metis SP.from_dims_scope Scope.correct(14) check_scope_fn_def check_scope_valid_input_fn) 
  subgoal
    apply (rule valid_pmfs)
    apply presburger
    apply presburger
    apply (auto split: if_splits intro!: )
    by (metis (no_types, lifting) SP.from_dims_scope check_scope_valid_input_fn local.Vec.some_idx subsetD)
  subgoal by (auto simp: dest:check_scoped_tree_valid  split: if_splits intro!: valid_pmfs)
  subgoal
    apply (auto split: if_splits)
    apply (subst (asm) SP.from_dims_scope)
    by blast+
  subgoal for a i
    apply (auto split: if_splits intro!: valid_pmfs)
    apply (subst (asm) SP.from_dims_scope)
    by blast+
  done

lemma mdp_code_valid: \<open>Code_Inst.mdp_code_valid\<close>
  unfolding Code_Inst.mdp_code_valid_def
  using dims_valid doms_valid effects_valid h_valid rewards_valid transitions_valid
  using Code_Inst.l_valid_def input_valid input_valid_def l_valid_def 
  by auto
  
print_locale MDPCode
sublocale Code_Inst: MDPCode where
  rewards_code = rewards_code and
  reward_dim_code = reward_dim_code and
  actions_code = actions_code and
  d_code = d_code and
  transitions_code = transitions_code and
  l_code = l_code and
  h_code = h_code and
  h_dim_code = h_dim_code and
  effects_code = effects_code and
  dims_code = dims_code and
  doms_code = doms_code
  using Code_Inst.dims_match_def Code_Inst.doms_match_def dims doms mdp_code_valid
  by unfold_locales blast+


lemma \<epsilon>_pos: \<open>0 < \<epsilon>_code\<close>
  using input_valid input_valid_def \<epsilon>_code_valid_def
  by auto

(* API Inst *)
sublocale Code_Inst: APIInst where
  rewards_code = rewards_code and
  reward_dim_code = reward_dim_code and
  actions_code = actions_code and
  d_code = d_code and
  transitions_code = transitions_code and
  l_code = l_code and
  h_code = h_code and
  h_dim_code = h_dim_code and
  effects_code = effects_code and
  constr_map_ops = constr_map_ops and
  lp_oracle = lp_oracle and
  dims_code = dims_code and
  doms_code = doms_code and
  \<epsilon>_code = \<epsilon>_code and
  t_max_code = t_max_code
  using \<epsilon>_pos 
  by unfold_locales

lemma api_rel_code:
  assumes \<open>solver_checked = Some res\<close>
  shows \<open>Code_Inst.API_Code_Interp.MDP_Code_Rel.api_rel res Code_Inst.API_Code_Interp.MDP_Code_Rel.api\<close>
proof -
  have *: \<open>res = Code_Inst.API_Code_Interp.api_code\<close>
    using assms
    unfolding solver_checked_def Code_Inst.api_code_def
    by (auto simp only: split: if_splits)
  thus ?thesis
    unfolding *
    using Code_Inst.API_Code_Interp.MDP_Code_Rel.api_rel
    by meson
qed

end

context Factored_API_Input_Defs
begin

sublocale Code_Inst: APIInstDefs where
  rewards_code = rewards_code and
  reward_dim_code = reward_dim_code and
  actions_code = actions_code and
  d_code = d_code and
  transitions_code = transitions_code and
  l_code = l_code and
  h_code = h_code and
  h_dim_code = h_dim_code and
  effects_code = effects_code and
  constr_map_ops = constr_map_ops and
  lp_oracle = lp_oracle and
  dims_code = dims_code and
  doms_code = doms_code and
  \<epsilon>_code = \<epsilon>_code and
  t_max_code = t_max_code
  by unfold_locales

lemma api_rel_code:
  assumes \<open>solver_checked = Some res\<close>
  shows \<open>Code_Inst.API_Code_Interp.MDP_Code_Rel.api_rel res Code_Inst.API_Code_Interp.MDP_Code_Rel.api\<close>
proof -
  interpret Factored_API_Input
    using assms
    by unfold_locales (auto split: if_splits simp: solver_checked_def)
  show ?thesis
    using api_rel_code assms
    by blast
qed

end
end