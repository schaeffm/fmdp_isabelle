chapter \<open>Code Generation\<close>
theory Code_Setup
  imports
    Code_Util
    Auto_subst
    "../algorithm/Factored_MDP_Util"
    "../algorithm/Factored_MDP_Thy"
    "../algorithm/Decision_List_Policy"
    "collections/Vec_Code"
    "collections/Scoped_Fn_Rel"
    "collections/Scoped_State"
    "collections/PMF_Code"
    "HOL-Library.IArray"
    States_Code
begin  

section \<open>Util\<close>

instance ereal :: linordered_ab_semigroup_add
  by standard

lemma IArray_nth[simp]: \<open>IArray x !! n = x ! n\<close>
  by auto

text \<open>Relationships between \<^const>\<open>sum_list\<close> and \<^const>\<open>sum\<close>\<close>

lemma prod_list_distinct_conv_prod_set:
  "distinct xs \<Longrightarrow> prod_list (map f xs) = prod f (set xs)"
  by (induct xs) simp_all

lemma interv_prod_list_conv_prod_set_nat:
  "prod_list (map f [m..<n]) = prod f (set [m..<n])"
  by (simp add: prod_list_distinct_conv_prod_set)

lemma prod_list_prod_nth:
  "prod_list xs = (\<Prod> i = 0 ..< length xs. xs ! i)"
  using interv_prod_list_conv_prod_set_nat [of "(!) xs" 0 "length xs"] by (simp add: map_nth)

lemma prod_list_prod_nth_map:
  "prod_list (map f xs) = (\<Prod> i = 0 ..< length xs. f (xs ! i))"
  unfolding prod_list_prod_nth by auto

lemma sum_list_sum_nth_map:
  "sum_list (map f xs) = (\<Sum> i = 0 ..< length xs. f (xs ! i))"
  unfolding sum_list_sum_nth by auto

lemma map_upt_nth[simp]: \<open>i < n \<Longrightarrow> map f [0..<n] ! i = f i\<close>
  by auto

section \<open>Basic Code Equations\<close>
context Factored_MDP_Default_Consts
begin

fun assignments_abs_aux where
  \<open>assignments_abs_aux [] v = [v]\<close>
| \<open>assignments_abs_aux (i#is) v =
  concat (map (\<lambda>y. assignments_abs_aux is (v(i \<mapsto> y))) (sorted_list_of_set (doms i)))\<close>

definition "assignments_abs is = assignments_abs_aux (sorted_list_of_set is) Map.empty"

end

context Factored_MDP_Default
begin

lemma partial_states_on_eq_imp_on_subs: \<open>x \<in> partial_states_on_eq X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> 
  x \<in> partial_states_on Y\<close>
  by blast

lemmas doms_fin[simp, intro!]

section \<open>Alternative version of assignments\<close>

lemma assignments_abs_aux_keep_dim:
  assumes \<open>i \<notin> set is\<close> \<open>x \<in> set (assignments_abs_aux is v)\<close>
  shows \<open>x i = v i\<close>
  using assms
  by (induction rule: assignments_abs_aux.induct) auto

lemma set_assignments_abs_aux:
  assumes \<open>set xs \<subseteq> vars\<close> \<open>disjnt (dom v) (set xs)\<close> \<open>distinct xs\<close>
  shows \<open>set (assignments_abs_aux xs v) = 
    {v'. (\<forall>i \<in> UNIV - set xs. v' i = v i) \<and> (\<forall>i \<in> set xs. v' i \<noteq> None \<and> the (v' i) \<in> doms i)}\<close>
  using assms
  by (induction xs arbitrary: v) auto

lemma set_assignments_abs_aux':
  assumes \<open>set xs \<subseteq> vars\<close> \<open>disjnt (dom v) (set xs)\<close> \<open>distinct xs\<close>
  shows \<open>set (assignments_abs_aux xs v) = 
    {v'. (\<forall>i \<in> UNIV - set xs. v' i = v i) \<and> (\<forall>i \<in> set xs. case v' i of None \<Rightarrow> False | Some y \<Rightarrow> y \<in> doms i)}\<close>
  using assms set_assignments_abs_aux[of xs v]
  by (auto split: option.splits)

lemma set_assignments_abs[simp]: \<open>X \<subseteq> vars \<Longrightarrow> set (assignments_abs X) = partial_states_on_eq X\<close>
  unfolding assignments_abs_def
  by (subst set_assignments_abs_aux')
      (fastforce intro!: partial_states_on_eqI elim!: partial_states_on_eqE ball_diffE split: option.splits)+

lemma assignments_abs_aux_ne:
 \<open>set xs \<subseteq> vars \<Longrightarrow> assignments_abs_aux xs v \<noteq> []\<close>
  using doms_ne
  by (induction xs arbitrary: v) auto

lemma assignments_abs_aux_xor: 
  assumes \<open>a \<notin> set xs\<close>\<open>y \<noteq> z\<close> \<open>set xs \<subseteq> vars\<close>
  shows \<open>x \<in> set (assignments_abs_aux xs (v(a \<mapsto> y))) \<Longrightarrow> x \<notin> set (assignments_abs_aux xs (v(a \<mapsto> z)))\<close>
  using assms 
    assignments_abs_aux_keep_dim[of a xs x \<open>(v(a \<mapsto> z))\<close>] 
    assignments_abs_aux_keep_dim[of a xs x \<open>(v(a \<mapsto> y))\<close>]
  by fastforce

lemma assignments_abs_aux_disj:
  assumes \<open>a \<notin> set xs\<close>\<open>y \<noteq> z\<close> \<open>set xs \<subseteq> vars\<close>
  shows \<open>disjnt (set (assignments_abs_aux xs (v(a \<mapsto> y)))) (set (assignments_abs_aux xs (v(a \<mapsto> z))))\<close>
  using assms assignments_abs_aux_xor[of a xs y z]
  by (auto simp: disjnt_iff)

lemma assignments_abs_aux_neq:
  assumes \<open>a \<notin> set xs\<close>\<open>y \<noteq> z\<close> \<open>set xs \<subseteq> vars\<close>
  shows \<open>assignments_abs_aux xs (v(a \<mapsto> y)) \<noteq> (assignments_abs_aux xs (v(a \<mapsto> z)))\<close>
  using assms assignments_abs_aux_xor[of a xs y z] assignments_abs_aux_ne[of xs]
  by (metis last_in_set)

lemma distinct_assignments_abs_aux:
  assumes \<open>set xs \<subseteq> vars\<close> \<open>distinct xs\<close>
  shows \<open>distinct (assignments_abs_aux xs v)\<close>
  using assms
proof (induction xs arbitrary: v)
  case (Cons a xs)
  show ?case
    unfolding assignments_abs_aux.simps
  proof (rule distinct_concat, goal_cases)
    case 1 show ?case
      using Cons assignments_abs_aux_neq[of a xs]
      by (auto intro!: inj_onI simp: distinct_map)
    case 2 thus ?case
      using Cons by auto
    case 3 thus ?case
      using Cons assignments_abs_aux_xor[of a xs]
      by auto metis
  qed
qed auto

end

locale MDPCodeDefs =
  Scope: NatSet set_ops +
  Vec: Vec vec_ops set_ops dims doms +
  SR: ScopedStateReal sr_ops vec_ops set_ops dims doms +
  SP: ScopedStatePmf sp_ops sp_pmf_ops vec_ops set_ops pmf_set_ops dims doms
  for
    sr_ops :: \<open>('sr, 'state, 'nat_set) scoped_fn_real_ops\<close> and
    sp_ops :: \<open>('sp, 'state, 'pmf, 'nat_set) scoped_fn_basic_ops\<close> and 
  vec_ops :: \<open>('state, nat, 'nat_set) vec_ops\<close> and 
  set_ops :: \<open>(nat, 'nat_set) oset_ops\<close> and 
  sp_pmf_ops ::  "('pmf, nat, 'pmf_set) pmf_ops" and 
  pmf_set_ops
  and dims doms +
  fixes
    dims_code :: nat and
    doms_code :: \<open>nat \<Rightarrow> nat\<close> and
    rewards_code :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'sr\<close> and
    reward_dim_code :: \<open>nat \<Rightarrow> nat\<close> and

    actions_code :: \<open>nat\<close> and
    d_code :: \<open>nat\<close> and

    transitions_code :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'sp\<close> and

    l_code :: real and

    h_code :: \<open>nat \<Rightarrow> 'sr\<close> and
    h_dim_code :: \<open>nat\<close> and

    effects_code :: \<open>nat \<Rightarrow> 'nat_set\<close>
begin

definition \<open>\<Gamma>\<^sub>a_code a X =
  Scope.Union_sets (map (\<lambda>i. SP.scope (transitions_code a i)) (Scope.to_list X))\<close>
lemmas refl[of \<Gamma>\<^sub>a_code, cong]

fun assignments_impl_aux where
  \<open>assignments_impl_aux [] xs = xs\<close>
| \<open>assignments_impl_aux (i#is) xs = 
    assignments_impl_aux is (concat (map (\<lambda>x. map (\<lambda>y. Vec.update x i y) ([0..<doms_code i])) xs))\<close>

fun assignments_impl_aux' where
  \<open>assignments_impl_aux' [] v = [v]\<close>
| \<open>assignments_impl_aux' (i#is) v = 
    concat (map (\<lambda>y. assignments_impl_aux' is (Vec.update v i y)) ([0..<doms_code i]))\<close>

definition \<open>assignments_impl X = assignments_impl_aux' (Scope.to_sorted_list X) Vec.empty\<close>
lemmas refl[of assignments_impl, cong]

definition \<open>g_elem h hs h_ys i a x = (
  let
    ts = transitions_code a
  in
    \<Sum>y \<leftarrow> h_ys. (\<Prod>i \<leftarrow> Scope.to_list hs. 
      SP.Pmf.prob_at (SP.scoped_\<alpha> (ts i) x) (Vec.idx y i)) * 
      SR.scoped_\<alpha> h y
)\<close>
lemmas refl[of g_elem, cong]

definition \<open>g_code_i_a h hs h_ys i a = (
  let
    parents = \<Gamma>\<^sub>a_code a hs;
    gi = g_elem h hs h_ys i a
  in
    SR.scoped_eval (SR.from_fn parents gi))\<close>

definition \<open>g_code_i i = 
  (let 
    h = h_code i;
    hs = SR.scope h;
    h_ys = assignments_impl hs;
    as = [0..<actions_code];
    gi = g_code_i_a h hs h_ys i;
    arr = IArray (map gi as)
 in 
    (IArray.sub arr))\<close>

definition \<open>g_arr = (
  let
    is = [0..<h_dim_code];
    arr = IArray (map g_code_i is)
  in
    arr)\<close>

lemmas refl[of g_code, cong]
definition \<open>g_code = (
  let
    is = [0..<h_dim_code];
    arr = IArray (map g_code_i is)
  in
    IArray.sub arr)\<close>
lemmas refl[of g_code, cong]

definition \<open>R\<^sub>a_code a x = 
  (\<Sum>i = reward_dim_code d_code..<reward_dim_code a. SR.scoped_\<alpha> (rewards_code a i) x)\<close>
lemmas refl[of R\<^sub>a_code, cong]

definition \<open>I\<^sub>a_code a =
  Scope.from_list 
  (filter 
    (\<lambda>i. \<not>Scope.disjoint (effects_code a) (SR.scope (h_code i))) 
    [0..<h_dim_code])\<close>
lemmas refl[of I\<^sub>a_code, cong]

definition \<open>dims_match \<longleftrightarrow> dims_code = dims\<close>
definition \<open>doms_match \<longleftrightarrow> (\<forall>i < dims. {..<doms_code i} = doms i)\<close>

definition \<open>dims_valid \<longleftrightarrow> dims > 0\<close>
definition \<open>doms_valid \<longleftrightarrow> (\<forall>i < dims. doms_code i > 0)\<close>

definition \<open>rewards_valid \<longleftrightarrow> (\<forall>a < actions_code. \<forall>i < reward_dim_code a. 
  SR.invar (rewards_code a i) \<and> SR.scoped_scope_\<alpha> (rewards_code a i) \<subseteq> {..<dims}) \<and>
  (\<forall>a < actions_code. reward_dim_code a \<ge> reward_dim_code d_code) \<and>
  (\<forall>a < actions_code. \<forall>i < reward_dim_code d_code. rewards_code a i = rewards_code d_code i)\<close>

definition \<open>valid_pmf p i \<longleftrightarrow> SP.Pmf.invar p \<and> SP.Pmf.Set.\<alpha> (SP.Pmf.supp p) \<subseteq> doms i\<close>

definition \<open>transitions_valid \<longleftrightarrow> (\<forall>a < actions_code. \<forall>i < dims. 
  SP.invar (transitions_code a i) \<and> 
  SP.scoped_scope_\<alpha> (transitions_code a i) \<subseteq> {..<dims} \<and>
  (\<forall>v \<in> {v. Vec.invar v \<and> SP.scoped_scope_\<alpha> (transitions_code a i) \<subseteq> Vec.scope_\<alpha> v}. 
    valid_pmf (SP.scoped_\<alpha> (transitions_code a i) v) i))\<close>

definition \<open>h_valid \<longleftrightarrow> (\<forall>i < h_dim_code. 
  SR.invar (h_code i) \<and> SR.scoped_scope_\<alpha> (h_code i) \<subseteq> {..<dims})\<close>

definition \<open>effects_valid \<longleftrightarrow>
  d_code < actions_code \<and>
  Scope.isEmpty (effects_code d_code) \<and>
  (\<forall>a < actions_code. Scope.invar (effects_code a) \<and> (\<forall>i \<in> {..<dims} - Scope.\<alpha> (effects_code a).
      (transitions_code a i) = (transitions_code d_code i)))\<close>

definition \<open>l_valid \<longleftrightarrow> 0 \<le> l_code \<and> l_code < 1\<close>

definition \<open>mdp_code_valid \<longleftrightarrow>
  l_valid \<and> dims_valid \<and> doms_valid \<and> rewards_valid \<and> transitions_valid \<and> h_valid \<and> effects_valid\<close>

subsection \<open>@{term consistent_code}\<close>

definition \<open>consistent_code x t \<longleftrightarrow> (Scope.ball (Vec.scope t) (\<lambda>i. Vec.idx x i = Vec.idx t i))\<close>

lemma consistent_code_def': \<open>Vec.invar t \<Longrightarrow> consistent_code x t \<longleftrightarrow> (\<forall>i\<in>Vec.scope_\<alpha> t. Vec.idx x i = Vec.idx t i)\<close>
  unfolding consistent_code_def
  by auto

end

print_locale MDPCodeDefs
locale MDPCode =
  Scope: NatSet set_ops +
  Vec: Vec vec_ops set_ops dims doms +
  SR: ScopedStateReal sr_ops vec_ops set_ops dims doms +
  SP: ScopedStatePmf sp_ops sp_pmf_ops vec_ops set_ops pmf_set_ops dims doms +
  MDPCodeDefs sr_ops sp_ops vec_ops set_ops sp_pmf_ops pmf_set_ops dims doms
  for sr_ops :: \<open>('f, 'state, 'nat_set) scoped_fn_real_ops\<close> and
    sp_ops :: \<open>('pf, 'state, 'natpmf, 'nat_set) scoped_fn_basic_ops\<close>
and vec_ops :: \<open>('state, nat,  'nat_set) vec_ops\<close>
and set_ops :: \<open>(nat, 'nat_set) oset_ops\<close> 
and sp_pmf_ops :: \<open>('natpmf, nat, 'pmf_set) pmf_ops\<close>
and pmf_set_ops :: \<open>(nat, 'pmf_set) oset_ops\<close> 
and dims doms +
assumes 
  dims_match: \<open>dims_match\<close> and
  doms_match: \<open>doms_match\<close> and
  mdp_valid: \<open>mdp_code_valid\<close>

locale MDP_Code_Transfer =
  MDPCodeDefs
  where doms = doms +
  Factored_MDP_Default_Consts
  where doms = doms and actions = actions
  for doms :: \<open>nat \<Rightarrow> nat set\<close> and actions :: \<open>nat set\<close>
begin

sublocale Vec: Vec vec_ops set_ops dims doms
  by unfold_locales

sublocale States_Code_Transfer dims doms doms_code dims_code .

definition \<open>w_rel = rel_fun (rel_on (=) {..<h_dim}) (=)\<close>

interpretation PmfSet: StdOSet \<open>pmf_set_ops\<close>
  using SP.Pmf.set.

abbreviation \<open>state_rel \<equiv> Vec.state_rel\<close>

abbreviation \<open>pol_rel \<equiv> list_all2 (rel_prod state_rel (rel_on (=) actions))\<close>

lemma state_rel_partialD[dest]: \<open>state_rel x_code x \<Longrightarrow> x \<in> partial_states\<close>
  by blast

lemma vec_inv_imp_partial_states[intro, dest]:
  assumes \<open>Vec.invar v\<close>
  shows \<open>Vec.\<alpha> v \<in> partial_states\<close>
  using assms 
  by auto

subsection \<open>@{term dims} and @{term doms}\<close>
definition \<open>dims_rels \<longleftrightarrow> dims_rel \<and> doms_rel\<close>

subsection \<open>@{term actions}\<close>

definition \<open>actions_rel \<longleftrightarrow> {..<actions_code} = actions\<close>

definition \<open>d_rel \<longleftrightarrow> nat_rel d_code d\<close>

definition \<open>effects_rel \<longleftrightarrow> 
  rel_fun (\<lambda>a_code a. a_code = a \<and> a \<in> actions) Scope.set_rel effects_code effects\<close>

definition \<open>actions_rels \<longleftrightarrow> actions_rel \<and> d_rel \<and> effects_rel\<close>

subsection \<open>@{term rewards}\<close>

definition \<open>reward_dim_rel \<longleftrightarrow> nat_rel reward_dim_code reward_dim\<close>

definition \<open>rewards_rel \<longleftrightarrow> 
  fun_rel'
    (rel_on (=) actions)
    (\<lambda>a_code a f_code f. 
      rel_fun 
        (\<lambda>i_code i. i_code = i \<and> i < reward_dim a) 
        (SR.scoped_fn_vec_rel (=) (=))
        f_code
        f)
  rewards_code (\<lambda>a i. (rewards a i, reward_scope a i))\<close>

definition \<open>l_rel = nat_rel l_code l\<close>

definition \<open>reward_rels \<longleftrightarrow> reward_dim_rel \<and> rewards_rel \<and> l_rel\<close>

subsection \<open>@{term transitions}\<close>

definition \<open>transitions_rel \<longleftrightarrow>
  rel_fun
    (rel_on (=) actions)
    (rel_fun (rel_on (=) {..<dims}) 
      (SP.scoped_fn_vec_rel (=) (SP.Pmf.pmf_rel (=))))
  transitions_code (\<lambda>a i. (transitions a i, transitions_scope a i))\<close>

subsection \<open>@{term h}\<close>

definition \<open>h_dim_rel \<longleftrightarrow> nat_rel h_dim_code h_dim\<close>

definition \<open>h_rel \<longleftrightarrow> 
  rel_fun 
    (rel_on (=) {..<h_dim}) (SR.scoped_fn_vec_rel (=) (=)) 
    h_code 
    (\<lambda>i. (h i, h_scope i))\<close>

definition \<open>h_rels \<longleftrightarrow> h_dim_rel \<and> h_rel\<close>

definition \<open>MDP_rels \<longleftrightarrow> h_rels \<and> transitions_rel \<and> reward_rels \<and> dims_rels \<and> actions_rels\<close>

end

locale MDP_Code_Transfer_Rel =
  MDP_Code_Transfer +
  MDPCode +
  Factored_MDP_Default +
  assumes MDP_rels: MDP_rels
begin

lemmas 
  Vec.scope_invar[dest]
  SR.scoped_invar_scope[dest]

lemma MDP_rels_list[intro]: \<open>h_rels\<close> \<open>transitions_rel\<close> \<open>reward_rels\<close> \<open>dims_rels\<close> \<open>actions_rels\<close>
  using MDP_rels 
  unfolding MDP_rels_def 
  by auto

lemma reward_rels[intro]: \<open>reward_dim_rel\<close> \<open>rewards_rel\<close> \<open>l_rel\<close>
  using reward_rels_def by auto

lemma action_rels[intro]: \<open>actions_rel\<close> \<open>d_rel\<close> \<open>effects_rel\<close>
  using actions_rels_def by auto

lemma h_rels[intro]: \<open>h_dim_rel\<close> \<open>h_rel\<close>
  using h_rels_def 
  by auto

lemma dims_rels[intro]: \<open>dims_rel\<close> \<open>doms_rel\<close>
  using dims_rels_def 
  by auto

lemma actions_rel[simp]: \<open>{..<actions_code} = actions\<close>
    using actions_rel_def by blast

definition \<open>act_rel a_code a \<longleftrightarrow> a_code = a \<and> a \<in> actions\<close>

lemma act_relD[dest, simp]: 
  \<open>act_rel a_code a \<Longrightarrow> a_code = a\<close>
  \<open>act_rel a_code a \<Longrightarrow> a \<in> actions\<close>
  unfolding act_rel_def by auto

subsection \<open>doms and dims\<close>

lemma doms_code[intro, simp]: \<open>i < dims \<Longrightarrow> {..<doms_code i} = doms i\<close>
  using dims_rels 
  unfolding doms_rel_def 
  by fastforce

lemma dims_code[intro, simp]: \<open>dims_code = dims\<close>
  using dims_rels 
  unfolding dims_rel_def 
  by auto


lemma doms_code_eq[simp]: \<open>i < dims \<Longrightarrow> doms_code i = card (doms i)\<close>
  using atLeast0LessThan card_lessThan doms_code 
  by metis

lemma card_doms_in_doms[simp, dest]: \<open>ia < card (doms i) \<Longrightarrow> i < dims \<Longrightarrow> ia \<in> doms i\<close>
  using doms_code 
  by auto


lemma lt_card_doms_iff[simp]: \<open>i < dims \<Longrightarrow> j < card (doms i) \<longleftrightarrow> j \<in> doms i\<close>
  by (metis doms_code doms_code_eq lessThan_iff)

subsection \<open>rewards\<close>
lemma rewards_rel[intro]: 
  assumes \<open>a \<in> actions\<close> \<open>i < reward_dim a\<close>
  shows \<open>SR.scoped_fn_state_rel (=) (rewards_code a i) (rewards a i, reward_scope a i)\<close>
  using reward_rels assms unfolding rewards_rel_def by fastforce

lemma partial_states_on_dom[dest]: \<open>x \<in> partial_states_on X \<Longrightarrow> X \<subseteq> dom x\<close>
  by auto

lemma reward_eq_codeI[intro!, simp]:
  assumes \<open>a \<in> actions\<close> \<open>i < reward_dim a\<close>
  assumes \<open>state_rel x_code x\<close> \<open>reward_scope a i \<subseteq> dom x\<close>
  shows \<open>SR.scoped_\<alpha> (rewards_code a i) x_code = rewards a i x\<close>
  using assms rewards_rel 
  by (auto intro!: SR.scoped_fn_state_rel_eqI)

lemma reward_scope_invar[intro!, simp]:
  assumes \<open>a \<in> actions\<close> \<open>i < reward_dim a\<close>
  shows \<open>SR.invar (rewards_code a i)\<close>
  using rewards_rel assms 
  by auto
  
lemma reward_scope_rel[intro!]:
  assumes \<open>a \<in> actions\<close> \<open>i < reward_dim a\<close>
  shows \<open>Scope.set_rel (SR.scope (rewards_code a i)) (reward_scope a i)\<close>
  using assms rewards_rel 
  by fastforce

lemma reward_scope_eq[simp]:
  assumes \<open>a \<in> actions\<close> \<open>i < reward_dim a\<close>
  shows \<open>SR.scoped_scope_\<alpha> (rewards_code a i) = (reward_scope a i)\<close>
  using assms rewards_rel 
  by fastforce

lemma reward_dim_eq[simp, intro]: \<open>a \<in> actions \<Longrightarrow> reward_dim_code a = reward_dim a\<close>
  using reward_dim_rel_def 
  by blast

lemma d_code_eq[simp]: \<open>d_code = d\<close>
  using d_rel_def 
  by blast

lemma l_code_eq[simp]: \<open>l_code = l\<close>
  using reward_rels unfolding l_rel_def 
  by auto

lemma actions_codeI[intro]: \<open>a < actions_code \<Longrightarrow> a \<in> actions\<close>
  using actions_rel 
  by blast

lemmas default_act[simp]

lemma \<open>a \<in> actions \<Longrightarrow> rel_fun (rel_on state_rel (partial_states_on (U\<^sub>a a))) (=) (R\<^sub>a_code a) (R\<^sub>a a)\<close>
  unfolding R\<^sub>a_code_def R\<^sub>a_def 
  by (auto intro!: rel_funI sum.cong)+

lemma R\<^sub>a_rel: \<open>fun_rel'
  (rel_on (=) actions)
  (\<lambda>_ a. rel_fun (rel_on state_rel (partial_states_on (U\<^sub>a a))) (=)) 
  R\<^sub>a_code R\<^sub>a\<close>
  unfolding R\<^sub>a_code_def R\<^sub>a_def 
  by (auto intro!: fun_relI' rel_funI sum.cong)+

lemma R\<^sub>a_impl_correct[simp, intro!]:
  assumes \<open>a \<in> actions\<close> \<open>state_rel x_code x\<close> \<open>U\<^sub>a a \<subseteq> dom x\<close>
  shows \<open>R\<^sub>a_code a x_code = R\<^sub>a a x\<close>
  using assms
  by (intro R\<^sub>a_rel[THEN fun_relD', THEN rel_funD]) auto

subsection \<open>effects\<close>

lemma
  assumes \<open>a \<in> actions\<close>
  shows effects_rel[intro]: \<open>Scope.set_rel (effects_code a) (effects a)\<close>
  and invar_effects_code[simp, intro!]: \<open>Scope.invar (effects_code a)\<close>
  and set_effects_code[simp]: \<open>Scope.\<alpha> (effects_code a) = effects a\<close>
  using action_rels assms
  unfolding effects_rel_def 
  by auto

subsection \<open>h\<close>

lemma
  assumes \<open>i < h_dim\<close>
  shows h_rel[intro]: \<open>SR.scoped_fn_state_rel (=) (h_code i) (h i, h_scope i)\<close>
  and invar_h_code[simp, intro!]: \<open>SR.invar (h_code i)\<close>
  and invar_scope_h_code[intro!, simp]: \<open>Scope.invar (SR.scope (h_code i))\<close>
  and scope_h_code[simp]: \<open>SR.scoped_scope_\<alpha> (h_code i) = h_scope i\<close>
  and h_scope_rel[simp, intro]: \<open>Scope.set_rel (SR.scope (h_code i)) (h_scope i)\<close>
  using h_rels assms
  unfolding h_rel_def 
  by fastforce+

lemma h_dim_code[simp, intro]: \<open>h_dim_code = h_dim\<close>
  using h_rels unfolding h_dim_rel_def by auto

lemma h_code_rel[simp, intro]: \<open>
  i < h_dim \<Longrightarrow>
  h_scope i \<subseteq> dom y \<Longrightarrow> 
  state_rel y_code y \<Longrightarrow> 
  SR.scoped_\<alpha> (h_code i) y_code = h i y\<close>
  using h_rel[of i]
  by auto

lemmas h_scope_dims[simp]

subsection \<open>@{term transitions_code}\<close>
lemma invar_transitions_code[simp, intro!]: 
  \<open>a \<in> actions \<Longrightarrow> i < dims \<Longrightarrow> SP.invar (transitions_code a i)\<close>
  using MDP_rels_list 
  unfolding transitions_rel_def 
  by (auto dest: rel_funD)

lemma scope_transitions_code[simp]: 
  \<open>a \<in> actions \<Longrightarrow> i < dims \<Longrightarrow> SP.scoped_scope_\<alpha> (transitions_code a i) = transitions_scope a i\<close>
  using MDP_rels_list 
  unfolding transitions_rel_def 
  by (auto dest!: rel_funD)

lemma transitions_rel[intro!]:
  assumes \<open>a \<in> actions\<close> \<open>i < dims\<close>
  shows \<open>SP.scoped_fn_vec_rel (=) (SP.Pmf.pmf_rel (=)) (transitions_code a i) (transitions a i, transitions_scope a i)\<close>
  using assms MDP_rels_list unfolding transitions_rel_def
  by fastforce

lemma transitions_rel'[intro!]:
  assumes \<open>a \<in> actions\<close> \<open>i < dims\<close> \<open>state_rel x_code x\<close> \<open>transitions_scope a i \<subseteq> dom x\<close>
  shows \<open>SP.Pmf.pmf_rel (=) (SP.scoped_\<alpha> (transitions_code a i) x_code) (transitions a i x)\<close>
  using assms 
  by (auto elim!: SP.scoped_fn_vec_relE[OF transitions_rel[of a i]])

lemma prob_at_eq[simp]:
  assumes \<open>j \<in> doms i\<close> \<open>i < dims\<close> \<open>a \<in> actions\<close> \<open>state_rel x_code x\<close> \<open>transitions_scope a i \<subseteq> dom x\<close>
  shows \<open>SP.Pmf.prob_at (SP.scoped_\<alpha> (transitions_code a i) x_code) j = pmf (transitions a i x) j\<close>
  using transitions_rel' assms 
  by auto

subsection \<open>@{const I\<^sub>a}\<close>

lemma I\<^sub>a_rel: \<open>rel_fun (rel_on (=) actions) Scope.set_rel I\<^sub>a_code I\<^sub>a\<close>
  unfolding I\<^sub>a_code_def I\<^sub>a_def 
  by fastforce

lemma I\<^sub>a_code_correct[simp, intro!]:
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.\<alpha> (I\<^sub>a_code a) = I\<^sub>a a\<close>
  using assms I\<^sub>a_rel 
  by auto

lemma I\<^sub>a_code_invar[intro!, simp]:
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.invar (I\<^sub>a_code a)\<close>
  using I\<^sub>a_rel assms 
  by auto

subsection \<open>@{const \<Gamma>\<^sub>a}\<close>

lemma lt_actions_code[simp]: \<open>x \<in> actions \<Longrightarrow> x < actions_code\<close>
  using actions_rel 
  by force

unbundle lifting_syntax
lemma \<Gamma>\<^sub>a_rel: assumes \<open>a \<in> actions\<close>
  shows \<open>(rel_on Scope.set_rel {X. X \<subseteq> vars} ===> Scope.set_rel)
  (\<Gamma>\<^sub>a_code a) (\<Gamma>\<^sub>a a)\<close>
  using assms
  unfolding \<Gamma>\<^sub>a_code_def \<Gamma>\<^sub>a_def
  supply Scope.Union_sets_correct[subst]
  by (fastforce simp: subset_iff)

lemma \<Gamma>\<^sub>a_code_correct[intro!]:
  assumes \<open>a \<in> actions\<close> \<open>X' \<subseteq> vars\<close> \<open>Scope.set_rel X X'\<close>
  shows \<open>Scope.\<alpha> (\<Gamma>\<^sub>a_code a X) = \<Gamma>\<^sub>a a X'\<close>
  using assms \<Gamma>\<^sub>a_rel 
  by blast

lemma
  assumes \<open>Scope.invar X\<close> \<open>a \<in> actions\<close> \<open>Scope.\<alpha> X \<subseteq> vars\<close>
  shows \<Gamma>\<^sub>a_code_eq[simp]: \<open>Scope.\<alpha> (\<Gamma>\<^sub>a_code a X) = \<Gamma>\<^sub>a a (Scope.\<alpha> X)\<close>
  and \<Gamma>\<^sub>a_impl_invar[intro!, simp]: \<open>Scope.invar (\<Gamma>\<^sub>a_code a X)\<close>
  using assms \<Gamma>\<^sub>a_rel 
  by blast+

subsection \<open>assignments\<close>

lemma sorted_list_of_doms[simp]: \<open>i < dims \<Longrightarrow> sorted_list_of_set (doms i) = [0..<card (doms i)]\<close>
  by (metis atLeast_upt doms_code doms_code_eq set_upt sorted_list_of_set_range)

lemma assignments_aux_eq:
  assumes  \<open>set xs \<subseteq> vars\<close> \<open>state_rel x y\<close>
  shows "list_all2 state_rel (assignments_impl_aux' xs x) (assignments_abs_aux xs y)"
  using assms
proof (induction xs arbitrary: x y)
  case (Cons a xs)
  show ?case
    using Cons.prems
    by (auto simp: set_zip intro!: List.concat_transfer[THEN rel_funD] 
        list_all2I[of _ _ \<open>(list_all2 state_rel)\<close>] Cons.IH)
qed auto

lemma assignments_aux_rel:
  assumes  \<open>set xs \<subseteq> vars\<close> \<open>state_rel x y\<close>
  shows "(state_rel ===> list_all2 state_rel) (assignments_impl_aux' xs ) (assignments_abs_aux xs)"
  using assms assignments_aux_eq by auto

lemma to_sorted_list_eq[simp]: \<open>Scope.set_rel X_code X \<Longrightarrow> (Scope.to_sorted_list X_code) = sorted_list_of_set X\<close>
  by (metis Scope.to_sorted_list_correct StdSetDefs.set_relE sorted_list_of_set.idem_if_sorted_distinct)

lemma assignments_rel:
  assumes \<open>X \<subseteq> vars\<close> \<open>Scope.set_rel X_code X\<close>
  shows "list_all2 state_rel (assignments_impl X_code) (assignments_abs X)"
  unfolding assignments_impl_def assignments_abs_def
  using assms by (auto intro!: assignments_aux_rel[THEN rel_funD])

lemma assignments_impl_set: 
  assumes \<open>Scope.set_rel X_code X\<close> \<open>X \<subseteq> vars\<close> 
  shows \<open>rel_set state_rel 
      (set (assignments_impl X_code)) 
      (partial_states_on_eq X)\<close>
proof -
  have \<open>list_all2 state_rel (assignments_impl X_code) (assignments_abs (Scope.\<alpha> X_code))\<close>
    using assignments_rel assms by (auto intro: list_all2I)
  hence \<open>rel_set state_rel (set (assignments_impl X_code)) (set (assignments_abs X))\<close>
    using assms list.set_transfer rel_funD by blast
  thus ?thesis
    by (simp add: assms)
qed

lemma distinct_assignments_abs: \<open>X \<subseteq> vars \<Longrightarrow> distinct (assignments_abs X)\<close>
  by (simp add: assignments_abs_def distinct_assignments_abs_aux)

lemma distinct_list_rel:
  assumes 
    \<open>list_all2 R_elem xs ys\<close> 
    \<open>distinct ys\<close> 
    \<open>\<And>x y x' y'. R_elem x y \<Longrightarrow> R_elem x' y' \<Longrightarrow> y \<noteq> y' \<Longrightarrow> x \<noteq> x'\<close>
  shows \<open>distinct xs\<close>
  using assms list_rel_nthE
  unfolding distinct_conv_nth
  by metis

lemma distinct_assignments_impl[intro]:
  assumes \<open>Scope.\<alpha> X \<subseteq> vars\<close> \<open>Scope.invar X\<close>
  shows \<open>distinct (assignments_impl X)\<close>
  using assignments_rel assms distinct_assignments_abs 
  by (blast intro: distinct_list_rel)

lemma set_assignments_abs'[simp]:
assumes \<open>a \<in> actions\<close> \<open>i < h_dim\<close>
shows \<open>set (assignments_abs (\<Gamma>\<^sub>a a ((h_scope i)))) = partial_states_on_eq (\<Gamma>\<^sub>a a ((h_scope i)))\<close>
  using assms 
  by (simp add: \<Gamma>\<^sub>a_subs h_scope_dims)

subsection \<open>@{const g}\<close>

lemma g_elem_correct:
  assumes \<open>i < h_dim\<close>
    and \<open>a \<in> actions\<close>
    and \<open>x \<in> partial_states_on (\<Gamma>\<^sub>a a (h_scope i))\<close>
    and \<open>state_rel x_code x\<close>
  shows \<open>g_elem (h_code i) (SR.scope (h_code i)) (assignments_impl (SR.scope (h_code i))) i a x_code = g' i a x\<close>
proof -
  have prod_eq:\<open>(\<Prod>i\<in>h_scope i. 
    SP.Pmf.prob_at (SP.scoped_\<alpha> (transitions_code a i) x_code) (Vec.idx y i)) * SR.scoped_\<alpha> (h_code i) y
    = (\<Prod>i\<in>h_scope i. pmf (transitions a i x) (the (y' i))) * h i y'\<close> if \<open>state_rel y y'\<close>\<open>y' \<in> partial_states_on (h_scope i)\<close> for y y'
    using assms that partial_states_on_dom[OF that(2)] 
    by (auto simp: subset_iff intro!: prob_at_eq prod.cong) 

  have h_scope_vars: \<open>h_scope i \<subseteq> vars\<close>
    using assms by auto

  show ?thesis
  unfolding g_elem_def g'_def
  using assms h_scope_vars partial_states_on_eq_imp_on_subs distinct_assignments_abs partial_states_on_dom
  by (auto simp flip: set_assignments_abs sum_list_distinct_conv_sum_set prod.distinct_set_conv_list
      intro!: list_rel_sum_list[OF assignments_rel] arg_cong2[where f = \<open>(*)\<close>] prod_eq) auto
qed

lemma valid_input_g_elem[intro!]:
  assumes i: \<open>i < h_dim\<close>
    and a: \<open>a \<in> actions\<close>
  shows \<open>SP.valid_input_fn (\<Gamma>\<^sub>a_code a (SR.scope (h_code i)))
     (g_elem (h_code i) (SR.scope (h_code i)) (assignments_impl (SR.scope (h_code i))) i a)\<close>
    unfolding SP.valid_input_fn_def
    using assms
    supply g_elem_correct[of _ _ \<open>Vec.\<alpha> i\<close> i for i, subst]
    by safe (auto intro: scope_g'_2)

lemma g_i_a_impl_correct[simp, intro]:
  assumes i: \<open>i < h_dim\<close>
    and a: \<open>a \<in> actions\<close>  and \<open>state_rel x_code x\<close>
    and x_partial: \<open>\<Gamma>\<^sub>a a (h_scope i) \<subseteq> dom x\<close>
  shows \<open>SR.scoped_\<alpha> (
    g_code_i_a (h_code i) (SR.scope (h_code i)) (assignments_impl (SR.scope (h_code i))) i a) x_code = g' i a x\<close>
    unfolding g_code_i_a_def
    supply SR.scoped_apply_eval[subst] SR.scoped_from_dims_apply[subst] g_elem_correct[subst]
    using assms valid_input_g_elem
    by auto

lemma g_i_impl_correct[simp, intro]:
  assumes i: \<open>i < h_dim\<close>
    and a: \<open>a \<in> actions\<close> and \<open>state_rel x_code x\<close>
    and x_partial: \<open>\<Gamma>\<^sub>a a (h_scope i) \<subseteq> dom x\<close>
  shows \<open>SR.scoped_\<alpha> (g_code_i i a) x_code = g' i a x\<close>
  unfolding g_code_i_def Let_def
  using assms 
  by auto

lemma g_impl_correct[simp, intro]:
  assumes i: \<open>i < h_dim\<close>
    and a: \<open>a \<in> actions\<close>  and \<open>state_rel x_code x\<close>
    and x_partial: \<open>(\<Gamma>\<^sub>a a (h_scope i)) \<subseteq> dom x\<close>
  shows \<open>SR.scoped_\<alpha> (g_code i a) x_code = g' i a x\<close>
  unfolding g_code_def Let_def
  using assms 
  by auto

lemma g_code_i_a_invar[intro!]:
  assumes \<open>i < h_dim\<close> \<open>a \<in> actions\<close>  
  shows \<open>SR.invar (g_code_i_a (h_code i) (SR.scope (h_code i)) (assignments_impl (SR.scope (h_code i))) i a)\<close>
  unfolding g_code_i_a_def Let_def
  using assms by auto

lemma g_code_i_invar[intro!]:
  assumes \<open>i < h_dim\<close> \<open>a \<in> actions\<close>  
  shows \<open>SR.invar (g_code_i i a)\<close>
  unfolding g_code_i_def Let_def 
  using assms 
  by auto

lemma g_impl_invar[intro!, simp]:
  assumes \<open>i < h_dim\<close> \<open>a \<in> actions\<close>  
  shows \<open>SR.invar (g_code i a)\<close>
  unfolding g_code_def Let_def 
  using assms 
  by auto

lemma g_impl_scope[simp]:
  assumes \<open>i < h_dim\<close> \<open>a \<in> actions\<close>
  shows \<open>SR.scoped_scope_\<alpha> ((g_code i a)) = \<Gamma>\<^sub>a a ((h_scope i))\<close>
  unfolding g_code_def g_code_i_def g_code_i_a_def Let_def
  using assms
  supply SR.scope_eval[subst] SR.from_dims_scope[subst] 
  by auto

lemma g_rel:
  assumes \<open>i < h_dim\<close> \<open>a \<in> actions\<close>
  shows \<open>SR.scoped_fn_state_rel (=) ((g_code i a)) (g' i a, \<Gamma>\<^sub>a a ((h_scope i)))\<close>
  using assms by force

lemma consistent_code': \<open>consistent_code x = (\<lambda>t. Scope.ball (Vec.scope t) (\<lambda>i. Vec.idx x i = Vec.idx t i))\<close>
  unfolding consistent_code_def
  by auto

lemma consistent_code_eq[simp]:
  assumes \<open>state_rel x_code x\<close> \<open>state_rel t_code t\<close> \<open>dom t \<subseteq> dom x\<close>
  shows \<open>consistent_code x_code t_code \<longleftrightarrow> consistent x t\<close>
  using assms 
  unfolding consistent_code_def consistent_iff
  by (fastforce simp: subset_iff elim!: ballE)

end

end
