theory Decision_List_Policy
  imports 
    Factored_MDP_Util
    "HOL-Data_Structures.Set_Specs"
begin

section \<open>Policy Improvement\<close>
context Factored_MDP_Default_Consts
begin
definition actions_nondef :: \<open>'a list\<close> where
  \<open>actions_nondef = sorted_list_of_set (Set.remove d actions)\<close>

text \<open>The g function, i.e. the one-step lookahead of the basis functions.\<close>
definition g :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'x state \<Rightarrow> real\<close> where
  \<open>g i a x = (\<Sum>x' \<in> states. p\<^sub>a a x x' * h i x')\<close>

text \<open>Computationally efficient version of @{const g}, that works on partial states.\<close>
definition \<open>g' i a x =
  (\<Sum>y'\<in>partial_states_on_eq (h_scope i). 
    (\<Prod>i\<in>h_scope i. pmf (transitions a i x) (the (y' i))) * h i y')\<close>

text \<open>Additional reward in state x with action choice a vs. default action.\<close>
definition bonus :: \<open>weights \<Rightarrow> 'a \<Rightarrow> 'x state \<Rightarrow> real\<close> where
  \<open>bonus w a x = Q w x a - Q w x d\<close>

text \<open>Computationally efficient version of @{const bonus}.\<close>
definition \<open>bonus' w a x = R\<^sub>a a x + l * (\<Sum>i \<in> I\<^sub>a a. w i * (g' i a x - g' i d x))\<close>

text \<open>List of all possible states with domain @{term X}.\<close>
definition \<open>assignments_lists X =
  map (zip (sorted_list_of_set X)) 
    (product_lists (map (sorted_list_of_set o doms) (sorted_list_of_set X)))\<close>

(* definition \<open>assignments_lists' X = doms ` X\<close> *)

definition assignment_list :: \<open>nat set \<Rightarrow> ('x state) list\<close> where
  \<open>assignment_list D = map map_of (assignments_lists D)\<close>

text \<open>Comparison Functions for bonus triples, to order decision list policy.\<close>
definition \<open>le_bonus = (\<lambda>(_, _, b) (_, _, b'::real). b \<ge> b')\<close>
definition \<open>less_bonus = (\<lambda>(_, _, b) (_, _, b'::real). b > b')\<close>

text \<open>Given a policy + a state, selects the action.\<close>
definition dec_list_to_pol:: \<open>('x state \<times> 'a) list \<Rightarrow> 'x state \<Rightarrow> 'a\<close> where
  \<open>dec_list_to_pol dl x = (snd o the) (List.find (\<lambda>(t, a). consistent x t) dl)\<close>


definition \<open>is_dec_list_pol p \<longleftrightarrow>
  fst ` set p \<subseteq> partial_states \<and>
  snd ` set p \<subseteq> actions \<and>
  distinct p \<and> \<comment> \<open>distinct state-action pairs\<close>
  (\<forall>x \<in> states. \<exists>(t, a) \<in> set p. consistent x t) 
    \<comment> \<open>for each state, the policy contains a consistent partial state\<close>\<close>

definition \<open>rewards_bound a i = (\<Squnion>x \<in> partial_states_on_eq (reward_scope a i). \<bar>rewards a i x\<bar>)\<close>

definition \<open>reward_bound = (\<Squnion>a \<in> actions. (\<Sum>i < reward_dim a. rewards_bound a i))\<close>

end

context Factored_MDP_Default
begin

lemma finite_vars[simp, intro]: \<open>finite vars\<close>
  by auto

lemma sorted_list_of_set_vars[simp, intro]: \<open>X \<subseteq> vars \<Longrightarrow> set (sorted_list_of_set X) = X\<close>
  by (simp add: finite_subset)

subsection \<open>@{term \<open>actions_nondef\<close>}\<close>

lemma set_actions_nondef[simp]: \<open>set actions_nondef = Set.remove d actions\<close>
  using actions_fin
  by (auto simp: actions_nondef_def)

lemma distinct_actions_nondef: \<open>distinct actions_nondef\<close>
  by (auto simp: actions_nondef_def)

subsection \<open>@{term g}\<close>

text \<open>The g function can be efficiently computed.\<close>
lemma g_restr:
  assumes h_dim: \<open>i < h_dim\<close>
  assumes a: \<open>a \<in> actions\<close>
  assumes x: \<open>x \<in> states\<close>
  shows \<open>g i a x = g' i a x\<close>
proof -
  let ?hs = \<open>h_scope i\<close>
  let ?hi = \<open>\<lambda>x. (h i) (restrict_map x (h_scope i))\<close>
  let ?ta = \<open>\<lambda>i x'. pmf (transitions a i x) (the (x' i))\<close>

  let ?ph = \<open>partial_states_on_eq (h_scope i)\<close>
  let ?ph' = \<open>partial_states_on_eq (vars - h_scope i)\<close>

  have "g i a x = (\<Sum>x' \<in> states. p\<^sub>a a x x' * h i x')"
    unfolding g_def
    using assms
    by auto
  also have \<open>\<dots> = (\<Sum>x' \<in> states. p\<^sub>a a x x' * ?hi x')\<close>
  proof -
    have \<open>(h i) (x' |` (h_scope i)) = h i x'\<close> if \<open>x' \<in> partial_states\<close> for x'
      using that h_dim
      by (auto intro!: has_scope_on_restr[of _ partial_states] elim!: partial_statesE)
    thus ?thesis
      using states_imp_partial by force
  qed
  also have \<open>\<dots> = (\<Sum>x' \<in> states. (\<Prod>i<dims. ?ta i x') * ?hi x')\<close>
    unfolding p\<^sub>a_def
    by auto
  also have \<open>\<dots> = (\<Sum>x' \<in> (\<lambda>(y', z'). y' ++ z') ` (?ph \<times> ?ph'). ((\<Prod>i<dims. ?ta i x') * ?hi x'))\<close>
  proof -
    have *: \<open>vars = h_scope i \<union> (vars - h_scope i)\<close>
      using h_dim h_scope_dims by blast
    hence x_split:
      \<open>x = (x |` h_scope i) ++ (x |` (vars - h_scope i))\<close> if \<open>x \<in> states\<close> for x
      using that restrict_dom[of x]
      by (simp add: states_domD)
    have \<open>(\<lambda>(y', z'). y' ++ z') ` (?ph \<times> ?ph') = states\<close>
    proof safe
      fix a b
      assume \<open>a \<in> ?ph\<close> \<open>b \<in> ?ph'\<close>
      thus \<open>a ++ b \<in> states\<close> using h_dim by (intro statesI) auto
    next
      fix x
      assume \<open>x \<in> states\<close>
      hence \<open>(x |` h_scope i, x |` (vars - h_scope i)) \<in> ?ph \<times> ?ph'\<close>
        using h_dim
        by (auto elim!: statesE intro!: restr_partial_states_on_eqI)
      thus \<open>x \<in> (\<lambda>(y', z'). y' ++ z') ` (?ph \<times> ?ph')\<close>
        using x_split \<open>x \<in> states\<close>
        by (metis pair_imageI)
    qed
    thus ?thesis
      using h_dim h_scope
      by auto
  qed
  also have \<open>\<dots> = (\<Sum>y'\<in> ?ph. \<Sum>z'\<in> ?ph'. (\<Prod>i<dims. (?ta i) (y' ++ z')) * ?hi y')\<close>
  proof -
    have *: \<open>inj_on (\<lambda>(y', z'). y' ++ z') (?ph \<times> ?ph')\<close>
      by (rule inj_onI; safe; drule map_add_eq_comp_eq) blast+
    thus ?thesis
      by (subst sum.reindex) (auto intro!: sum.cong simp: Int_commute add_restr_dom sum.cartesian_product)
  qed
  also have \<open>\<dots> = (\<Sum>y'\<in> ?ph. \<Sum>z'\<in> ?ph'. (((\<Prod>i\<in>vars - h_scope i. ?ta i z'))) * (\<Prod>i \<in> h_scope i . ?ta i y') * ?hi y')\<close>
    using h_dim h_scope_dims
    by (auto intro!: sum.cong simp: prod.subset_diff[of \<open>(h_scope i)\<close>] map_add_dom_app_simps)
  also have \<open>\<dots> = (\<Sum>y'\<in> ?ph. (\<Prod>i\<in> h_scope i. ?ta i y') * ?hi y' * (\<Sum>z'\<in> ?ph'. (\<Prod>i\<in>vars - (h_scope i). ?ta i z')))\<close>
    by (auto simp: sum_distrib_left algebra_simps)
  also have \<open>\<dots> = (\<Sum>y'\<in> ?ph. (\<Prod>i\<in> h_scope i. ?ta i y') * ?hi y')\<close>
  proof -
    have *: \<open>partial_states_on_eq (vars - h_scope i) = {v. dom v = vars - h_scope i  \<and> (\<forall>i\<in>dom v. v i \<in> Some ` doms i)}\<close> 
      by (auto  elim: ballE2 intro!: partial_states_on_eqI)
    have \<open>(\<Sum>z'\<in> ?ph'. (\<Prod>i\<in>vars - (h_scope i). ?ta i z')) = 1\<close>
      unfolding *
      using a x
      by (intro sum_pmf[of \<open>(vars - h_scope i)\<close> doms \<open>\<lambda>i. (transitions a i x)\<close>])
        (auto simp: \<Gamma>\<^sub>a_def partial_states_on_states transitions_scope_dims)
    thus ?thesis
      by auto
  qed
  also have \<open>\<dots> = (\<Sum>y'\<in> ?ph. (\<Prod>i\<in> h_scope i. ?ta i y') * (h i) y')\<close>
    by (auto intro!: sum.cong)
  also have \<open>\<dots> = g' i a x\<close>
    unfolding g'_def ..
  finally show ?thesis .
qed

lemma scope_g':
  assumes a: \<open>a \<in> actions\<close>
  assumes i: \<open>i < h_dim\<close>
  shows \<open>has_scope_on (g' i a) partial_states (\<Gamma>\<^sub>a a (h_scope i))\<close>
  unfolding g'_def
  using  assms transitions_scope
  apply (intro has_scope_on_sum has_scope_on_prod has_scope_on_mult)
  apply (rule has_scope_on_compose[where g = \<open>\<lambda>x. pmf x _\<close>])
  by (auto intro!: has_scope_on_subs_dom[of _ partial_states _ \<open>partial_states_on (\<Gamma>\<^sub>a a (h_scope i))\<close>])

lemma scope_g:
  assumes a: \<open>a \<in> actions\<close>
  assumes i: \<open>i < h_dim\<close>
  shows \<open>has_scope_on (g i a) states (\<Gamma>\<^sub>a a (h_scope i))\<close>
  using  assms scope_g'  partial_states_on_states
  by (auto simp: g_restr intro: states_imp_partial cong: has_scope_on_cong)

lemma scope_g_2:
  assumes a: \<open>a \<in> actions\<close>
  assumes i: \<open>i < h_dim\<close>
  assumes \<open>x \<in> states\<close>
  assumes \<open>y \<in> states\<close>
  assumes \<open>x |` (\<Gamma>\<^sub>a a (h_scope i)) = y |`  (\<Gamma>\<^sub>a a (h_scope i))\<close>
  shows \<open>g i a x = g i a y\<close>
  using assms scope_g[of a i] scope_restrict_imp_eq 
  by blast

lemma scope_g'_2:
  assumes a: \<open>a \<in> actions\<close>
  assumes i: \<open>i < h_dim\<close>
  assumes \<open>x \<in> partial_states\<close>
  assumes \<open>y \<in> partial_states\<close>
  assumes \<open>x |` (\<Gamma>\<^sub>a a (h_scope i)) = y |`  (\<Gamma>\<^sub>a a (h_scope i))\<close>
  shows \<open>g' i a x = g' i a y\<close>
  using assms scope_g'[of a i] scope_restrict_imp_eq 
  by blast

lemma no_effect_transitions: 
  assumes \<open>i < dims\<close> \<open>a \<in> actions\<close> \<open>x \<in> partial_states\<close> \<open>i \<notin> effects a\<close>
  shows \<open>transitions a i x = transitions d i x\<close>                  
  using assms effects states_imp_partial by blast

lemma g_eq_d:
  assumes \<open>a \<in> actions\<close> \<open>i < h_dim\<close> \<open>x \<in> states\<close> \<open>i \<notin> I\<^sub>a a\<close> 
  shows \<open>g i a x = g i d x\<close>
  using default_act effects h_scopeD assms scope_g' states_imp_partial[of x]
  by (auto simp: g_restr g'_def intro!: I\<^sub>a_I sum.cong prod.cong) metis

subsection \<open>@{term \<open>bonus\<close>}\<close>

lemma G\<^sub>a_g: \<open>G\<^sub>a a w x = (\<Sum>i < h_dim. w i * g i a x)\<close>
  unfolding G\<^sub>a_eq g_def
  using sum.swap
  by (auto simp: sum_distrib_left algebra_simps)

lemma Q_g:
  assumes \<open>a \<in> actions\<close> \<open>x \<in> partial_states\<close>
  shows \<open>Q w x a = reward a x + l * (\<Sum>i < h_dim. w i * g i a x)\<close>
  by (simp add: assms Q_def G\<^sub>a_g)

lemma bonus_eq_effects:
  assumes \<open>a \<in> actions\<close> \<open>x \<in> states\<close>
  shows \<open>bonus w a x = bonus' w a x\<close>
proof -
  have \<open>bonus w a x = R\<^sub>a a x + l * (\<Sum>i < h_dim. w i * (g i a x - g i d x))\<close>
    unfolding bonus_def
    using assms states_imp_partial
    by (simp add: Q_g default_act algebra_simps sum_subtractf reward_split_default)
  thus ?thesis
    using assms  default_act g_eq_d[of a]
    by (auto intro!: sum.mono_neutral_cong_right simp: bonus'_def g_restr[symmetric])
qed

lemma scope_bonus':
  assumes \<open>a \<in> actions\<close>
  shows \<open>has_scope_on (bonus' w a) partial_states (T\<^sub>a a)\<close>
proof -
  have 1: \<open>has_scope_on (R\<^sub>a a) partial_states (U\<^sub>a a)\<close>
    using assms scope_R\<^sub>a
    by force

  have \<open>has_scope_on (\<lambda>x. (g' i a x - g' i d x)) partial_states (\<Gamma>\<^sub>a' a (h_scope i))\<close> if \<open>i \<in> I\<^sub>a a\<close> for i
    using that default_act scope_g' I\<^sub>a_D assms 
    by (intro has_scope_on_diff) auto

  hence 2: \<open>has_scope_on (\<lambda>x. \<Sum>i \<in> I\<^sub>a a. w i * (g' i a x - g' i d x)) partial_states (T\<^sub>a a)\<close>
    using assms
    by (auto intro!: has_scope_on_scale has_scope_on_sum)

  show ?thesis
    using 1 2 bonus_eq_effects[OF assms] assms
    by (auto intro!: has_scope_on_add simp: bonus'_def)
qed

lemma scope_bonus:
  assumes \<open>a \<in> actions\<close>
  shows \<open>has_scope_on (bonus w a) states (T\<^sub>a a)\<close>
proof -
  have 1: \<open>has_scope_on (R\<^sub>a a) partial_states (U\<^sub>a a)\<close>
    using assms scope_R\<^sub>a
    by force
  have \<open>has_scope_on (g i a) states (\<Gamma>\<^sub>a a (h_scope i))\<close> if \<open>i \<in> I\<^sub>a a\<close> for i
    using assms scope_g that 
    by blast
  hence \<open>has_scope_on (\<lambda>x. (g i a x - g i d x)) states (\<Gamma>\<^sub>a' a (h_scope i))\<close> if \<open>i \<in> I\<^sub>a a\<close> for i
    using that default_act scope_g inf_sup_ord(3) 
    by blast
  hence 2: \<open>has_scope_on (\<lambda>x. \<Sum>i \<in> I\<^sub>a a. w i * (g i a x - g i d x)) states (T\<^sub>a a)\<close>
    using assms
    by (auto intro!: has_scope_on_scale has_scope_on_sum)
  show ?thesis
    using bonus_eq_effects 1 2 assms states_imp_partial I\<^sub>a_D default_act 
    by (auto intro!: has_scope_on_add has_scope_on_scale 
        intro: has_scope_on_subs_subs simp: g_restr bonus'_def)
qed

lemma bonus_default_zero[simp]: \<open>x \<in> partial_states \<Longrightarrow> bonus w d x = 0\<close>
  by (simp add: bonus_def)


lemma bonus_default_zero'[simp]: \<open>x \<in> partial_states \<Longrightarrow> bonus' w d x = 0\<close>
  by (simp add: bonus'_def)

subsection \<open>State Enumeration\<close>

lemma set_prod_assignments:
  assumes \<open>X \<subseteq> vars\<close>
  shows \<open>set (product_lists (map (sorted_list_of_set o doms) (sorted_list_of_set X))) = 
  {xs. length xs = card X \<and> (\<forall>i < card X. xs ! i \<in> doms (sorted_list_of_set X ! i))}\<close>
proof -
  have \<open>finite X\<close>
    using assms finite_nat_iff_bounded by blast
  hence *: \<open>i < card X \<Longrightarrow> finite (doms (sorted_list_of_set X ! i))\<close> for i
    using assms
    by blast
  thus ?thesis
    using assms
    by (auto simp: set_product_lists')
qed

lemma set_assignments_lists:
  assumes \<open>X \<subseteq> vars\<close> 
  shows \<open>set (assignments_lists X) = {xs. map fst xs = sorted_list_of_set X \<and> (\<forall>i<card X. snd (xs ! i) \<in> doms (fst (xs ! i)))}\<close>
proof -
  have [simp]: \<open>finite X\<close>
    using assms finite_nat_iff_bounded 
    by blast
  have \<open>set (assignments_lists X) = zip (sorted_list_of_set X) ` {xs. length xs = card X \<and> (\<forall>i<card X. xs ! i \<in> doms (sorted_list_of_set X ! i))}\<close>
    unfolding assignments_lists_def
    using assms
    by (simp add: set_prod_assignments)
  also have \<open>\<dots> = {xs. map fst xs = sorted_list_of_set X \<and> length xs = card X \<and> (\<forall>i<card X. snd (xs ! i) \<in> doms (sorted_list_of_set X ! i))}\<close> (is \<open>?L = ?R\<close>)
  proof -
    have \<open>x \<in> ?R \<Longrightarrow> x \<in> ?L\<close> for x
      using zip_map_fst_snd[of x]
      by (auto simp: image_iff intro!: exI[of _ \<open>map snd _\<close>])
    thus ?thesis
      by auto
  qed
  also have \<open>\<dots> = {xs. map fst xs = sorted_list_of_set X \<and> length xs = card X \<and> (\<forall>i<card X. snd (xs ! i) \<in> doms (fst (xs ! i)))}\<close>
    using assms 
    by (auto simp: nth_map[of _ _ fst, symmetric])
  also have \<open>\<dots> = {xs. map fst xs = sorted_list_of_set X \<and> (\<forall>i<card X. snd (xs ! i) \<in> doms (fst (xs ! i)))}\<close>
    using length_sorted_list_of_set[of X, symmetric] length_map
    by metis
  finally show ?thesis .
qed

lemma bexD: \<open>(\<forall>x \<in> X. P x) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> P x)\<close>
  by auto

lemma set_assignments_lists':
  assumes \<open>X \<subseteq> vars\<close> 
  shows \<open>set (assignments_lists X) = {xs. map fst xs = sorted_list_of_set X \<and> (\<forall>p \<in> set xs. fst p \<in> X \<and> snd p \<in> doms (fst p))}\<close>
  using assms finite_subset
  by (fastforce simp: list_eq_iff_nth_eq set_assignments_lists in_set_conv_nth dest: bexD)

lemma map_of_map[simp]: \<open>map_of (map (\<lambda>i. (i, f i)) xs) i = (if i \<in> set xs then Some (f i) else None)\<close>
  by (induction xs arbitrary: i ) auto

lemma map_of_ex_Some_fst:
  assumes \<open>i \<in> set (map fst x)\<close>
  shows \<open>\<exists>y. map_of x i = Some y\<close>
  by (metis assms list.set_map map_of_eq_None_iff not_None_eq)

text \<open>Correctness of @{const assignment_list}\<close>
lemma set_assignments:
  assumes \<open>X \<subseteq> {..<dims}\<close>
  shows \<open>set (assignment_list X) = partial_states_on_eq X\<close>
proof safe
  fix x
  assume \<open>x \<in> set (assignment_list X)\<close>
  then obtain x' where \<open>x' \<in> set (assignments_lists X)\<close> \<open>map_of x' = x\<close>
    using \<open>x \<in> set (assignment_list X)\<close> assignment_list_def 
    by auto
  moreover have \<open>finite X\<close>
    using assms finite_nat_iff_bounded by blast
  ultimately show \<open>x \<in> partial_states_on_eq X\<close>
    using assms 
    by (fastforce simp: map_of_eq_None_iff image_set set_assignments_lists' intro!: partial_states_on_eqI)
next
  fix x
  assume x: \<open>x \<in> partial_states_on_eq X\<close>
  let ?x = \<open>map (\<lambda>i. (i, the (x i))) (sorted_list_of_set X)\<close>
  have \<open>?x \<in> set (assignments_lists X)\<close>
    using x
    by (force simp: set_assignments_lists' comp_def)
  moreover have \<open>map_of ?x = x\<close>
    using x assms map_of_map_keys
    by fastforce
  ultimately show  \<open>x \<in> set (assignment_list X)\<close>
    unfolding assignment_list_def
    by (force simp: image_iff)
qed

lemma preorder_le_bonus: \<open>class.preorder le_bonus less_bonus\<close>
  unfolding less_bonus_def le_bonus_def
  by standard auto

lemma find_Some_in_set[dest]: \<open>find P xs = Some y \<Longrightarrow> y \<in> set xs\<close> 
  by (auto simp: find_Some_iff)

lemma dec_list_to_pol[intro!]:
  assumes \<open>is_dec_list_pol p\<close> 
  shows \<open>is_policy (dec_list_to_pol p)\<close>
proof -
  {
    fix s
    assume \<open>s \<in> states\<close>
    hence \<open>find (\<lambda>p. consistent s (fst p)) p \<noteq> None\<close>
      using assms
      unfolding find_None_iff is_dec_list_pol_def
      by (force simp: case_prod_unfold)
    hence \<open>dec_list_to_pol p s \<in> actions\<close>
      unfolding dec_list_to_pol_def case_prod_unfold
      using assms
      by (fastforce simp: is_dec_list_pol_def image_iff)
  }
  thus ?thesis
    unfolding is_policy_def 
    by auto
qed

lemma le_rewards_bound:
  assumes \<open>x \<in> partial_states_on (reward_scope a i)\<close> \<open>a \<in> actions\<close> \<open>i < reward_dim a\<close>
  shows \<open>\<bar>rewards a i x\<bar> \<le> rewards_bound a i\<close>
proof -
  have \<open>rewards a i x = rewards a i (x |` reward_scope a i)\<close>
    apply (rule has_scope_on_restr[symmetric, OF reward_scope])
    using assms 
    by blast+
  thus ?thesis
    unfolding rewards_bound_def
    using fin_partial_states_eq reward_scope_dims assms
    by (auto intro!: cSUP_upper2 restr_partial_states_on_eqI)
qed

lemma reward_bound: 
  assumes \<open>x \<in> states\<close> \<open>a \<in> actions\<close>
  shows \<open>\<bar>reward a x\<bar> \<le> reward_bound\<close>
  unfolding reward_def reward_bound_def
  using actions_fin assms 
  by (auto intro!: cSUP_upper2[of _ _ a] order.trans[OF sum_abs] sum_mono partial_states_onI le_rewards_bound)

end

text \<open>To make the theorems more general, we postulate functions to sort the decision list, 
  generate a list of all states and a list of all actions (minus the default action).
  We then specify their behavior rather than strictly defining their implementation.\<close>
locale DecListPol_Consts =
  Factored_MDP_Default_Consts
  where 
    transitions = transitions
  for
    transitions :: \<open>'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> 'x::{countable, linorder} state \<Rightarrow> 'x pmf\<close>  +
  fixes 
    sort_dec_list :: \<open>('x state \<times> 'a \<times> real) list \<Rightarrow> ('x state \<times> 'a \<times> real) list\<close> and
    assignment_list :: \<open>nat set \<Rightarrow> ('x state) list\<close> and
    actions_nondef :: \<open>'a list\<close>
begin

definition dec_list_act :: \<open>weights \<Rightarrow> 'a \<Rightarrow> ('x state \<times> 'a \<times> real) list\<close> where
  \<open>dec_list_act w a = (
  let
    ts = assignment_list (T\<^sub>a a);
    ts' = filter (\<lambda>t. bonus' w a t > 0) ts;
    ts'' = map (\<lambda>t. (t, a, bonus' w a t)) ts'
  in
    ts''
)\<close>

abbreviation \<open>\<pi>_unsorted w \<equiv> (\<lambda>_. None, d, 0) # concat (map (dec_list_act w) actions_nondef)\<close>
abbreviation \<open>\<pi>_sorted w \<equiv> sort_dec_list (\<pi>_unsorted w)\<close>

definition dec_list_pol :: \<open>weights \<Rightarrow> ('x state \<times> 'a) list\<close> where 
  \<open>dec_list_pol w = map (\<lambda>(t, a, _). (t, a)) (\<pi>_sorted w)\<close>

fun dec_list_pol_filter_aux where
 \<open>dec_list_pol_filter_aux X ((t, a) # xs) = 
   (if (\<forall>x \<in> X. \<not>consistent t x) 
     then              
       (t, a)#dec_list_pol_filter_aux (insert t X) xs 
     else 
       dec_list_pol_filter_aux X xs)\<close> |
 \<open>dec_list_pol_filter_aux X [] = []\<close>

definition \<open>dec_list_pol_filter p = dec_list_pol_filter_aux {} p\<close>
   
definition \<open>dec_list_pol_sel w = dec_list_to_pol (dec_list_pol_filter (dec_list_pol w))\<close>
 
 lemma find_append: \<open>List.find p (xs @ ys) = (case List.find p xs of Some y \<Rightarrow> Some y | None \<Rightarrow>List.find p ys)\<close>
   apply (induction xs arbitrary: ys)
   by auto
 
 lemma append_Cons_eq_append_append: \<open>xs @ (y#ys) = (xs @ [y]) @ ys\<close>
   by auto
 
 lemma consistent_trans: \<open>consistent a b \<Longrightarrow> consistent b c \<Longrightarrow> consistent a c\<close>
   unfolding consistent_def
   by (metis Map.restrict_restrict dom_restrict)
   
 
 lemma dec_list_to_pol_eq_filter: \<open>dec_list_to_pol xs = dec_list_to_pol (dec_list_pol_filter xs)\<close>
 proof -
   have \<open>find (\<lambda>(t, a). consistent x t) (xs @ ys) = (case 
     List.find (\<lambda>(t, a). consistent x t) xs of Some y \<Rightarrow> Some y | None \<Rightarrow> 
     find (\<lambda>(t, a). consistent x t) (dec_list_pol_filter_aux X ys))\<close> if \<open>X \<subseteq> fst ` set xs\<close> for x X ys xs
     using that
     apply (induction ys arbitrary: X xs)
     subgoal by (auto simp: find_append split: option.splits)
     subgoal premises p for y  ys X xs
       apply (cases \<open>find (\<lambda>(t, a). consistent x t) xs\<close>)
       subgoal
         apply (cases \<open>consistent x (fst y)\<close>)
         subgoal
           apply (cases \<open>(\<forall>x \<in> X. \<not>consistent (fst y) x)\<close>)
           subgoal
             apply (cases y)
             by (auto simp: find_append split: option.splits)
           subgoal
             apply (cases y)
             using p(2)
             apply (auto simp: subset_iff find_append find_None_iff split: option.splits)
             by (metis (no_types, lifting) consistent_trans image_iff prod.exhaust_sel)+
           done
         apply (cases y)
         apply (auto simp: find_None_iff split: option.splits)
         subgoal
            apply (subst append_Cons_eq_append_append)
         apply (subst p(1)[of \<open>insert (fst y) X\<close>])
         subgoal using p by auto
         apply (auto split: option.splits simp: find_Some_iff find_append find_None_iff case_prod_unfold nth_mem)
         by (metis fst_conv nth_mem)
       subgoal
         by (auto simp: find_append)
       subgoal
         using p
         apply (auto simp: find_append find_None_iff find_Some_iff split: option.splits)
          apply (metis (no_types, lifting) case_prodE find_None_iff2 case_prod_unfold option.simps(4))
         by (metis nth_mem)
       by (simp add: find_append)
     by (simp add: find_append)
   done
   from this[of \<open>{}\<close> \<open>[]\<close> _ xs]
   show ?thesis
     unfolding dec_list_to_pol_def dec_list_pol_filter_def
     by (auto intro!: ext)
 qed 

end

locale DecListPol =
  DecListPol_Consts +
  Factored_MDP_Default +
  assumes
    mset_sort_dec_list: 
    \<open>\<And>xs. mset (sort_dec_list xs) = mset xs\<close> and
    sorted_sort_dec_list: 
    \<open>\<And>xs. sorted_wrt le_bonus (sort_dec_list xs)\<close> and
    set_actions_nondef[simp]: \<open>set (actions_nondef) = Set.remove d actions\<close> and
    distinct_actions_nondef: \<open>distinct actions_nondef\<close>
    and
    set_assignments: \<open>\<And>X. X \<subseteq> vars \<Longrightarrow> set (assignment_list X) = partial_states_on_eq X\<close> and
    distinct_assignments: \<open>\<And>X. X \<subseteq> vars \<Longrightarrow> distinct (assignment_list X)\<close>
begin

lemma set_sort_dec_list: \<open>set (sort_dec_list xs) = set xs\<close>
  using mset_sort_dec_list mset_eq_setD 
  by blast

subsection \<open>@{term dec_list_act}\<close>

lemma set_dec_list_act: 
  assumes \<open>a \<in> actions\<close>
  shows \<open>set (dec_list_act w a) = 
    {(t, a, bonus' w a t) | t. t \<in> partial_states_on_eq (T\<^sub>a a) \<and> bonus' w a t > 0}\<close>
  unfolding dec_list_act_def
  using set_assignments T\<^sub>a_dims assms
  by auto

lemma distinct_fst_dec_list_act: 
  assumes \<open>a \<in> actions\<close>
  shows \<open>distinct (map fst (dec_list_act w a))\<close>
  unfolding dec_list_act_def
  by (simp add: T\<^sub>a_dims assms distinct_assignments map_idI)

lemmas refl[of dec_list_pol, cong]

lemma set_\<pi>_unsorted: \<open>set (\<pi>_unsorted w) = insert (\<lambda>_. None, d, 0) 
  {(t, a, (bonus' w a) t) |t a. a \<in> Set.remove d actions \<and> t \<in> partial_states_on_eq (T\<^sub>a a) \<and> 0 < (bonus' w a) t}\<close>
  using set_dec_list_act set_actions_nondef
  by auto

lemma partial_states_on_eq_ne: \<open>X \<subseteq> vars \<Longrightarrow> partial_states_on_eq X \<noteq> {}\<close>
  unfolding ex_in_conv[symmetric]
  apply (rule exI[of _ "(\<lambda>i. if i \<in> X then Some (SOME x. x \<in> doms i) else None)"])
  using doms_ne
  by (auto intro!: partial_states_on_eqI simp: some_in_eq split: if_splits)+

lemma assignment_list_ne: \<open>X \<subseteq> vars \<Longrightarrow> assignment_list X \<noteq> []\<close>
  using partial_states_on_eq_ne empty_set set_assignments by metis

lemma dec_list_act_neq_or_empty: 
  assumes \<open>a \<in> actions\<close> \<open>a' \<in> actions\<close> \<open>a \<noteq> a'\<close>
  shows \<open>map (\<lambda>(x, a, b). (x, a)) (dec_list_act w a) \<noteq> map (\<lambda>(x, a, b). (x, a)) (dec_list_act w a') \<or> dec_list_act w a = []\<close>
proof -
  {
    fix t b
    assume \<open>(t, a, b) \<in> set (dec_list_act w a)\<close>
      \<open>dec_list_act w a = dec_list_act w a'\<close>
    hence \<open>(t, a, b) \<in> set (dec_list_act w a')\<close>
      by auto
    hence \<open>False\<close>
      using assms
      by (auto simp: set_dec_list_act)
  }
  thus ?thesis    
    using assms
    unfolding set_empty2[symmetric] set_dec_list_act[OF assms(1)]
    by (auto simp: Setcompr_eq_image[symmetric] set_dec_list_act dest!: arg_cong[of _ _ set])+
qed

lemma removeAll_map_map: \<open>removeAll [] (map (\<lambda>x. map f (f' x)) xs) = map (map f) (removeAll [] (map f' xs))\<close>
  by (induction xs) auto

lemma removeAll_map: \<open>removeAll x (map f xs) = map  f (filter (\<lambda>i. f i \<noteq> x) xs)\<close>
  by (induction xs) auto

lemma distinct_dec_list_act: \<open>a \<in> actions \<Longrightarrow> distinct (dec_list_act w a)\<close>
  unfolding dec_list_act_def
  using distinct_assignments
  by (auto simp: distinct_map inj_on_def intro!: distinct_filter)

lemma distinct_\<pi>_unsorted: \<open>distinct (map (\<lambda>(x, a, b). (x, a)) (\<pi>_unsorted w))\<close>
  using distinct_actions_nondef dec_list_act_neq_or_empty distinct_dec_list_act
  by (auto simp: distinct_map map_concat comp_def set_dec_list_act distinct_concat_iff removeAll_map 
      intro!: inj_onI)

lemma distinct_\<pi>_sorted: \<open>distinct (map (\<lambda>(x, a, b). (x, a)) (\<pi>_sorted w))\<close>
  using distinct_\<pi>_unsorted mset_sort_dec_list
  by (subst mset_eq_imp_distinct_iff[of _ \<open>map (\<lambda>(x, a, b). (x, a)) (\<pi>_unsorted w)\<close>]) force

lemma ex_consistent:
  assumes \<open>X \<subseteq> vars\<close> \<open>t \<in> partial_states_on_eq X\<close>
  shows \<open>\<exists>x. consistent x t \<and> x \<in> states\<close>
proof -
  let ?x = \<open>\<lambda>i. if i \<in> vars - X then Some (SOME x. x \<in> doms i) else t i\<close>
  have \<open>consistent ?x t\<close>
    using assms
    by fastforce
  moreover have \<open>?x \<in> states\<close>
    using assms doms_ne
    by (auto simp: some_in_eq intro!: statesI split: if_splits)+
  ultimately show ?thesis
    by blast
qed

lemma ex_consistent_T\<^sub>a:
  assumes \<open>a \<in> actions\<close> \<open>t \<in> partial_states_on_eq (T\<^sub>a a)\<close>
  shows \<open>\<exists>x. consistent x t \<and> x \<in> states\<close>
  using assms ex_consistent
  using T\<^sub>a_dims
  by blast

lemma aux_dec_list_set: 
  \<open>{(t, a, bonus' w a t) |t a. a \<in> Set.remove d actions \<and> t \<in> partial_states_on_eq (T\<^sub>a a) \<and> 0 < bonus' w a t}
  = {(x |` (T\<^sub>a a), a, bonus w a x) | x a. a \<in> Set.remove d actions \<and> x \<in> states \<and> 0 < bonus w a x}\<close> (is \<open>?L = ?R\<close>)
proof safe
  fix t a 
  assume h: \<open>a \<in> Set.remove d actions\<close> \<open>t \<in> partial_states_on_eq (T\<^sub>a a)\<close> \<open>0 < (bonus' w a) t\<close> 
  moreover then have 
    \<open>consistent (SOME x'. consistent x' t \<and> x' \<in> states) t\<close> 
    \<open>(SOME x'. consistent x' t \<and> x' \<in> states) \<in> states\<close> 
    by (auto intro!: someI2_ex[OF ex_consistent_T\<^sub>a[of a t]])
  moreover then have \<open>bonus' w a (SOME x'. consistent x' t \<and> x' \<in> states) = (bonus' w a) t\<close>
    using h states_imp_partial partial_states_on_eq_imp_partial T\<^sub>a_dims
    by (intro scope_restrict_imp_eq[OF scope_bonus']) (force simp add: partial_states_on_states)+
  moreover have \<open>bonus w a (SOME x'. consistent x' t \<and> x' \<in> states) = (bonus' w a) t\<close>
    using bonus_eq_effects h calculation by auto
  ultimately show
    \<open>\<exists>x' a'. (t, a, (bonus' w a) t) = (x' |` T\<^sub>a a', a', bonus w a' x') \<and> a' \<in> Set.remove d actions \<and> x' \<in> states \<and> 0 < bonus w a' x'\<close>
    by (intro exI[of _ \<open>SOME x. consistent x t \<and> x \<in> states\<close>]) fastforce
next
  fix x  a'
  assume h: \<open>a' \<in> Set.remove d actions\<close> \<open>x \<in> states\<close> \<open>0 < bonus w a' x\<close>
  have \<open>bonus w a' x = bonus' w a' x\<close>
    using bonus_eq_effects h(1) h(2) by auto
  also have \<open>\<dots> = bonus' w a' (x |` T\<^sub>a a')\<close>
    using h 
    by (intro has_scope_on_restr[OF scope_bonus', symmetric]) 
      (auto dest: states_imp_partial intro!: partial_statesI)
  finally show \<open>\<exists>t a. (x |` T\<^sub>a a', a', bonus w a' x) = (t, a, bonus' w a t) \<and>
             a \<in> Set.remove d actions \<and> t \<in> partial_states_on_eq (T\<^sub>a a) \<and> 0 < bonus' w a t\<close>
    using h
    by (auto intro!: restr_partial_states_on_eqI partial_states_onI)
qed

lemma set_\<pi>_sorted: \<open>set (\<pi>_sorted w) =
  insert (\<lambda>_. None, d, 0) 
    {(t, a, (bonus' w a) t) |t a. a \<in> Set.remove d actions \<and> t \<in> partial_states_on_eq (T\<^sub>a a) \<and> 0 < (bonus' w a) t}\<close>
  unfolding set_sort_dec_list
  using set_\<pi>_unsorted
  by auto

lemma sorted_\<pi>_sorted: \<open>sorted_wrt le_bonus (\<pi>_sorted w)\<close>
  using sorted_sort_dec_list .

lemma set_dec_list_pol: \<open>set (dec_list_pol w) = 
  insert (\<lambda>_. None, d) {(t, a) |t a. a \<in> Set.remove d actions \<and> t \<in> partial_states_on_eq (T\<^sub>a a) \<and> 0 < (bonus' w a) t}\<close>
  unfolding dec_list_pol_def Let_def set_map set_\<pi>_sorted
  by (auto simp: image_iff)

lemma empty_partial_states: \<open>Map.empty \<in> partial_states\<close>
  by auto

lemma bonus_\<pi>_sorted:
  assumes \<open>(t, a, b) \<in> set (\<pi>_sorted w)\<close> \<open>consistent x t\<close> \<open>x \<in> states\<close>
  shows \<open>bonus w a x = b\<close>
proof -
  have a: \<open>a \<in> actions\<close>
    using assms default_act
    unfolding set_\<pi>_sorted
    by auto

  have \<open>t \<in> partial_states_on_eq (T\<^sub>a a)\<close>
    using assms default_act
    unfolding set_\<pi>_sorted
    by auto

  hence \<open>dom t = T\<^sub>a a\<close>
    by auto

  thm set_\<pi>_sorted
  have \<open>b = (bonus' w a) t\<close>
    using default_act assms bonus_default_zero empty_partial_states
    by (cases \<open>a = d\<close>) (auto simp: set_\<pi>_sorted)

  have *:\<open>t = x |` T\<^sub>a a\<close>
    using \<open>dom t = T\<^sub>a a\<close> assms(2) by fastforce

  have \<open>(bonus' w a) t = bonus' w a x\<close>
    using assms a \<open>t \<in> partial_states_on_eq (T\<^sub>a a)\<close> scope_bonus
    unfolding *
    by (intro has_scope_on_restr[OF scope_bonus']) blast+
  thus ?thesis
    unfolding \<open>b = (bonus' w a) t\<close> 
    using bonus_eq_effects assms a
    by simp
qed

lemma le_dec_\<pi>_sorted:
  assumes 
    \<open>x \<in> states\<close> 
    \<open>find (\<lambda>(t, a, b). consistent x t) (\<pi>_sorted w) = Some (t, a, b)\<close> 
    \<open>(t', a', b') \<in> set (\<pi>_sorted w)\<close>
    \<open>consistent x t'\<close>
  shows \<open>le_bonus (t, a, b) (t', a', b')\<close>
  using sorted_\<pi>_sorted assms preorder_le_bonus
  by (auto intro: sorted_wrt_find[of le_bonus \<open>(\<pi>_sorted w)\<close> less_bonus \<open>(\<lambda>(t, a, b). consistent x t)\<close>])

lemma le_dec_\<pi>_sorted':
  assumes 
    \<open>x \<in> states\<close> 
    \<open>find (\<lambda>(t, a, b). consistent x t) (\<pi>_sorted w) = Some (t, a, b)\<close> 
    \<open>(t', a', b') \<in> set (\<pi>_sorted w)\<close>
    \<open>consistent x t'\<close>
  shows \<open>b' \<le> b\<close>
  using le_dec_\<pi>_sorted[OF assms]
  unfolding le_bonus_def
  by auto

lemma \<pi>_sorted_bonus_in_opt:
  assumes 
    \<open>x \<in> states\<close> 
    \<open>find (\<lambda>(t, a, b). consistent x t) (\<pi>_sorted w) = Some (t, a, b)\<close> 
    \<open>(t', a', b') \<in> set (\<pi>_sorted w)\<close>
    \<open>consistent x t'\<close>
  shows \<open>bonus w a' x \<le> bonus w a x\<close>
proof -
  have \<open>(t, a, b) \<in> set (\<pi>_sorted w)\<close>
    using assms
    by auto
  hence \<open>b = bonus w a x\<close> \<open>b' = bonus w a' x\<close>
    using set_\<pi>_sorted assms
    by (auto intro!: bonus_\<pi>_sorted[symmetric] simp: find_Some_iff)
  thus ?thesis
    using assms le_dec_\<pi>_sorted'
    by force
qed

lemma restrict_elim_Some: \<open>(x |` D) i = Some y \<Longrightarrow> (i \<in> D \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by fastforce

lemma restr_assignments[intro]: \<open>x \<in> states \<Longrightarrow> D \<subseteq> vars \<Longrightarrow> x |` D \<in> partial_states_on_eq D\<close>
  by (blast intro: restr_partial_states_on_eqI)

lemma restr_self_partial_states_on[intro!]: \<open>x \<in> partial_states_on X \<Longrightarrow>  x |` X \<in> partial_states_on X\<close>
  by (smt (verit, best) partial_states_onE partial_states_onI restrict_elim_Some restrict_map_def)

lemma \<pi>_sorted_bonus_opt:
  assumes 
    \<open>x \<in> states\<close> 
    \<open>find (\<lambda>(t, a, b). consistent x t) (\<pi>_sorted w) = Some (t, a, b)\<close> 
    \<open>a' \<in> actions\<close>
  shows \<open>bonus w a' x \<le> bonus w a x\<close>
proof -
  have \<open>b \<ge> 0\<close>
    using set_\<pi>_sorted assms
    by fastforce

  have \<open>(t, a, b) \<in> set (\<pi>_sorted w)\<close>
    using assms
    by auto

  hence b: \<open>b = bonus w a x\<close>
    using set_\<pi>_sorted assms
    by (auto intro!: bonus_\<pi>_sorted[symmetric] simp: find_Some_iff)

  hence \<open>bonus w a' x \<le> bonus w a x\<close> if \<open>bonus w a' x \<le> 0\<close>
    using that \<open>0 \<le> b\<close> by auto

  moreover have \<open>bonus w a' x \<le> bonus w a x\<close> if \<open>bonus w a' x > 0\<close>
  proof -
    have \<open>a' \<noteq> d\<close>
      using bonus_def that 
      by force
    have ba': \<open>bonus' w a' x = (bonus' w a') (x |` T\<^sub>a a')\<close>
      using assms states_imp_partial T\<^sub>a_dims partial_states_on_states
      by (subst has_scope_on_restr[OF scope_bonus']) (auto intro!: partial_states_on_eq_imp_partial)
    hence \<open>(x |` T\<^sub>a a', a', (bonus' w a') (x |` T\<^sub>a a')) \<in> set (\<pi>_sorted w)\<close>
      unfolding set_\<pi>_sorted
      using assms that bonus_eq_effects
      by (simp add: T\<^sub>a_dims \<open>a' \<noteq> d\<close> restr_assignments)
    thus \<open>bonus w a' x \<le> bonus w a x\<close>
      using consistent_restr assms bonus_eq_effects
      by (auto intro!: le_dec_\<pi>_sorted' simp: ba' b)
  qed
  ultimately show ?thesis
    by fastforce
qed


lemma \<pi>_sorted_find_Some: 
  \<open>\<exists>y. Some y = find (\<lambda>(t, a, b). consistent x t) (\<pi>_sorted w)\<close>
  unfolding Some_ex_find_iff
  using set_\<pi>_sorted consistent_None
  by auto

lemma le_dec_list_pol:
  assumes 
    \<open>x \<in> states\<close>
    \<open>find (\<lambda>(t, a). consistent x t) (dec_list_pol w) = Some (t, a)\<close>
    \<open>a' \<in> actions\<close>
  shows \<open>bonus w a' x \<le> bonus w a x\<close>
proof -
  obtain t' a' b' where *: \<open>find (\<lambda>(t, a, b). consistent x t) (\<pi>_sorted w) = Some (t', a', b')\<close>
    using \<pi>_sorted_find_Some assms
    by (metis surj_pair)
  hence \<open>find (\<lambda>(t, a). consistent x t) (dec_list_pol w) = Some (t', a')\<close>
    unfolding dec_list_pol_def
    by (auto simp: find_map case_prod_beta cong: find_cong)
  thus ?thesis
    using * assms \<pi>_sorted_bonus_opt
    by auto
qed

lemma ex_consistent_dec_list_pol:
  shows \<open>\<exists>ta. find (\<lambda>(t, a). consistent x t) (dec_list_pol w) = Some ta\<close>
proof -
  have \<open>\<exists>t a. Some (t, a) = List.find (\<lambda>(t, a). consistent x t) (dec_list_pol w)\<close>
    using consistent_None set_dec_list_pol Some_ex_find_iff[of \<open>(\<lambda>(t, a). consistent x t)\<close>] 
    by fast
  thus ?thesis
    by metis
qed

theorem dec_list_pol_sel_bonus_opt:
  assumes \<open>x \<in> states\<close> \<open>a \<in> actions\<close>
  shows \<open>bonus w a x \<le> bonus w (dec_list_pol_sel w x) x\<close>
proof -
  obtain t a where \<open>find (\<lambda>(t, a). consistent x t) (dec_list_pol w) = Some (t, a)\<close> \<open>a = dec_list_pol_sel w x\<close>
    unfolding dec_list_pol_sel_def dec_list_to_pol_def dec_list_to_pol_eq_filter[symmetric]
    using ex_consistent_dec_list_pol assms
    by fastforce
  thus ?thesis
    using le_dec_list_pol assms
    by blast
qed

theorem dec_list_pol_sel_Q_opt:
  assumes \<open>x \<in> states\<close> \<open>a \<in> actions\<close>
  shows \<open>Q w x a \<le> Q w x (dec_list_pol_sel w x)\<close>
  using assms dec_list_pol_sel_bonus_opt
  unfolding bonus_def
  by force

lemma distinct_dec_list_pol: \<open>distinct (dec_list_pol w)\<close>
  by (simp add: dec_list_pol_def distinct_\<pi>_sorted)

lemma dec_list_pol_partial: \<open>fst ` set (dec_list_pol w) \<subseteq> partial_states\<close>
  unfolding dec_list_pol_def
  using partial_states_on_eq_imp_partial set_\<pi>_sorted
  by auto

lemma dec_list_pol_acts: \<open>snd ` set (dec_list_pol w) \<subseteq> actions\<close>
  unfolding dec_list_pol_def
  using default_act set_\<pi>_sorted[of w]
  by auto

lemma dec_list_pol_ex_consistent: \<open>x \<in> states \<Longrightarrow> (\<exists>(t, a)\<in>set (dec_list_pol w). consistent x t)\<close>
  using ex_consistent_dec_list_pol[of x w] Some_ex_find_iff[of _ \<open>(dec_list_pol w)\<close>]
  by metis

text \<open>
The main property of @{const dec_list_pol} is: Given a state, the first element of the policy it is
consistent with is the greedy action in that state.
\<close>
lemma dec_list_pol_sel_greedy:
  assumes \<open>x \<in> states\<close>
  shows \<open>is_greedy_act w x (dec_list_pol_sel w x)\<close>
  unfolding is_greedy_act_def
  using dec_list_pol_sel_Q_opt assms
  by blast

lemma dec_list_pol_is_pol: \<open>is_dec_list_pol (dec_list_pol w)\<close>
  unfolding is_dec_list_pol_def
  using distinct_dec_list_pol dec_list_pol_ex_consistent dec_list_pol_partial dec_list_pol_acts
  by auto

lemma dec_list_pol_filter_aux_subs: \<open>set (dec_list_pol_filter_aux X xs) \<subseteq> set xs\<close>
   apply (induction xs arbitrary: X)
   by (fastforce split: if_splits)+
 
 lemma dec_list_pol_filter_subs: \<open>set (dec_list_pol_filter xs) \<subseteq> set xs\<close>
   using dec_list_pol_filter_aux_subs dec_list_pol_filter_def
   by metis
 
 lemma dec_list_pol_filter_subs_distinct: 
   assumes \<open>distinct xs\<close> 
   shows \<open>distinct (dec_list_pol_filter xs)\<close>
 proof -
   have \<open>distinct (dec_list_pol_filter_aux X xs)\<close> for X
     using assms 
     apply (induction xs arbitrary: X)
     subgoal by auto
     subgoal for x
       apply (cases x)
       using dec_list_pol_filter_aux_subs
       by auto
     done
   thus ?thesis
     unfolding dec_list_pol_filter_def
     by auto
 qed
 
 lemma consistent_None_iff: \<open>consistent (\<lambda>_. None) x \<longleftrightarrow> x = (\<lambda>_. None)\<close>
   unfolding consistent_def
   by auto
 
 lemma default_nonfilter: 
   assumes \<open>(\<lambda>_. None, d) \<in> set xs\<close> 
   shows \<open>\<exists>d. (\<lambda>_. None, d) \<in> set (dec_list_pol_filter xs)\<close>
 proof -
   have \<open>(\<exists>a :: 'b. (\<lambda>_ :: 'c. None, a) \<in> set xs) \<Longrightarrow> \<exists>a. (\<lambda>_ :: 'c. None, a) \<in> set (dec_list_pol_filter_aux X xs)\<close> if \<open>(\<lambda>_ :: 'c. None) \<notin> X\<close> for X
     using consistent_None that
   apply (induction xs arbitrary: X)
      apply (auto simp: consistent_None_iff)
     subgoal for a
       apply (cases \<open>a = (\<lambda>_. None)\<close>)
        apply (auto simp: )
       unfolding consistent_None_iff
       by fastforce
     by blast
   from this[of \<open>{}\<close>]
   show ?thesis
     unfolding dec_list_pol_filter_def
     using assms
     by auto
 qed

 lemma default_in_dec_list_pol: \<open>(\<lambda>_. None, d) \<in> set (dec_list_pol w)\<close>
   unfolding dec_list_pol_def
   by (auto simp: image_iff case_prod_unfold set_sort_dec_list)
  
 lemma dec_list_pol_filter_is_pol: \<open>is_dec_list_pol (dec_list_pol_filter (dec_list_pol w))\<close>
   using dec_list_pol_filter_subs dec_list_pol_is_pol  
   unfolding is_dec_list_pol_def
   apply (auto simp: subset_iff image_iff)
      apply fastforce
   apply fastforce
   using dec_list_pol_filter_subs_distinct
   using default_nonfilter default_in_dec_list_pol
   by fastforce+

end
end