theory Factored_MDP_Util
  imports Factored_MDP_Thy MDP_Util Min_Dist
begin

section \<open>(Greedy) Policies on Factored MDPs\<close>
context Factored_MDP_Consts
begin

definition \<open>expl_pol p s = (if s \<in> states_expl then p (from_expl s) else (SOME x. x \<in> actions))\<close>

definition \<open>is_greedy_w w x a = is_arg_max (\<lambda>a. Q w x a) (\<lambda>a. a \<in> actions) a\<close>

definition \<open>is_greedy_pol_w w p = (\<forall>x \<in> states. is_greedy_w w x (p x))\<close>

definition \<open>is_policy p \<longleftrightarrow> (\<forall>s \<in> states. p s \<in> actions)\<close>

definition \<open>bellman_err_w w = (\<Squnion>x \<in> states. dist (\<nu>\<^sub>w w x) (\<Squnion> a \<in> actions. (Q w x a)))\<close>

text \<open>Projection error given a policy and weights\<close>
definition \<open>proj_err_w p w = (\<Squnion>x \<in> states. dist (\<nu>\<^sub>w w x) (Q w x (p x)))\<close>

text \<open>Minimum projection error given a policy\<close>
definition \<open>proj_err_pol p = (\<Sqinter>w. proj_err_w p w)\<close>

end

context Factored_MDP
begin

type_synonym ('c, 'd) pol = \<open>'c state \<Rightarrow> 'd\<close>

lemma is_policyE[elim]:
  assumes \<open>is_policy p\<close>
  obtains \<open>s \<in> states \<Longrightarrow> p s \<in> actions\<close>
  using assms is_policy_def
  by auto

lemma in_actions_expl_iff[simp]: \<open>a \<in> actions_expl (to_expl x) \<longleftrightarrow> a \<in> actions\<close>
  by auto

lemma is_greedy_w_iff:
  assumes \<open>x \<in> states\<close>
  shows \<open>is_greedy_w w x a = E.is_opt_act (\<nu>\<^sub>w_expl w) (to_expl x) a\<close>
  unfolding is_greedy_w_def E.is_opt_act_def
  using assms
  by (auto simp: Q_r_G\<^sub>a intro!: is_arg_max_cong)

lemma expl_pol_eq: \<open>x \<in> states_expl \<Longrightarrow> expl_pol p x = p (from_expl x)\<close>
  using expl_pol_def by force

lemma expl_pol_eq': \<open>x \<in> states \<Longrightarrow> p x = expl_pol p (to_expl x)\<close>
  using expl_pol_def by force

lemma expl_pol_no_state: \<open>s \<notin> states_expl \<Longrightarrow> expl_pol p s \<in> actions\<close>
  unfolding expl_pol_def
  using actions_ne some_in_eq
  by auto

lemma is_policy_iff_expl: \<open>is_policy p \<longleftrightarrow> E.is_dec_det (expl_pol p)\<close>
  using expl_pol_no_state in_states_expl'
  by (auto simp: expl_pol_def E.is_dec_det_def is_policy_def)

lemma reward_expl_no_state[simp]: \<open>x \<notin> states_expl \<Longrightarrow> reward_expl (x, a) = 0\<close>
  by simp

lemma r_dec_no_state[simp]: \<open>x \<notin> states_expl \<Longrightarrow> E.r_dec p x = 0\<close>
  by auto

lemma L\<^sub>a_w_no_state[simp]: \<open>x \<notin> states_expl \<Longrightarrow> E.L\<^sub>a a (\<nu>\<^sub>w_expl w) x = 0\<close>
  by (auto simp: transition_expl_def)

lemma \<L>\<^sub>b_w_no_state[simp]: \<open>x \<notin> states_expl \<Longrightarrow> E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w) x = 0\<close>
  by (metis E.ex_opt_act L\<^sub>a_w_no_state actions_expl_def actions_fin)

lemma transition_expl_no_state[simp]: \<open>s \<notin> states_expl \<Longrightarrow> transition_expl (s, a) = return_pmf s\<close>
  unfolding transition_expl_def by auto

lemma \<nu>\<^sub>w_expl_eq: \<open>x \<in> states_expl \<Longrightarrow> \<nu>\<^sub>w_expl w x = \<nu>\<^sub>w w (from_expl x)\<close>
  unfolding \<nu>\<^sub>w_expl.rep_eq
  by auto

lemma \<nu>\<^sub>w_to_expl[simp]: \<open>x \<in> states \<Longrightarrow> (\<nu>\<^sub>w_expl w) (to_expl x) = \<nu>\<^sub>w w x\<close>
  by (simp add: \<nu>\<^sub>w_expl_eq in_states_expl)

lemma sup_Sup_eq_le: \<open>bdd_above X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (\<forall>x\<in>X. (c::real) \<le> x) \<Longrightarrow> c \<squnion> (\<Squnion>X) = (\<Squnion>X)\<close>
  by (metis all_not_in_conv cSup_le_iff le_iff_sup nle_le)

lemma is_policy_dec_det[dest]: \<open>is_policy p \<Longrightarrow> E.is_dec_det (expl_pol p)\<close>
  using actions_ne 
  unfolding expl_pol_def is_policy_def
  by (fastforce simp: some_in_eq)  

lemma is_greedy_pol_imp_greedy: \<open>is_greedy_pol_w w p \<Longrightarrow> x \<in> states \<Longrightarrow> is_greedy_w w x (p x)\<close>
  unfolding is_greedy_pol_w_def
  by (auto simp: expl_pol_eq' is_greedy_w_def E.is_greedy_def)

lemma expl_pol_act[intro]: \<open>is_policy p \<Longrightarrow> expl_pol p s \<in> actions\<close>
  using is_policy_dec_det
  by fastforce

lemma is_greedy_imp_greedy_pol_: 
  assumes \<open>\<And>x. x \<in> states \<Longrightarrow> is_greedy_w w x (p x)\<close>
  shows \<open>is_greedy_pol_w w p\<close>
  unfolding is_greedy_pol_w_def
  using assms 
  by auto

lemma is_greedy_pol_w_imp_greedy: 
  assumes \<open>is_greedy_pol_w w p\<close>
  shows \<open>E.is_greedy (\<nu>\<^sub>w_expl w) (expl_pol p)\<close>
proof -
  have \<open>E.is_opt_act (apply_bfun (\<nu>\<^sub>w_expl w)) (to_expl s) (expl_pol p (to_expl s))\<close> if \<open>s \<in> states\<close> for s
    using assms
    unfolding is_greedy_pol_w_def 
    by (auto simp: is_greedy_w_iff expl_pol_eq' that)
  hence \<open>E.is_opt_act (apply_bfun (\<nu>\<^sub>w_expl w)) s (expl_pol p s)\<close> for s
    by (cases \<open>s \<in> states_expl\<close>) (force simp add: E.L\<^sub>a_eq_\<L>_imp_opt_act expl_pol_no_state)+
  thus ?thesis
    unfolding  E.is_greedy_def
    by auto
qed

lemma greedy_imp_is_greedy_pol_w: \<open>E.is_greedy (\<nu>\<^sub>w_expl w) (expl_pol p) \<Longrightarrow> is_greedy_pol_w w p\<close>
  by (simp add: E.is_greedy_def expl_pol_eq' is_greedy_pol_w_def is_greedy_w_iff)

lemma is_greedy_pol_w_iff: \<open>is_greedy_pol_w w p = (E.is_greedy (\<nu>\<^sub>w_expl w) (expl_pol p))\<close>
  using is_greedy_pol_w_imp_greedy greedy_imp_is_greedy_pol_w
  by auto

lemmas is_greedy_pol_iff = is_greedy_pol_w_def

lemma is_opt_act_no_state: \<open>x \<notin> states_expl \<Longrightarrow> a \<in> actions \<Longrightarrow> E.is_opt_act (\<nu>\<^sub>w_expl w) x a\<close>
  by (auto simp: transition_expl_def E.is_opt_act_def)

lemma \<nu>\<^sub>w_cong:
  assumes \<open>(\<And>i. i < h_dim \<Longrightarrow> w i = w' i)\<close>
  shows \<open>\<nu>\<^sub>w w = \<nu>\<^sub>w w'\<close>
  unfolding \<nu>\<^sub>w_def
  using assms
  by auto

lemma \<nu>\<^sub>w_expl_cong:
  assumes \<open>(\<And>i. i < h_dim \<Longrightarrow> w i = w' i)\<close>
  shows \<open>\<nu>\<^sub>w_expl w = \<nu>\<^sub>w_expl w'\<close>
  using assms \<nu>\<^sub>w_cong[of w w']
  by (auto simp: \<nu>\<^sub>w_expl.rep_eq)

lemma L_zero[simp]: \<open>E.L p 0 = E.r_dec\<^sub>b p\<close>
  unfolding E.L_def
  by auto

lemma r\<^sub>M_factored: \<open>E.r\<^sub>M = (MAX x\<in>states. MAX a\<in>actions. \<bar>reward a x\<bar>)\<close>
proof (rule order_antisym)
  show \<open>E.r\<^sub>M \<le>(MAX x\<in>states. MAX a\<in>actions. \<bar>reward a x\<bar>)\<close>
    unfolding E.r\<^sub>M_def
    using states_ne actions_ne
    by (intro cSUP_least) 
      (auto simp: reward_expl_def Max_ge_iff Let_def fin_states actions_fin split: if_splits)+
next
  have \<open>\<bar>reward a x\<bar> \<le> E.r\<^sub>M\<close> if \<open>x \<in> states\<close> \<open>a\<in>actions\<close> for x a
    unfolding E.r\<^sub>M_def
      using E.r_bounded' that
      by (auto intro!: cSUP_upper2[of _ _ \<open>(to_expl x, a)\<close>] bounded_imp_bdd_above)
    thus \<open>(MAX x\<in>states. MAX a\<in>actions. \<bar>reward a x\<bar>) \<le> E.r\<^sub>M\<close>
      by (auto simp: fin_states actions_fin states_ne actions_ne)
  qed

  section \<open>Projection Error\<close>

lemma proj_err_w_eq_restr: 
  assumes \<open>is_policy p\<close>
  shows \<open>proj_err_w p w = 
    (\<Squnion>x \<in> states_expl. dist (\<nu>\<^sub>w_expl w x) (E.L (E.mk_dec_det (expl_pol p)) (\<nu>\<^sub>w_expl w) x))\<close>
proof -
  have *: \<open>UNIV = -states_expl \<union> states_expl\<close>
    by auto
  thus ?thesis
    unfolding states_expl_def proj_err_w_def
    using assms expl_pol_def
    by (auto simp: E.L_eq_L\<^sub>a_det image_image Q_r_G\<^sub>a is_policy_def intro!: SUP_cong)
  qed

lemma proj_err_w_eq: 
  assumes \<open>is_policy p\<close>
  shows \<open>proj_err_w p w = dist (\<nu>\<^sub>w_expl w) ((E.L (E.mk_dec_det (expl_pol p)) (\<nu>\<^sub>w_expl w)))\<close>
proof -
  have *: \<open>UNIV = -states_expl \<union> states_expl\<close>
    by auto
  thus ?thesis
  proof (cases \<open>-states_expl = {}\<close>)
    case False
    thus ?thesis
      using states_expl_ne finite_states_expl assms
    unfolding  dist_bfun.rep_eq *
    by (subst cSUP_union) (auto simp: proj_err_w_eq_restr E.L_eq_L\<^sub>a_det sup_Sup_eq_le)
qed (auto simp: proj_err_w_eq_restr assms dist_bfun.rep_eq)
qed

lemma proj_err_w_nonneg: \<open>proj_err_w p w \<ge> 0\<close>
  unfolding proj_err_w_def
  using some_in_states fin_states
  by (auto intro!: cSup_upper2)

lemma proj_err_w_factored:
  assumes \<open>is_policy p\<close>
  shows \<open>proj_err_w p w = (\<Squnion>x \<in> states. dist (\<nu>\<^sub>w w x) (Q w x (p x)))\<close>
  unfolding proj_err_w_def
  by auto

term \<open>push_exp (E.K_st d)\<close>

lemma proj_err_w_as_dist: 
  assumes \<open>is_policy p\<close>
  shows \<open>proj_err_w p (apply_bfun w) =
  dist ((\<nu>\<^sub>w_expl\<^sub>L - (l *\<^sub>R E.\<P>\<^sub>1 (E.mk_dec_det (expl_pol p)) o\<^sub>L \<nu>\<^sub>w_expl\<^sub>L)) w) (E.r_dec\<^sub>b (E.mk_dec_det (expl_pol p)))\<close>
  unfolding proj_err_w_eq[OF assms] dist_norm blinfun.diff_left E.L_def \<nu>\<^sub>w_expl\<^sub>L.rep_eq
  by (auto simp add: algebra_simps \<nu>\<^sub>w_expl\<^sub>L.rep_eq \<nu>\<^sub>w_expl\<^sub>b.rep_eq blinfun.scaleR_left)
  
lemma proj_err_w_cong:
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> w i = w' i\<close> and \<open>is_policy p\<close>
  shows \<open>proj_err_w p w = proj_err_w p w'\<close>
  unfolding proj_err_w_eq[OF assms(2)]
  using \<nu>\<^sub>w_expl_cong[OF assms(1)] assms
  by simp

lemma proj_err_w_min_bfun_ex:
  assumes \<open>is_policy p\<close>
  shows \<open>\<exists>w. \<forall>w'. proj_err_w p (apply_bfun w) \<le> proj_err_w p (apply_bfun w')\<close>
proof (cases \<open>h_dim = 0\<close>)
  case True
  then show ?thesis
    using proj_err_w_cong nle_le \<open>is_policy p\<close> by blast
next
  case False

  let ?A = \<open>(\<nu>\<^sub>w_expl\<^sub>L - (l *\<^sub>R E.\<P>\<^sub>1 (E.mk_dec_det (expl_pol p)) o\<^sub>L \<nu>\<^sub>w_expl\<^sub>L))\<close>
  let ?dims = \<open>{..<h_dim}\<close>
  let ?outs = \<open>states_expl\<close>
  let ?c = \<open>(E.r_dec\<^sub>b (E.mk_dec_det (expl_pol p)))\<close>

  have 1: \<open>finite' ?dims\<close>
    using False by auto

  have 2: \<open>finite' ?outs\<close>
    using finite_states_expl states_expl_ne by auto

  have 3: \<open>\<forall>i\<in>{..<h_dim}. apply_bfun x i = apply_bfun x' i \<Longrightarrow> ?A x = ?A x'\<close> for x x'
    using \<nu>\<^sub>w_expl_cong[of x x']
    by (auto intro!: bfun_eqI simp:  \<nu>\<^sub>w_expl\<^sub>b.rep_eq \<nu>\<^sub>w_expl\<^sub>L.rep_eq blinfun.diff_left blinfun.scaleR_left)

  have 4: \<open>i \<notin> states_expl \<Longrightarrow> ?A x i = 0\<close> for x i
    by (auto simp: E.K_st_def E.\<P>\<^sub>1.rep_eq \<nu>\<^sub>w_expl\<^sub>L.rep_eq \<nu>\<^sub>w_expl\<^sub>b.rep_eq blinfun.diff_left blinfun.scaleR_left)
    
  have 5: \<open>i \<notin> states_expl \<Longrightarrow> apply_bfun ?c i = 0\<close> for i
    using E.r_dec\<^sub>b.rep_eq r_dec_no_state by presburger

  have \<open>has_arg_min (\<lambda>v. dist (?A v) ?c) UNIV\<close>
    using A_dist_c_has_arg_min_UNIV[OF 1 2 3 4 5].

  thus ?thesis
    unfolding proj_err_w_as_dist[OF \<open>is_policy p\<close>] has_arg_min_def is_arg_min_linorder
    by auto
qed

lemma proj_err_w_min_ex:
  assumes \<open>is_policy p\<close>
  shows \<open>\<exists>w. \<forall>w'. proj_err_w p w \<le> proj_err_w p w'\<close>
proof-
  obtain w where \<open>proj_err_w p (apply_bfun w) \<le> proj_err_w p (apply_bfun w')\<close> for w'
  using proj_err_w_min_bfun_ex \<open>is_policy p\<close> by fastforce

  moreover have \<open>proj_err_w p w' = proj_err_w p (Bfun (\<lambda>i. if i < h_dim then w' i else 0))\<close> for w'
    apply (rule proj_err_w_cong)
    apply (subst Bfun_inverse)
    by (auto intro!: bfun_def finite_bounded \<open>is_policy p\<close>)

  ultimately show ?thesis
    by (metis (full_types))
qed

lemma (in MDP_reward_disc) dist_L_lt_dist_\<nu>\<^sub>b:
  assumes \<open>p \<in> D\<^sub>R\<close>
  shows "dist v (L p v) \<le> 2 * dist v (\<nu>\<^sub>b (mk_stationary p))"
proof -
  have "dist v (L p v) \<le> dist v (\<nu>\<^sub>b (mk_stationary p)) + dist (\<nu>\<^sub>b (mk_stationary p)) (L p v)"
    by (auto simp: dist_triangle)
  hence "dist v (L p v) \<le> dist v (\<nu>\<^sub>b (mk_stationary p)) + dist (L p v) (\<nu>\<^sub>b (mk_stationary p))"
    by (auto simp: dist_commute)
  moreover have "dist (L p v) (\<nu>\<^sub>b (mk_stationary p)) \<le> l * dist v (\<nu>\<^sub>b (mk_stationary p))"
    by (metis L_\<nu>_fix contraction_L)
  ultimately show ?thesis
    using zero_le_disc disc_le_one by (smt (verit) mult_left_le_one_le zero_le_dist)
qed  

text \<open>The projection error of a policy is by definition always optimal.\<close>
lemma proj_err_pol_le_w:
  assumes \<open>is_policy p\<close> 
  shows \<open>proj_err_pol p \<le> proj_err_w p w\<close>
  unfolding proj_err_pol_def
  using proj_err_w_nonneg
  by (auto intro!: cInf_lower intro!: bdd_belowI)

text \<open>The projection error is never negative.\<close>
lemma proj_err_pol_nonneg: 
  assumes \<open>is_policy p\<close> 
  shows \<open>proj_err_pol p \<ge> 0\<close>
  unfolding proj_err_pol_def
  using proj_err_w_nonneg
  by (auto intro!: cINF_greatest)

lemma bellman_err_w_eq_restr: 
  \<open>bellman_err_w w = (\<Squnion> x \<in> states_expl. dist (\<nu>\<^sub>w_expl w x) (E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w) x))\<close>
  unfolding bellman_err_w_def states_expl_def
  by (auto simp: Q_r_G\<^sub>a image_image \<nu>\<^sub>w_expl.rep_eq E.SUP_step_det_eq E.\<L>\<^sub>b_eq_SUP_det 
      intro!: SUP_cong arg_cong2[where f = dist])

lemma bellman_err_w_eq_expl: \<open>bellman_err_w w = E.bellman_err\<^sub>b (\<nu>\<^sub>w_expl w)\<close>
proof -
  have *: \<open>UNIV = -states_expl \<union> states_expl\<close>
    by auto
  thus ?thesis
  proof (cases \<open>-states_expl = {}\<close>)
    case False
    thus ?thesis
      using states_expl_ne finite_states_expl
    unfolding  dist_bfun.rep_eq * bellman_err_w_eq_restr E.bellman_err\<^sub>b_def
    by (subst cSUP_union) (auto simp: E.L_eq_L\<^sub>a_det sup_Sup_eq_le)
qed (auto simp: bellman_err_w_eq_restr  E.bellman_err\<^sub>b_def dist_bfun.rep_eq)
qed

end

end