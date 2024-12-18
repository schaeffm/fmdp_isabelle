theory Factored_MDP_Thy
  imports Factored_To_Explicit
begin

section \<open>Basic Definitions on Factored MDPs\<close>

context Factored_MDP_Consts
begin

text \<open>The transition probabilities between states x and x' after selecting action a.\<close>
definition p\<^sub>a :: \<open>'a \<Rightarrow> 'x state \<Rightarrow> 'x state \<Rightarrow> real\<close> where
"p\<^sub>a a x x' = (\<Prod>i < dims. pmf (transitions a i x) (the (x' i)))"

text \<open>We define the evaluation of the basis functions with weights @{term w} as @{term \<nu>\<^sub>w}.\<close>
definition \<open>\<nu>\<^sub>w w x = (if x \<in> partial_states then (\<Sum>i < h_dim. w i * h i x) else 0)\<close>

text \<open>One-step lookahead of the weights @{term w} in state @{term x} with action @{term a}.\<close>
definition \<open>G\<^sub>a a w x = (\<Sum>x' \<in> states. p\<^sub>a a x x' * \<nu>\<^sub>w w x')\<close>

text \<open>The well-known Q function can be expressed in terms of @{const G\<^sub>a}.\<close>
definition \<open>Q w x a = reward a x + l * G\<^sub>a a w x\<close>
                        
text \<open>The maximum absolute value any basis function can take on.\<close>
definition \<open>h\<^sub>M = (if h_dim = 0 then 0 else (MAX x \<in> states. MAX i \<in> {..<h_dim}. \<bar>h i x\<bar>))\<close>

text \<open>A greedy action wrt. weights @{term w} is one that maximizes the @{const Q} function.\<close>
definition \<open>is_greedy_act w x a \<longleftrightarrow> (\<forall>a' \<in> actions. Q w x a' \<le> Q w x a)\<close>

end

context Factored_MDP
begin


subsection \<open>@{term h\<^sub>M}\<close>
lemma abs_h_le_h\<^sub>M: \<open>i < h_dim \<Longrightarrow> x \<in> states \<Longrightarrow> \<bar>h i x\<bar> \<le> h\<^sub>M\<close>
  unfolding h\<^sub>M_def
  using fin_states states_ne finite_lessThan lessThan_empty_iff
  by (auto simp: Max_ge_iff)

lemma h\<^sub>M_nonneg: \<open>h\<^sub>M \<ge> 0\<close>
  unfolding h\<^sub>M_def 
  using fin_states states_ne  lessThan_empty_iff
  by (auto simp: Max_ge_iff intro!: Max_ge)

subsection \<open>@{term \<nu>\<^sub>w_expl}\<close>
text \<open>We connect the value function on factored MDPs to the definition on explicit MDPs.\<close>
lift_definition \<nu>\<^sub>w_expl :: \<open>(nat \<Rightarrow> real) \<Rightarrow> ('x list \<Rightarrow>\<^sub>b real)\<close> is
  \<open>\<lambda>w s. if s \<in> states_expl then \<nu>\<^sub>w w (from_expl s) else 0\<close>
  using bounded_const finite_states_expl
  by fastforce

lift_definition \<nu>\<^sub>w_expl\<^sub>b :: \<open>(nat \<Rightarrow>\<^sub>b real) \<Rightarrow> ('x list \<Rightarrow>\<^sub>b real)\<close> is
  \<open>\<nu>\<^sub>w_expl\<close> .

lemma \<nu>\<^sub>w_expl\<^sub>b_eq: \<open>\<nu>\<^sub>w_expl\<^sub>b v xs = (if xs \<in> states_expl then \<nu>\<^sub>w v (from_expl xs) else 0)\<close>
  unfolding \<nu>\<^sub>w_expl\<^sub>b.rep_eq \<nu>\<^sub>w_expl.rep_eq
  by auto

lemma \<nu>\<^sub>w_expl\<^sub>b_bounded_linear: \<open>bounded_linear \<nu>\<^sub>w_expl\<^sub>b\<close>
proof (rule bounded_linear_intro, goal_cases)
  case (1 x y)
  then show ?case
    by (auto simp: sum.distrib algebra_simps \<nu>\<^sub>w_expl\<^sub>b_eq \<nu>\<^sub>w_def)
next
  case (2 r x)
  then show ?case
    by (auto simp: sum_distrib_left algebra_simps \<nu>\<^sub>w_expl\<^sub>b_eq \<nu>\<^sub>w_def)
next
  case (3 x)
  then show \<open>norm (\<nu>\<^sub>w_expl\<^sub>b x) \<le> norm x * (h_dim * h\<^sub>M)\<close> for x
  proof -
    have \<open>norm (\<nu>\<^sub>w_expl\<^sub>b x) \<le> (\<Squnion>s. \<bar>\<nu>\<^sub>w_expl x s\<bar>)\<close>
      by (auto simp: \<nu>\<^sub>w_expl\<^sub>b.rep_eq \<nu>\<^sub>w_expl.rep_eq norm_bfun_def')
    also have \<open>\<dots> \<le> (\<Squnion>s\<in>states_expl. \<bar>\<nu>\<^sub>w (apply_bfun x) (from_expl s)\<bar>)\<close>
      unfolding \<nu>\<^sub>w_expl.rep_eq
      using bdd_above_finite finite_imageI finite_states_expl states_expl_ne
      by (auto intro!: cSUP_mono)
    also have \<open>\<dots> \<le> (\<Squnion>s\<in>states_expl. \<Sum>i < h_dim. \<bar>x i * h i (from_expl s)\<bar>)\<close>
      using finite_states_expl states_expl_ne
      by (auto intro!: cSUP_mono simp: \<nu>\<^sub>w_def)
    also have \<open>\<dots> \<le> (\<Squnion>s\<in>states_expl. \<Sum>i < h_dim. \<bar>x i\<bar> * h\<^sub>M)\<close>
      using states_expl_ne abs_h_le_h\<^sub>M
      by (intro cSUP_mono' sum_mono) (auto intro!: mult_left_mono simp: abs_mult)
    also have \<open>\<dots> \<le> (\<Squnion>s\<in>states_expl. \<Sum>i < h_dim. norm x * h\<^sub>M)\<close>
      using states_expl_ne h\<^sub>M_nonneg
      by (intro cSUP_mono' sum_mono) (auto simp: abs_le_norm_bfun intro!: mult_right_mono)
    also have \<open>\<dots> \<le> norm x * h_dim * h\<^sub>M\<close>
      using states_expl_ne
      by auto
    finally show ?thesis
      by auto
  qed
qed

lift_definition \<nu>\<^sub>w_expl\<^sub>L :: \<open>(nat \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('x list \<Rightarrow>\<^sub>b real)\<close> is
  \<open>\<nu>\<^sub>w_expl\<^sub>b\<close>
  using \<nu>\<^sub>w_expl\<^sub>b_bounded_linear .

lemma \<nu>\<^sub>w_expl_eq:
  \<open>\<nu>\<^sub>w_expl w s = (if s \<in> states_expl then (\<Sum>i < h_dim. w i * h i (from_expl s)) else 0)\<close>
  unfolding \<nu>\<^sub>w_expl.rep_eq \<nu>\<^sub>w_def
  using states_imp_partial
  by auto

lemma \<nu>\<^sub>w_zero[simp]: \<open>\<nu>\<^sub>w (\<lambda>_. 0) s = 0\<close>
  unfolding \<nu>\<^sub>w_def
  by simp

lemma \<nu>\<^sub>w_expl_no_state[simp]: \<open>x \<notin> states_expl \<Longrightarrow> \<nu>\<^sub>w_expl w x = 0\<close>
  unfolding \<nu>\<^sub>w_expl.rep_eq
  by auto

lemma \<nu>\<^sub>w_expl_zero[simp]: \<open>\<nu>\<^sub>w_expl (\<lambda>_. 0) = 0\<close>
  by (auto simp: \<nu>\<^sub>w_expl_eq)


subsection \<open>@{term p\<^sub>a}\<close>
lemma p\<^sub>a_expl:
  assumes \<open>a \<in> actions\<close> \<open>x \<in> states\<close> \<open>x' \<in> states\<close>
  shows \<open>p\<^sub>a a x x' = pmf (transition_expl (to_expl x, a)) (to_expl x')\<close>
  unfolding p\<^sub>a_def
  using assms transition_expl_pmf
  by auto

subsection \<open>@{term G\<^sub>a}\<close>
lemma G\<^sub>a_eq: \<open>G\<^sub>a a w x = (\<Sum>x'\<in>states. p\<^sub>a a x x' * (\<Sum>i<h_dim. w i * h i x'))\<close>
  unfolding G\<^sub>a_def \<nu>\<^sub>w_def
  by (force intro!: sum.cong)

lemma G\<^sub>a_expl:
  assumes \<open>a \<in> actions\<close> \<open>x \<in> states\<close>
  shows \<open>G\<^sub>a a w x = measure_pmf.expectation (transition_expl (to_expl x, a)) (\<nu>\<^sub>w_expl w)\<close>
proof -
  have \<open>G\<^sub>a a w x = (\<Sum>x' \<in> states. p\<^sub>a a x x' * \<nu>\<^sub>w w x')\<close>
    unfolding G\<^sub>a_def ..
  also have \<open>\<dots> = (\<Sum>x' \<in> states_expl. pmf (transition_expl (to_expl x, a)) x' * \<nu>\<^sub>w_expl w x')\<close>
    unfolding states_expl_def
    using inj_to_expl
    by (auto simp: sum.reindex assms p\<^sub>a_expl \<nu>\<^sub>w_expl.rep_eq intro!: sum.cong)
  also have \<open>\<dots> = measure_pmf.expectation (transition_expl (to_expl x, a)) (\<nu>\<^sub>w_expl w)\<close>
    using \<nu>\<^sub>w_expl_no_state finite_states_expl
    by (subst integral_measure_pmf[of \<open>states_expl\<close>]) fastforce+
  finally show ?thesis .
qed

lemma Q_r_G\<^sub>a:
  assumes \<open>a \<in> actions\<close> \<open>x \<in> states\<close>
  shows \<open>Q w x a = E.L\<^sub>a a (\<nu>\<^sub>w_expl w) (to_expl x)\<close>
  unfolding Q_def
  using G\<^sub>a_expl assms
  by simp

end

section \<open>Factored MDPs with Default Actions\<close>
text \<open>We define MDPs with a default action @{term d}, where the behavior of all other actions 
  @{term a} only differs in dimensions in the set @{term \<open>effects a\<close>}.\<close>
locale Factored_MDP_Default_Consts = Factored_MDP_Consts
  where 
    transitions = transitions
  for
    transitions :: \<open>'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> 'x::{countable, linorder} state \<Rightarrow> 'x pmf\<close> +
  fixes
    d :: \<open>'a\<close> and
    effects :: \<open>'a \<Rightarrow> nat set\<close>
begin

subsection \<open>Reward Functions and their Scopes\<close>
definition \<open>R\<^sub>d x = (\<Sum>i < reward_dim d. rewards d i x)\<close>

definition \<open>U\<^sub>d = (\<Union>i < reward_dim d. reward_scope d i)\<close>

definition U\<^sub>a :: \<open>'a \<Rightarrow> nat set\<close> where
  \<open>U\<^sub>a a = (\<Union>i \<in> {reward_dim d..<reward_dim a}. reward_scope a i)\<close>

definition \<open>R\<^sub>a a x = (\<Sum>i \<in> {reward_dim d..<reward_dim a}. rewards a i x)\<close>

definition \<open>I\<^sub>a a = {i. i < h_dim \<and> effects a \<inter> h_scope i \<noteq> {}}\<close>

definition \<Gamma>\<^sub>a :: \<open>'a \<Rightarrow> nat set \<Rightarrow> nat set\<close> where
  \<open>\<Gamma>\<^sub>a a I = (\<Union>i \<in> I. transitions_scope a i)\<close>

definition \<Gamma>\<^sub>a' :: \<open>'a \<Rightarrow> nat set \<Rightarrow> nat set\<close> where
  \<open>\<Gamma>\<^sub>a' a X = \<Gamma>\<^sub>a a X \<union> \<Gamma>\<^sub>a d X\<close>

definition T\<^sub>a :: \<open>'a \<Rightarrow> nat set\<close> where
 \<open>T\<^sub>a a = U\<^sub>a a \<union> (\<Union>i \<in> I\<^sub>a a. \<Gamma>\<^sub>a' a (h_scope i))\<close>

end

locale Factored_MDP_Default = 
  Factored_MDP_Default_Consts
  where 
    transitions = transitions +
  Factored_MDP
  where
    transitions = transitions
  for
    transitions :: \<open>'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> 'x::{countable, linorder} state \<Rightarrow> 'x pmf\<close> +
  assumes
    default_act: \<open>d \<in> actions\<close> and
    effects: \<open>\<And>i a.
      i < dims \<Longrightarrow>
      a \<in> actions \<Longrightarrow> 
      (\<exists>x \<in> partial_states. transitions a i x \<noteq> transitions d i x) \<Longrightarrow> i \<in> effects a\<close> and
    effects_default:
      \<open>effects d = {}\<close> and
    
    rewards_default_dim: \<open>\<And>a. a \<in> actions \<Longrightarrow> reward_dim a \<ge> reward_dim d\<close> and
    rewards_eq: \<open>\<And>a i. a \<in> actions \<Longrightarrow> i < reward_dim d \<Longrightarrow> rewards a i = rewards d i\<close> and
    reward_scope_eq: \<open>\<And>a i. a \<in> actions \<Longrightarrow> i < reward_dim d \<Longrightarrow> reward_scope a i = reward_scope d i\<close>
    \<comment> \<open>The first @{term \<open>reward_dim d\<close>} reward functions coincide for all actions.\<close>
begin

lemmas rewards_default_dim[intro]

lemma effectsD[dest]: \<open>i \<in> effects d \<Longrightarrow> False\<close>
  using effects_default
  by blast

subsection \<open>Rewards\<close>

lemma scope_R\<^sub>d: \<open>has_scope_on R\<^sub>d partial_states U\<^sub>d\<close>
  unfolding R\<^sub>d_def U\<^sub>d_def
  using reward_scope default_act
  by auto

lemma R\<^sub>d_act:
  assumes "a \<in> actions"
  shows "R\<^sub>d x = (\<Sum>i<reward_dim d. rewards a i x)"
  unfolding R\<^sub>d_def 
  using rewards_default_dim rewards_eq[of a] assms
  by simp


subsection \<open>@{term \<open>R\<^sub>a\<close>}\<close>
lemma U\<^sub>a_I[intro]:  
  assumes "a \<in> actions"
    and "reward_dim d \<le> i"
    and "i < reward_dim a"
    and "j \<in> reward_scope a i"
  shows "j \<in> U\<^sub>a a"
  unfolding U\<^sub>a_def
  using assms
  by auto

lemma U\<^sub>a_D[dest]: \<open>i \<in> U\<^sub>a a \<Longrightarrow> a \<in> actions \<Longrightarrow> i < dims\<close>
  unfolding U\<^sub>a_def
  by auto

lemma U\<^sub>a_D2[dest]: 
  assumes "i \<in> U\<^sub>a a"
    and "a \<in> actions"
  shows "\<exists>j\<in>{reward_dim d..<reward_dim a}. i \<in> reward_scope a j"
  using assms
  unfolding U\<^sub>a_def
  by auto

lemma U\<^sub>a_subs[intro]: \<open>a \<in> actions \<Longrightarrow> U\<^sub>a a \<subseteq> {..<dims}\<close>
  by fastforce

lemma U\<^sub>a_default[simp]: \<open>U\<^sub>a d = {}\<close>
  using default_act
  by auto

lemma scope_R\<^sub>a: \<open>a \<in> actions \<Longrightarrow> has_scope_on (R\<^sub>a a) partial_states (U\<^sub>a a)\<close>
  unfolding U\<^sub>a_def R\<^sub>a_def
  using has_scope_on_subs[OF reward_scope]
  by (metis SUP_upper atLeastLessThan_iff has_scope_on_sum)

lemma R\<^sub>a_d[simp]: \<open>R\<^sub>a d x = 0\<close>
  unfolding R\<^sub>a_def
  by auto

lemma reward_split_default: \<open>a \<in> actions \<Longrightarrow> reward a x = R\<^sub>d x + R\<^sub>a a x\<close>
  unfolding R\<^sub>a_def reward_def
  using rewards_default_dim
  by (auto simp: R\<^sub>d_act atLeast0LessThan[symmetric] sum.atLeastLessThan_concat)
  
lemma reward_split_scope: \<open>a \<in> actions \<Longrightarrow> has_scope_on (reward a) partial_states (U\<^sub>a a \<union> U\<^sub>d)\<close>
  using scope_R\<^sub>a scope_R\<^sub>d
  by (auto simp: reward_split_default cong: has_scope_on_cong)

subsection \<open>@{term \<open>\<Gamma>\<^sub>a\<close>}\<close>
lemma \<Gamma>\<^sub>a_subs[intro]: \<open>a \<in> actions \<Longrightarrow> X \<subseteq> {..<dims} \<Longrightarrow> \<Gamma>\<^sub>a a X \<subseteq> {..<dims}\<close>
  unfolding \<Gamma>\<^sub>a_def
  using transitions_scope_dims
  by auto

lemma \<Gamma>\<^sub>a_I[intro]: \<open>x \<in> X \<Longrightarrow> i \<in> transitions_scope a x \<Longrightarrow> i \<in> \<Gamma>\<^sub>a a X\<close>
  unfolding \<Gamma>\<^sub>a_def
  by auto

lemma \<Gamma>\<^sub>a_E[elim]: 
  assumes \<open>i \<in> \<Gamma>\<^sub>a a X\<close> \<open>a \<in> actions\<close> 
  shows \<open>(\<And>x. x \<in> X \<Longrightarrow> i \<in> transitions_scope a x \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using assms
  unfolding \<Gamma>\<^sub>a_def
  by auto

lemma \<Gamma>\<^sub>a_D[dest]: \<open>i \<in> \<Gamma>\<^sub>a a X \<Longrightarrow> a \<in> actions \<Longrightarrow> \<exists>x \<in> X. i \<in> transitions_scope a x\<close>
  by auto

lemma \<Gamma>\<^sub>a_D2[dest]: \<open>i \<in> \<Gamma>\<^sub>a a X \<Longrightarrow> a \<in> actions \<Longrightarrow> X \<subseteq> vars \<Longrightarrow> i < dims\<close>
  by auto

subsection \<open>@{term \<open>\<Gamma>\<^sub>a'\<close>}\<close>

lemma \<Gamma>\<^sub>a'_subs: \<open>a \<in> actions \<Longrightarrow> X \<subseteq> {..<dims} \<Longrightarrow> \<Gamma>\<^sub>a' a X \<subseteq> {..<dims}\<close>
  unfolding \<Gamma>\<^sub>a'_def
  using \<Gamma>\<^sub>a_subs default_act
  by auto

lemma \<Gamma>\<^sub>a'_act[intro]: \<open>i \<in> \<Gamma>\<^sub>a a X \<Longrightarrow> i \<in> \<Gamma>\<^sub>a' a X\<close>
  unfolding \<Gamma>\<^sub>a'_def
  by auto

lemma \<Gamma>\<^sub>a'_default[intro]: \<open>i \<in> \<Gamma>\<^sub>a d X \<Longrightarrow> i \<in> \<Gamma>\<^sub>a' a X\<close>
  unfolding \<Gamma>\<^sub>a'_def
  by auto

lemma \<Gamma>\<^sub>a'_D[dest]: \<open>i \<in> \<Gamma>\<^sub>a' a X \<Longrightarrow> i \<in> \<Gamma>\<^sub>a a X \<or> i \<in> \<Gamma>\<^sub>a d X\<close>
  unfolding \<Gamma>\<^sub>a'_def
  by auto

subsection \<open>@{term \<open>I\<^sub>a\<close>}\<close>

lemma I\<^sub>d[simp]: \<open>I\<^sub>a d = {}\<close>
  unfolding I\<^sub>a_def
  using effects_default by blast

lemma I\<^sub>a_h_dim: \<open>a \<in> actions \<Longrightarrow> I\<^sub>a a \<subseteq> {..<h_dim}\<close>
  unfolding I\<^sub>a_def
  by auto

lemma I\<^sub>a_D[dest]: \<open>i \<in> I\<^sub>a a \<Longrightarrow> a \<in> actions \<Longrightarrow> i < h_dim\<close>
  using I\<^sub>a_h_dim
  by auto

lemma I\<^sub>a_E[elim]: \<open>i \<in> I\<^sub>a a \<Longrightarrow> (i < h_dim \<Longrightarrow> effects a \<inter> h_scope i \<noteq> {} \<Longrightarrow> P) \<Longrightarrow> P\<close>
  unfolding I\<^sub>a_def
  by auto

lemma I\<^sub>a_E'[elim]: 
  assumes \<open>i \<notin> I\<^sub>a a\<close> \<open>i < h_dim\<close> 
  obtains \<open>effects a \<inter> h_scope i = {}\<close>
  using assms
  unfolding I\<^sub>a_def
  by auto

lemma I\<^sub>a_E''[elim]: \<open>i \<notin> I\<^sub>a a \<Longrightarrow> i < h_dim \<Longrightarrow> (\<And>j. j \<notin> effects a \<Longrightarrow> j \<notin> h_scope i \<Longrightarrow> P) \<Longrightarrow> 
  (\<And>j. j \<in> effects a \<Longrightarrow> j \<notin> h_scope i \<Longrightarrow> P) \<Longrightarrow> (\<And>j. j \<notin> effects a \<Longrightarrow> j \<in> h_scope i \<Longrightarrow> P) \<Longrightarrow> P\<close>
  unfolding I\<^sub>a_def
  by auto

lemma I\<^sub>a_I[intro]: \<open>i < h_dim \<Longrightarrow> (\<exists>j. j \<in> effects a \<and> j \<in> h_scope i) \<Longrightarrow> i \<in> I\<^sub>a a\<close>
  unfolding I\<^sub>a_def
  by auto

subsection \<open>@{term \<open>T\<^sub>a\<close>}\<close>
lemma T\<^sub>d[simp]: \<open>T\<^sub>a d = {}\<close>
  unfolding T\<^sub>a_def
  by auto

lemma T\<^sub>a_dims: \<open>a \<in> actions \<Longrightarrow> T\<^sub>a a \<subseteq> {..<dims}\<close>
  unfolding T\<^sub>a_def
  using \<Gamma>\<^sub>a'_subs h_scope_dims
  by auto

lemma T\<^sub>a_D[dest]: \<open>i \<in> T\<^sub>a a \<Longrightarrow> a \<in> actions \<Longrightarrow> i < dims\<close>
  using T\<^sub>a_dims by blast

lemma T\<^sub>a_I1[intro]: \<open>i \<in> U\<^sub>a a \<Longrightarrow> a \<in> actions \<Longrightarrow> i \<in> T\<^sub>a a\<close>
  unfolding T\<^sub>a_def
  by blast

lemma T\<^sub>a_I2[intro]: \<open>i \<in> I\<^sub>a a \<Longrightarrow> j \<in> \<Gamma>\<^sub>a' a (h_scope i) \<Longrightarrow> a \<in> actions \<Longrightarrow> j \<in> T\<^sub>a a\<close>
  unfolding T\<^sub>a_def
  by blast

lemma T\<^sub>a_E[elim]: \<open>i \<in> T\<^sub>a a \<Longrightarrow> (\<And>j. j \<in> U\<^sub>a a \<Longrightarrow> P) \<Longrightarrow> (\<And>i j. i \<in> I\<^sub>a a \<Longrightarrow> j \<in> \<Gamma>\<^sub>a' a (h_scope i) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  unfolding T\<^sub>a_def
  by auto

end

section \<open>Consistency of States\<close>
text \<open>We say that a partial state @{term x} is consistent with a state @{term x'}, 
  if it agrees with @{term x'} on the whole domain of @{term x'}.\<close>
definition \<open>consistent x x' \<longleftrightarrow> x |` dom x' = x'\<close>

lemma consistentI[intro]: \<open>(\<And>i. i \<in> dom x' \<Longrightarrow> x i = x' i) \<Longrightarrow> consistent x x'\<close>
  unfolding consistent_def restrict_map_def
  by (auto simp: domIff)

lemma consistentD[dest]: \<open>consistent x x' \<Longrightarrow> i \<in> dom x' \<Longrightarrow> x i = x' i\<close>
  unfolding consistent_def
  by (metis restrict_in)

lemma consistent_iff: \<open>consistent x x' \<longleftrightarrow> (\<forall>i\<in>dom x'. x i = x' i)\<close>
  by auto

lemma consistent_None: \<open>consistent x (\<lambda>_. None)\<close>
  by auto

lemma consistent_restr: \<open>consistent x (x |` S)\<close>
  by force

lemma consistent_dom_subs: \<open>consistent x t \<Longrightarrow> dom t \<subseteq> dom x\<close>
  by auto

lemma consistent_restr_D[dest]: \<open>consistent x x' \<Longrightarrow> x |` dom x' = x'\<close>
  by (auto simp: consistent_def)

end