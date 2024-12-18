theory API
imports Decision_List_Policy Factored_MDP_Util
begin

locale API_Interface_Consts =
  Factored_MDP_Default_Consts +
  fixes
    \<epsilon> :: real and \<comment> \<open>desired precision\<close>
    t_max :: nat and \<comment> \<open>max number of iterations\<close>

    update_dec_list :: \<open>weights \<Rightarrow> ('a state \<times> 'b) list\<close> and
    update_weights :: \<open>nat \<Rightarrow> ('a state \<times> 'b) list \<Rightarrow> weights\<close>
begin

definition \<open>is_greedy_dec_list_pol w p \<longleftrightarrow>
  is_dec_list_pol p \<and>
  (is_greedy_pol_w w (dec_list_to_pol p)) \<comment> \<open>turned into a policy, it is optimal wrt the weights\<close>\<close>

text \<open>Specification of subprograms\<close>
definition \<open>opt_weights_pol p w = is_arg_min (proj_err_w p) (\<lambda>_. True) w\<close>

definition \<open>update_weights_spec \<longleftrightarrow> (\<forall>p i. is_dec_list_pol p \<longrightarrow> opt_weights_pol (dec_list_to_pol p) (update_weights i p))\<close>

definition \<open>dec_list_pol_w w = dec_list_to_pol (update_dec_list w)\<close>

definition \<open>dec_list_pol_spec \<longleftrightarrow> (\<forall>w. is_greedy_dec_list_pol w (update_dec_list w))\<close>

section \<open>Approximate Policy Iteration\<close>
definition body :: \<open>nat \<Rightarrow> weights \<Rightarrow> weights\<close> where
  \<open>body i = update_weights i o update_dec_list\<close>

definition w0 :: \<open>weights\<close> where
  \<open>w0 _ = 0\<close>

type_synonym ('c, 'd) lpol = \<open>('c state \<times> 'd) list\<close>

definition p0 :: \<open>('a, 'b) lpol\<close> where
  \<open>p0 = update_dec_list w0\<close>

definition wp0 :: \<open>nat \<times> weights \<times> ('a, 'b) lpol\<close> where
  \<open>wp0 = (0, w0, p0)\<close>

definition api_step :: \<open>(nat \<times> weights \<times> ('a, 'b) lpol) \<Rightarrow> (nat \<times> weights \<times> ('a, 'b) lpol)\<close> where
  \<open>api_step = (\<lambda>(i, w, p). let w' = update_weights i p in (Suc i, w', update_dec_list w'))\<close>

definition \<open>api_seq_aux wp t = (api_step ^^ t) wp\<close>

definition \<open>api_seq t = api_seq_aux wp0 t\<close>

definition \<open>pol_t t = snd (snd (api_seq t))\<close>
definition \<open>w_t t = fst (snd (api_seq t))\<close>
definition \<open>i_t t = fst (api_seq t)\<close>

function api_aux where
\<open>api_aux pw t = (
  let
    (p, w) = pw;
    w' = update_weights t p;
    p' = update_dec_list w';
    err = proj_err_w (dec_list_to_pol p') w';
    t' = t + 1;
    w_eq = (\<forall>i < h_dim. w' i = w i);
    err_le = (err \<le> \<epsilon>);
    timeout = (t' \<ge> t_max) in
    (if w_eq \<or> err_le \<or> timeout then (w', p', err, t, w_eq, err_le, timeout)
     else api_aux (p', w') t'))\<close>
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(w, t). t_max - t)") auto

definition \<open>api =
  (let 
    w0 = (\<lambda>_. 0);
    p0 = update_dec_list w0
  in api_aux (p0, w0) 0)\<close>

end

locale API_Interface = 
  API_Interface_Consts +
  Factored_MDP_Default +
  assumes
    update_weights_spec: \<open>update_weights_spec\<close> and
    dec_list_pol_spec: \<open>dec_list_pol_spec\<close>
begin

lemma opt_update_weights:
  assumes \<open>is_dec_list_pol p\<close>
  shows \<open>opt_weights_pol (dec_list_to_pol p) (update_weights i p)\<close>
  using update_weights_spec assms unfolding update_weights_spec_def
  by blast

text \<open>Relationship of @{const w_t}, @{const pol_t}\<close>
lemma fst_wp0[simp]: \<open>fst (snd wp0) = w0\<close>
  unfolding wp0_def by auto

lemma fst_wp0'[simp]: \<open>fst wp0 = 0\<close>
  unfolding wp0_def by auto

lemma snd_wp0[simp]: \<open>snd (snd wp0) = p0\<close>
  unfolding wp0_def by auto

lemma api_seq_aux_zero[simp]: \<open>api_seq_aux wp 0 = wp\<close>
  unfolding api_seq_aux_def
  by auto

lemma api_seq_aux_Suc[simp]: \<open>api_seq_aux wp (Suc n) = api_step (api_seq_aux wp n)\<close>
  unfolding api_seq_aux_def
  by auto

lemma api_seq_zero[simp]: \<open>api_seq 0 = wp0\<close>
  by (auto simp: api_seq_def)

lemma api_seq_Suc[simp]: \<open>api_seq (Suc n) = api_step (api_seq n)\<close>
  by (auto simp: api_seq_def)

lemma w_t_zero[simp]: \<open>w_t 0 = w0\<close>
  unfolding w_t_def by auto

lemma pol_t_zero[simp]: \<open>pol_t 0 = p0\<close>
  unfolding pol_t_def by auto

lemma fst_api_seq[simp]: \<open>(fst (api_seq t)) = t\<close>
  by (induction t) (auto simp: api_step_def case_prod_unfold Let_def)

lemma w_t_Suc: \<open>w_t (Suc t) = update_weights (t) (pol_t t)\<close>
  by (auto simp: w_t_def pol_t_def api_step_def Let_def case_prod_unfold)

lemma pol_t_eq_w: \<open>pol_t t = update_dec_list (w_t (t))\<close>
  apply (cases t) 
  by (auto simp: p0_def pol_t_def api_step_def Let_def w_t_Suc case_prod_unfold)

text \<open>Property of Decision List Policies\<close>
lemma is_greedy_dec_list_pol: \<open>is_greedy_dec_list_pol w (update_dec_list w)\<close>
  using dec_list_pol_spec[unfolded dec_list_pol_spec_def]
  unfolding is_greedy_dec_list_pol_def dec_list_pol_w_def
  by auto

lemma dec_list_pol: \<open>is_dec_list_pol (update_dec_list w)\<close>
  using is_greedy_dec_list_pol is_greedy_dec_list_pol_def by blast

lemma is_policy_p0: \<open>is_dec_list_pol p0\<close>
  using dec_list_pol unfolding p0_def
  using dec_list_pol_w_def
  by blast

lemma is_policy_t: \<open>is_dec_list_pol (pol_t t)\<close>
  using dec_list_pol is_policy_p0 pol_t_eq_w
  by (induction t) auto

lemma pol_t_dec_det: \<open>expl_pol (dec_list_to_pol (pol_t t)) \<in> E.D\<^sub>D\<close>
  using is_policy_t
  using dec_list_to_pol is_policy_dec_det by auto

lemma dec_list_expl_pol_greedy: \<open>E.is_greedy (\<nu>\<^sub>w_expl w) (expl_pol (dec_list_pol_w w))\<close>
  using is_greedy_dec_list_pol
  using is_greedy_pol_w_iff
  by (simp add: dec_list_pol_w_def is_greedy_dec_list_pol_def is_greedy_pol_w_def)

lemmas dec_list_pol_w_def[symmetric, simp]

lemma greedy_w_pol_t: \<open>E.is_greedy (\<nu>\<^sub>w_expl (w_t t)) (expl_pol (dec_list_to_pol (pol_t t)))\<close>
  by (simp add: dec_list_expl_pol_greedy pol_t_eq_w)

lemma proj_err_update_le:
  assumes \<open>is_dec_list_pol p\<close>
  shows \<open>proj_err_w (dec_list_to_pol p) (update_weights i p) \<le> proj_err_w (dec_list_to_pol p) w'\<close>
  using assms is_arg_min_linorder opt_update_weights opt_weights_pol_def
  by metis

text \<open>By the assumptions on @{term update_weights}, its projection error is minimal.\<close>
lemma proj_err_pol_upd_weights:
  assumes \<open>is_dec_list_pol p\<close> 
  shows \<open>proj_err_pol (dec_list_to_pol p) = proj_err_w (dec_list_to_pol p) (update_weights i p)\<close>
  unfolding proj_err_pol_def
  using assms proj_err_w_nonneg proj_err_update_le
  by (auto intro!: antisym cINF_greatest cINF_lower2 bdd_below.I2)

section \<open>Error Analysis\<close>
subsection \<open>Section 7\<close>

text \<open>Optimality of the decision list policy is bounded in terms of the Bellman error.\<close>
text \<open>Equation 22\<close>
definition \<open>pol_err p = dist E.\<nu>\<^sub>b_opt (E.\<nu>\<^sub>b (E.mk_stationary_det (expl_pol p)))\<close>

lemma eqn_22: 
  \<open>(1 - l) * pol_err (dec_list_pol_w w) \<le> 2 * l * bellman_err_w w\<close>
  unfolding pol_err_def bellman_err_w_eq_expl E.bellman_err\<^sub>b_def
  using E.dist_greedy_opt_bound dist_commute dec_list_expl_pol_greedy
  by metis

text\<open>
  This is Lemma 7.1 from the paper.
  If we converge, then the bellman-error of the last step equals the approximation error.
\<close>
text \<open>Lemma 7.1\<close>

lemma proj_err_w_cong:
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> w i = w' i\<close> \<open>is_policy p\<close>
  shows \<open>proj_err_w p w = proj_err_w p w'\<close>
  using assms proj_err_w_eq \<nu>\<^sub>w_expl_cong[of w w']
  by auto

lemma conv_bellman_eq_proj_err:
  assumes \<open>\<And>i t. i < h_dim \<Longrightarrow> body t w i = w i\<close>
  shows \<open>bellman_err_w w = proj_err_w (dec_list_pol_w w) w\<close>
proof -
  let ?p = \<open>dec_list_pol_w w\<close>
  have \<open>proj_err_w ?p w = proj_err_w ?p (body t w)\<close>
    using assms proj_err_w_cong
    using dec_list_pol dec_list_pol_w_def dec_list_to_pol by presburger
  also have \<open>\<dots> = dist (\<nu>\<^sub>w_expl w) (E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w))\<close>
    using proj_err_w_eq
    using E.is_greedy_L_eq_\<L>\<^sub>b is_greedy_dec_list_pol is_greedy_pol_w_def
    using assms \<nu>\<^sub>w_expl_cong[of \<open>body t w\<close> w]
    using dec_list_expl_pol_greedy
    by (metis dec_list_pol dec_list_pol_w_def dec_list_to_pol)
  also have \<open>\<dots> = bellman_err_w w\<close>
    unfolding bellman_err_w_eq_expl E.bellman_err\<^sub>b_def
    by auto
  finally show ?thesis
    by auto
qed

lemma conv_bellman_eq_proj_err':
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> body t w i = w i\<close>
  shows \<open>bellman_err_w w = proj_err_w (dec_list_pol_w w) w\<close>
proof -
  let ?p = \<open>dec_list_pol_w w\<close>
  have \<open>proj_err_w ?p w = proj_err_w ?p (body t w)\<close>
    using assms proj_err_w_cong
    using dec_list_pol dec_list_pol_w_def dec_list_to_pol by presburger
  also have \<open>\<dots> = dist (\<nu>\<^sub>w_expl w) (E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w))\<close>
    using proj_err_w_eq
    using E.is_greedy_L_eq_\<L>\<^sub>b is_greedy_dec_list_pol is_greedy_pol_w_def
    using assms \<nu>\<^sub>w_expl_cong[of \<open>body t w\<close> w]
    using dec_list_expl_pol_greedy
    by (metis dec_list_pol dec_list_pol_w_def dec_list_to_pol)
  also have \<open>\<dots> = bellman_err_w w\<close>
    unfolding bellman_err_w_eq_expl E.bellman_err\<^sub>b_def
    by auto
  finally show ?thesis
    by auto
qed


lemma \<nu>\<^sub>w_w_cong:
    assumes \<open>\<And>i. i < h_dim \<Longrightarrow> w' i = w i\<close>
    shows \<open>\<nu>\<^sub>w w = \<nu>\<^sub>w w'\<close>
  using assms
  unfolding \<nu>\<^sub>w_def
  by auto


lemma Q_w_cong:
    assumes \<open>\<And>i. i < h_dim \<Longrightarrow> w' i = w i\<close>
    shows \<open>Q w x a = Q w' x a\<close>
  using assms \<nu>\<^sub>w_w_cong[OF assms]
  unfolding Q_def G\<^sub>a_def
  by auto

lemma bellman_err_w_cong:
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> w' i = w i\<close>
  shows \<open>bellman_err_w w = bellman_err_w w'\<close>
  unfolding bellman_err_w_def
  using \<nu>\<^sub>w_w_cong[OF assms] Q_w_cong[OF assms]
  by auto


lemma proj_err_w_cong':
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> w' i = w i\<close>
  shows \<open>proj_err_w p w = proj_err_w p w'\<close>
  unfolding proj_err_w_def
  using \<nu>\<^sub>w_w_cong[OF assms] Q_w_cong[OF assms]
  by auto

lemma bellman_err_conv:
  assumes \<open>\<And>i t. i < h_dim \<Longrightarrow> body t w i = w i\<close>
  shows \<open>bellman_err_w w = proj_err_pol (dec_list_pol_w w)\<close>
  using assms body_def dec_list_pol proj_err_pol_upd_weights proj_err_w_cong
  apply (subst conv_bellman_eq_proj_err) 
   apply fastforce
  by (metis (mono_tags, lifting) comp_apply dec_list_pol_w_def dec_list_to_pol)


lemma bellman_err_conv':
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> body t w i = w i\<close>
  shows \<open>bellman_err_w w = proj_err_pol (dec_list_pol_w w)\<close>
  using assms body_def dec_list_pol proj_err_pol_upd_weights proj_err_w_cong
  apply (subst conv_bellman_eq_proj_err')
  apply fastforce
  by (metis (mono_tags, lifting) comp_apply dec_list_pol_w_def dec_list_to_pol)

text \<open>
Corollary 7.2 from the paper
\<close>
corollary weights_conv_bound:
  assumes \<open>\<And>i. i < h_dim \<Longrightarrow> body t w i = w i\<close>
  shows \<open>(1 - l) * pol_err (dec_list_pol_w w) \<le> 2 * l * proj_err_pol (dec_list_pol_w w)\<close>
  using bellman_err_conv' assms eqn_22
  by metis

subsection \<open>Section 3.2.4\<close>
definition \<open>beta_t t = proj_err_w (dec_list_to_pol (pol_t t)) (w_t (Suc t))\<close>

lemma beta_t_nonneg: \<open>beta_t t \<ge> 0\<close>
  using beta_t_def proj_err_w_nonneg
  by auto

text \<open>Lemma 3.3\<close>
lemma proj_err_w0_le_r\<^sub>M: \<open>is_policy p \<Longrightarrow> proj_err_w p w0 \<le> E.r\<^sub>M\<close>
  unfolding  w0_def
  using E.norm_r_dec_le
  apply (subst proj_err_w_eq)
  by auto

lemma proj_err_Suc_opt: 
  \<open>proj_err_w (dec_list_to_pol (pol_t t)) (w_t (Suc t)) \<le> proj_err_w (dec_list_to_pol (pol_t t)) w'\<close>
  using is_policy_t proj_err_update_le
  by (auto simp: w_t_Suc)

lemma beta_t_le_r\<^sub>M: \<open>beta_t t \<le> E.r\<^sub>M\<close>
  using proj_err_w0_le_r\<^sub>M proj_err_Suc_opt order.trans is_policy_t
  unfolding beta_t_def
  by blast
  
lemma beta_t_bound: \<open>\<exists>\<beta>\<^sub>P. \<beta>\<^sub>P \<le> E.r\<^sub>M \<and> (\<forall>t. \<beta>\<^sub>P \<ge> beta_t t)\<close>
  using beta_t_le_r\<^sub>M by blast

definition \<open>beta_bound b \<longleftrightarrow> (\<forall>t. beta_t t \<le> b)\<close>

lemma beta_bound_r\<^sub>M: \<open>beta_bound E.r\<^sub>M\<close>
  using beta_bound_def beta_t_le_r\<^sub>M by blast

fun beta_bar where
\<open>beta_bar 0 = 0\<close> |
\<open>beta_bar (Suc n) = beta_t n + l * beta_bar n\<close>

lemma beta_bar_def': \<open>beta_bar t = (\<Sum>i < t. l ^ (t - i - 1) * beta_t i)\<close>
  by (induction t) (auto simp: algebra_simps Suc_diff_Suc[symmetric] sum_distrib_left)

lemma beta_bar_bound: 
  assumes \<open>\<And>t. t < n \<Longrightarrow> \<beta>\<^sub>P \<ge> beta_t t\<close>
  shows \<open>(1 - l) * beta_bar n \<le> \<beta>\<^sub>P * (1 - l ^ n)\<close>
proof -
  have \<open>(1 - l) * beta_bar n \<le>  (1 - l) * (\<Sum>i<n. l ^ (n - i - 1) * \<beta>\<^sub>P)\<close>
    unfolding beta_bar_def'
    using assms beta_t_nonneg
    by (auto intro!: sum_mono mult_mono)
  also have \<open>\<dots> = (1 - l) * \<beta>\<^sub>P * (\<Sum>i<n. l ^ (n - i - 1))\<close>
    by (subst sum_distrib_right[symmetric]) auto
  also have \<open>\<dots> = (1 - l) * \<beta>\<^sub>P * (\<Sum>i<n. l ^ i)\<close>
    using sum.nat_diff_reindex by auto
  also have \<open>\<dots> =  \<beta>\<^sub>P * (1 - l ^ n)\<close>
    by (simp add: one_diff_power_eq)
  finally show ?thesis.
qed

lemma beta_bar_bound_r\<^sub>M: \<open>(1 - l) * beta_bar n \<le> E.r\<^sub>M * (1 - l ^ n)\<close>
  using beta_bar_bound beta_t_le_r\<^sub>M by blast

text \<open>Theorem 3.5\<close>
definition \<open>bellman_err_t t = E.bellman_err\<^sub>b (E.\<nu>\<^sub>b (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t t)))))\<close>

section \<open>Error Bounds\<close>
text \<open>
We formalize the error bound from Thm 3.5 in the paper.
The proof is adapted from the book Neural Dynamic Programming by Bertsekas (1996), Lemma 6.2, p.277.
\<close>

text \<open>
The distance of the next policy to optimality can be bounded in terms of the distance of the 
previous policy plus the approximation error.
\<close>

lemma err_Suc:
  shows \<open>(1 - l)\<^sup>2 * dist E.\<nu>\<^sub>b_opt (E.\<nu>\<^sub>b (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t (Suc t))))))
    \<le> (1 - l)\<^sup>2 * (l * dist E.\<nu>\<^sub>b_opt (E.\<nu>\<^sub>b (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t t)))))) +  (2 * l * (beta_t t))\<close>
proof -
  text \<open>We first define abbreviations for the most-used terms in the proof.\<close>
  define v where \<open>v = \<nu>\<^sub>w_expl (w_t (Suc t))\<close>
  define p where \<open>p = (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t t))))\<close>
  define d where \<open>d = (E.mk_dec_det (expl_pol (dec_list_to_pol (pol_t t))))\<close>

  define p' where \<open>p' = (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t (Suc t)))))\<close>
  define d' where \<open>d' = (E.mk_dec_det (expl_pol (dec_list_to_pol (pol_t (Suc t)))))\<close>

  define opt where \<open>opt = E.\<nu>\<^sub>b_opt\<close> 

  define vp where \<open>vp = E.\<nu>\<^sub>b p\<close>
  define vp' where \<open>vp' = E.\<nu>\<^sub>b p'\<close>

  define \<xi> where \<open>\<xi> = (\<Squnion>x. vp x - vp' x)\<close>
    \<comment> \<open>The largest amount that the policy decreased (due to the approximation error).\<close>

  define \<epsilon> where \<open>\<epsilon> = dist v vp\<close>
    \<comment> \<open>approximation error\<close>

  text \<open>We show that the approximation error can be bounded in terms of @{const beta_t}.\<close>
  have \<epsilon>_bound: \<open>(1 - l) * \<epsilon> \<le> beta_t t\<close>
  proof -
    have \<open>\<epsilon> \<le> dist (E.L d v) v + dist (E.L d v) (E.L d vp)\<close>
      by (simp add: dist_commute dist_triangle2 \<epsilon>_def v_def vp_def d_def p_def E.L_\<nu>_fix[symmetric])
    also have \<open>\<dots> \<le> dist (E.L d v) v + l * \<epsilon>\<close>
      by (auto simp: \<epsilon>_def intro: E.contraction_L)
    also have \<open>\<dots> = beta_t t + l * \<epsilon>\<close>
      unfolding beta_t_def  v_def d_def
      using is_policy_t
      apply (subst proj_err_w_eq)
      by (auto simp add: dist_commute)
    finally show ?thesis
      by argo
  qed

  text \<open>The decrease in policy quality @{term \<xi>} can be upper-bounded by the approximation error.\<close>
  have lemma_6_1: \<open>(1 - l) * \<xi> \<le> 2 * l * \<epsilon>\<close>
    unfolding \<xi>_def vp_def vp'_def \<epsilon>_def v_def p_def p'_def
    unfolding w_t_Suc
    using is_policy_t dec_list_expl_pol_greedy pol_t_eq_w w_t_Suc  E.is_greedy_iff
    by (auto intro!: E.approx_policy_lemma E.is_greedy_L_eq_\<L>\<^sub>b)+

  define \<zeta> where \<open>\<zeta> = dist opt vp\<close>

  have lemma_bertsekas: \<open>(1 - l) * dist opt vp' \<le> (1 - l) * (l * \<zeta>) + (2 * l * \<epsilon>)\<close>
  proof -
    have \<L>\<^sub>b_v_eq_L: \<open>E.\<L>\<^sub>b v = E.L d' v\<close>
      unfolding d'_def v_def
      using greedy_w_pol_t
      by (rule E.is_greedy_L_eq_\<L>\<^sub>b[symmetric])

    have \<open>vp' \<le> opt\<close>
      unfolding p'_def opt_def vp'_def
      using pol_t_dec_det by auto

    text \<open>
The value of the next policy is close to the optimal value wrt. the value of the previous policy.
\<close>
    have \<open>opt - vp' \<le> (l * \<zeta>) *\<^sub>R 1 + (2 * l * \<epsilon>) *\<^sub>R 1 + (l * \<xi>) *\<^sub>R 1\<close>
    proof -
      have \<open>opt - vp' = opt - E.L d' vp'\<close>
        using E.L_\<nu>_fix d'_def p'_def vp'_def 
        by auto
      also have \<open>\<dots> \<le> opt - E.L d' (vp - \<xi> *\<^sub>R 1)\<close>
      proof -
        have \<open>vp - vp' \<le> (\<xi> *\<^sub>R 1)\<close>
          by (fastforce simp: vp_def vp'_def \<xi>_def intro!: cSUP_upper2 bounded_imp_bdd_above bounded_minus_comp)
        thus ?thesis
          by (auto simp: algebra_simps)
      qed
      also have \<open>\<dots> = opt - E.L d' vp + (l * \<xi>) *\<^sub>R 1\<close>
        unfolding E.L_def
        by (auto simp: blinfun.diff_right blinfun.scaleR_right scaleR_right_diff_distrib)
      also have \<open>\<dots> \<le> (l * \<zeta>) *\<^sub>R 1 + (2 * l * \<epsilon>) *\<^sub>R 1 + (l * \<xi>) *\<^sub>R 1\<close>
      proof -
        have \<open>opt - E.L d' vp \<le> opt - E.L d' (v - \<epsilon> *\<^sub>R 1)\<close>
          unfolding \<epsilon>_def
          by (auto simp add: dist_bfun_ge dist_commute \<epsilon>_def)
        also have \<open>\<dots> = opt - E.L d' v + (l * \<epsilon>) *\<^sub>R 1\<close>
          unfolding E.L_diff
          by auto
        also have \<open>\<dots> = opt - E.\<L>\<^sub>b v + (l * \<epsilon>) *\<^sub>R 1\<close>
          by (simp add: \<L>\<^sub>b_v_eq_L)
        also have \<open>\<dots> \<le> opt - E.\<L>\<^sub>b (vp - \<epsilon> *\<^sub>R 1) + (l * \<epsilon>) *\<^sub>R 1\<close>
          using dist_bfun_ge unfolding \<epsilon>_def by fastforce
        also have \<open>\<dots> = opt - E.\<L>\<^sub>b vp + (2 * l * \<epsilon>) *\<^sub>R 1\<close>
          by (auto simp: E.\<L>\<^sub>b_diff)
        also have \<open>\<dots> \<le> opt - E.\<L>\<^sub>b (opt - \<zeta> *\<^sub>R 1) + (2 * l * \<epsilon>) *\<^sub>R 1\<close>
          unfolding \<zeta>_def
          using dist_bfun_le
          by (fastforce simp: algebra_simps)
        also have \<open>\<dots> = (l * \<zeta>) *\<^sub>R 1 + (2 * l * \<epsilon>) *\<^sub>R 1\<close>
          by (simp add: opt_def E.\<L>\<^sub>b_diff)
        finally have \<open>opt - E.L d' vp \<le> (l * \<zeta>) *\<^sub>R 1 + (2 * l * \<epsilon>) *\<^sub>R 1\<close> .
        thus ?thesis
          by simp
      qed
      finally show \<open>opt - vp' \<le> (l * \<zeta>) *\<^sub>R 1 + (2 * l * \<epsilon>) *\<^sub>R 1 + (l * \<xi>) *\<^sub>R 1\<close> .
    qed
    hence \<open>dist opt vp' \<le> l * \<zeta> + 2 * l * \<epsilon> + l * \<xi>\<close>
      using \<open>vp' \<le> opt\<close>[unfolded less_eq_bfun_def]
      by (auto intro!: cSUP_least simp: dist_real_def dist_bfun.rep_eq)
    hence \<open>(1 - l) * dist opt vp' \<le> (1 - l) * ((l * \<zeta>) + (2 * l * \<epsilon>) + (l * \<xi>))\<close>
      using E.disc_le_one
      by auto
    also have \<open>\<dots> \<le> (1 - l) * (l * \<zeta>) + (1 - l) * (2 * l * \<epsilon>) + l * ((1 - l) * \<xi>)\<close> (is "_ \<le> ?X + l * ((1 - l) * \<xi>)")
      by argo
    also have \<open>\<dots> \<le> ?X + l * (2 * l * \<epsilon>)\<close>
      using lemma_6_1
      by (auto intro: mult_left_mono)
    finally have \<open>(1 - l) * dist opt vp' \<le> ?X + l * (2 * l * \<epsilon>)\<close> .
    thus ?thesis
      by (auto simp: algebra_simps)
  qed

  text \<open>Now all that's left to do is to plug in the bound on @{term \<epsilon>}.\<close>
  hence \<open>(1 - l)^2 * dist opt vp' \<le> (1 - l) * ((1 - l) * (l * \<zeta>) + (2 * l * \<epsilon>))\<close>
    by (auto simp: power2_eq_square)
  also have \<open>\<dots> \<le> ((1 - l)^2 * (l * \<zeta>)) +  (2 * l * ((1 - l) * \<epsilon>))\<close>
    by (auto simp: power2_eq_square algebra_simps)
  also have \<open>\<dots> \<le> ((1 - l)^2 * (l * \<zeta>)) +  (2 * l * (beta_t t))\<close>
    by (auto simp: \<epsilon>_bound mult_left_mono)
  finally show ?thesis
    unfolding p_def opt_def p'_def \<zeta>_def vp_def vp'_def .
qed                                               

text \<open>
By a simple induction, the lemma @{thm err_Suc} can be used to derive an error bound after any 
number of iterations.
This theorem corresponds to Theorem 3.5 in the paper the formalization is based on.
\<close>
lemma err_bound:
  shows
    \<open>(1 - l) ^ 2 * dist E.\<nu>\<^sub>b_opt (E.\<nu>\<^sub>b (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t t))))) \<le> 
   (1 - l) ^ 2 *  l ^ t * dist E.\<nu>\<^sub>b_opt (E.\<nu>\<^sub>b (E.mk_stationary_det (expl_pol (dec_list_to_pol (pol_t 0))))) 
      + 2 * l * beta_bar t\<close>
    using mult_left_mono
    by (induction t) (fastforce simp: algebra_simps intro!: order.trans[OF err_Suc])+

text \<open>Guarantees for api'\<close>

lemma api_aux_pol_eq_upd:
  assumes \<open>api_aux pw t0 = (w, p, err, t, w_eq, err_le, timeout)\<close>
  shows \<open>p = update_dec_list w\<close>
  using assms
proof (induction pw t0 arbitrary: w p err t w_eq err_le timeout rule: api_aux.induct)
  case (1 pw t)
  show ?case
    using 1 
    apply (subst (asm) (2) api_aux.simps)
    by (auto simp: Let_def case_prod_unfold simp del: api_aux.simps split: if_splits)
      (metis prod.collapse)
qed

lemma
  assumes \<open>api_aux pw t0 = (w, p, err, t, w_eq, err_le, timeout)\<close>
  shows 
    api_aux_err: \<open>err = proj_err_w (dec_list_to_pol p) w\<close>
  using assms
proof (induction pw t0 arbitrary: w p err t w_eq err_le timeout rule: api_aux.induct)
  case (1 pw t)
  show ?case
    using 1
    apply (subst (asm) (2) api_aux.simps)
    unfolding Let_def case_prod_unfold
    by (auto simp: simp del: api_aux.simps split: if_splits) (metis prod.collapse)
qed

lemma
  assumes \<open>api = (w, p, err, t, w_eq, err_le, timeout)\<close>
  shows 
    api_err: \<open>err = proj_err_w (dec_list_to_pol p) w\<close>
  using assms api_aux_err 
  unfolding api_def Let_def
  by blast


lemma api_pol_eq_upd:
  assumes \<open>api = (w, p, err, t, w_eq, err_le, timeout)\<close>
  shows \<open>p = update_dec_list w\<close>
  using assms api_aux_pol_eq_upd 
  unfolding api_def Let_def
  by blast

lemma api_aux_obt_prev_w:
  assumes \<open>api_aux pw t0 = (w, p, err, t, w_eq, err_le, timeout)\<close> \<open>fst pw = update_dec_list (snd pw)\<close>
  obtains w' where \<open>w = body t w'\<close>
  using assms
proof (induction pw t0 arbitrary: w p err t w_eq err_le timeout thesis rule: api_aux.induct)
  case (1 pw t)
  show ?case
    using 1
    apply (subst (asm) (2) api_aux.simps)
    unfolding Let_def case_prod_unfold body_def
    by (auto simp: simp del: api_aux.simps split: if_splits) (metis prod.collapse)+ 
qed

lemma api_aux_obt_prev_w_conv:
  assumes \<open>api_aux pw t0 = (w, p, err, t, w_eq, err_le, timeout)\<close> \<open>fst pw = update_dec_list (snd pw)\<close> w_eq
  obtains w' where \<open>w = body t w'\<close> and \<open>\<And>i. i < h_dim \<Longrightarrow> w i = w' i\<close>
  using assms
proof (induction pw t0 arbitrary: w p err t w_eq err_le timeout thesis rule: api_aux.induct)
  case (1 pw t0 w p err t w_eq err_le timeout thesis)
  show ?case
    using 1
    using 1(1)[OF refl _ refl refl refl refl refl refl refl, of \<open>fst pw\<close> \<open>snd pw\<close> w t thesis p err w_eq err_le timeout]
    apply (subst (asm) (2) api_aux.simps)
    by (auto simp: Let_def case_prod_unfold body_def simp del: api_aux.simps split: if_splits)
      (metis "1.prems"(1) prod.collapse)
qed

lemma api_obt_prev_w_conv:
  assumes \<open>api = (w, p, err, t, True, err_le, timeout)\<close>
  obtains w' where \<open>w = body t w'\<close> and \<open>\<And>i. i < h_dim \<Longrightarrow> w i = w' i\<close>
  using api_aux_obt_prev_w_conv assms
  by (auto simp: api_def Let_def simp del: api_aux.simps split: if_splits) metis

theorem conv_bellman_eq_proj_err'':
  fixes t :: "nat"
    and w :: "nat \<Rightarrow> real"
  assumes "body t w' = w" "\<And>i. i < h_dim \<Longrightarrow> w' i = w i"
  shows "bellman_err_w w = proj_err_w (dec_list_pol_w w) w"
  using assms
  by (metis E.bellman_err\<^sub>b_def E.is_greedy_L_eq_\<L>\<^sub>b bellman_err_w_eq_expl dec_list_expl_pol_greedy dec_list_pol dec_list_pol_w_def dec_list_to_pol proj_err_w_eq)

theorem api_correct:
  assumes \<open>api = (w, p, err, t, True, err_le, timeout)\<close>
  shows \<open>(1 - l) * pol_err (dec_list_to_pol p) \<le> 2 * l * err\<close>
proof -
  have \<open>dec_list_pol_w w = dec_list_to_pol p\<close>
    using api_pol_eq_upd[OF assms(1)]
    by auto

  obtain w' where *: \<open>body t w' = w\<close> \<open>\<And>i. i < h_dim \<Longrightarrow> w i = w' i\<close>
    using assms
    by (metis api_obt_prev_w_conv)

  have \<open>proj_err_w (dec_list_to_pol p) w = err\<close>
    using api_err assms by blast

  hence \<open>bellman_err_w w = err\<close>
    using conv_bellman_eq_proj_err'' *  \<open>dec_list_pol_w w = dec_list_to_pol p\<close> conv_bellman_eq_proj_err 
    by fastforce

  thus ?thesis
    using assms
    by (metis \<open>dec_list_pol_w w = dec_list_to_pol p\<close> eqn_22)
qed

end
end