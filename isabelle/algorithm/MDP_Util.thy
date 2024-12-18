theory MDP_Util
  imports Util
begin

section \<open>Auxiliary Lemmas on Explicit MDPs\<close>
context MDP_reward_disc
begin

lemma approx_policy_lemma:
  assumes \<open>p \<in> D\<^sub>R\<close>
  assumes \<open>dist v (\<nu>\<^sub>b (mk_stationary p)) \<le> \<epsilon>\<close>
  assumes \<open>(L p' v) = (\<L>\<^sub>b v)\<close>
  shows \<open>(1 - l) * (\<Squnion>s. (\<nu>\<^sub>b (mk_stationary p)) s - (\<nu>\<^sub>b (mk_stationary p')) s) \<le> 2 * l * \<epsilon>\<close>
proof -
  define \<xi> where \<open>\<xi> = (\<Squnion>s. (\<nu>\<^sub>b (mk_stationary p) s) - (\<nu>\<^sub>b (mk_stationary p') s))\<close>
  let ?p' = \<open>mk_stationary p'\<close>
  let ?p = \<open>mk_stationary p\<close>

  have diff_\<nu>_le_\<xi>:\<open>\<nu>\<^sub>b ?p - \<nu>\<^sub>b ?p' \<le> \<xi> *\<^sub>R 1\<close>
    unfolding \<xi>_def
    by (auto intro!: bounded_minus_comp cSUP_upper less_eq_bfunI bounded_imp_bdd_above)

  have \<open>L p' (\<nu>\<^sub>b ?p) - (l * \<xi>) *\<^sub>R 1 \<le> L p' (\<nu>\<^sub>b ?p - \<xi> *\<^sub>R 1)\<close>
    unfolding L_def
    by (simp add: algebra_simps blinfun.add_right blinfun.diff_right blinfun.scaleR_right)
  also have \<open>\<dots> \<le> L p' (\<nu>\<^sub>b ?p')\<close>
    using diff_\<nu>_le_\<xi>
    by (auto simp: algebra_simps)
  also have \<open>\<dots> = \<nu>\<^sub>b ?p'\<close>
    using L_\<nu>_fix
    by auto
  finally have \<nu>'_ge: \<open>\<nu>\<^sub>b ?p' \<ge> L p' (\<nu>\<^sub>b ?p) - (l * \<xi>) *\<^sub>R 1\<close>.

  have \<open>\<nu>\<^sub>b ?p - \<nu>\<^sub>b ?p' \<le> \<nu>\<^sub>b ?p  - L p' (\<nu>\<^sub>b ?p)  + (l * \<xi>) *\<^sub>R 1\<close>
    using \<nu>'_ge
    by (auto simp: algebra_simps)
  also have \<open>\<dots> \<le> (L p (\<nu>\<^sub>b ?p) - L p v) + (L p' v  - L p' (\<nu>\<^sub>b ?p))  + (l * \<xi>) *\<^sub>R 1\<close>
    using assms L_le_\<L>\<^sub>b L_\<nu>_fix
    by auto
  also have \<open>\<dots> \<le> dist (L p (\<nu>\<^sub>b ?p)) (L p v) *\<^sub>R 1 + dist (L p' v) (L p' (\<nu>\<^sub>b ?p)) *\<^sub>R 1  + (l * \<xi>) *\<^sub>R 1\<close>
    by (intro add_mono sub_bfun_le_dist) auto
  also have \<open>\<dots> \<le> (l * dist (\<nu>\<^sub>b ?p) v) *\<^sub>R 1 + (l * dist (\<nu>\<^sub>b ?p) v) *\<^sub>R 1  + (l * \<xi>) *\<^sub>R 1\<close> 
    using contraction_L[of _ \<open>\<nu>\<^sub>b (mk_stationary p)\<close> v]
    by (intro add_mono) (auto simp: algebra_simps dist_commute)
  also have \<open>\<dots> \<le> (2 * l * \<epsilon>) *\<^sub>R 1 + (l * \<xi>) *\<^sub>R 1\<close>
    by (auto simp: mult_left_mono dist_commute assms)
  finally have diff_\<nu>_le: \<open>\<nu>\<^sub>b ?p - \<nu>\<^sub>b ?p' \<le> (2 * l * \<epsilon>) *\<^sub>R 1 + (l * \<xi>) *\<^sub>R 1\<close> .

  have \<open>\<xi> *\<^sub>R (1 ::  's \<Rightarrow>\<^sub>b real) \<le> (2 * l * \<epsilon>) *\<^sub>R (1 ::  's \<Rightarrow>\<^sub>b real) + (l * \<xi>) *\<^sub>R 1\<close>
    using diff_\<nu>_le
    by (fastforce simp: \<xi>_def cSUP_le_iff algebra_simps bounded_imp_bdd_above bounded_minus_comp)
  hence \<open>\<xi> \<le> 2 * l * \<epsilon> + l * \<xi>\<close>
    by (auto dest!: less_eq_bfunD intro!: less_eq_bfunI simp: algebra_simps)
  hence \<open>(1 - l) * \<xi> \<le> 2 * l * \<epsilon>\<close>
    by (simp add: mult.commute right_diff_distrib')
  thus \<open>(1 - l) * (\<Squnion>s. (\<nu>\<^sub>b (mk_stationary p)) s - (\<nu>\<^sub>b (mk_stationary p')) s) \<le> 2 * l * \<epsilon>\<close>
    unfolding \<xi>_def
    by auto
qed

definition \<open>bellman_err\<^sub>b v = dist v (\<L>\<^sub>b v)\<close>

definition \<open>bellman_err v = dist (Bfun v) (\<L>\<^sub>b (Bfun v))\<close>

lemma \<open>v \<in> bfun \<Longrightarrow> bellman_err v = bellman_err\<^sub>b (Bfun v)\<close>
  by (auto simp: bellman_err_def bellman_err\<^sub>b_def)

section \<open>Greedy Policies\<close>

lemma L\<^sub>a_le_\<L>\<^sub>b:
  assumes \<open>a \<in> A s\<close>
  shows \<open>L\<^sub>a a (apply_bfun v) s \<le> apply_bfun (\<L>\<^sub>b v) s\<close>
  unfolding \<L>\<^sub>b_eq_SUP_L\<^sub>a SUP_L\<^sub>a_eq_det
  using L\<^sub>a_le' assms
  by (auto intro!: bdd_aboveI cSUP_upper2)

lemma L\<^sub>a_eq_\<L>_imp_opt_act:
  assumes a: \<open>a \<in> A s\<close> and L_a: \<open>L\<^sub>a a (v :: 's \<Rightarrow>\<^sub>b real) s = \<L>\<^sub>b v s\<close>
  shows \<open>is_opt_act v s a\<close>
proof -
  have \<open>L\<^sub>a a' v  s \<le> L\<^sub>a a v s\<close> if \<open>a' \<in> A s\<close> for a'
    unfolding L_a
    using L_a that L\<^sub>a_le_\<L>\<^sub>b by auto
  thus ?thesis
    unfolding is_opt_act_def
    using assms by auto
qed

lemma is_opt_act_act[dest]: \<open>is_opt_act v s a \<Longrightarrow> a \<in> A s\<close>
  unfolding is_opt_act_def by auto

lemma is_opt_act_le[dest]: \<open>is_opt_act v s a \<Longrightarrow> a' \<in> A s \<Longrightarrow> L\<^sub>a a' v s \<le> L\<^sub>a a v s\<close>
  unfolding is_opt_act_def by auto

lemma opt_act_imp_L\<^sub>a_eq_\<L>:
  assumes \<open>is_opt_act (apply_bfun v) s a\<close> 
  shows \<open>L\<^sub>a a (apply_bfun v) s = apply_bfun (\<L>\<^sub>b v) s\<close>
proof -
  have \<open>L\<^sub>a a v s \<le> \<L>\<^sub>b v s\<close>
    using assms L\<^sub>a_le_\<L>\<^sub>b by auto
  moreover have \<open>\<L>\<^sub>b v s \<le> L\<^sub>a a v s\<close>
    unfolding \<L>\<^sub>b_eq_SUP_L\<^sub>a SUP_L\<^sub>a_eq_det
    using A_ne assms
    by (auto intro!: cSUP_least)
  ultimately show ?thesis
    by auto
qed

lemma is_opt_act_iff: \<open>is_opt_act (v :: 's \<Rightarrow>\<^sub>b real) s a \<longleftrightarrow> a \<in> A s \<and> (L\<^sub>a a v s = \<L>\<^sub>b v s)\<close>
  using L\<^sub>a_eq_\<L>_imp_opt_act opt_act_imp_L\<^sub>a_eq_\<L>
  by auto

definition \<open>is_greedy (v :: 's \<Rightarrow>\<^sub>b real) p = (\<forall>s. is_opt_act v s (p s))\<close>

lemma is_greedy_iff: \<open>is_greedy (v :: 's \<Rightarrow>\<^sub>b real) p = (\<forall>s. p s \<in> A s \<and> L\<^sub>a (p s) v s = \<L>\<^sub>b v s)\<close>
  unfolding is_greedy_def is_opt_act_iff
  by auto

lemma is_greedy_L\<^sub>a_eq_\<L>\<^sub>b:
  assumes \<open>is_greedy (v :: 's \<Rightarrow>\<^sub>b real) p\<close>
  shows \<open>L\<^sub>a (p s) v s = \<L>\<^sub>b v s\<close>
  using assms
  unfolding is_greedy_iff by auto
  
lemma is_greedy_L_eq_\<L>\<^sub>b:
  assumes \<open>is_greedy (v :: 's \<Rightarrow>\<^sub>b real) p\<close>
  shows \<open>L (mk_dec_det p) v = \<L>\<^sub>b v\<close>
  using assms is_greedy_L\<^sub>a_eq_\<L>\<^sub>b L_eq_L\<^sub>a_det
  by fastforce

lemma disc_le_one: \<open>l \<le> 1\<close>
  using disc_lt_one by linarith

lemma dist_opt_bound: \<open>(1 - l) * dist \<nu>\<^sub>b_opt v \<le> dist (\<L>\<^sub>b v) v\<close>
proof -
  have \<open>dist \<nu>\<^sub>b_opt v \<le> dist (\<L>\<^sub>b \<nu>\<^sub>b_opt) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) v\<close>
    using dist_triangle
    by auto
  also have \<open>\<dots> \<le> l * dist \<nu>\<^sub>b_opt v + dist (\<L>\<^sub>b v) v\<close>
    using contraction_\<L>
    by (auto simp del: \<L>\<^sub>b_opt)
  finally show ?thesis
    by (auto simp: algebra_simps)
qed

lemma dist_greedy_bound:
    assumes \<open>is_greedy v d\<close>
    shows \<open>(1 - l) * dist v (\<nu>\<^sub>b (mk_stationary_det d)) \<le> dist (\<L>\<^sub>b v) v\<close>
proof -
  have "dist v (\<nu>\<^sub>b (mk_stationary_det d)) \<le> dist (\<nu>\<^sub>b (mk_stationary_det d)) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) v"
    by (auto simp: add.commute dist_commute dist_triangle)
  also have \<open>\<dots> = dist (L (mk_dec_det d) (\<nu>\<^sub>b (mk_stationary_det d))) (L (mk_dec_det d) v) + dist (\<L>\<^sub>b v) v\<close>
    using assms is_greedy_L_eq_\<L>\<^sub>b L_\<nu>_fix
    by auto
  also have \<open>\<dots> \<le> l * dist (\<nu>\<^sub>b (mk_stationary_det d)) v + dist (\<L>\<^sub>b v) v\<close>
    using contraction_L
    by auto
  finally show ?thesis
    by (auto simp: algebra_simps dist_commute)
qed

lemma dist_greedy_opt_bound:
  assumes \<open>is_greedy v d\<close>
  shows \<open>(1 - l) * dist \<nu>\<^sub>b_opt (\<nu>\<^sub>b (mk_stationary_det d)) \<le> 2 * l * dist (\<L>\<^sub>b v) v\<close>
proof -
  let ?v = "(\<nu>\<^sub>b (mk_stationary_det d))"
  let ?d = "((mk_dec_det d))"

  have \<open>dist \<nu>\<^sub>b_opt ?v \<le> dist \<nu>\<^sub>b_opt (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) ?v\<close>  
    using dist_triangle by auto
  also have \<open>\<dots> = dist (\<L>\<^sub>b \<nu>\<^sub>b_opt) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) ?v\<close>  
    using \<L>\<^sub>b_opt by presburger
  also have \<open>\<dots> = dist (\<L>\<^sub>b \<nu>\<^sub>b_opt) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) (L ?d ?v)\<close>
    using L_\<nu>_fix by auto
  also have \<open>\<dots> = dist (\<L>\<^sub>b \<nu>\<^sub>b_opt) (\<L>\<^sub>b v) + dist (L ?d v) (L ?d ?v)\<close>
    using assms is_greedy_L_eq_\<L>\<^sub>b by fastforce
  also have \<open>\<dots> \<le> l * dist \<nu>\<^sub>b_opt v + l * dist v ?v\<close>
    using contraction_L contraction_\<L>
    by (auto intro: add_mono simp del: \<L>\<^sub>b_opt)
  finally have \<open>dist \<nu>\<^sub>b_opt ?v \<le> l * dist \<nu>\<^sub>b_opt v + l * dist v ?v\<close>.
  hence \<open>(1 - l) * dist \<nu>\<^sub>b_opt ?v \<le> (1 - l) * (l * (dist \<nu>\<^sub>b_opt v + dist v ?v))\<close>
    using disc_le_one
    by (intro mult_left_mono) (auto simp: algebra_simps)
 hence *: \<open>(1 - l) * dist \<nu>\<^sub>b_opt ?v \<le> l * ((1 - l) * dist \<nu>\<^sub>b_opt v + (1 - l) * dist v ?v)\<close>
   by (auto simp: algebra_simps)
  hence \<open>(1 - l) * dist \<nu>\<^sub>b_opt ?v \<le> l * (2 * dist (\<L>\<^sub>b v) v)\<close>
    using dist_opt_bound[of v] dist_greedy_bound[OF assms]
    by (auto intro!: order.trans[OF *] mult_left_mono)
  thus ?thesis
    by auto
qed

lemma L_add: \<open>L p (v + c *\<^sub>R 1) = L p v + (l * c) *\<^sub>R 1\<close>
  unfolding L_def
  by (simp add: blinfun.add_right blinfun.scaleR_right scaleR_right_distrib)

lemma L_diff: \<open>L p (v - c *\<^sub>R 1) = L p v - (l * c) *\<^sub>R 1\<close>
  by (metis L_add add_implies_diff diff_add_cancel)

lemma \<L>\<^sub>b_add: \<open>\<L>\<^sub>b (v + c *\<^sub>R 1) = \<L>\<^sub>b v + (l * c) *\<^sub>R 1\<close>
  by (auto simp: \<L>\<^sub>b.rep_eq L_add \<L>_def cSUP_add)

lemma \<L>\<^sub>b_diff: \<open>\<L>\<^sub>b (v - c *\<^sub>R 1) = \<L>\<^sub>b v - (l * c) *\<^sub>R 1\<close>
  by (metis \<L>\<^sub>b_add add_implies_diff diff_add_cancel)

lemma is_dec_detI[intro]:
  assumes \<open>\<And>s. d s \<in> A s\<close>
  shows \<open>is_dec_det d\<close>
  using assms is_dec_det_def 
  by auto

lemma is_dec_detD[dest]:
  assumes \<open>is_dec_det d\<close>
  shows \<open>\<And>s. d s \<in> A s\<close>
  using assms is_dec_det_def 
  by auto
end
end