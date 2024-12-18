(* Code correctness done *)

theory PMF_Code
imports Set_Code "HOL-Probability.Probability"
begin

record ('pmf, 'x, 'xset) pmf_ops =
  pmf_\<alpha> :: \<open>'pmf \<Rightarrow> 'x pmf\<close>
  pmf_op_prob_at :: \<open>'pmf \<Rightarrow> 'x \<Rightarrow> real\<close>
  pmf_op_supp :: \<open>'pmf \<Rightarrow> 'xset\<close>
  pmf_op_invar :: \<open>'pmf \<Rightarrow> bool\<close>

locale PmfDefs =
  fixes ops :: "('pmf, 'x::linorder, 'xset) pmf_ops" and
    pmf_set_ops :: \<open>('x, 'xset) oset_ops\<close>
begin

  abbreviation \<alpha> where "\<alpha> == pmf_\<alpha> ops"
  abbreviation prob_at where "prob_at == pmf_op_prob_at ops"
  abbreviation supp where "supp == pmf_op_supp ops"
  abbreviation invar where "invar == pmf_op_invar ops"
  abbreviation dom_ops where "dom_ops == pmf_set_ops"

sublocale Set: StdOSetDefs dom_ops .

definition \<open>pmf_rel R_elem p1 p2 \<longleftrightarrow>
  invar p1 \<and>
  Set.invar (supp p1) \<and>
  (set_pmf p2) \<subseteq> Set.\<alpha> (supp p1) \<and>
  (\<forall>x y. R_elem x y \<longrightarrow> prob_at p1 x = pmf p2 y)\<close>

end

locale Pmf = PmfDefs ops pmf_set_ops for ops pmf_set_ops +
  assumes
    supp_invar[intro]: \<open>\<And>p. invar p \<Longrightarrow> Set.invar (supp p)\<close> and
    supp_sup: \<open>\<And>p. invar p \<Longrightarrow> set_pmf (\<alpha> p) \<subseteq> Set.\<alpha> (supp p)\<close> and
    prob_at_correct[simp]: \<open>\<And>p x. invar p \<Longrightarrow> prob_at p x = pmf (\<alpha> p) x\<close> and
    set: \<open>StdOSet pmf_set_ops\<close>
begin

lemma pmf_relE[elim]:
  assumes \<open>pmf_rel R p_code p\<close> 
  obtains \<open>invar p_code\<close> \<open>Set.invar (supp p_code)\<close> \<open>(set_pmf p) \<subseteq> Set.\<alpha> (supp p_code)\<close>
    \<open>\<And>x y. R x y \<Longrightarrow> prob_at p_code x = pmf p y\<close>
  using assms pmf_rel_def
  by auto

lemma pmf_rel_pmf_eq[simp]:
  assumes \<open>pmf_rel R p_code p\<close> \<open>R x y\<close>  
  shows \<open>prob_at p_code x = pmf p y\<close>
  using assms
  by auto

lemma pmf_eq_rel_pmf_eq[simp]:
  assumes \<open>pmf_rel (=) p_code p\<close>
  shows \<open>prob_at p_code x = pmf p x\<close>
  using assms 
  by auto

sublocale Set: StdOSet dom_ops
  using set .
end

locale PmfNat = Pmf ops pmf_set_ops
  for ops :: \<open>('pmf, nat, 'natset) pmf_ops\<close> and pmf_set_ops
begin

sublocale Set: StdOSet dom_ops
  using set .

lemma prob_nonneg: \<open>\<And>p. invar p \<Longrightarrow> prob_at p x \<ge> 0\<close>
  by auto

lemma prob_zero[simp]: \<open>invar p \<Longrightarrow> x \<notin> Set.\<alpha> (supp p) \<Longrightarrow> prob_at p x = 0\<close>
  using supp_sup[of p] by (auto simp: set_pmf_iff subset_iff)

lemma prob_one[simp]: \<open>invar p \<Longrightarrow> sum (prob_at p) (Set.\<alpha> (supp p)) = 1\<close>
  using supp_sup by (auto intro!: sum_pmf_eq_1)

lemma finite_supp[intro!]: \<open>invar p \<Longrightarrow> finite (Set.\<alpha> (supp p))\<close>
  by auto

lemma nn_integral_prob_at_one:
  assumes \<open>invar p\<close>
  shows \<open>\<integral>\<^sup>+ x. ennreal (prob_at p x) \<partial>count_space UNIV = 1\<close>
proof -
  have \<open>(\<integral>\<^sup>+ x. prob_at p x \<partial>count_space UNIV) = \<integral>\<^sup>+ x \<in> Set.\<alpha> (supp p). prob_at p x \<partial>count_space UNIV\<close>
    unfolding indicator_def
    using prob_zero assms
    by (auto intro!: nn_integral_cong)
  also have \<open>\<dots> = sum (prob_at p) (Set.\<alpha> (supp p))\<close>
    using assms
    by (subst nn_integral_indicator_finite) auto
  finally show ?thesis
    using prob_one assms
    by auto
qed

lemma pmf_embed_prob_at[simp]: \<open>invar p \<Longrightarrow> pmf (embed_pmf (prob_at p)) x = prob_at p x\<close>
  using nn_integral_prob_at_one prob_nonneg
  by (auto simp: pmf_embed_pmf)

lemma set_pmf_embed_prob_at: \<open>invar p \<Longrightarrow> 
  set_pmf (embed_pmf (prob_at p)) \<subseteq> Set.\<alpha> (supp p)\<close>
  using nn_integral_prob_at_one prob_nonneg prob_zero
  by (fastforce simp: set_embed_pmf)

lemma set_pmf_embed_prob_at'[simp]: \<open>invar p \<Longrightarrow> 
  set_pmf (embed_pmf (prob_at p)) = {x. prob_at p x \<noteq> 0}\<close>
  using nn_integral_prob_at_one prob_nonneg
  by (fastforce simp: set_embed_pmf)

end

end