theory Pmf_Inst
  imports 
  "../Code_Setup"
begin

type_synonym dom_set_ty = nat

type_synonym set_ty = \<open>nat\<close>

locale PmfNat_Inst =
  S: NatSet \<open>set_ops :: (nat, 'natset) oset_ops\<close> +
  M: StdMap \<open>map_ops :: (nat, real, 'm) map_ops\<close>
  for map_ops set_ops
begin

lemmas M.lookup_correct[simp] M.ball_correct[simp]

definition \<open>range_nonneg v \<longleftrightarrow> M.ball v (\<lambda>(x, p). p \<ge> 0)\<close>

definition \<open>range_sum_one v \<longleftrightarrow> 1 = M.iterate v (\<lambda>(_, p) acc. p + acc) 0\<close>

lemma iterate_sum: \<open>M.invar v \<Longrightarrow>
  M.iterate v (\<lambda>(_, p) acc. p + acc) init = init + (\<Sum>(k, v)\<in>map_to_set (M.\<alpha> v). v)\<close>
  by (rule M.iterate_rule_insert_P[where I = \<open>\<lambda>X acc. finite X \<and> acc + (\<Sum>(k, v)\<in>map_to_set (M.\<alpha> v) - X. v) = 
    (\<Sum>(k, v)\<in>map_to_set (M.\<alpha> v). v) + init\<close>])
        (auto simp: algebra_simps sum_diff finite_map_to_set)

lemma set_map_to_list: \<open>M.invar v \<Longrightarrow> set (M.to_list v) = map_to_set (M.\<alpha> v)\<close>
  using M.to_list_correct
  using map_to_set_map_of
  by fastforce

lemma mem_map_to_setD: \<open>(k, v) \<in> map_to_set m \<Longrightarrow> m k = Some v\<close>
  by (simp add: map_to_set_def)

lemma sum_to_list: \<open>M.invar v \<Longrightarrow>
  (\<Sum>i\<in> (fst ` set (M.to_list v)). case M.\<alpha> v i of None \<Rightarrow> 0 | Some p \<Rightarrow> p) = M.iterate v (\<lambda>(_, p) acc. p + acc) 0\<close>
  unfolding range_sum_one_def
  supply sum.reindex[subst]
  using inj_on_fst_map_to_set
  by (auto intro!: sum.cong simp: set_map_to_list iterate_sum dest!: mem_map_to_setD)

definition \<open>pmf_lookup v i = (case (M.lookup i v) of Some p \<Rightarrow> p | None \<Rightarrow> 0)\<close>

definition \<open>pmf_invar v s \<longleftrightarrow> range_nonneg v \<and> range_sum_one v \<and> M.invar v \<and> S.invar s \<and> 
  (set (map fst (M.to_list v)) = set(S.to_list s))\<close>

lemma the_lookup_nonneg: \<open>pmf_invar v s \<Longrightarrow> M.\<alpha> v x = Some y \<Longrightarrow> y \<ge> 0\<close>
  unfolding pmf_invar_def range_nonneg_def
  by auto

lemma pmf_finite_supp: \<open>pmf_invar v s \<Longrightarrow> finite {i. pmf_lookup v i \<noteq> 0}\<close>
  unfolding pmf_invar_def pmf_lookup_def
  by (fastforce simp: set_map_to_list map_to_set_dom[symmetric] split: option.splits intro!: finite_subset[of _ \<open>S.\<alpha> s\<close>])

lemma 
  assumes \<open>pmf_invar v s\<close>
  shows pmf_lookup_nonneg: \<open>\<And>x. 0 \<le> pmf_lookup v x\<close> and 
    pmf_lookup_sum_one: \<open>\<integral>\<^sup>+ x. ennreal (pmf_lookup v x) \<partial>count_space UNIV = 1\<close>
proof -

  have [simp, intro]: \<open>M.invar v\<close>
    using assms 
    unfolding pmf_invar_def 
    by auto

  show \<open>0 \<le> pmf_lookup v x\<close> for x
    using assms the_lookup_nonneg[of v s]
      unfolding pmf_lookup_def pmf_invar_def
      by (force split: option.splits)
      
  have \<open>1 = (\<Sum>x\<in>map_to_set (M.\<alpha> v). snd x)\<close>
    using assms iterate_sum
    unfolding pmf_invar_def range_sum_one_def 
    by (auto simp:  case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>x\<in> map_to_set (M.\<alpha> v). the (M.\<alpha> v (fst x)))\<close>
    by (rule sum.cong) (auto simp: case_prod_unfold map_to_set_def cong: sum.cong)
  also have \<open>\<dots> = (\<Sum>x\<in> dom (M.\<alpha> v). the (M.\<alpha> v x))\<close>
    unfolding map_to_set_dom 
    by (subst sum.reindex) (auto simp: map_to_set_def intro!: inj_onI)
  also have \<open>\<dots> = (\<Sum>x\<in> dom (M.\<alpha> v). ennreal (the (M.\<alpha> v x)))\<close>
    using assms the_lookup_nonneg
    by (subst sum_ennreal) auto
  also have \<open>\<dots> = (\<Sum>x\<in> {i. pmf_lookup v i > 0}. ennreal (pmf_lookup v x))\<close>
    by (rule sum.mono_neutral_cong_right) (auto simp add: ennreal_eq_0_iff pmf_lookup_def split: option.splits)
  also have \<open>\<dots> = \<integral>\<^sup>+ x. ennreal (pmf_lookup v x) \<partial>count_space UNIV\<close>
    using assms pmf_finite_supp[of v s]
    by (subst nn_integral_count_space) 
     (auto intro: sum.cong finite_subset simp: rev_finite_subset Collect_mono  split: option.splits)
 finally show \<open>(\<integral>\<^sup>+ x. ennreal (pmf_lookup v x) \<partial>count_space UNIV) = 1\<close>
    by auto
qed

definition [code del]: \<open>pmf_\<alpha>_impl vs = (case vs of (v, s) \<Rightarrow> embed_pmf (pmf_lookup v))\<close>

definition [icf_rec_def]: \<open>pmf_ops = \<lparr>
  pmf_\<alpha> = pmf_\<alpha>_impl,
  pmf_op_prob_at = (\<lambda>(v, s). pmf_lookup v),
  pmf_op_supp = snd,
  pmf_op_invar = (\<lambda>(v, s). pmf_invar v s)\<rparr>\<close>

lemma fst_set_to_list[simp]: \<open>M.invar m \<Longrightarrow> fst ` set (M.to_list m) = dom (M.\<alpha> m)\<close>
  using M.correct(25)[of m] M.correct(26)[of m] weak_map_of_SomeI[of m] set_map_of_compr
  by fastforce

lemma pmf_invar_setD[dest]: "pmf_invar a b \<Longrightarrow> S.invar b"
  unfolding pmf_invar_def
  by auto

lemma embed_pmf_lookup[simp]: \<open>pmf_invar a b \<Longrightarrow> pmf (embed_pmf (pmf_lookup a)) = pmf_lookup a\<close>
  using pmf_lookup_nonneg pmf_lookup_sum_one
  by (auto simp: pmf_embed_pmf)

lemma set_pmf_lookup[simp]: \<open>pmf_invar a b \<Longrightarrow> set_pmf (embed_pmf (pmf_lookup a)) = {x. pmf_lookup a x \<noteq> 0}\<close>
  unfolding set_pmf_eq
  by auto

lemma pmf_lookup_correct[simp]: \<open>pmf_invar a b \<Longrightarrow> pmf_lookup a x = pmf (pmf_\<alpha>_impl (a, b)) x\<close>
  using pmf_lookup_nonneg pmf_lookup_sum_one
  unfolding pmf_lookup_def pmf_\<alpha>_impl_def
  by (auto split: option.splits simp: pmf_embed_pmf)

lemma pmf_lookup_nz_in_b: \<open>pmf_invar a b \<Longrightarrow> pmf_lookup a x \<noteq> 0 \<Longrightarrow> x \<in> S.\<alpha> b\<close>
  using embed_pmf_lookup
  unfolding pmf_invar_def pmf_lookup_def
  by (auto simp: M.correct(5) domIff)
  
lemma pmf_\<alpha>_nz_in_b: \<open>pmf_invar a b \<Longrightarrow> pmf (pmf_\<alpha>_impl (a, b)) x \<noteq> 0 \<Longrightarrow> x \<in> S.\<alpha> b\<close>
  using pmf_lookup_nz_in_b
  by auto

lemma set_pmf_\<alpha>_impl[simp]: \<open>pmf_invar a b \<Longrightarrow> set_pmf (pmf_\<alpha>_impl (a, b)) = {x \<in> S.\<alpha> b. pmf (pmf_\<alpha>_impl (a, b)) x \<noteq> 0}\<close>
  using pmf_\<alpha>_nz_in_b
  by (auto simp: set_pmf_eq)

sublocale PmfNat pmf_ops set_ops
  unfolding pmf_ops_def
  by unfold_locales auto
end
end