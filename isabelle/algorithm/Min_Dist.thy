theory Min_Dist
  imports "Util"
begin

chapter \<open>Existence of Vector with Minimum Error\<close>
text \<open>We prove that for a Matrix A and a vector c, there exists a vector x with minimum max-norm 
  distance between Ax and c.\<close>

section \<open>Util\<close>
lemma compact_aux:
  fixes f :: "nat \<Rightarrow> 'd \<Rightarrow>\<^sub>b 'b::euclidean_space"
  assumes \<open>bounded (range f)\<close> \<open>finite X\<close>
  shows \<open>\<forall>d\<subseteq>X. \<exists>l::'d \<Rightarrow>\<^sub>b 'b. \<exists> r. strict_mono r \<and> (\<forall>e>0. \<forall>\<^sub>F n in sequentially. \<forall>i\<in>d. dist (((f (r n))) i) (l i) < e)\<close>
proof -
  have *: \<open>bounded (range (\<lambda>i. if i \<in> X \<or> bounded (range f) then f i else 0))\<close> for f
    using \<open>finite X\<close> bounded_const
    by (cases \<open>bounded (range f)\<close>) auto
  show ?thesis
    using assms 
    by (intro compact_lemma_general[where unproj = "\<lambda>f. Bfun (\<lambda>i. if i \<in> X \<or> bounded (range f) then f i else 0)"])
      (auto simp: bounded_apply_bfun' apply_bfun_inverse Bfun_inverse[OF range_bfunI[OF *]])
qed

text \<open>Bounded and closed spaces (with finite basis) are compact.\<close>
lemma bdd_closed_compact: 
  assumes 
    \<open>bounded (X::('b \<Rightarrow>\<^sub>b real) set)\<close> 
    \<open>closed X\<close> 
    \<open>finite' D\<close> 
    \<open>\<And>v i. v \<in> X \<Longrightarrow> i \<notin> D \<Longrightarrow> v i = 0\<close>
  shows \<open>compact X\<close>
proof -
  {
    fix f :: "nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real"
    have \<open>finite D\<close>
      using assms by auto
    assume f_in_S: \<open>f i \<in> X\<close> for i
    hence f: "bounded (range f)"
      using assms
      by (simp add: Elementary_Metric_Spaces.bounded_subset image_subsetI)

    then obtain l::"'b \<Rightarrow>\<^sub>b real" and r where r: "strict_mono r"
      and l: "\<And>e. e > 0 \<Longrightarrow> eventually (\<lambda>n. \<forall>i\<in>D. dist (f (r n) i) (l i) < e) sequentially"
      using compact_aux [OF f \<open>finite D\<close>] by blast

    let ?l = \<open>bfun_if (\<lambda>i. i \<in> D) l 0\<close>

    have \<open>dist (f (r n) i) (?l i) = 0\<close> if \<open>i \<notin> D\<close> for i n
      using that assms f_in_S
      by (auto simp: bfun_if.rep_eq)

    hence dist_l_eq: \<open>dist (f (r n)) ?l = (\<Squnion>i \<in> D. dist (f (r n) i) (?l i))\<close> for n
      unfolding dist_bfun.rep_eq
      using assms
      by (fastforce intro!: antisym cSUP_mono simp: bounded_dist_comp bounded_imp_bdd_above)

    hence "eventually (\<lambda>n. dist (f (r n)) ?l < e) sequentially" if \<open>e > 0\<close> for e
      using assms that
      by (intro eventually_mono[OF l, of e]) (auto intro!: finite_imp_Sup_less simp: bfun_if.rep_eq)

    hence \<open>(\<lambda>n. (f (r n))) \<longlonglongrightarrow> ?l\<close>
      unfolding lim_sequentially eventually_sequentially
      by fastforce

    moreover then have \<open>?l \<in> X\<close>
      using assms f_in_S
      by (fastforce intro: closed_sequentially)

    ultimately have \<open>(\<exists>l\<in>X. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l)\<close>
      using r
      by (auto simp: comp_def)
  }
  thus ?thesis
    unfolding compact_def
    using assms by fastforce 
qed

text \<open>The space of vectors with the same norm is compact.\<close>
lemma norm_eq_compact: 
  assumes \<open>finite D\<close> \<open>D\<noteq> {}\<close>
  shows \<open>compact {x::'d \<Rightarrow>\<^sub>b real. norm x = b \<and> (\<forall>i\<in>-D. apply_bfun x i = 0)}\<close>
proof -
  {
    fix f :: "nat \<Rightarrow> 'd \<Rightarrow>\<^sub>b real"
    define S where \<open>S = {x::'d \<Rightarrow>\<^sub>b real. (norm x = b) \<and> (\<forall>i \<in> -D. apply_bfun x i = 0)}\<close>
    assume f_in_S: \<open>f i \<in> S\<close> for i
    hence f: "bounded (range f)"
      unfolding S_def bounded_iff
      by auto
    then obtain l::"'d \<Rightarrow>\<^sub>b real" and r where r: "strict_mono r"
      and l: "\<And>e. e>0 \<Longrightarrow> eventually (\<lambda>n. \<forall>i\<in>D. dist (f (r n) i) (l i) < e) sequentially"
      using compact_aux [OF f assms(1)] by blast

    let ?l = \<open>bfun_if (\<lambda>i. i \<in> D) l 0\<close>

    have \<open>dist (f (r n) i) (?l i) = 0\<close> if \<open>i \<notin> D\<close> for i n
      using that assms f_in_S
      by (simp add: S_def bfun_if.rep_eq)

    hence dist_l_eq: \<open>dist (f (r n)) ?l = (\<Squnion>i \<in> D. dist (f (r n) i) (?l i))\<close> for n
      unfolding dist_bfun.rep_eq
      using assms
      by (fastforce intro!: antisym cSUP_mono simp: bounded_dist_comp bounded_imp_bdd_above)

    hence "eventually (\<lambda>n. dist (f (r n)) ?l < e) sequentially" if \<open>e > 0\<close> for e
      using assms that
      by (intro eventually_mono[OF l, of e]) (auto intro!: finite_imp_Sup_less simp: bfun_if.rep_eq)

    hence lim: \<open>(\<lambda>n. (f (r n))) \<longlonglongrightarrow> ?l\<close>
      unfolding lim_sequentially eventually_sequentially
      by fastforce

    hence\<open>(\<lambda>n. norm (f (r n))) \<longlonglongrightarrow> norm (?l)\<close>
      by (intro tendsto_norm) auto
    hence\<open>norm ?l = b\<close>
      using LIMSEQ_unique S_def f_in_S by auto


    hence \<open>?l \<in> S\<close>
      using assms f_in_S lim S_def
      by (simp add: bfun_if.rep_eq)   

    hence \<open>(\<exists>l\<in>S. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l)\<close>
      using r lim
      by (auto simp: comp_def)
  }
  thus ?thesis
    unfolding compact_def
    by auto
qed

lemma finite_nz_range:
  assumes \<open>(finite {b. f b \<noteq> (0::_::real_normed_vector)})\<close>
  shows \<open>finite (range f)\<close>
proof -
  have \<open>range f \<subseteq> (insert 0 {f b | b. f b \<noteq> 0})\<close>
    by auto
  moreover have \<open>finite (insert 0 {f b | b. f b \<noteq> 0})\<close>
    using assms
    by auto
  ultimately show ?thesis
    using infinite_super by blast
qed

lemma finite_bounded: 
  assumes \<open>(finite {b. f b \<noteq> (0::_::real_normed_vector)})\<close>
  shows \<open>bounded (range f)\<close>
  using assms finite_nz_range
  by auto

lemma fin_nz_bdd: 
  assumes \<open>finite {x:: _ :: real_normed_vector. x \<in> X \<and> x \<noteq> 0}\<close> 
  shows \<open>bounded X\<close>
proof -
  have \<open>X \<subseteq> insert 0 {x. x \<in> X \<and> x \<noteq> 0}\<close>
    by auto

  moreover have \<open>bounded {x. x \<in> X \<and> x \<noteq> 0}\<close>
    using finite_imp_bounded[of \<open>{x \<in> X. x \<noteq> 0}\<close>] assms by auto

  ultimately show ?thesis
    using Elementary_Metric_Spaces.bounded_subset bounded_insert
    by metis
qed

subsection \<open>Existence of an Argmin\<close>
definition \<open>has_arg_min f X \<longleftrightarrow> (\<exists>x. is_arg_min f (\<lambda>x. x \<in> X) x)\<close>

lemma has_arg_minI[intro]: \<open>is_arg_min f (\<lambda>x. x \<in> X) x \<Longrightarrow> has_arg_min f X\<close>
  unfolding has_arg_min_def by auto


lemma compact_cont_has_arg_min:
  assumes \<open>compact X\<close> \<open>X \<noteq> {}\<close> \<open>continuous_on X f\<close>
  shows \<open>has_arg_min (f :: _ \<Rightarrow> real) X\<close>
  unfolding has_arg_min_def
  using assms continuous_attains_inf 
  by (fastforce simp: is_arg_min_linorder)

text \<open>Given a linear transformation A, a target c, we try to find a vector x with minimum distance 
  of Ax to c.\<close>
context
  fixes
    A :: \<open>('s \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('t \<Rightarrow>\<^sub>b real)\<close> and
    c :: \<open>'t \<Rightarrow>\<^sub>b real\<close> and
    dims :: \<open>'s set\<close> and
    outs :: \<open>'t set\<close>
  assumes \<open>finite' dims\<close>
    and \<open>finite' outs\<close>
    and 
    A_indep: \<open>\<And>x x'. (\<forall>i \<in> dims. (x :: 's \<Rightarrow>\<^sub>b real) i = (x' :: 's \<Rightarrow>\<^sub>b real) i) \<Longrightarrow> A x = A x'\<close> and
    A_outs: \<open>\<And>i x. i \<notin> outs \<Longrightarrow> A x i = 0\<close>  and
    c_outs: \<open>\<And>i x. i \<notin> outs \<Longrightarrow> c i = 0\<close>
begin

lemmas is_arg_min_linorder[simp]

definition \<open>valid_vecs_on X = {v :: _ \<Rightarrow>\<^sub>b real. \<forall>i \<in> -X. v i = 0}\<close>

definition \<open>A_range = A ` valid_vecs_on dims\<close>

definition \<open>is_opt v \<longleftrightarrow> is_arg_min (\<lambda>v. dist (A v) c) (\<lambda>v. v \<in> valid_vecs_on dims) v\<close>

text \<open>We only need to consider vectors with an error less than @{term \<open>norm c\<close>}.\<close>
definition \<open>v_cands = {v \<in> valid_vecs_on dims. dist (A v) c \<le> norm c}\<close>

definition \<open>A_cands = {v \<in> A_range. dist v c \<le> norm c}\<close>

lemma zero_v_cands: \<open>0 \<in> v_cands\<close>
  unfolding v_cands_def valid_vecs_on_def by simp

lemma v_cands_ne[simp, intro]: \<open>v_cands \<noteq> {}\<close>
  using zero_v_cands by auto

lemma zero_valid: \<open>0 \<in> valid_vecs_on X\<close>
  unfolding valid_vecs_on_def by auto

lemma zero_A_range: \<open>0 \<in> A_range\<close>
  unfolding A_range_def
  using zero_valid image_iff by fastforce

lemma zero_A_cands: \<open>0 \<in> A_cands\<close>
  using zero_A_range A_cands_def by auto

lemma A_cands_ne[simp, intro]: \<open>A_cands \<noteq> {}\<close>
  using zero_A_cands by auto

lemma cont_A[intro, simp]: \<open>continuous_on X (\<lambda>x. A x)\<close>
  by (rule blinfun.continuous_on) auto

lemma cont_dist_A[intro, simp]: \<open>continuous_on X (\<lambda>x. dist (A x) c)\<close>
  by (rule continuous_on_dist) auto

lemma A_min_imp_v_min:
  assumes \<open>has_arg_min (\<lambda>v. dist v c) A_cands\<close>
  shows \<open>has_arg_min (\<lambda>v. dist (A v) c) v_cands\<close>
  using assms
  unfolding has_arg_min_def is_arg_min_linorder
  unfolding A_cands_def v_cands_def A_range_def
  by auto

text \<open>The proof will show that the set of candidates is compact, from which the result follows.\<close>
lemma A_compact_imp_A_min:
  assumes \<open>compact A_cands\<close>
  shows \<open>has_arg_min (\<lambda>v. dist v c) A_cands\<close>
  using assms
  by (auto intro!: compact_cont_has_arg_min continuous_on_dist)

lemma v_cands_subs_valids: \<open>v_cands \<subseteq> valid_vecs_on dims\<close>
  unfolding v_cands_def by auto

lemma compact_imp_has_arg_min:
  assumes \<open>compact A_cands\<close>
  shows \<open>has_arg_min (\<lambda>v. dist (A v) c) (valid_vecs_on dims)\<close>
  using A_min_imp_v_min[OF A_compact_imp_A_min[OF assms]]
  unfolding has_arg_min_def is_opt_def v_cands_def
  by fastforce

section \<open>Compactness of @{const A_cands}\<close>
  \<comment> \<open>A trivial set that spans A's range\<close>
definition \<open>(A_space_dom :: ('t \<Rightarrow>\<^sub>b real) set) = {bfun_if (\<lambda>i. i = n) 1 0 |n. n \<in> outs}\<close>

lemma finite_A_space_dom: \<open>finite A_space_dom\<close>
  unfolding A_space_dom_def
  using \<open>finite' outs\<close>
  by auto

lemma A_space_span_works:
  \<open>A x \<in> span A_space_dom\<close>
proof -
  have x_eq_sum: \<open>A x = (\<Sum>i \<in> outs. A x i *\<^sub>R bfun_if (\<lambda>j. j = i) 1 0)\<close>
    using A_outs \<open>finite' outs\<close>
    by (auto simp: sum_apply_bfun' bfun_if.rep_eq if_distrib cong: if_cong)
  also have \<open>\<dots> = (\<Sum>a\<in>A_space_dom. (A x (THE i. apply_bfun a i \<noteq> 0)) *\<^sub>R a)\<close>
    unfolding A_space_dom_def setcompr_eq_image
    by (subst sum.reindex) (auto simp: inj_on_def bfun_if.rep_eq split: if_splits)
  finally show ?thesis
    using finite_A_space_dom
    unfolding span_explicit
    by auto
qed

lemma A_range_subs_span_A_space_dom: \<open>A_range \<subseteq> span A_space_dom\<close>
  using A_space_span_works
  unfolding span_explicit A_range_def
  by blast

lemma Ax_eq: \<open>A x = A (bfun_if (\<lambda>i. i \<in> dims) x 0)\<close>
  by (simp add: A_indep bfun_if.rep_eq)

lemma if_in_valids: \<open>(bfun_if (\<lambda>i. i \<in> X) x 0) \<in> valid_vecs_on X\<close>
  unfolding valid_vecs_on_def by (auto simp: bfun_if.rep_eq)

lemma A_range_eq_range: \<open>A_range = range A\<close>
  using Ax_eq if_in_valids
  unfolding A_range_def
  by auto

definition \<open>basis = (SOME b.
  independent b \<and> 
  finite b \<and>
  A_range \<subseteq> span b \<and>  
  card b = dim (A_range) \<and> (\<forall>b' \<in> b. norm b' = 1))\<close>

lemma basis_ex: \<open>(\<exists>b. 
  independent b \<and>
  A_range \<subseteq> span b \<and> 
  span b \<subseteq> span A_space_dom \<and>
  card b = dim A_range)\<close>
  using basis_exists[of A_range]
  using A_range_subs_span_A_space_dom  maximal_independent_subset
  using span_mono span_subspace subspace_span
  by (metis (no_types, lifting))

lemma finite_basis_ex: \<open>(\<exists>b. 
  independent b \<and> 
  finite b \<and>
  A_range \<subseteq> span b \<and> 
  card b = dim A_range)\<close>
proof -
  obtain b where \<open>independent b \<and> A_range \<subseteq> span b \<and> span b \<subseteq> span A_space_dom \<and> card b = dim A_range\<close>
    using basis_ex by auto

  moreover then have \<open>finite b\<close>
    using finite_A_space_dom independent_span_bound span_superset
    by blast

  ultimately show ?thesis
    by auto
qed

lemma basis_ex': \<open>(\<exists>b. 
  independent b \<and>
  finite b \<and>
  A_range \<subseteq> span b \<and>
  card b = dim A_range \<and> (\<forall>b' \<in> b. norm b' \<noteq> 0))\<close>
  using finite_basis_ex dependent_zero
  using A_range_subs_span_A_space_dom  maximal_independent_subset
  using span_mono span_subspace subspace_span
  using basis_ex dependent_zero by auto

lemma indep_scaleR_eq_imp_eq:
  assumes \<open>independent b\<close> \<open>x \<in> b\<close> \<open>y \<in> b\<close> \<open>c1 *\<^sub>R x = c2 *\<^sub>R y\<close> \<open>c1 \<noteq> 0 \<or> c2 \<noteq> 0\<close>
  shows \<open>x = y\<close>
proof -
  {
    assume \<open>x \<noteq> y\<close>
    let ?u = \<open>(undefined(x := c1, y := -c2))\<close>
    have \<open>(\<Sum>v \<in> {x, y}. ?u v *\<^sub>R v) = 0\<close>
      using assms \<open>x \<noteq> y\<close> by auto
    hence \<open>?u x = 0\<close> \<open>?u y = 0\<close>
      using independentD[of b \<open>{x, y}\<close> ?u] assms by force+
    hence \<open>c1 = 0\<close> \<open>c2 = 0\<close>
      using \<open>x \<noteq> y\<close> by auto
    hence False
      using assms(5) by blast
  }
  thus ?thesis by auto
qed

lemma unit_basis_ex: \<open>(\<exists>b. 
  independent b \<and>
  finite b \<and>
  A_range \<subseteq> span b \<and>
  card b = dim A_range \<and> (\<forall>b' \<in> b. norm b' = 1))\<close>
proof -
  obtain b where b: \<open>independent b \<and>
  finite b \<and>
  A_range \<subseteq> span b \<and>
  card b = dim A_range \<and> (\<forall>b' \<in> b. norm b' \<noteq> 0)\<close>
    using basis_ex' by auto

  define b' where \<open>b' = (\<lambda>v. (1 / (norm v)) *\<^sub>R v) ` b\<close>

  have inj_norm_div: \<open>inj_on (\<lambda>v. (1 / norm v) *\<^sub>R v) b\<close>
    unfolding inj_on_def
    by (metis b indep_scaleR_eq_imp_eq zero_eq_1_divide_iff)

  have \<open>card b' = card b\<close>
    using b inj_norm_div
    unfolding b'_def
    by (subst card_image) auto

  moreover have \<open>finite b'\<close>
    using b
    unfolding b'_def
    by auto

  moreover have \<open>independent b'\<close>
  proof (rule independent_if_scalars_zero)
    show \<open>f x = 0\<close> if \<open>(\<Sum>x\<in>b'. f x *\<^sub>R x) = 0\<close> \<open>x \<in> b'\<close> for f x
      using independentD[of b b \<open>\<lambda>x. (f ((1 / norm x) *\<^sub>R x) / norm x)\<close>] b that
      unfolding b'_def
      by (auto simp: sum.reindex inj_norm_div image_iff)
  qed (simp add: \<open>finite b'\<close>)

  moreover have \<open>span b = span b'\<close>
    using b 
    unfolding b'_def
    by (auto intro!: span_image_scale[symmetric])
  moreover have \<open>\<forall>v \<in> b'. norm v = 1\<close>
    unfolding b'_def using b by auto

  ultimately show ?thesis
    using b
    by auto
qed

lemma indep_span_basis[intro, simp]: 
  \<open>independent basis\<close> 
  \<open>finite basis\<close> 
  \<open>A_range \<subseteq> span basis\<close> 
  \<open>card basis = dim (A_range)\<close> 
  \<open>(\<forall>b'\<in>basis. norm b' = 1)\<close>
  unfolding basis_def
  using someI_ex[OF unit_basis_ex]
  by auto

lemma cands_subs_span[intro, simp]: \<open>A_cands \<subseteq> span basis\<close>
  unfolding A_cands_def
  using indep_span_basis
  by blast

text \<open>Evaluate weights given to a set of basis vectors.\<close>
definition T_eval :: "(('t \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>b real) \<Rightarrow> ('t \<Rightarrow>\<^sub>b real)" where
  \<open>T_eval l = (\<Sum>b \<in> basis. l b *\<^sub>R b)\<close>

text \<open>Inverse function: vector to basis weights.\<close>
lift_definition repr :: \<open>('t \<Rightarrow>\<^sub>b real) \<Rightarrow> (('t \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>b real)\<close> is \<open>representation basis\<close>
  using finite_representation
  by (auto intro!: finite_bounded)

lemma T_works: 
  assumes \<open>v \<in> A_range\<close> 
  shows \<open>T_eval (repr v) = v\<close>
  unfolding T_eval_def repr.rep_eq
  using assms indep_span_basis
  by (subst sum_representation_eq) blast+

lemma A_candsD[dest]: 
  assumes \<open>v \<in>A_cands\<close> 
  shows \<open>v \<in> A_range\<close>
  using assms
  unfolding A_cands_def
  by auto

lemma continuous_on_apply_bfun[continuous_intros]: \<open>continuous_on X (\<lambda>x. apply_bfun x b)\<close>
  using dist_bfun_bounded less_le_not_le continuous_onI
  by metis

lemma T_cont: \<open>continuous_on X T_eval\<close>
  unfolding T_eval_def
  by (auto intro!: continuous_intros)

text \<open>All possible weights that have an error of less than @{term \<open>norm c\<close>}.\<close>
definition \<open>M = {l. T_eval l \<in> A_cands \<and> (\<forall>i\<in>-basis. l i = 0)}\<close>

lemma T_unique:
  fixes l :: \<open>(('t \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>b real)\<close>
  shows \<open>(\<forall>i\<in>- basis. l i = 0) \<Longrightarrow> T_eval l = 0 \<Longrightarrow> l = 0\<close>
  unfolding T_eval_def
  using independentD[of basis basis l]
  by fastforce

lemma basis_empty_imp_M_empty: \<open>basis = {} \<Longrightarrow> M = {0}\<close>
  unfolding M_def T_eval_def
  using zero_A_cands
  by auto

lemma A_cands_eq_T_M: \<open>A_cands = T_eval ` M\<close>
proof -
  have \<open>v \<in> A_cands \<Longrightarrow> v \<in> T_eval ` M\<close> for v
    unfolding M_def 
    using A_candsD representation_ne_zero
    by (fastforce simp: repr.rep_eq T_works image_iff  intro!: exI[of _ \<open>repr v\<close>])
  thus ?thesis
    unfolding M_def
    by auto
qed

text \<open>The problem can be reduced to the compactness of @{term M}.\<close>
lemma compact_M_suffices: 
  assumes \<open>compact M\<close>
  shows \<open>compact A_cands\<close>
  unfolding A_cands_eq_T_M
  using T_cont compact_continuous_image assms 
  by blast

lemma closed_bounded_compact_M:
  assumes \<open>closed M\<close> \<open>bounded M\<close>
  shows \<open>compact M\<close>
proof (cases \<open>basis = {}\<close>)
  case True
  then show ?thesis 
    by (auto simp: basis_empty_imp_M_empty)
next
  case False
  then show ?thesis 
    using M_def assms indep_span_basis
    by (auto intro: bdd_closed_compact[of _ basis])
qed

(* adapted from HOL-Analysis.Linear_Algebra *)
text \<open>Next, we show that subspaces are closed, then that @{term A_range} is actually a subspace.
  Since the space of vectors with a given norm is also closed, this completes the proof.\<close>
context 
  fixes X :: \<open>'c set\<close>
  assumes \<open>finite' X\<close>
begin

definition \<open>bfun_inner x y = (\<Sum>i \<in> X. apply_bfun x i * apply_bfun y i)\<close>

definition \<open>fin_indep d \<longleftrightarrow> (independent d \<and> finite d \<and> (\<forall>v \<in> d. \<forall>x \<in> -X. apply_bfun v x = 0))\<close>

lemma indep_nz: \<open>independent d \<Longrightarrow> v \<in> d \<Longrightarrow> v \<noteq> 0\<close>
  using dependent_zero by blast

lemma fin_indep_nz: \<open>fin_indep b \<Longrightarrow> v \<in> b \<Longrightarrow> (\<exists>i \<in> X. v i \<noteq> 0)\<close>
  unfolding fin_indep_def
  by (metis Compl_iff bfun_eqI dependent_zero zero_bfun.rep_eq)

lemma sq_sum_zeroD: \<open>(\<Sum>x \<in> X. f x * (f x) ::real) = 0 \<Longrightarrow> finite X \<Longrightarrow> x \<in> X \<Longrightarrow> f x = 0\<close>
  using sum_nonneg_0[of X \<open>\<lambda>x. f x * f x\<close> x]
  by auto

definition \<open>B = (\<lambda>j. bfun_if (\<lambda>i. i = j) (1:: _ \<Rightarrow>\<^sub>b real) 0) ` X\<close>

lemma fin_B: \<open>finite B\<close>
  by (simp add: B_def \<open>finite' X\<close>)

lemma indep_B: \<open>independent B\<close>
proof (rule independent_if_scalars_zero[OF fin_B])
  fix f x
  assume \<open>(\<Sum>x\<in>B. f x *\<^sub>R x) = 0\<close>
  hence \<open>\<And>i. (\<Sum>x\<in>B. f x *\<^sub>R x) i = 0\<close>
    by auto

  hence \<open>\<And>i. (\<Sum>x\<in>B. f x *\<^sub>R x i) = 0\<close>
    by (auto simp: sum_apply_bfun')

  hence 1: \<open>(if i \<in> X then f (bfun_if (\<lambda>j. j = i) 1 0) else 0) = 0\<close> for i
    unfolding B_def
    using \<open>finite' X\<close>
    by (subst (asm) sum.reindex) 
      (auto simp: inj_on_def bfun_if.rep_eq if_distrib split: if_splits cong: if_cong)

  have \<open>i \<in> X \<Longrightarrow> f (bfun_if (\<lambda>j. j = i) 1 0) = 0\<close> for i
    using 1[of i] by (auto split: if_splits)

  thus \<open>x \<in> local.B \<Longrightarrow> f x = 0\<close>
    using B_def by auto
qed

lemma inner_B:
  assumes \<open>u \<in> B\<close> \<open>v \<in> B\<close> 
  shows \<open>bfun_inner u (v :: _ \<Rightarrow>\<^sub>b real) = (if u = v then 1 else 0)\<close>
  using assms \<open>finite' X\<close> fin_indep_nz unfolding fin_indep_def bfun_inner_def
  by (auto dest!: sq_sum_zeroD simp: sum.neutral bfun_if.rep_eq B_def if_distrib cong: if_cong)

lemma B_euclidean_representation: 
  assumes \<open>x \<in> valid_vecs_on X\<close> 
  shows \<open>(\<Sum>b\<in>B. bfun_inner x b *\<^sub>R b) = x\<close>
proof -
  have \<open>(\<Sum>b\<in>B. bfun_inner x b *\<^sub>R b) = (\<Sum>j\<in>X. x j *\<^sub>R bfun_if (\<lambda>i. i = j) 1 0)\<close>
    unfolding B_def
    using \<open>finite' X\<close>
    by (subst sum.reindex) 
      (auto simp: if_distrib bfun_inner_def inj_on_def bfun_if.rep_eq split: if_splits cong: if_cong)
  also have \<open>\<dots> = x\<close>
    using \<open>finite' X\<close> assms
    unfolding valid_vecs_on_def
    by (auto simp: sum_apply_bfun' bfun_if.rep_eq if_distrib  cong: if_cong)
  finally show ?thesis.
qed

lemma B_valid: \<open>B \<subseteq> valid_vecs_on X\<close>
  unfolding B_def valid_vecs_on_def by (auto simp: bfun_if.rep_eq)

lemma B_dim_substandard:
  assumes d: "d \<subseteq> B"
  shows "dim {x\<in>valid_vecs_on X. \<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0} = card d" (is "dim ?A = _")
proof (rule dim_unique)
  from d show "d \<subseteq> ?A"
    using inner_B  B_valid by auto
  from d show "independent d"
    by (rule independent_mono [OF indep_B])
  have "x \<in> span d" if \<open>x \<in> valid_vecs_on X\<close> "\<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0" for x
  proof -
    have "finite d"
      by (rule finite_subset [OF d fin_B])
    then have "(\<Sum>i\<in>d. (bfun_inner x i) *\<^sub>R i) \<in> span d"
      by (simp add: span_sum span_clauses)
    also have "(\<Sum>i\<in>d. bfun_inner x i *\<^sub>R i) = (\<Sum>i\<in>B. bfun_inner x i *\<^sub>R i)"
      by (rule sum.mono_neutral_cong_left [OF fin_B d]) (auto simp: that)
    finally show "x \<in> span d"
      by (simp only: B_euclidean_representation[OF that(1)])
  qed
  then show "?A \<subseteq> span d"
    by auto
qed simp

lemma bfun_inner_add_left: \<open>bfun_inner (((x :: _ \<Rightarrow>\<^sub>b real) + y)) z = bfun_inner x z + bfun_inner y z\<close>
  unfolding bfun_inner_def
  using \<open>finite' dims\<close>
  by (simp add: algebra_simps sum.distrib)

lemma B_subspace_substandard: \<open>subspace {x \<in> valid_vecs_on X. \<forall>i\<in>B. P i \<longrightarrow> bfun_inner x i = 0}\<close>
  unfolding subspace_def valid_vecs_on_def bfun_inner_def
  using \<open>finite' X\<close>
  by (auto simp: sum.distrib sum_distrib_left[symmetric] algebra_simps)

lemma bfun_eq_iff: \<open>x = y \<longleftrightarrow> (\<forall>i. apply_bfun x i = apply_bfun y i)\<close>
  by auto

lemma span_B_full: "valid_vecs_on X = span B"
proof -
  have \<open>x \<in> span B\<close> if x: \<open>x \<in> valid_vecs_on X\<close> for x
  proof -
    have *: \<open>x = (\<Sum>i \<in> X. x i *\<^sub>R (bfun_if (\<lambda>j. j = i) 1 0))\<close>
      using \<open>finite' X\<close> x
      unfolding span_explicit valid_vecs_on_def
      by (auto simp: if_distrib sum_apply_bfun' bfun_if.rep_eq split: if_splits cong: if_cong)
    also have \<open>\<dots> = (\<Sum>b \<in> B. x (THE i. apply_bfun b i \<noteq> 0) *\<^sub>R b)\<close>
      unfolding B_def
      by (subst sum.reindex) (auto simp: if_distrib bfun_inner_def inj_on_def bfun_if.rep_eq split: if_splits cong: if_cong)

    finally show \<open>x \<in> span B\<close>
      unfolding span_explicit
      using fin_B by auto
  qed
  moreover have \<open>x \<in> valid_vecs_on X\<close> if \<open>x \<in> span B\<close> for x
  proof -
    obtain t r where x_eq: \<open>x = (\<Sum>i \<in> t. r i *\<^sub>R i)\<close> \<open>finite t\<close> \<open>t \<subseteq> B\<close>
      using \<open>x \<in> span B\<close>
      unfolding span_explicit B_def valid_vecs_on_def
      by auto

    moreover have \<open>b i = 0\<close> if \<open>b \<in> t\<close> \<open>i \<notin> X\<close> for b i
      using that \<open>t \<subseteq> B\<close>
      unfolding B_def by (auto simp: subset_iff image_iff bfun_if.rep_eq)

    ultimately have \<open>x i = 0\<close> if \<open>i \<notin> X\<close> for i
      unfolding x_eq
      by (simp add: sum_apply_bfun' that)

    thus ?thesis
      by (auto simp: valid_vecs_on_def)
  qed
  ultimately show ?thesis 
    by auto
qed

lemma cardB_eq_dim_vecs:\<open>card B = dim (valid_vecs_on X)\<close>
  by (simp add: dim_eq_card_independent indep_B span_B_full)

lemma valid_vecs_subs_has_basis:
  assumes \<open>S \<subseteq> valid_vecs_on X\<close>
  obtains B where "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" and "finite B"
  using assms basis_exists[of S]  independent_span_bound[OF fin_B] span_B_full 
  by force

lemma B_subspace_isomorphism:
  assumes s: "subspace (S :: (_ \<Rightarrow>\<^sub>b real) set)" and s_v: \<open>S \<subseteq> valid_vecs_on X\<close>
    and t: "subspace S'" and s_v': \<open>S' \<subseteq> valid_vecs_on X\<close>
    and d: "dim S = dim S'"
  shows "\<exists>f. linear f \<and> f ` S = S' \<and> inj_on f S"
proof -
  from basis_exists[of S] finiteI_independent
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S" and fB: "finite B"
    by (metis s_v valid_vecs_subs_has_basis)

  from basis_exists[of S'] finiteI_independent
  obtain C where C: "C \<subseteq> S'" "independent C" "S' \<subseteq> span C" "card C = dim S'" and fC: "finite C"
    by (metis s_v' valid_vecs_subs_has_basis)
  from B(4) C(4) card_le_inj[of B C] d
  obtain f where f: "f ` B \<subseteq> C" "inj_on f B" using \<open>finite B\<close> \<open>finite C\<close>
    by auto
  from linear_independent_extend[OF B(2)]
  obtain g where g: "linear g" "\<forall>x\<in> B. g x = f x" by auto
  interpret g: linear g by fact
  from inj_on_iff_eq_card[OF fB, of f] f(2) have "card (f ` B) = card B"
    by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C"
    using d by simp
  have "g ` B = f ` B"
    using g(2) by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B"
    using f(2) g(2) by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  {
    fix x y
    assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> span B" and y': "y \<in> span B"
      by blast+
    from gxy have th0: "g (x - y) = 0"
      by (simp add: linear_diff g)
    have th1: "x - y \<in> span B"
      using x' y' by (metis span_diff)
    have "x = y"
      using g0[OF th1 th0] by simp
  }
  then have giS: "inj_on g S"
    unfolding inj_on_def by blast
  from span_subspace[OF B(1,3) s] have "g ` S = span (g ` B)"
    by (simp add: g.span_image span_raw_def)
  also have "\<dots> = span C" unfolding gBC ..
  also have "\<dots> = S'" using span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = S'" .
  from g(1) gS giS show ?thesis
    by auto
qed


lemma B_le_norm: \<open>b \<in> B \<Longrightarrow> \<bar>bfun_inner x b\<bar> \<le> card X * norm x\<close>
  using sum_norm_bound[of X \<open>\<lambda>i.  apply_bfun x i * apply_bfun b i\<close> \<open>norm x\<close>]
  unfolding bfun_inner_def B_def
  by (auto simp add: abs_le_norm_bfun bfun_if.rep_eq)

lemma linear_bound:
  fixes f :: "(_ \<Rightarrow>\<^sub>b real) \<Rightarrow> (_ \<Rightarrow>\<^sub>b real)"
  assumes lf: "linear f"
  shows \<open>\<forall>x \<in> valid_vecs_on X. norm (f x) \<le> real (card X) * (\<Sum>b\<in>local.B. norm (f b)) * norm x\<close>
proof -
  interpret linear f by fact
  let ?B = "card X * (\<Sum>b\<in>B. norm (f b))"
  show "\<forall>x \<in> valid_vecs_on X. norm (f x) \<le> ?B * norm x"
  proof
    fix x
    assume x: \<open>x \<in> valid_vecs_on X\<close>

    let ?g = "\<lambda>b. bfun_inner x b *\<^sub>R f b"
    have "norm (f x) = norm (f (\<Sum>b\<in>B. bfun_inner x b *\<^sub>R b))"
      using B_euclidean_representation x by auto 
    also have "\<dots> = norm (sum ?g B)"
      by (simp add: sum scale)
    finally have th0: "norm (f x) = norm (sum ?g B)" .
    have th: "norm (?g i) \<le> norm (f i) * real (card X) * norm x" if "i \<in> B" for i
    proof -
      show "norm (?g i) \<le> norm (f i) * real (card X) * norm x"
        unfolding norm_scaleR 
        using order.trans[OF mult_right_mono[OF B_le_norm[OF that, of x]]]
        by auto
    qed
    from sum_norm_le[of _ ?g, OF th]
    show "norm (f x) \<le> ?B * norm x"
      unfolding th0 sum_distrib_right
      by (simp add: mult_of_nat_commute sum_distrib_right)
  qed
qed

lemma linear_bounded:
  fixes f :: "(_ \<Rightarrow>\<^sub>b real) \<Rightarrow> (_ \<Rightarrow>\<^sub>b real)"
  assumes lf: "linear f"
  shows "\<exists>B. \<forall>x \<in> valid_vecs_on X. norm (f x) \<le> B * norm x"
  using assms linear_bound by auto

lemma valid_vecs_ne: \<open>valid_vecs_on X \<noteq> {}\<close>
  unfolding ex_in_conv[symmetric]
  by (auto simp: valid_vecs_on_def bfun_if.rep_eq intro: exI[of _ \<open>bfun_if (\<lambda>i. i \<in> X) 1 0\<close>])

lemma linear_bound':
  fixes f :: "(_ \<Rightarrow>\<^sub>b real) \<Rightarrow> (_ \<Rightarrow>\<^sub>b real)"
  assumes lf: "linear f" and \<open>\<forall>x \<in> -valid_vecs_on X. f x = f (bfun_if (\<lambda>i. i \<in> X) x 0) \<close>
  shows "\<forall>x. norm (f x) \<le> norm x * max (real (card X) * (\<Sum>b\<in>local.B. norm (f b))) 0"
proof -
  define B where \<open>B = real (card X) * (\<Sum>b\<in>local.B. norm (f b))\<close>
  have b: \<open>norm (f x) \<le> B * norm x\<close> if \<open>x \<in> valid_vecs_on X\<close> for x
    using lf local.linear_bound that unfolding B_def by blast

  hence b_max: \<open>norm (f x) \<le> max B 0 * norm x\<close> if \<open>x \<in> valid_vecs_on X\<close> for x
    using that
    by (auto simp add: mult_right_mono intro: order.trans[OF b])

  have *: \<open>norm (bfun_if (\<lambda>i. i \<in> X) x 0) \<le> norm x\<close> for x
    unfolding norm_bfun_def dist_bfun.rep_eq
    by (auto intro!: cSUP_mono simp add: bfun_if.rep_eq bfun_bounded_norm_range bounded_imp_bdd_above)

  have \<open>(bfun_if (\<lambda>i. i \<in> X) (x) 0) \<in> valid_vecs_on X\<close> for x
    by (auto simp: valid_vecs_on_def bfun_if.rep_eq)

  hence \<open>norm (f x) \<le> max B 0 * norm (bfun_if (\<lambda>i. i \<in> X) x 0)\<close> if \<open>x \<in> - valid_vecs_on X\<close> for x
    using assms b_max that
    by auto

  hence \<open>norm (f x) \<le> max B 0 * norm x\<close> if \<open>x \<in> - valid_vecs_on X\<close> for x
    using assms * b_max that
    by (fastforce intro: order.trans mult_left_mono)

  hence \<open>\<forall>x. norm (f x) \<le> (max B 0) * norm x\<close>
    using assms b_max by blast

  thus ?thesis
    unfolding B_def
    by (metis mult.commute)
qed


lemma linear_bounded':
  fixes f :: "(_ \<Rightarrow>\<^sub>b real) \<Rightarrow> (_ \<Rightarrow>\<^sub>b real)"
  assumes lf: "linear f" and \<open>\<forall>x \<in> -valid_vecs_on X. f x = f (bfun_if (\<lambda>i. i \<in> X) x 0) \<close>
  shows "\<exists>B. \<forall>x. norm (f x) \<le> norm x * B"
  using assms linear_bound' by auto

lemma tendsto_const_apply_bfun: \<open>f \<longlonglongrightarrow> l \<Longrightarrow> (\<And>n. apply_bfun (f n) i = y) \<Longrightarrow> l i = y\<close>
  unfolding tendsto_iff eventually_sequentially
  by (metis dist_bounded dist_nz dual_order.strict_iff_not order_refl)

lemma closed_valids: \<open>closed (valid_vecs_on X)\<close>
  unfolding closed_sequential_limits
proof safe
  fix x l
  assume *: \<open>\<forall>n. x n \<in> valid_vecs_on X\<close> \<open>x \<longlonglongrightarrow> l\<close> 

  hence \<open>(\<lambda>n. x n i) \<longlonglongrightarrow> l i\<close> for i
    using bfun_tendsto_apply_bfun
    by fast

  moreover have \<open>x n i = 0\<close> if \<open>i \<notin> X\<close> for i n
    using * that
    by (auto simp: valid_vecs_on_def)

  moreover then have \<open>l i = 0\<close> if \<open>i \<notin> X\<close> for i n
    using tendsto_const_apply_bfun * that by metis

  ultimately show \<open>l \<in> valid_vecs_on X\<close>
    unfolding valid_vecs_on_def
    by auto
qed

lemma collect_int: \<open>{x \<in> X. P x} = X \<inter> {x. P x}\<close>
  by auto

lemma continuous_on_bfun_inner[continuous_intros]:
  shows "continuous_on s (\<lambda>x. bfun_inner (x :: _ \<Rightarrow>\<^sub>b real) i)"
  unfolding bfun_inner_def
  by (fastforce intro: continuous_intros)

lemma B_closed_substandard: "closed {x \<in> valid_vecs_on X. \<forall>i\<in>B. P i \<longrightarrow> bfun_inner x i = 0}"
  (is "closed ?A")
proof -
  let ?D = "{i\<in>B. P i}"

  have "closed ((\<Inter>i\<in>?D. {x. x \<in> valid_vecs_on X \<and> bfun_inner x i = 0}) \<inter> valid_vecs_on X)"
    unfolding collect_int
    using continuous_closed_preimage_constant closed_valids continuous_on_bfun_inner
    by (blast intro!: closed_INT closed_Int closed_Collect_eq)

  also have "(\<Inter>i\<in>?D. {x \<in> valid_vecs_on X. bfun_inner x i = 0}) \<inter> valid_vecs_on X = ?A"
    by (cases \<open>?D = {}\<close>) auto

  finally show "closed ?A" .
qed

proposition injective_imp_isometric:
  fixes f :: "(_ \<Rightarrow>\<^sub>b real) \<Rightarrow> (_ \<Rightarrow>\<^sub>b real)"
  assumes s: "closed s" "subspace s" \<open>s \<subseteq> valid_vecs_on X\<close>
    and f: "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0"
  shows "\<exists>e>0. \<forall>x\<in>s. norm (f x) \<ge> e * norm x"
proof (cases "s \<subseteq> {0}")
  case True

  have "norm x \<le> norm (f x)" if "x \<in> s" for x
  proof -
    from True that have "x = 0" by auto
    then show ?thesis by simp
  qed

  then show ?thesis
    by (auto intro!: exI[where x=1])
next
  case False
  interpret f: bounded_linear f by fact
  from False obtain a where a: "a \<noteq> 0" "a \<in> s"
    by auto
  from False have "s \<noteq> {}"
    by auto
  let ?S = "{f x| x. x \<in> s \<and> norm x = norm a}"
  let ?S' = "{x :: _ \<Rightarrow>\<^sub>b real. x\<in>s \<and> norm x = norm a}"
  let ?S'' = "{x::_ \<Rightarrow>\<^sub>b real. norm x = norm a \<and> x \<in> valid_vecs_on X }"

  have "compact ?S''"
    using norm_eq_compact[of X \<open>norm a\<close>] \<open>finite' X\<close> 
    unfolding valid_vecs_on_def
    by auto

  moreover have "?S' = s \<inter> ?S''" 
    using s(3) by fastforce
  ultimately have "compact ?S'"
    using closed_Int_compact[of s ?S''] using s(1) by auto
  moreover have *:"f ` ?S' = ?S" by auto
  ultimately have compact_S: "compact ?S"
    using compact_continuous_image[OF linear_continuous_on[OF f(1)], of ?S'] by auto
  then have cl_S: "closed ?S"
    using compact_imp_closed by auto
  moreover from a have S_ne: "?S \<noteq> {}" by auto

  have \<open>\<exists>b' \<in> ?S. \<forall>y \<in> ?S. norm b' \<le> norm y\<close>
    using continuous_on_norm_id
    by (intro continuous_attains_inf[OF compact_S S_ne]) blast
  then obtain b' where "b'\<in>?S" "\<forall>y\<in>?S. norm b' \<le> norm y"
    by auto
  then obtain b where "b\<in>s"
    and ba: "norm b = norm a"
    and b: "\<forall>x\<in>{x \<in> s. norm x = norm a}. norm (f b) \<le> norm (f x)"
    unfolding *[symmetric] unfolding image_iff by auto

  let ?e = "norm (f b) / norm b"
  have "norm b > 0"
    using ba and a and norm_ge_zero by auto
  moreover have "norm (f b) > 0"
    using f(2)[THEN bspec[where x=b], OF \<open>b\<in>s\<close>] \<open>norm b >0\<close> 
    by simp
  ultimately have "0 < norm (f b) / norm b" by simp
  moreover have "norm (f b) / norm b * norm x \<le> norm (f x)" if "x\<in>s" for x
  proof (cases "x = 0")
    case True
    then show "norm (f b) / norm b * norm x \<le> norm (f x)"
      by auto
  next
    case False
    with \<open>a \<noteq> 0\<close> have *: "0 < norm a / norm x"
      unfolding zero_less_norm_iff[symmetric] by simp
    have "\<forall>x\<in>s. c *\<^sub>R x \<in> s" for c
      using s[unfolded subspace_def] by simp
    with \<open>x \<in> s\<close> \<open>x \<noteq> 0\<close> have "(norm a / norm x) *\<^sub>R x \<in> {x \<in> s. norm x = norm a}"
      by simp
    with \<open>x \<noteq> 0\<close> \<open>a \<noteq> 0\<close> show "norm (f b) / norm b * norm x \<le> norm (f x)"
      using b[THEN bspec[where x="(norm a / norm x) *\<^sub>R x"]]
      unfolding f.scaleR and ba
      by (auto simp: mult.commute pos_le_divide_eq pos_divide_le_eq)
  qed
  ultimately show ?thesis by auto
qed


proposition closed_injective_image_subspace:
  fixes f :: "(_ \<Rightarrow>\<^sub>b real) \<Rightarrow> (_ \<Rightarrow>\<^sub>b real)"
  assumes "subspace s" \<open>s \<subseteq> valid_vecs_on X\<close>"bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0" "closed s"
  shows "closed(f ` s)"
proof -
  obtain e where e: "e > 0" "\<forall>x\<in>s. e * norm x \<le> norm (f x)"
    using assms injective_imp_isometric by metis

  show ?thesis
    using e complete_isometric_image assms complete_eq_closed
    by metis
qed

lemma fin_closed_subspace:
  fixes s :: "(_ \<Rightarrow>\<^sub>b real) set"
  assumes "subspace s" \<open>s \<subseteq> valid_vecs_on X\<close>
  shows "closed s"
proof -
  have "dim s \<le> card B"
    using dim_subset_UNIV assms dim_le_card 
    using fin_B span_B_full by auto
  with ex_card[OF this] obtain d :: "_ set" where t: "card d = dim s" and d: "d \<subseteq> B"
    by auto
  let ?t = "{x::_ \<in> valid_vecs_on X. \<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0}"
  have "\<exists>f. linear f \<and> f ` ?t = s \<and> inj_on f ?t"
    using B_dim_substandard[of d] t d assms
    by (intro B_subspace_isomorphism[OF B_subspace_substandard[of "\<lambda>i. i \<notin> d"]]) auto
  then obtain f' where f':
    "linear f'"
    "f' ` {x \<in> valid_vecs_on X . \<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0} = s"
    "inj_on f' {x \<in> valid_vecs_on X . \<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0}"
    by auto
  moreover have *: \<open>f' (bfun_if (\<lambda>i. i \<in> X) (x) 0) = f' x\<close> if \<open>x \<in> valid_vecs_on X\<close> for x
    using that
    by (auto simp: bfun_if.rep_eq valid_vecs_on_def intro!: arg_cong[of _ _ f'])

  let ?f = \<open>\<lambda>x. f' (bfun_if (\<lambda>i. i \<in> X) x 0)\<close>
  have \<open>linear ?f\<close>
    using f'   
    by (auto intro: linearI simp: bfun_if.rep_eq linear_cmul linear_add
        bfun_if_scaleR[of _ _ _ 0, simplified, symmetric] bfun_if_add[of _ _ _ 0  0, simplified])

  moreover have \<open>?f ` ?t = s\<close>
    by (simp add: "*" f')


  ultimately have "\<exists>f. linear f \<and> f ` ?t = s \<and> inj_on f ?t \<and> (\<forall>x \<in> - valid_vecs_on X. f x = f (bfun_if (\<lambda>i. i \<in> X) x 0))"
    by (intro exI[of _ \<open>\<lambda>x. f' (bfun_if (\<lambda>i. i \<in> X) (x) 0)\<close>]) (simp add: "*" inj_on_def if_in_valids)

  then obtain f where f:
    "linear f"
    "f ` {x \<in> valid_vecs_on X . \<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0} = s"
    "inj_on f {x \<in> valid_vecs_on X . \<forall>i\<in>B. i \<notin> d \<longrightarrow> bfun_inner x i = 0}"
    "(\<forall>x \<in> - valid_vecs_on X. f x = f (bfun_if (\<lambda>i. i \<in> X) x 0))"
    by auto

  interpret f: bounded_linear f
    using f
    by (auto intro!: bounded_linear.intro linear_bounded' simp: bounded_linear_axioms_def)

  have "x \<in> ?t \<Longrightarrow> f x = 0 \<Longrightarrow> x = 0" for x
    using f.zero d f(3)[THEN inj_onD, of x 0]
    using B_subspace_substandard subspace_0 by auto 
  moreover have "closed ?t" by (rule B_closed_substandard)
  moreover have "subspace ?t" by (rule B_subspace_substandard)
  ultimately show ?thesis
    using closed_injective_image_subspace[of ?t f]
    unfolding f(2) using f(1) unfolding linear_conv_bounded_linear 
    using f.bounded_linear_axioms by fastforce
qed
end

lemma subspace_A_range: \<open>subspace A_range\<close>
  using zero_A_range  
  unfolding A_range_eq_range
  by (auto intro!: subspaceI blinfun.add_right blinfun.scaleR_right rangeI 
      simp: blinfun.add_right[symmetric] blinfun.scaleR_right[symmetric])

lemma closed_A_range: \<open>closed A_range\<close>
  using A_outs \<open>finite' outs\<close> subspace_A_range
  by (auto simp:  A_range_def valid_vecs_on_def intro: fin_closed_subspace[of \<open>outs\<close>])

lemma dist_le_compact: 
  assumes \<open>finite' X\<close> \<open>\<And>i. i \<in> -X \<Longrightarrow> apply_bfun y i = 0\<close>
  shows \<open>compact {x::'d \<Rightarrow>\<^sub>b real. dist x y \<le> b \<and> (\<forall>i \<in> -X. apply_bfun x i = 0)}\<close>
proof -
  {
    fix f :: "nat \<Rightarrow> 'd \<Rightarrow>\<^sub>b real"
    define S where \<open>S = {x::'d \<Rightarrow>\<^sub>b real. dist x y \<le> b \<and> (\<forall>i \<in> -X. apply_bfun x i = 0)}\<close>
    assume f_in_S: \<open>f i \<in> S\<close> for i
    hence f: "bounded (range f)"
      unfolding S_def
      by (metis (no_types, lifting) bounded_any_center bounded_iff dist_commute mem_Collect_eq rangeE)
    then obtain l::"'d \<Rightarrow>\<^sub>b real" and r where r: "strict_mono r"
      and l: "\<And>e. e > 0 \<Longrightarrow> eventually (\<lambda>n. \<forall>i\<in>X. dist (f (r n) i) (l i) < e) sequentially"
      using compact_aux [OF f ] \<open>finite' X\<close> by blast
    let ?l = \<open>bfun_if (\<lambda>i. i \<in> X) l 0\<close>

    have \<open>dist (f (r n) i) (?l i) = 0\<close> if \<open>i \<notin> X\<close> for i n
      using that assms f_in_S
      by (simp add: S_def bfun_if.rep_eq)

    hence dist_l_eq: \<open>dist (f (r n)) ?l = (\<Squnion>i \<in> X. dist (f (r n) i) (?l i))\<close> for n
      unfolding dist_bfun.rep_eq
      using assms
      by (fastforce intro!: antisym cSUP_mono simp: bounded_dist_comp bounded_imp_bdd_above)

    hence "eventually (\<lambda>n. dist (f (r n)) ?l < e) sequentially" if \<open>e > 0\<close> for e
      using assms that
      by (intro eventually_mono[OF l, of e]) (auto intro!: finite_imp_Sup_less simp: bfun_if.rep_eq)

    hence lim: \<open>(\<lambda>n. (f (r n))) \<longlonglongrightarrow> ?l\<close>
      unfolding lim_sequentially eventually_sequentially
      by fastforce

    have lim': \<open>(\<lambda>n. dist (f (r n)) y) \<longlonglongrightarrow> dist ?l y\<close>
      by (rule continuous_on_tendsto_compose[OF _ lim, of UNIV \<open>\<lambda>x. dist x y\<close>]) (auto intro: continuous_intros)

    hence\<open>dist ?l y \<le> b\<close>
      using LIMSEQ_unique  f_in_S S_def
      by (simp add: Lim_bounded dist_commute)

    hence \<open>?l \<in> S\<close>
      using assms f_in_S lim S_def
      by (simp add: bfun_if.rep_eq)   

    hence \<open>(\<exists>l\<in>S. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l)\<close>
      using r lim
      by (auto simp: comp_def)
  }
  thus ?thesis
    unfolding compact_def
    by auto
qed

lemma A_cands_eq: \<open>A_cands = A_range \<inter> {v \<in> valid_vecs_on outs. dist v c \<le> norm c} \<close>
  unfolding A_range_def A_cands_def valid_vecs_on_def
  using A_outs 
  by auto

lemma closed_A_cands: \<open>closed A_cands\<close>
  unfolding A_cands_eq
  using closed_A_range dist_le_compact[of outs c] \<open>finite' outs\<close> c_outs
  by (auto simp: valid_vecs_on_def Collect_conj_eq compact_imp_closed inf_commute)

lemma closed_M:
  shows \<open>closed M\<close>
proof -
  {
    fix f l
    assume \<open>\<And>n. f n \<in> M\<close> \<open>f \<longlonglongrightarrow> l\<close>

    hence \<open>(\<lambda>n. T_eval (f n)) \<longlonglongrightarrow> T_eval l\<close>
      using T_cont[unfolded continuous_on_sequentially, of UNIV]
      by (auto simp: comp_def)

    moreover have \<open>T_eval (f n) \<in> A_cands\<close> for n
      using M_def \<open>\<And>n. f n \<in> M\<close> by blast

    ultimately have \<open>T_eval l \<in> A_cands\<close>
      using closed_A_cands
      by (meson closed_sequentially)

    have 1:  \<open>f n i = 0\<close> if \<open>i \<notin> basis\<close> for n i
      using M_def \<open>\<And>n. f n \<in> local.M\<close> that by fastforce

    have \<open>(\<lambda>n. f n i) \<longlonglongrightarrow> l i\<close> for i
      by (simp add: \<open>f \<longlonglongrightarrow> l\<close> bfun_tendsto_apply_bfun)
    moreover have \<open>l i = 0\<close> if \<open>i \<notin> basis\<close> for i
      using 1[of i] that LIMSEQ_unique[OF \<open>(\<lambda>n. f n i) \<longlonglongrightarrow> l i\<close>, of 0]
      by auto

    ultimately have \<open>l \<in> M\<close> 
      unfolding M_def
      using \<open>T_eval l \<in> A_cands\<close> by force
  }
  thus ?thesis
    using closed_sequential_limits by blast
qed

definition \<open>l1 = {l:: ('t \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>b real. norm l = 1 \<and> (\<forall>i\<in>- basis. apply_bfun l i = 0)}\<close>

lemma basis_l1_empty: \<open>basis = {} \<Longrightarrow> l1 = {}\<close>
  using T_eval_def T_unique l1_def 
  by fastforce

lemma bfun_if_in_l1: \<open>j \<in> basis \<Longrightarrow> bfun_if (\<lambda>i. i = j) 1 0 \<in> l1\<close>
  unfolding l1_def 
  by (auto simp: bfun_if.rep_eq  norm_bfun_def dist_bfun_def intro!: antisym cSup_least cSup_upper2)

lemma basis_l1_empty_iff: \<open>l1 = {} \<longleftrightarrow> basis = {}\<close>
  using basis_l1_empty bfun_if_in_l1 by auto

lemma compact_l1: \<open>compact l1\<close>
proof (cases \<open>basis = {}\<close>)
  case True
  then show ?thesis 
    using basis_l1_empty compact_empty by auto
next
  case False
  then show ?thesis
    using norm_eq_compact l1_def by auto
qed

lemma T_norm_cont[intro]: \<open>continuous_on X (\<lambda>l. norm (T_eval l))\<close>
  by (auto intro!: continuous_on_norm T_cont)

lemma has_min_T_l1: \<open>basis \<noteq> {} \<Longrightarrow> has_arg_min (\<lambda>l. norm (T_eval l)) l1\<close>
  using T_norm_cont compact_l1 basis_l1_empty_iff 
  by (fastforce intro: compact_cont_has_arg_min)

lemma A_bdd: \<open>bounded A_cands\<close>
  unfolding A_cands_def bounded_def
  by (fastforce simp: dist_commute)

lemma F_bound: \<open>f \<in> A_cands \<Longrightarrow> norm f \<le> 2 * norm c\<close>
  unfolding A_cands_def
  using norm_triangle_ineq[of \<open>f - c\<close> c]
  by (auto simp: dist_norm)

lemma M_ne: \<open>M \<noteq> {}\<close>
  using A_cands_eq_T_M zero_A_cands 
  by fastforce

lemma bdd_M: \<open>bounded M\<close>
proof (cases \<open>basis \<noteq> {}\<close>)
  case True

  obtain l where *: \<open>is_arg_min (\<lambda>l. norm (T_eval l)) (\<lambda>l. l \<in> l1) l\<close>
    by (metis True has_arg_min_def has_min_T_l1)

  define \<alpha> where \<open>\<alpha> = norm (T_eval l)\<close>

  have \<open>\<alpha> = 0 \<Longrightarrow> (\<exists>l \<in> l1. T_eval l = 0)\<close>
    by (metis "*" \<alpha>_def is_arg_min_linorder norm_eq_zero)

  hence \<open>\<alpha> = 0 \<Longrightarrow> (\<exists>l \<in> l1. l = 0)\<close>
    using T_unique l1_def by blast

  hence \<open>\<alpha> \<noteq> 0\<close>
    by (auto simp: l1_def)

  hence \<alpha>_gt: \<open>\<alpha> > 0\<close>
    using *
    unfolding is_arg_min_linorder
    by (simp add: \<alpha>_def)

  moreover have \<alpha>_le: \<open>\<forall>l \<in> l1. \<alpha> \<le> norm (T_eval l)\<close>
    by (metis "*" \<alpha>_def is_arg_min_linorder)

  hence \<open>norm (T_eval l) \<ge> \<alpha> * norm l\<close> if \<open>l \<noteq> 0\<close> \<open>\<And>i. i \<notin> basis \<Longrightarrow> apply_bfun l i = 0\<close> for l
  proof -
    have *: \<open>norm x * norm r = norm (norm r *\<^sub>R x)\<close> for x r
      by auto 
    have \<open>((1 / norm l) *\<^sub>R l) \<in> {l. (\<forall>i\<in>- basis. apply_bfun l i = 0)}\<close>
      using that  by auto
    hence \<open>\<alpha> * norm l \<le> norm (T_eval ((1 / norm l) *\<^sub>R l)) * norm l\<close>
      using that \<alpha>_gt \<alpha>_le
      by (simp add: l1_def)
    also have \<open>\<dots> = norm (T_eval (l))\<close>
      using that
      unfolding T_eval_def * scale_sum_right
      by auto
    finally show ?thesis .
  qed

  hence \<alpha>_le_norm: \<open>norm (T_eval l) \<ge> \<alpha> * norm l\<close> if \<open>l \<noteq> 0\<close> \<open>l \<in> M\<close> for l
    using M_def that by force

  define B where \<open>B = 2 * norm c\<close>

  have B: \<open>norm (T_eval l) \<le> B\<close> if \<open>l \<in> M\<close> for l
    using F_bound that
    unfolding B_def A_cands_eq_T_M
    by auto

  hence \<open>B \<ge> 0\<close>
    by (meson M_ne ex_in_conv norm_ge_zero order_trans)
  hence \<open>norm l \<le> B / \<alpha>\<close> if \<open>l \<in> M\<close> for l
    using that \<alpha>_gt \<alpha>_le_norm B
    by (cases \<open>l = 0\<close>) (fastforce simp: algebra_simps le_divide_eq)+
  thus \<open>bounded M\<close>
    by (meson bounded_iff imageI)
qed (auto dest: basis_empty_imp_M_empty)

lemma compact_F: \<open>compact A_cands\<close>
  using bdd_M closed_M closed_bounded_compact_M compact_M_suffices 
  by blast

text \<open>Finally we can show that a vector with minimal distance exists, since @{term F} is compact.\<close>
lemma A_dist_c_has_arg_min:
  shows \<open>has_arg_min (\<lambda>v. dist (A v) c) (valid_vecs_on dims)\<close>
  using compact_imp_has_arg_min A_cands_def compact_F
  by auto

lemma A_dist_c_has_arg_min_UNIV:
  shows \<open>has_arg_min (\<lambda>v. dist (A v) c) UNIV\<close>
proof -
  from A_dist_c_has_arg_min
  obtain v where \<open>v \<in> valid_vecs_on dims\<close> \<open>\<forall>v' \<in> valid_vecs_on dims. dist (A v) c \<le> dist (A v') c\<close>
    unfolding has_arg_min_def 
    by auto

  hence \<open>dist (A v) c \<le> dist (A v') c\<close> for v'
    using if_in_valids Ax_eq[of v']
    by auto

  thus ?thesis
    unfolding has_arg_min_def 
    by fastforce
qed

end
end
