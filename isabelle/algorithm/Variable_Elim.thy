theory Variable_Elim
  imports Complex_Main Util
begin

section \<open>Variable Elimination\<close>
subsection \<open>Util\<close>

lemma upd_in_dom_same: "l \<in> dom v \<Longrightarrow> v(l \<mapsto> the (v l)) = v"
  by auto

lemma has_scope_on_MAX:
  assumes \<open>\<And>y. y \<in> Y \<Longrightarrow> has_scope_on (f y) D R\<close> \<open>finite' Y\<close>
  shows\<open>has_scope_on (\<lambda>x. MAX y\<in>Y. f y x) D R\<close>
  using assms
  by (auto intro!: has_scope_onI Max_cong dest!: has_scope_on_eq)

lemma has_scope_on_updI:
  assumes \<open>has_scope_on f {(x(i \<mapsto> y)) | x. x \<in> D} (insert i R)\<close>
  shows \<open>has_scope_on (\<lambda>x. f (x(i \<mapsto> y))) D R\<close>
  using assms
  by (auto intro!: has_scope_onI dest: has_scope_on_eq)

lemma sum_list_add: \<open>sum_list xs + sum_list ys = sum_list (xs @ ys)\<close>
  by simp

lemma bij_betw_imp_eq: \<open>bij_betw f D R \<Longrightarrow> f x = f y \<Longrightarrow> x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> x = y\<close>
  by (metis bij_betw_inv_into_left)

lemma Sigma_compr: \<open>X \<times> Y = {(x, y) | x y. x \<in> X \<and> y \<in> Y}\<close>
  by auto

lemma sum_list_compl: \<open>(sum_list (map f (filter P xs)) :: _ :: {comm_monoid_add,linorder, linordered_ab_semigroup_add}) + sum_list (map f (filter (\<lambda>x. \<not>P x) xs)) = sum_list (map f xs)\<close>
  unfolding sum_list_add
  unfolding  sum_mset_sum_list[symmetric]
  by (metis map_append mset_append mset_filter mset_map multiset_partition)

lemma bij_betw_imp_Max_eq: \<open>bij_betw f X Y \<Longrightarrow> finite' X \<Longrightarrow> finite' Y \<Longrightarrow> Max (g ` f ` X) = Max (g ` Y)\<close>
  unfolding bij_betw_def by blast

lemma bij_betw_imp_Max_eq': \<open>f ` X = Y \<Longrightarrow> finite' X \<Longrightarrow> finite' Y \<Longrightarrow> Max (g ` f ` X) = Max (g ` Y)\<close>
  using arg_cong .

lemma Max_cong': \<open>X = Y \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f x = g x) \<Longrightarrow> Max (f ` X) = Max (g ` Y)\<close>
  by auto

lemma sum_list_add_ereal: 
  assumes \<open>\<And>x. x \<in> set xs \<Longrightarrow> f x \<noteq> (\<infinity> :: ereal)\<close> \<open>\<And>x. x \<in> set xs \<Longrightarrow> g x \<noteq> \<infinity>\<close> 
  shows \<open>sum_list (map f xs) + sum_list (map g xs) = sum_list (map (\<lambda>x. f x + g x) xs)\<close>
  using assms
  by (induction xs) (auto simp: algebra_simps)

lemma Max_inftyD: \<open>Max X = \<infinity> \<Longrightarrow> finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x \<in> X. x = (\<infinity> :: ereal)\<close>
  by (auto simp: Max_eq_iff)

lemma sum_list_inftyD: \<open>\<infinity> = sum_list xs \<Longrightarrow> \<exists>x \<in> set xs. x = (\<infinity> :: ereal)\<close>
  by (induction xs) auto

subsection \<open>Algorithm Definition\<close>

text \<open>
  We use a locale to define a Variable elimination algorithm.
  Inputs to the algorithm are a list of functions @{term \<F>} with scopes.
  The algorithm will maximize the sum of these functions over all possible vectors of length 
  @{term dims} with entries in @{term doms}.\<close>
locale Variable_Elimination_Consts =
  fixes
    \<F> :: \<open>(((nat \<rightharpoonup> 'a) \<Rightarrow> ereal) \<times> nat set) list\<close> and \<comment> \<open>Functions to be maximized with scopes\<close>
    dims :: \<open>nat\<close> and \<comment> \<open>Number of variables\<close>
    \<O> :: \<open>nat \<Rightarrow> nat\<close> and \<comment> \<open>Elimination order\<close>
    doms :: \<open>nat \<Rightarrow> 'a set\<close> \<comment> \<open>Domains of the dimensions\<close>
begin

text \<open>We define the notions of partial vectors, vectors with a set domain and vectors with full domain.\<close>
definition \<open>partial_vecs = {x. \<forall>(i, j) \<in> Map.graph x. i \<in> {..<dims} \<and> j \<in> doms i}\<close>
definition \<open>vecs_on D = {x. dom x = D} \<inter> partial_vecs\<close>
definition \<open>full_vecs = vecs_on {..<dims}\<close>

abbreviation \<open>scope \<equiv> snd\<close>
abbreviation \<open>fn \<equiv> fst\<close>

text \<open>The body of the algorithm, in a single iteration, we first select the variable to eliminate as
  @{term \<open>\<O> i\<close>}, then partition the work set of functions @{term F} based on whether @{term \<open>\<O> i\<close>}
  is in their scope.
  Next we build a new function that maximizes all functions that contain \<open>@{term \<open>\<O> i\<close>}\<close> over this
  variable, and add it to the working set.\<close>
definition \<open>elim_step iF = (
  let
    (i, F) = iF;
    l = \<O> i;
    E = filter (\<lambda>f. l \<in> scope f) F;
    e = (\<lambda>x. MAX x\<^sub>l \<in> doms l. \<Sum>f \<leftarrow> E. (fn f (x(l \<mapsto> x\<^sub>l))));
    scope_e = (\<Union>f\<in>set E. scope f) - {l}
  in
    (i + 1, (e, scope_e) # filter (\<lambda>f. l \<notin> scope f) F)
  )\<close>

text \<open>The body of the algorithms needs to be iterated @{term dims} times.\<close>
definition \<open>elim_aux = (elim_step ^^ dims) (0, \<F>)\<close>

text \<open>Finally, we are left with only functions with empty scopes, and we return their sum.\<close>
definition \<open>elim_max = (\<Sum>(f, f_scope) \<leftarrow> snd elim_aux. f Map.empty)\<close>

text \<open>@{term expl_max} is the inefficient variant of the algorithm that enumerates all states.\<close>
definition \<open>expl_max_\<F> \<F>' = (MAX x \<in> full_vecs. \<Sum>f \<leftarrow> \<F>'. fst f x)\<close>

definition \<open>expl_max = expl_max_\<F> \<F>\<close>

text \<open>The invariant @{term invar_max} can be used to show the algorithm @{term elim_max} correct.\<close>
definition \<open>invar_max \<F>' i \<longleftrightarrow>
  (\<forall>f \<in> set \<F>'. \<forall>x. fst f x \<noteq> \<infinity>) \<and>
  (\<forall>f \<in> set \<F>'. has_scope_on (fst f) partial_vecs (snd f)) \<and>
  (\<forall>f \<in> set \<F>'. snd f \<subseteq> {..<dims} - \<O> ` {..<i}) \<and>
  (MAX x\<in>vecs_on ({..<dims} - \<O> ` {..<i}). \<Sum>f\<leftarrow>\<F>'. fst f x) = expl_max_\<F> \<F>\<close>

end

locale Variable_Elimination = Variable_Elimination_Consts \<F> dims \<O> doms
  for
    \<F> :: \<open>(((nat \<rightharpoonup> 'a) \<Rightarrow> ereal) \<times> nat set) list\<close> and \<comment> \<open>Functions to be maximized with scopes\<close>
    dims :: \<open>nat\<close> and \<comment> \<open>Number of variables\<close>
    \<O> :: \<open>nat \<Rightarrow> nat\<close> and \<comment> \<open>Elimination order\<close>
    doms :: \<open>nat \<Rightarrow> 'a set\<close> \<comment> \<open>Domains of the dimensions\<close> +
  assumes 
    \<O>_bij: \<open>bij_betw \<O> {..<dims} {..<dims}\<close> and
    \<F>_scopes: \<open>\<forall>(f, s) \<in> set \<F>. s \<subseteq> {..<dims} \<and>
    has_scope_on f {x. \<forall>(i, j) \<in> Map.graph x. i \<in> {..<dims} \<and> j \<in> doms i} s\<close> and
    domains_ne: \<open>\<And>i. i < dims \<Longrightarrow> doms i \<noteq> {}\<close> and
    domains_fin: \<open>\<And>i. i < dims \<Longrightarrow> finite (doms i)\<close> and
    \<F>_not_inf: \<open>\<And>f x. f \<in> set \<F> \<Longrightarrow> (fst f) x \<noteq> \<infinity>\<close>
begin

subsection \<open>Properties of (Partial) Vectors\<close>

lemma vecs_on_empty[simp]: \<open>vecs_on {} = {Map.empty}\<close>
  unfolding vecs_on_def partial_vecs_def
  by auto

lemma finite_partial_vecs: \<open>finite partial_vecs\<close>
  unfolding partial_vecs_def
  by (rule finite_subset[OF _ finite_set_of_finite_maps'[of \<open>{..<dims}\<close> \<open>\<Union>i < dims. doms i\<close>]])
    (fastforce simp: Map.graph_def domains_fin domains_ne elim!: ranE)+

lemma finite_vecs_on[intro]: 
  \<open>X \<subseteq> {..<dims} \<Longrightarrow> finite (vecs_on X)\<close>
  using finite_partial_vecs
  unfolding partial_vecs_def vecs_on_def
  by auto

lemma finite_full_vecs:
  \<open>finite full_vecs\<close>
  unfolding full_vecs_def vecs_on_def 
  using finite_partial_vecs 
  by auto

lemma vecs_on_ne: 
  assumes \<open>X \<subseteq> {..<dims}\<close> shows \<open>vecs_on X \<noteq> {}\<close>
proof -
  have \<open>(\<lambda>i. if i \<in> X then Some (SOME x. x \<in> doms i) else None) \<in> vecs_on X\<close>
    unfolding full_vecs_def vecs_on_def partial_vecs_def
    using some_in_eq domains_ne assms
    by (fastforce simp: Map.graph_def split: if_splits)
  thus ?thesis by auto
qed

lemma full_vecs_ne: \<open>full_vecs \<noteq> {}\<close>
  using vecs_on_ne full_vecs_def 
  by auto

lemma partial_vecs_updI:
  assumes \<open>x \<in> partial_vecs\<close> \<open>i < dims\<close> \<open>y \<in> doms i\<close>
  shows \<open>x(i \<mapsto> y) \<in> partial_vecs\<close>
  using assms 
  unfolding partial_vecs_def Map.graph_def 
  by auto

lemma partial_vecs_if:
  assumes \<open>v \<in> partial_vecs\<close> \<open>i < dims\<close> \<open>y \<in> doms i\<close>
  shows \<open>(\<lambda>a. if a = i then Some y else v a) \<in> partial_vecs\<close> 
  using assms 
  unfolding partial_vecs_def Map.graph_def
  by auto

lemma vecs_on_imp_partial:
  assumes \<open>v \<in> vecs_on X\<close> \<open>X \<subseteq> {..<dims}\<close>
  shows \<open>v \<in> partial_vecs\<close> 
  using assms 
  unfolding partial_vecs_def vecs_on_def 
  by auto

lemma vecs_on_insert:
  assumes \<open>X \<subseteq> {..<dims}\<close> \<open>i < dims\<close> \<open>Y = insert i X\<close> \<open>i \<notin> X\<close>
  shows \<open>vecs_on Y = (\<lambda>(v, y). (v(i \<mapsto> y))) ` (vecs_on X \<times> doms i)\<close>
proof safe
  fix x assume \<open>x \<in> vecs_on Y\<close>
  hence 1: \<open>the (x i) \<in> doms i\<close> 
    using assms
    by (cases \<open>x i\<close>) (auto simp: vecs_on_def partial_vecs_def Map.graph_def)
  have 2: \<open>x = x(i \<mapsto> the (x i))\<close>
    using assms \<open>x \<in> vecs_on Y\<close>
    by (cases \<open>x i\<close>) (auto simp: vecs_on_def partial_vecs_def Map.graph_def)

  show \<open>x \<in> (\<lambda>(v, y). v(i \<mapsto> y)) ` (vecs_on X \<times> doms i)\<close>
    unfolding image_iff  case_prod_unfold
    using assms \<open>x \<in> vecs_on Y\<close> 1 2
    by (intro bexI[of _ \<open>(x(i:= None), the (x i))\<close>])
      (auto simp: vecs_on_def  partial_vecs_def Map.graph_def)
next  
  fix x y assume \<open>x \<in> vecs_on X\<close> \<open>y \<in> doms i\<close>
  thus \<open>x(i \<mapsto> y) \<in> vecs_on Y\<close>
    using assms
    unfolding vecs_on_def partial_vecs_def Map.graph_def
    by auto
qed

subsection \<open>Algorithm Correctness\<close>
lemma invar_has_scope_on:
  assumes \<open>invar_max \<F>' i\<close> \<open>(f, s) \<in> set \<F>'\<close>
  shows \<open>has_scope_on f partial_vecs s\<close>
  using assms unfolding invar_max_def
  by auto

lemma invar_scope:
  assumes \<open>invar_max \<F>' i\<close> \<open>(f, s) \<in> set \<F>'\<close>
  shows \<open>s \<subseteq> {..<dims} - \<O> ` {..<i}\<close>
  using assms unfolding invar_max_def
  by fastforce

text \<open>Maximum sum of all functions is preserved.\<close>
lemma expl_max_\<F>_step:
  assumes \<open>i < dims\<close> \<open>invar_max F i\<close>
  shows \<open>(MAX x\<in>vecs_on ({..<dims} - \<O> ` {..<Suc i}). \<Sum>f\<leftarrow>snd (elim_step (i, F)). fst f x) = expl_max_\<F> \<F>\<close>
proof -
  define l where \<open>l = \<O> i\<close>
  have \<open>l < dims\<close>
    using l_def \<O>_bij assms bij_betwE by fastforce
  hence fin_l: \<open>finite' (doms l)\<close>
    using domains_ne domains_fin by auto

  have upd_eq_F: \<open>(a, b) \<in> set F \<Longrightarrow> a v = a (v(l \<mapsto> y))\<close> if \<open>l \<notin> b\<close> \<open>v \<in> partial_vecs\<close> \<open>y \<in> doms l\<close> for  v y a b
    using assms that \<open>l < dims\<close>
    by (auto intro!: has_scope_on_eq[OF invar_has_scope_on[OF assms(2)], of  _ _ _ \<open>_(_ \<mapsto> _)\<close>]  partial_vecs_updI)

  have diff_eq: \<open>{..<dims} - \<O> ` {..<i} = insert l ({..<dims} - \<O> ` {..<Suc i})\<close>
    unfolding l_def
    using less_Suc_eq \<open>l < dims\<close> l_def assms  
    by (fastforce dest: bij_betw_imp_eq[OF \<O>_bij])+

  let ?vs = \<open>vecs_on ({..<dims} - \<O> ` {..<Suc i})\<close>

  have F_not_inv: \<open>fst f x \<noteq> \<infinity>\<close> if \<open>f \<in> set F\<close> for f x
    using that fin_l \<F>_not_inf assms(2) invar_max_def
    by auto

  have \<open>(MAX x\<in>?vs. \<Sum>f\<leftarrow>snd (elim_step (i, F)). fst f x) =
    (MAX x\<in>?vs. (MAX x\<^sub>l \<in> doms l. \<Sum>f \<leftarrow> filter (\<lambda>f. l \<in> scope f) F. (fn f (x(l \<mapsto> x\<^sub>l)))) + (\<Sum>f \<leftarrow> filter (\<lambda>f. l \<notin> scope f) F. fn f x))\<close>
    unfolding elim_step_def by (auto simp: Let_def l_def)
  also have \<open>\<dots> = (MAX x\<in>?vs. (MAX x\<^sub>l \<in> doms l. (\<Sum>f \<leftarrow> F. (fn f (x(l \<mapsto> x\<^sub>l))))))\<close>
    using fin_l vecs_on_ne finite_vecs_on F_not_inv upd_eq_F vecs_on_imp_partial
    by (auto simp: Max_add_commute_ereal[symmetric] sum_list_map_filter' sum_list_add_ereal intro!: sum_list_map_cong Max_cong)
  also have \<open>\<dots> =  (MAX (x, x\<^sub>l)\<in>(?vs \<times> doms l) . (\<Sum>f \<leftarrow> F. (fn f (x(l \<mapsto> x\<^sub>l)))))\<close>
    using finite_vecs_on vecs_on_ne fin_l
    by (subst Max_Max) (auto simp: Sigma_compr image_Collect simp del: Collect_case_prod)
  also have \<open>\<dots> =  (MAX x\<in>((\<lambda>(x, x\<^sub>l). (x(l \<mapsto> x\<^sub>l)))) ` (?vs \<times> doms l) . (\<Sum>f \<leftarrow> F. (fn f (x))))\<close>
    by (simp add: image_image case_prod_unfold)
  also have \<open>\<dots> =  (MAX x\<in>vecs_on ({..<dims} - \<O> ` {..<i}). (\<Sum>f \<leftarrow> F. (fn f x)))\<close>
    using diff_eq assms l_def \<open>l < dims\<close> fin_l finite_vecs_on vecs_on_ne
    by (intro bij_betw_imp_Max_eq' vecs_on_insert[symmetric]) auto
  also have \<open>\<dots> = expl_max_\<F> \<F>\<close>
    using assms(2) invar_max_def 
    by blast
  finally show ?thesis .
qed

text \<open>Preservation of the invariant.\<close>
lemma invar_max_Suc:
  assumes \<open>invar_max F i\<close> \<open>i < dims\<close>
  shows \<open>invar_max (snd (elim_step (i, F))) (Suc i)\<close>
proof -
  {
    fix f t
    assume h: \<open>(f, t) \<in> set (snd (elim_step (i, F)))\<close>
    hence \<open>t \<subseteq> {..<dims} - \<O> ` {..< i}\<close>  \<open>\<O> i \<notin> t\<close>
      using assms
      unfolding invar_max_def elim_step_def
      by (fastforce simp: Let_def)+
    hence \<open>t \<subseteq> {..<dims} - \<O> ` {..< Suc i}\<close>
      using assms less_Suc_eq
      by auto
  }

  have \<open>\<O> i < dims\<close>
    using assms \<O>_bij[THEN bij_betwE]
    by auto

  moreover have F_ninfty: \<open>f \<in> set F \<Longrightarrow> fn f x \<noteq> \<infinity>\<close> for f x
    using assms unfolding invar_max_def
    by auto

  ultimately have elim_step_ninfty: \<open>\<forall>f\<in>set (snd (elim_step (i, F))). \<forall>x. fst f x \<noteq> \<infinity>\<close>
    using domains_fin domains_ne \<O>_bij F_ninfty 
    unfolding elim_step_def Let_def
    by (auto dest!: Max_inftyD sum_list_inftyD intro!: finite_imageI elim!: bij_betwE) metis

  have scope_max: \<open>
    has_scope_on 
      (\<lambda>x. MAX x\<^sub>l\<in>doms (\<O> i). \<Sum>f\<leftarrow>filter (\<lambda>f. \<O> i \<in> snd f) F. fst f (x(\<O> i \<mapsto> x\<^sub>l))) 
      partial_vecs 
      ((\<Union> (snd ` set (filter (\<lambda>f. \<O> i \<in> snd f) F))) - {\<O> i})\<close>
    apply (intro has_scope_on_MAX has_scope_on_sum_list has_scope_on_updI)
     apply (rule has_scope_on_subs_dom[of _ partial_vecs])
    using assms bij_betwE[OF \<O>_bij]  domains_ne domains_fin
    by (auto intro!: partial_vecs_updI simp: invar_max_def)

  have *: \<open>snd f \<subseteq> ({..<dims} - \<O> ` {..<Suc i})\<close> if \<open>f \<in> set (snd (elim_step (i, F)))\<close> for f
    using that assms unfolding elim_step_def invar_max_def Let_def
    by (fastforce simp: less_Suc_eq)

  have \<open>has_scope_on (fst f) partial_vecs (snd f)\<close> if \<open>f \<in> set (snd (elim_step (i, F)))\<close> for f
    using assms that *[OF that]
    unfolding invar_max_def elim_step_def Let_def case_prod_unfold snd_conv
    by (fastforce intro!: has_scope_on_subs[OF scope_max])

  then show ?thesis
    using assms expl_max_\<F>_step[symmetric, of i] * elim_step_ninfty
    unfolding invar_max_def
    by auto
qed      

text \<open>Invariant holds in the beginning.\<close>
lemma invar_max_zero: \<open>invar_max \<F> 0\<close>
  unfolding invar_max_def partial_vecs_def
  using \<F>_scopes \<F>_not_inf
  by (auto simp: case_prod_beta expl_max_\<F>_def full_vecs_def)

lemma fst_elim_step_pow: \<open>fst ((elim_step ^^ i) cfg) = i + fst cfg\<close>
  by (induction i) (auto simp: elim_step_def Let_def case_prod_unfold)

lemma elim_step_eq_pair: \<open>(elim_step ^^ i) (0, F) = (i, snd ((elim_step ^^ i) (0, F))) \<close>
  using fst_elim_step_pow[of _ \<open>(0, _)\<close>]
  by (induction i) (auto simp: elim_step_def Let_def case_prod_unfold)

lemma invar_max_elim_steps: \<open>i \<le> dims \<Longrightarrow> invar_max (snd ((elim_step ^^ i) (0, \<F>))) i\<close>
proof (induction i)
  case 0
  then show ?case 
    using invar_max_zero 
    by auto
next
  case (Suc i)
  then show ?case
    using invar_max_Suc 
    by auto (metis Suc_le_eq elim_step_eq_pair)
qed

lemma invar_max_elim_aux: \<open>invar_max (snd elim_aux) dims\<close>
  unfolding elim_aux_def
  using invar_max_elim_steps 
  by auto

lemma scope_elim_aux_empty: \<open>(f, s) \<in> set (snd elim_aux) \<Longrightarrow> s = {}\<close>
  by (metis Diff_cancel Diff_empty Diff_eq_empty_iff \<O>_bij bij_betw_def invar_max_elim_aux invar_scope)

lemma scope_elim_aux_empty': \<open>fs \<in> set (snd elim_aux) \<Longrightarrow> snd fs = {}\<close>
  by (metis prod.exhaust_sel scope_elim_aux_empty)

text \<open>Main correctness theorem:\<close>
lemma elim_max_correct: \<open>elim_max = expl_max\<close>
proof -
  have *: \<open>{..<dims} - \<O> ` {..<dims} = {}\<close>
    using \<O>_bij bij_betw_imp_surj_on 
    by fastforce
  show ?thesis
    using invar_max_elim_aux
    unfolding elim_max_def invar_max_def
    by (auto simp: * expl_max_def case_prod_unfold)
qed

end

end