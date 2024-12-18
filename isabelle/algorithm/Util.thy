theory Util
  imports "Explicit-MDPs.MDP_reward"
begin
chapter \<open>Util\<close>
section \<open>Auxiliary theorems for Factored MDPs\<close>

lemma ballE2: \<open>\<forall>x\<in>A. P x \<Longrightarrow> x \<in>A \<Longrightarrow> (x \<in> A \<Longrightarrow> P x \<Longrightarrow> R) \<Longrightarrow> R\<close>
  using ballE
  by auto

subsection \<open>Lists\<close>
lemma sum_list_map_cong: \<open>(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> 
  sum_list (map f xs) = sum_list (map g xs)\<close>
  by (metis map_cong)

subsection \<open>Maps\<close>
lemma finite_set_of_finite_maps':
  assumes \<open>finite X\<close>
  assumes \<open>finite Y\<close>
    shows \<open>finite {x. dom x \<subseteq> X \<and> ran x \<subseteq> Y}\<close>
proof - 
  have \<open>{x. dom x \<subseteq> X \<and> ran x \<subseteq> Y} = (\<Union>X' \<in> {x. x \<subseteq> X}. {x. dom x = X' \<and> ran x \<subseteq> Y})\<close>
    by auto
  thus ?thesis
    using assms
      by (simp add: finite_set_of_finite_maps finite_subset)
  qed

lemma map_add_eq_comp_eq:
  assumes \<open>a ++ b = a' ++ b'\<close> and \<open>dom a = dom a'\<close> \<open>dom b = dom b'\<close> \<open>dom a \<inter> dom b = {}\<close> \<open>dom a' \<inter> dom b' = {}\<close> 
  shows \<open>a = a' \<and> b = b'\<close>
proof -
  {
  fix x
  have *: \<open>(a ++ b) x = (a' ++ b') x\<close>
    using assms by simp
  hence **: \<open>a x = a' x\<close> 
    using assms(2-5) *
    unfolding map_add_def
    by (cases \<open>a x\<close>; cases \<open>a' x\<close>; cases \<open>(a ++ b) x\<close>; cases \<open>(a' ++ b') x\<close>) auto
  have ***: \<open>b x = b' x\<close>
    using assms(2-5)
    unfolding map_add_def
    using *
    by (cases \<open>b x\<close>; cases \<open>b' x\<close>; cases \<open>(a ++ b) x\<close>; cases \<open>(a' ++ b') x\<close>) auto
  note this = ** ***
}
  thus \<open>a = a' \<and> b = b'\<close>
    by auto
qed

lemma ranE:
  assumes \<open>i \<in> ran m\<close>
  obtains x where \<open>m x = Some i\<close>
  using assms
  unfolding ran_def
  by auto

subsection \<open>Supremum\<close>

lemma image_SUP:
  fixes f g X
  shows \<open>(\<Squnion>x \<in> g ` X. f x) = (\<Squnion>x \<in> X. f (g x))\<close>
  by (simp add: image_image)

lemma cSUP_add: \<open>X\<noteq>{} \<Longrightarrow> bdd_above (f ` X) \<Longrightarrow> (\<Squnion>x \<in> X. f x + c::real) = (\<Squnion>x \<in> X. f x) + c\<close>
proof (rule antisym, goal_cases)
  case 2
  have \<open>bdd_above ((\<lambda>x. f x + c) ` X)\<close>
    using 2 
    unfolding bdd_above.unfold
    by auto (metis add.commute add_le_cancel_left)
  hence \<open>\<Squnion> (f ` X) \<le> (\<Squnion>x\<in>X. f x + c) - c\<close>
    using 2
    by (intro cSUP_least) (auto intro!: cSUP_upper2 simp: algebra_simps)
  thus ?case
    by (auto simp: algebra_simps)
next
  case 1
  thus \<open>(\<Squnion>x\<in>X. f x + c) \<le> \<Squnion> (f ` X) + c\<close>
    by (intro cSUP_least) (auto simp: algebra_simps intro!: cSUP_upper2)
qed

lemma cSUP_mono':
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<le> g x\<close> \<open>bdd_above (g ` X)\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<Squnion>(f ` X) \<le> (\<Squnion>(g ` X) :: real)\<close>
  using assms 
  by (auto intro!: cSUP_mono)

lemma Max_cong:
  assumes \<open>X \<noteq> {}\<close> \<open>finite X\<close> \<open>\<And>x. x \<in> X \<Longrightarrow> f x = h x\<close>
  shows \<open>Max (f ` X) = Max (h ` X)\<close>
  using assms
  by auto

lemma Max_Max:
  assumes \<open>finite X\<close> \<open>X \<noteq> {}\<close> \<open>\<And>x. x \<in> X \<Longrightarrow> finite (Y x) \<and> Y x \<noteq> {}\<close>
  shows \<open>(MAX x \<in> X. MAX y \<in> Y x. f (g x y)) = (MAX x \<in> {g x y | x y. x \<in> X \<and> y \<in> Y x}. f x)\<close>
proof -
  have fin: \<open>finite {g x y |x y. x \<in> X \<and> y \<in> Y x}\<close> 
    by (rule finite_subset [where B = "\<Union>x \<in> X. (g x ` Y x)"]) (auto simp: assms)

  have ne: \<open>{g x y |x y. x \<in> X \<and> y \<in> Y x} \<noteq> {}\<close>
    using assms by auto

  show ?thesis
    apply (intro antisym)
    subgoal
      using assms fin ne
      by simp (auto simp:  image_is_empty finite_imageI Max_ge_iff)
    subgoal
    using assms fin ne
    by (subst Max_le_iff) (auto simp:  Max_ge_iff)
  done
qed

lemma Max_add_commute_ereal:
  fixes k :: ereal
  assumes "finite S" and "S \<noteq> {}"
  shows "Max ((\<lambda>x. f x + k) ` S) = Max(f ` S) + k"
proof -
  have m: "\<And>x y. max x y + k = max (x+k) (y+k)"
    by (simp add: max_def order.antisym add_right_mono)
  have "(\<lambda>x. f x + k) ` S = (\<lambda>y. y + k) ` (f ` S)" by auto
  also have "Max \<dots> = Max (f ` S) + k"
    using assms hom_Max_commute [of "\<lambda>y. y+k" "f ` S", OF m, symmetric] by simp
  finally show ?thesis by simp
qed

  subsection \<open>Bounded Functions\<close>

lemma sub_bfun_le_dist: \<open>u - (v :: 'c \<Rightarrow>\<^sub>b real) \<le> dist u v *\<^sub>R 1\<close>
  using Bounded_Functions.dist_bounded[of u _ v] abs_ge_self order.trans
  by (fastforce simp: dist_real_def)

lemma dist_bfun_bounded: \<open>dist (a :: _ \<Rightarrow>\<^sub>b _) b \<le> d \<Longrightarrow> dist (a x) (b x) \<le> d\<close>
  by (metis Bounded_Functions.dist_bounded order.trans)

lemma dist_bfun_le: \<open>dist (a :: _ \<Rightarrow>\<^sub>b real) b \<le> d \<Longrightarrow> a \<le> b + d *\<^sub>R 1\<close>
  by (auto dest!: dist_bfun_bounded intro!: less_eq_bfunI simp: dist_real_def abs_diff_le_iff)

lemma dist_bfun_ge: \<open>dist (a :: _ \<Rightarrow>\<^sub>b real) b \<le> d \<Longrightarrow> a \<ge> b - d *\<^sub>R 1\<close>
  by (auto dest!: dist_bfun_bounded intro!: less_eq_bfunI simp: dist_real_def abs_diff_le_iff)

subsection \<open>Find\<close>

lemma sorted_wrt_find:
  assumes \<open>sorted_wrt f xs\<close> \<open>class.preorder f le'\<close> \<open>List.find P xs = Some y\<close> \<open>z \<in> set xs\<close> \<open>P z\<close>
  shows \<open>f y z\<close>
  using assms 
proof (induction xs arbitrary: y z)
  case Nil
  then show ?case     
    by auto
next
  case (Cons a xs)
  have 1: \<open>sorted_wrt f xs\<close>
    using Cons 
    by auto
  have \<open>f a x\<close> if \<open>x \<in> set xs\<close> for x
    using Cons.prems(1) that by auto
  
  then show ?case
  proof (cases \<open>P a\<close>)
    case True
    hence \<open>y = a\<close>
      using Cons.prems(3) by auto
    then show ?thesis
      using Cons class.linorder.axioms class.order.axioms preorder.order_refl
      by fastforce
  next
    case False
    hence 2: \<open>find P xs = Some y\<close>
      using Cons
      by auto
    hence \<open>z \<in> set xs \<Longrightarrow> P z \<Longrightarrow> f y z\<close>
      using Cons.IH[OF 1 Cons.prems(2) 2, of z]
      by auto
    then show ?thesis
      using Cons False
      by fastforce
  qed
qed

subsection \<open>Maps\<close>

lemma restrict_dom[simp]: \<open>m |` (dom m) = m\<close>
  by (auto simp: dom_def restrict_map_def)

lemma restrict_dom'[simp]: \<open>dom m \<subseteq> X \<Longrightarrow> m |` X = m\<close>
  by (metis Map.restrict_restrict inf.order_iff restrict_dom)

lemma restrict_eq_subset: \<open>restrict_map x X = restrict_map y X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> restrict_map x Y = restrict_map y Y\<close>
  by (metis Int_absorb1 Map.restrict_restrict)

lemma restrict_map_eq: \<open>restrict_map x X = restrict_map y X \<Longrightarrow> restrict x X = restrict y X\<close>
  by (metis restrict_ext restrict_in)

lemma restrict_map_eqD[dest]: \<open>x |` X = y |` X \<Longrightarrow> i \<in> X \<Longrightarrow> x i = y i\<close>
  by (metis restrict_in)

lemma restrict_SomeD[dest]: \<open>(x |` S) i = Some y \<Longrightarrow> x i = Some y\<close>
  by (metis domI domIff restrict_in restrict_out)

lemma map_of_enumerate: \<open>map_of (List.enumerate 0 xs) i = 
  (if i < length xs then Some (xs ! i) else None)\<close>
  by (auto simp add: in_set_enumerate_eq map_of_eq_None_iff)

lemma add_restr_dom: \<open>dom b \<inter> S = {} \<Longrightarrow> (a ++ b) |` S = a |` S\<close>
proof
  fix x
  show \<open>dom b \<inter> S = {} \<Longrightarrow> ((a ++ b) |` S) x = (a |` S) x\<close>
    by (cases \<open>x \<in> S\<close>; cases \<open>x \<in> dom b\<close>) (auto simp: map_add_dom_app_simps)
qed

lemma map_add_restr[simp]: \<open>m |` X ++ m = m\<close>
proof
  fix x
  show \<open>(m |` X ++ m) x = m x\<close>
    by (cases \<open>x \<in> X\<close>; cases \<open>x \<in> dom m\<close>) (auto simp: map_add_dom_app_simps)
qed

lemma map_add_restr'[simp]: \<open>m ++ m |` X = m\<close>
proof
  fix x
  show \<open>(m ++ (m |` X)) x = m x\<close>
    by (cases \<open>x \<in> X\<close>; cases \<open>x \<in> dom m\<close>) (auto simp: map_add_dom_app_simps domIff)
qed

lemma map_add_restr_un[simp]: \<open>(m |` X) ++ (m |` Y) = m |` (X \<union> Y)\<close>
proof
  fix x
  show \<open>((m |` X) ++ (m |` Y)) x = (m |` (X \<union> Y)) x\<close>
    by (cases \<open>x \<in> X\<close>; cases \<open>x \<in> Y\<close>; cases \<open>x \<in> dom m\<close>) (auto simp: map_add_dom_app_simps domIff)
qed

subsection \<open>List pmfs\<close>

fun list_pmf where
  "list_pmf [] = return_pmf []"
| "list_pmf [x] = map_pmf (\<lambda>i. [i]) x"
| "list_pmf (x#xs) = do {
    y \<leftarrow> x;
    ys \<leftarrow> list_pmf xs;
    return_pmf (y#ys)}"

lemma indicator_singleton: "indicator {x} y = (if x = y then 1 else 0)"
  by auto

lemma list_pmf_len_ne: 
  assumes \<open>length xs \<noteq> length p\<close> 
  shows \<open>pmf (list_pmf p) xs = 0\<close>
  using assms
  by (induction p arbitrary: xs rule: list_pmf.induct) (auto simp: pmf_eq_0_set_pmf)

lemma pmf_list_pmf: \<open>length xs = length p  \<Longrightarrow> 
  pmf (list_pmf p) xs = (\<Prod>i < length xs. pmf (p ! i) (xs ! i))\<close>
proof (induction p arbitrary: xs rule: list_pmf.induct)
  case 1
  then show ?case by auto
next
  case (2 x)
  then show ?case
    by (cases xs) (auto simp: pmf_map pmf.rep_eq vimage_def)
next
  case (3 x v va)

  then obtain a b xs' where xs: "xs = a#b#xs'"
    by (cases xs; cases \<open>tl xs\<close>) auto

  hence \<open>pmf (list_pmf (x # v # va)) xs = pmf (list_pmf (v # va)) (b # xs') * pmf x a\<close>
    unfolding xs
    using integral_measure_pmf_real[of "{a}"] integral_measure_pmf_real[of \<open>{b # xs'}\<close>] 
    by (fastforce simp: pmf_bind indicator_singleton)
  also have "\<dots> = (\<Prod>i< Suc(length xs'). pmf ((v # va) ! i) ((b # xs') ! i)) * pmf x a"
    using "3.IH" "3.prems" set_pmf_iff xs by fastforce
  also have "... = (\<Prod>i<length xs. pmf ((x # v # va) ! i) (xs ! i))"
    unfolding xs
    by (simp add: prod.lessThan_Suc_shift del: prod.lessThan_Suc)
  finally show ?case .
qed

lemma set_pmf_list_pmf:
  \<open>set_pmf (list_pmf xs) = {ys. length ys = length xs \<and> (\<forall>i < length xs. ys ! i \<in> set_pmf (xs ! i))}\<close>
proof safe
  show \<open>\<And>x. x \<in> set_pmf (list_pmf xs) \<Longrightarrow> length x = length xs\<close>
    by (meson list_pmf_len_ne pmf_eq_0_set_pmf)
  show \<open> \<And>x. length x = length xs \<Longrightarrow> \<forall>i<length xs. x ! i \<in> set_pmf (xs ! i) \<Longrightarrow> x \<in> set_pmf (list_pmf xs)\<close>
    by (auto simp: set_pmf_iff pmf_list_pmf)
next
  fix ys i
  assume \<open>ys \<in> set_pmf (list_pmf xs)\<close> \<open>i < length xs\<close>
  hence \<open>length ys = length xs\<close>
    using list_pmf_len_ne
    by (auto simp: set_pmf_iff pmf_list_pmf)
  hence \<open>pmf (list_pmf xs) ys = (\<Prod>i < length xs. pmf (xs ! i) (ys ! i))\<close>
    using pmf_list_pmf
    by fastforce
  thus \<open>ys ! i \<in> set_pmf (xs ! i)\<close>
    using \<open>ys \<in> set_pmf (list_pmf xs)\<close> \<open>i < length xs\<close>
    unfolding set_pmf_iff 
    by auto
qed

lemma finite_list_pmf_set: \<open>xs \<noteq> [] \<Longrightarrow> (\<forall>x \<in> set xs. finite (set_pmf x)) \<Longrightarrow> finite (set_pmf (list_pmf xs))\<close>
  by (rule finite_subset[OF _ finite_lists_length_eq[of \<open>(\<Union> (set_pmf ` set xs))\<close> \<open>length xs\<close>]])
    (fastforce simp: in_set_conv_nth set_pmf_list_pmf)+

subsection \<open>Misc\<close>

lemma finite_remove[simp]: \<open>finite (Set.remove x X) \<longleftrightarrow> finite X\<close>
  by (auto simp: Set.remove_def)

lemma finite_removeI[intro!]: \<open>finite X \<Longrightarrow> finite (Set.remove x X)\<close>
  by (auto simp: Set.remove_def)

lemma Some_ex_find_iff: \<open>(\<exists>x. Some x = List.find P xs) \<longleftrightarrow> (\<exists>x \<in> set xs. P x)\<close>
  by (auto simp: find_Some_iff2 in_set_conv_nth dest: Least_le intro!: exI[of _ \<open>LEAST i. P (xs ! i)\<close>] intro: LeastI)+ auto

lemma find_map: \<open>find P (map f xs) = (case (find (P o f) xs) of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x))\<close>
  by (induction xs) auto

lemma set_product_lists': \<open>set (product_lists xss) = {xs. length xs = length xss \<and> (\<forall>i < length xss. xs ! i \<in> set (xss ! i))}\<close>
  by (auto simp: product_lists_set list_all2_conv_all_nth)

lemma sorted_list_of_set_nth_mem[intro!]: \<open>finite X \<Longrightarrow> i < card X \<Longrightarrow> sorted_list_of_set X ! i \<in> X\<close>
  by (metis nth_mem sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set.set_sorted_key_list_of_set)

lemma restrict_map_SomeD[dest!]: \<open>(v |` F) i = Some y \<Longrightarrow> i \<in> F \<and> v i = Some y\<close>
  by (cases \<open>i \<in> F\<close>) auto

lemma map_upd_eq_imp_eq: \<open>m(x \<mapsto> a) = n(x \<mapsto> b) \<Longrightarrow> x \<notin> dom m \<Longrightarrow> x \<notin> dom n \<Longrightarrow> m = n \<and> a = b\<close>
  by (metis fun_upd_None_if_notin_dom fun_upd_upd map_upd_Some_unfold)

lemma sum_pmf:
  assumes 
    \<open>finite I\<close> 
    \<open>\<And>i. i \<in> I \<Longrightarrow> finite (D i) \<and> set_pmf (p i) \<subseteq> D i\<close>
  shows 
    \<open>(\<Sum>v\<in>{v. dom v = I \<and> (\<forall>i\<in>dom v. (v i) \<in> Some` D i)}. \<Prod>i\<in>I. pmf (p i) (the (v i))) = (1 :: real)\<close>
  using assms
proof (induction I arbitrary: D p rule: finite_induct)
  case (insert x F)

  hence neq_x[simp]: \<open>i \<in> F \<Longrightarrow> i \<noteq> x\<close> for i
    using insert by auto

  have *: \<open>v \<in> {v. dom v = insert x F \<and> (\<forall>i\<in>dom v. (v i) \<in> Some ` D i)} \<longleftrightarrow>
    v \<in> (\<lambda>(v, y). v(x \<mapsto> y)) ` ({v. dom v = F \<and> (\<forall>i\<in>dom v. (v i) \<in> Some ` D i)} \<times> (D x))\<close> for v
    by (auto simp: image_iff intro!: exI[of _ \<open>v |` F\<close>] split: if_splits) force+

  have inj: \<open>inj_on (\<lambda>(v, y). v(x \<mapsto> y)) ({v. dom v = F \<and> (\<forall>i\<in>dom v. v i \<in> Some ` D i)} \<times> D x)\<close>
    using insert.hyps map_upd_eq_imp_eq
    by (auto intro!: inj_onI dest!: map_upd_eq_imp_eq)

  then show ?case
    using insert *
    by (simp add: sum.reindex sum_pmf_eq_1 sum.swap[of _  \<open>D x\<close>] 
        sum_distrib_left[symmetric] sum_cartesian_product')
qed (auto simp: card_1_singleton_iff)

subsection \<open>Scopes\<close>

definition \<open>has_scope_on f D R =
  (\<forall>d \<in> D. \<forall>d' \<in> D. restrict d R = restrict d' R \<longrightarrow> f d = f d')\<close>

lemma has_scope_on_eq: 
  \<open>has_scope_on f D R \<Longrightarrow> d \<in> D \<Longrightarrow> d' \<in> D \<Longrightarrow> (\<And>i. i \<in> R \<Longrightarrow> d i = d' i) \<Longrightarrow> f d = f d'\<close>
  unfolding has_scope_on_def
  using restrict_ext 
  by blast

lemma has_scope_onI[intro]: 
  \<open>(\<And>d d'. d \<in> D \<Longrightarrow> d' \<in> D \<Longrightarrow> (\<And>i. i \<in> R \<Longrightarrow> d i = d' i) \<Longrightarrow> f d = f d') \<Longrightarrow> has_scope_on f D R\<close>
  unfolding has_scope_on_def
  using restrict_apply'
  by metis

lemma has_scope_on_compose[intro]: 
  assumes \<open>has_scope_on f D R\<close>
  shows \<open>has_scope_on (\<lambda>x. g (f x)) D R\<close>
  using assms
  unfolding has_scope_on_def
  by fastforce

lemma has_scope_on_cong[cong]: 
  assumes \<open>\<And>x. x \<in> D \<Longrightarrow> f x = g x\<close> \<open>D = D'\<close> \<open>R = R'\<close>
  shows \<open>has_scope_on f D R = has_scope_on g D' R'\<close>
  using assms
  unfolding has_scope_on_def
  by auto

lemma has_scope_on_add[intro]:
  assumes \<open>has_scope_on f D R\<close> \<open>has_scope_on g D R\<close>
  shows \<open>has_scope_on (\<lambda>x. f x + g x) D R\<close>
  using assms
  unfolding has_scope_on_def
  by metis

lemma has_scope_on_mult[intro]:
  assumes \<open>has_scope_on f D R\<close> \<open>has_scope_on g D R\<close>
  shows \<open>has_scope_on (\<lambda>x. f x * g x) D R\<close>
  using assms
  unfolding has_scope_on_def
  by metis

lemma has_scope_on_scale[intro]:
  assumes \<open>has_scope_on f D R\<close>
  shows \<open>has_scope_on (\<lambda>x. c * f x) D R\<close>
  using assms
  by auto

lemma has_scope_on_diff[intro]:
  assumes \<open>has_scope_on f D R\<close> \<open>has_scope_on g D R\<close>
  shows \<open>has_scope_on (\<lambda>x. f x - g x) D R\<close>
  using assms
  unfolding has_scope_on_def
  by metis

lemma has_scope_on_prod[intro]:
  assumes \<open>\<And>i. i \<in> X \<Longrightarrow> has_scope_on (f i) D R\<close>
  shows \<open>has_scope_on (\<lambda>x. prod (\<lambda>i. f i x) X) D R\<close>
  using assms
  unfolding has_scope_on_def
  by (blast intro!: prod.cong)

lemma has_scope_on_sum[intro]:
  assumes \<open>\<And>i. i \<in> X \<Longrightarrow> has_scope_on (f i) D R\<close>
  shows \<open>has_scope_on (\<lambda>x. sum (\<lambda>i. f i x) X) D R\<close>
  using assms
  unfolding has_scope_on_def
  by (blast intro!: sum.cong)

lemma has_scope_on_sum_list[intro]:
  assumes \<open>\<And>i. i \<in> set xs \<Longrightarrow> has_scope_on (f i) D R\<close>
  shows \<open>has_scope_on (\<lambda>x. \<Sum>i\<leftarrow>xs. f i x) D R\<close>
  using assms has_scope_on_eq
  by (blast intro!: has_scope_onI sum_list_map_cong)

lemma has_scope_on_subs[intro]:
  assumes \<open>has_scope_on f D R\<close> \<open>R \<subseteq> Q\<close>
  shows \<open>has_scope_on f D Q\<close>
  using assms
  unfolding has_scope_on_def
  by (metis FuncSet.restrict_restrict inf.absorb_iff2)

lemma has_scope_on_subs_dom[intro]:
  assumes \<open>has_scope_on f D' R\<close> \<open>D \<subseteq> D'\<close>
  shows \<open>has_scope_on f D R\<close>
  using assms
  unfolding has_scope_on_def
  by auto

lemma scope_restrict_imp_eq:
  assumes \<open>has_scope_on f D X\<close> \<open>x \<in> D\<close> \<open>y \<in> D\<close> \<open>x |` X = y |` X\<close>
  shows \<open>f x = f y\<close>
  using assms
  by (auto dest: has_scope_on_eq)

lemma has_scope_on_restr: \<open>has_scope_on f D R \<Longrightarrow> x \<in> D \<Longrightarrow> (x |` R) \<in> D \<Longrightarrow> f (x |` R) = f x\<close>
  by (metis Int_absorb Map.restrict_restrict scope_restrict_imp_eq)


lemma has_scope_on_subs_subs:
  assumes \<open>has_scope_on f D' R\<close> \<open>R \<subseteq> R'\<close> \<open>D \<subseteq> D'\<close>
  shows \<open>has_scope_on f D R'\<close>
  using assms has_scope_on_subs_dom has_scope_on_subs
  by blast
end