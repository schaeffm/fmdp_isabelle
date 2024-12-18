theory Rel_Util
  imports Main "Automatic_Refinement.Relators"
begin

hide_const nat_rel

definition \<open>rel_on R1 X = (\<lambda>x y. R1 x y \<and> y \<in> X)\<close>

lemma rel_onI[intro!]:
  assumes \<open>y \<in> X\<close> \<open>R1 x y\<close>
  shows \<open>rel_on R1 X x y\<close>
  using assms rel_on_def by metis

lemma rel_onE[elim!]:
  assumes \<open>rel_on R1 X x y\<close>
  obtains \<open>y \<in> X\<close> \<open>R1 x y\<close>
  using assms rel_on_def by metis

definition \<open>fun_rel' R1 R2 f1 f2 \<longleftrightarrow> (\<forall>x y. R1 x y \<longrightarrow> R2 x y (f1 x) (f2 y))\<close>

lemma fun_relE[elim]: 
  assumes \<open>rel_fun R1 R2 f1 f2\<close> obtains \<open>(\<And>x y. R1 x y \<Longrightarrow> R2 (f1 x) (f2 y))\<close>
  using assms 
  by (simp add: rel_funD)

lemma fun_relE'[elim]: 
  assumes \<open>fun_rel' R1 R2 f1 f2\<close> obtains \<open>(\<And>x y. R1 x y \<Longrightarrow> R2 x y (f1 x) (f2 y))\<close>
  using assms 
  unfolding fun_rel'_def 
  by auto

lemma fun_relD': \<open>fun_rel' R1 R2 f1 f2 \<Longrightarrow> R1 x y \<Longrightarrow> R2 x y (f1 x) (f2 y)\<close>
  by auto

lemma fun_relI'[intro]: \<open>(\<And>x y. R1 x y \<Longrightarrow> R2 x y (f1 x) (f2 y)) \<Longrightarrow> fun_rel' R1 R2 f1 f2\<close>
  unfolding fun_rel'_def 
  by auto

lemma list_rel_nthE[elim]: 
  assumes
    \<open>list_all2 R_elem xs ys\<close> 
  obtains 
    \<open>length xs = length ys\<close> and 
    \<open>\<And>i. i < length xs \<Longrightarrow> R_elem (xs ! i) (ys ! i)\<close>
  using assms list_all2_conv_all_nth by blast

lemma list_rel_nthE'[elim]: 
  assumes
    \<open>list_all2 R_elem xs ys\<close> 
  obtains 
    \<open>length xs = length ys\<close> and 
    \<open>i < length xs \<Longrightarrow> R_elem (xs ! i) (ys ! i)\<close>
  using assms by blast

lemma list_rel_E[elim]: 
  assumes
    \<open>list_all2 R_elem xs ys\<close> 
  obtains 
    \<open>length xs = length ys\<close> and 
    \<open>\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> R_elem x y\<close>
  using assms list_all2_iff case_prodD by metis

definition \<open>nat_rel x y \<longleftrightarrow> x = y\<close>

lemma nat_relD[dest!]: \<open>nat_rel x y \<Longrightarrow> x = y\<close>
  unfolding nat_rel_def by auto
definition \<open>and_rel R1 R2 x y \<longleftrightarrow> R1 x y \<and> R2 x y\<close>

lemma and_relI[intro!]: \<open>R1 x y \<Longrightarrow> R2 x y \<Longrightarrow> and_rel R1 R2 x y\<close>
  unfolding and_rel_def by auto


lemma and_relE[elim!]: 
  assumes \<open>and_rel R1 R2 x y\<close>
  obtains \<open>R1 x y\<close> \<open>R2 x y\<close>
  using assms unfolding and_rel_def by auto

lemma pair_relI[intro!]: \<open>R1 (fst p1) (fst p2) \<Longrightarrow> R2 (snd p1) (snd p2) \<Longrightarrow> rel_prod R1 R2 p1 p2\<close>
  by (simp add: rel_prod_sel)

lemma pair_relE[elim!]: 
  assumes \<open>rel_prod R1 R2 p1 p2\<close>
  obtains \<open>R1 (fst p1) (fst p2)\<close> \<open>R2 (snd p1) (snd p2)\<close>
  using assms by (simp add: rel_prod_sel)

section \<open>List relations\<close>
lemma list_rel_eq_iff[simp]: \<open>list_all2 (=) xs ys \<longleftrightarrow> xs = ys\<close>
  using list_eq_iff_nth_eq[of xs ys]
  by (simp add: list.rel_eq)

lemma list_rel_sum_list: \<open>list_all2 R_elem xs ys \<Longrightarrow> 
  (\<And>x y. R_elem x y \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x = f' y) \<Longrightarrow> 
  (sum_list (map f xs) :: _ :: comm_monoid_add) = sum_list (map f' ys)\<close>
  by (auto simp: sum_list_sum_nth intro!: sum.cong)

lemma list_rel_consE[elim!]: 
  assumes \<open>list_all2 R_elem (x#xs) (y#ys)\<close>
  obtains \<open>R_elem x y\<close> \<open>list_all2 R_elem xs ys\<close> 
  using assms
  by blast

lemma list_all2_cons_leftE[elim]:
  assumes \<open>list_all2 R_elem (x # xs) ys\<close>
  obtains y ys' where \<open>list_all2 R_elem xs ys'\<close> \<open>R_elem x y\<close> \<open>ys = y # ys'\<close>
  using assms
  by (cases ys) auto


lemma list_all2_cons_rightE[elim]:
  assumes \<open>list_all2 R_elem xs (y#ys)\<close>
  obtains x xs' where \<open>list_all2 R_elem xs' ys\<close> \<open>R_elem x y\<close> \<open>xs = x # xs'\<close>
  using assms
  by (cases xs) auto

lemma list_rel_filterI:
  assumes \<open>list_all2 R_elem xs ys\<close> \<open>rel_fun (\<lambda>x y. x \<in> set xs \<and> y \<in> set ys \<and> R_elem x y) (=) P Q\<close>
  shows \<open>list_all2 R_elem (filter P xs) (filter Q ys)\<close>
  using assms
proof (induction xs arbitrary: ys)
  case (Cons a xs)
  then show ?case 
    by (cases ys) (auto dest: rel_funD)
qed auto

lemma list_rel_mapI:
  assumes \<open>list_all2 R_in xs ys\<close> \<open>rel_fun (rel_on R_in (set ys)) R_out f g\<close>
  shows \<open>list_all2 R_out (map f xs) (map g ys)\<close>  
  using assms
proof (induction xs arbitrary: ys)
  case (Cons a xs)
  then show ?case 
    by (cases ys) (auto dest: rel_funD)
qed auto

section \<open>Ex rel\<close>

lemma bex_rel: 
  assumes \<open>\<exists>x \<in> X. P x\<close> \<open>rel_set R_elem X X'\<close> \<open>\<And>x x'. R_elem x x' \<Longrightarrow> P x \<longleftrightarrow> P' x'\<close>
  shows \<open>\<exists>x' \<in> X'. P' x'\<close>
  using assms
  by (fastforce simp: rel_set_def)

lemma ex_rel: 
  assumes \<open>\<exists>x \<in> X. P x\<close> \<open>rel_set R_elem X X'\<close> \<open>\<And>x x'. R_elem x x' \<Longrightarrow> P x \<longleftrightarrow> P' x'\<close>
  shows \<open>\<exists>x'. x' \<in> X' \<and> P' x'\<close>
  using assms
  by (fastforce simp: rel_set_def)

lemma bex_rel': 
  assumes \<open>\<exists>x' \<in> X'. P' x'\<close> \<open>rel_set R_elem X X'\<close> \<open>\<And>x x'. R_elem x x' \<Longrightarrow> P x \<longleftrightarrow> P' x'\<close>
  shows \<open>\<exists>x \<in> X. P x\<close>
  using assms
  by (fastforce simp: rel_set_def)

lemma ex_rel': 
  assumes \<open>\<exists>x' \<in> X'. P' x'\<close> \<open>rel_set R_elem X X'\<close> \<open>\<And>x x'. R_elem x x' \<Longrightarrow> P x \<longleftrightarrow> P' x'\<close>
  shows \<open>\<exists>x. x \<in> X \<and> P x\<close>
  using assms
  by (fastforce simp: rel_set_def)

end