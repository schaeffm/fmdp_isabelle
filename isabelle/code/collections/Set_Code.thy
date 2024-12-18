theory Set_Code
  imports 
    "Collections.HashSet" 
    "Collections.Collections" 
    Rel_Util
begin

section \<open>Util\<close>
lemma set_insert_hd_tl: \<open>xs \<noteq> [] \<Longrightarrow> Set.insert (hd xs) (List.set (tl xs)) = List.set xs\<close>
  by (cases xs) auto

section \<open>Executable Sets of Natural Numbers\<close>


text \<open>We add a couple of operations to sets\<close>

setup Locale_Code.open_block

context StdOSetDefs
begin

definition \<open>Union_sets X = fold union X (empty ())\<close>

definition \<open>max_set f X = (let xs = to_list X in fold (\<lambda>x m. Orderings.max (f x) m) ((tl xs)) (f (hd xs)))\<close>

definition \<open>set_sum X f = iterate X (\<lambda>p acc. f p + acc) 0\<close>

definition \<open>insert_list X xs = fold ins xs X\<close>

definition \<open>max_set' f X = (let xs = to_list X in List.fold (\<lambda>x m. Orderings.max (f x) m) ((tl xs)) (f (hd xs)))\<close>

end

setup Locale_Code.close_block

interpretation SetCode: StdOSetDefs rs_ops .

locale Set =
  StdSetDefs set_ops +
  StdSet set_ops
  for set_ops :: \<open>('x, 'set) oset_ops\<close>

locale NatSetDefs =
  StdOSetDefs nat_set_ops
  for nat_set_ops :: \<open>(nat, 'natset) oset_ops\<close>

locale NatSet =
  NatSetDefs nat_set_ops +
  StdOSet nat_set_ops
  for nat_set_ops :: \<open>(nat, 'natset) oset_ops\<close>

context NatSet
begin

sublocale Set nat_set_ops
  by unfold_locales

lemmas
  to_list_correct(2)[intro!]
  to_list_correct[simp]

  ball_correct[simp]
  filter_correct[simp]
  
  to_set_correct(1)[simp]
  to_set_correct(2)[simp, intro!]
  
  disjoint_correct[simp]
  
  ins_correct[simp]
  ins_correct(2)[intro]
  
  union_correct[simp]
  union_correct(2)[intro]
  
  empty_correct[simp]
  empty_correct(2)[intro]
  
  diff_correct[simp]
  diff_correct(2)[intro!]

  inter_correct[simp]
  inter_correct(2)[intro!]

  memb_correct[simp]

  delete_correct[simp]
  delete_correct(2)[intro!]

  isEmpty_correct[simp]

  to_sorted_list_correct[simp]
  to_sorted_list_correct(2-3)[intro!]

lemma insert_list_correct[simp]:
  assumes \<open>invar X\<close> 
  shows 
    \<open>\<alpha> (insert_list X xs) = \<alpha> X \<union> List.set xs\<close> 
    \<open>invar (insert_list X xs)\<close>
  using assms
  by (induction xs arbitrary: X) (auto simp: insert_list_def)

lemmas insert_list_correct(2)[intro!]

lemma Union_sets_correct[simp]:
  assumes \<open>\<And>x. x \<in> List.set X \<Longrightarrow> invar x\<close>
  shows 
    \<open>invar (Union_sets X)\<close> 
    \<open>\<alpha> (Union_sets X) = (\<Union>x \<in> List.set X. \<alpha> x)\<close>
  using assms empty_correct
  by (induction X rule: rev_induct) (auto simp: Union_sets_def)

lemmas Union_sets_correct(1)[intro!]

lemma inorder_nil_iff[simp]: 
  assumes \<open>invar X\<close>
  shows \<open>to_list X = [] \<longleftrightarrow> \<alpha> X = {}\<close>
  using assms to_list_correct(1)
  by fastforce

lemma to_list_eqD[dest]: \<open>to_list X = xs \<Longrightarrow> invar X \<Longrightarrow> \<alpha> X = set xs\<close>
  by force

lemma max_set_Max[simp]:
  assumes \<open>\<alpha> X \<noteq> {}\<close> \<open>invar X\<close>
  shows \<open>max_set f X = (MAX x \<in> \<alpha> X. f x)\<close>
proof -
  have \<open>fold (\<lambda>x m. Orderings.max (f x) m) xs (f a) = Max (f ` list.set (a#xs))\<close> for xs a
  proof (induction xs arbitrary: a rule: rev_induct)
    case (snoc a xs)
    thus ?case
      by (cases \<open>list.set xs = {}\<close>) (auto simp: max.commute max.left_commute)
  qed auto
  thus ?thesis
    unfolding max_set_def Let_def
    using assms
    by (cases \<open>to_list X\<close>) auto
qed

section \<open>Correctness of Union\<close>
lemma fold_union_aux: 
  assumes
    \<open>invar Y\<close> 
    \<open>\<And>i. i \<in> set xs \<Longrightarrow> invar (X i)\<close>
  shows 
    \<open>\<alpha> (fold (\<lambda>i acc. union (X i) acc) xs Y) = (\<Union>i \<in> set xs. \<alpha> (X i)) \<union> \<alpha> Y\<close>
  using assms
  by (induction xs arbitrary: Y) auto

lemma fold_union[simp]:
  assumes \<open>\<And>i. i \<in> set xs \<Longrightarrow> invar (X i)\<close> 
  shows \<open>\<alpha> (fold (\<lambda>i acc. union (X i) acc) xs (empty ())) = (\<Union>i \<in> set xs. \<alpha> (X i))\<close>
  using assms 
  by (subst fold_union_aux) auto

lemma invar_fold_union_aux[intro!]: 
  assumes \<open>invar Y\<close> and \<open>(\<And>i. i \<in> set xs \<Longrightarrow> invar (X i))\<close> 
  shows \<open>invar (fold (\<lambda>i acc. union (X i) acc) xs Y)\<close>
  using assms by (induction xs arbitrary: Y) auto

lemma invar_fold_union[intro!]: 
  \<open>(\<And>i. i \<in> set xs \<Longrightarrow> invar (X i)) \<Longrightarrow> invar (fold (\<lambda>i acc. union (X i) acc) xs (empty ()))\<close>
  by (subst invar_fold_union_aux | auto)+

section \<open>Correctness of setsum\<close>
lemma set_sum_correct[simp]: 
  assumes \<open>invar X\<close>
  shows \<open>set_sum X f = (\<Sum>p \<in> \<alpha> X. f p)\<close>
proof -
  
  have iterate_sum: \<open>iterate X (\<lambda>p acc. f p + acc) init = init + (\<Sum>p \<in> \<alpha> X. f p)\<close> for init
  by (rule iterate_rule_insert_P[where I = \<open>\<lambda>Y acc. acc + (\<Sum>v \<in> \<alpha> X - Y. f v) = (\<Sum>v \<in> \<alpha> X. f v) + init\<close>])
      (auto simp: algebra_simps Diff_insert[of \<open>\<alpha> X\<close>] sum.remove assms)
  
  show ?thesis
  unfolding set_sum_def 
  using iterate_sum[of 0]
  by auto
qed
end

hide_const set_rel

context StdSetDefs
begin

definition \<open>set_rel X_code X \<longleftrightarrow> 
  invar X_code \<and> (\<alpha> X_code = X)\<close>

lemmas set_rel_iff = set_rel_def

lemma set_relI[intro!, simp]:
  assumes \<open>invar X_code\<close> \<open>\<alpha> X_code = X\<close>
  shows \<open>set_rel X_code X\<close>
  using assms 
  unfolding set_rel_def 
  by auto

lemma set_relE[elim!]:
  assumes \<open>set_rel X_code X\<close>
  obtains \<open>invar X_code\<close> \<open>\<alpha> X_code = X\<close>
  using assms 
  unfolding set_rel_def 
  by auto

lemma set_rel_inv[dest]: \<open>set_rel X_code X \<Longrightarrow> invar X_code\<close>
  by auto

lemma set_rel_set[dest]: \<open>set_rel X_code X \<Longrightarrow> \<alpha> X_code = X\<close>
  by auto

end

context NatSet
begin

unbundle lifting_syntax
lemma set_rel_Un: \<open>(set_rel ===> set_rel ===> set_rel) union (\<union>) \<close>
  by fastforce

end

end