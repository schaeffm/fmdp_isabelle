theory ValueDet
  imports Factored_MDP_Util Decision_List_Policy API Constr
begin

locale Factored_MDP_gen_constr_Consts =
  Factored_MDP_Default_Consts where rewards = rewards +
  Constr_Consts where privates = privates for
  privates :: "'c \<Rightarrow> ((('x::{countable, linorder} state \<times> 'a::{countable, linorder}) \<times> bool)) set" and
  rewards :: "'a \<Rightarrow> nat \<Rightarrow> 'x state \<Rightarrow> real" + 
fixes
  \<comment> \<open>Given a state, and action, and all previous states generate LP constraints.\<close>
  gen_constr :: \<open>'x state \<Rightarrow> 'a \<Rightarrow> 'x state list \<Rightarrow> 'c\<close>
begin

definition \<open>inv_gen_constr = (\<forall>t a ts. 
  a \<in> actions \<longrightarrow> t \<in> partial_states \<longrightarrow> set ts \<subseteq> partial_states \<longrightarrow> inv_constr (gen_constr t a ts))\<close>

definition \<open>ge_gen_constr = (\<forall>t \<phi> w a ts. 
  a \<in> actions \<longrightarrow> t \<in> partial_states \<longrightarrow> set ts \<subseteq> partial_states \<longrightarrow> (\<phi>, w) \<in> constr_set (gen_constr t a ts) \<longleftrightarrow>
      (\<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> list_all (\<lambda>t'. \<not>consistent x t') ts}. 
  \<phi> \<ge> \<bar>reward a x + (\<Sum>j < h_dim. w j * (l * g j a x - h j x))\<bar>))\<close>

definition \<open>privs_constr = (\<forall>t a ts. 
  a \<in> actions \<longrightarrow> t \<in> partial_states \<longrightarrow> set ts \<subseteq> partial_states \<longrightarrow> 
  fst ` (privates (gen_constr t a ts)) \<subseteq> {(t, a)})\<close>

definition \<open>gen_constr_spec \<longleftrightarrow> inv_gen_constr \<and> ge_gen_constr \<and> privs_constr\<close>

end

locale Factored_MDP_gen_constr = Factored_MDP_gen_constr_Consts +
  Factored_MDP_Default +
  Constr_API

locale ValueDet_API_Consts' =
  Factored_MDP_gen_constr_Consts where rewards = rewards and privates = privates for
  privates :: "'c \<Rightarrow> ((('x::{countable, linorder} state \<times> 'a::{countable, linorder}) \<times> bool)) set" and
  rewards :: "'a \<Rightarrow> nat \<Rightarrow> 'x state \<Rightarrow> real" + 
fixes
  dec_pol :: \<open>('x state \<times> 'a) list\<close> 
begin
definition \<open>dec_pol_spec \<longleftrightarrow> fst ` set dec_pol \<subseteq> partial_states \<and> snd ` set dec_pol \<subseteq> actions \<and> distinct dec_pol \<and>
  (\<forall>x \<in> states. \<exists>y \<in> fst ` set dec_pol. consistent x y)\<close>
lemmas refl[of dec_pol_spec, cong]

definition \<open>update_weights_iter = (\<lambda>(t, a) (ts, cs). (t#ts, union_constr (gen_constr t a ts) cs))\<close>
lemmas refl[of update_weights_iter, cong]

definition \<open>constrs_list xs = snd (fold update_weights_iter xs ([], empty_constr))\<close>
lemmas refl[of constrs_list, cong]

definition \<open>constrs = constrs_list dec_pol\<close>
lemmas refl[of constrs, cong]
end

locale ValueDet_API_Consts = 
  ValueDet_API_Consts' +
  fixes
  min_sol :: \<open>real \<times> (nat \<Rightarrow> real)\<close>
begin

definition \<open>update_weights = snd min_sol\<close>
lemmas refl[of update_weights, cong]
end

locale ValueDet_API' = 
  ValueDet_API_Consts' +
  Factored_MDP_gen_constr +
  assumes
    gen_constr_correct: gen_constr_spec and
    dec_pol_spec: dec_pol_spec
begin

lemma privates_gen_constr: \<open>(a \<in> actions \<Longrightarrow> t \<in> partial_states \<Longrightarrow> set ts \<subseteq> partial_states \<Longrightarrow> 
  fst ` (privates (gen_constr t a ts)) \<subseteq> {(t, a)})\<close>
  using gen_constr_correct gen_constr_spec_def privs_constr_def by blast

lemma privates_gen_constr': \<open>(a \<in> actions \<Longrightarrow> t \<in> partial_states \<Longrightarrow> set ts \<subseteq> partial_states \<Longrightarrow> 
  (privates (gen_constr t a ts)) \<subseteq> {(((t, a), pos)) | pos. True})\<close>
  using privates_gen_constr[of a t ts]
  by fastforce+

lemma constrs_list_nil[simp]: \<open>constrs_list [] = empty_constr\<close>
  unfolding constrs_list_def
  by auto

lemma inv_gen_constrI[intro!]:
  assumes 
    \<open>t \<in> partial_states\<close> 
    \<open>set ts \<subseteq> partial_states\<close> 
    \<open>a \<in> actions\<close>
  shows 
    \<open>inv_constr (gen_constr t a ts)\<close>
  using assms gen_constr_correct gen_constr_spec_def inv_gen_constr_def by blast

lemma privates_fstD: \<open>x \<in> privates cs \<Longrightarrow> fst x \<in> fst ` privates cs\<close>
  by auto

lemma privates_fstD': \<open>(x,y) \<in> privates cs \<Longrightarrow> x \<in> fst ` privates cs\<close>
  by force

lemma disj_priv_iff: \<open>disj_priv X Y \<longleftrightarrow> (privates X) \<inter> (privates Y) = {}\<close>
  unfolding disj_priv_def disjnt_iff by auto

lemma disj_priv_gen_constr:
  assumes 
    \<open>t \<in> partial_states\<close> 
    \<open>set ts \<subseteq> partial_states\<close> 
    \<open>a \<in> actions\<close> 
    \<open>\<And>pos. (((t, a), pos)) \<notin> privates X\<close>
    \<open>inv_constr X\<close> 
  shows \<open>disj_priv (gen_constr t a ts) X\<close>
  unfolding disj_priv_iff
  using assms privates_gen_constr'[of a t ts]
  by auto

lemma inv_update_weights_iter: 
  assumes 
    \<open>t \<in> partial_states\<close> 
    \<open>set (fst tscs) \<subseteq> partial_states\<close> 
    \<open>a \<in> actions\<close> 
    \<open>\<And>pos p. (((t, a), pos)) \<notin> privates (snd tscs)\<close>
    \<open>inv_constr (snd tscs)\<close> 
  shows
    \<open>inv_constr (snd (update_weights_iter (t, a) tscs))\<close>
  using assms
  by (auto simp: update_weights_iter_def case_prod_unfold intro!: disj_priv_gen_constr)

lemma privs_update_weights_iter: 
  assumes 
    \<open>t \<in> partial_states\<close> 
    \<open>set (fst tscs) \<subseteq> partial_states\<close> 
    \<open>a \<in> actions\<close>
    \<open>\<And>pos p. (((t, a), pos)) \<notin> privates (snd tscs)\<close>
    \<open>inv_constr (snd tscs)\<close>
  shows
    \<open>privates (snd (update_weights_iter (t, a) tscs)) \<subseteq> {(((t, a), pos)) | pos. True} \<union> (privates (snd tscs))\<close>
  using assms privates_gen_constr'[of a t \<open>fst tscs\<close>]  
  unfolding update_weights_iter_def
  by (auto simp: case_prod_unfold inv_gen_constrI disj_priv_gen_constr)
 
lemma set_fst_fold_update_weights_iter[simp]:
  \<open>set (fst (fold update_weights_iter xs tscs)) = fst ` set xs \<union> set (fst tscs)\<close>
  by (induction xs arbitrary: tscs ) (auto simp: update_weights_iter_def case_prod_unfold)

lemma fst_fold_update_weights_iter[simp]: 
  \<open>(fst (fold update_weights_iter xs tscs)) = rev (map fst xs) @ (fst tscs)\<close>
  by (induction xs arbitrary: tscs ) (auto simp: update_weights_iter_def case_prod_unfold)

lemma fold_update_weights_iter: 
  assumes 
    \<open>set ts \<subseteq> partial_states\<close> 
    \<open>inv_constr cs\<close>
    \<open>fst ` set xs \<subseteq> partial_states\<close>
    \<open>snd ` set xs \<subseteq> actions\<close>
    \<open>distinct xs\<close>
    \<open>disjnt (set xs) (fst ` (privates cs))\<close>
  shows 
    \<open>((privates (snd (fold update_weights_iter xs (ts, cs)))) \<subseteq> {((ta, pos)) | ta pos. ta \<in> set xs} \<union> (privates cs)) \<and>
    inv_constr (snd (fold update_weights_iter xs (ts, cs)))\<close>
  using assms
proof (induction xs arbitrary: ts cs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have **: \<open>(privates (snd (fold update_weights_iter xs (ts, cs)))) \<subseteq> {((ta, pos)) | ta pos p. ta \<in> set xs} \<union> (privates cs)\<close>
    using snoc by auto
  have *: \<open>inv_constr (snd (fold update_weights_iter xs (ts, cs)))\<close>
    using snoc by auto
  show ?case
  proof (safe, goal_cases)
    case (1 a b ba )
    then show ?case
      using * ** privs_update_weights_iter[of \<open>fst x\<close> \<open>(fold update_weights_iter xs (ts, cs))\<close> \<open>snd x\<close>] snoc.prems
      by (auto simp: dest: privates_fstD')
     
  next
    case 2
    then show ?case
      using snoc.prems * **
      by (cases x) (auto simp: dest: privates_fstD' intro!: inv_update_weights_iter)+
  qed
qed

lemma inv_constr_fold_update_weights_iter: 
  \<open>set ts \<subseteq> partial_states \<Longrightarrow> 
  inv_constr cs \<Longrightarrow> 
  distinct xs \<Longrightarrow>
  disjnt (set xs) (fst ` (privates cs)) \<Longrightarrow>
  fst ` set xs \<subseteq> partial_states \<Longrightarrow> 
  snd ` set xs \<subseteq> actions \<Longrightarrow> 
  inv_constr (snd (fold update_weights_iter xs (ts, cs)))\<close>
  using fold_update_weights_iter  by auto

lemma privs_fold_update_weights_iter: \<open>
  set ts \<subseteq> partial_states \<Longrightarrow> 
  inv_constr cs \<Longrightarrow> 
  distinct xs \<Longrightarrow>
  disjnt (set xs) (fst ` (privates cs)) \<Longrightarrow>
  fst ` set xs \<subseteq> partial_states \<Longrightarrow> 
  snd ` set xs \<subseteq> actions \<Longrightarrow>
 (privates (snd (fold update_weights_iter xs (ts, cs)))) \<subseteq> {((ta, pos)) | ta pos. ta \<in> set xs} \<union> (privates cs)\<close>
  using fold_update_weights_iter by auto

lemma privates_empty[simp]: \<open>privates empty_constr = {}\<close>
  using empty_constr_spec empty_constr_spec_def by blast

lemma \<open>
  distinct xs \<Longrightarrow> 
  fst ` set xs \<subseteq> partial_states \<Longrightarrow> 
  snd ` set xs \<subseteq> actions \<Longrightarrow> 
  inv_constr (constrs_list xs)\<close>
  unfolding constrs_list_def
  by (auto intro!: inv_constr_fold_update_weights_iter )

lemma privates_gen_constrD: \<open>
  x \<in> privates (gen_constr t a ts) \<Longrightarrow> 
  a \<in> actions \<Longrightarrow> 
  t \<in> partial_states \<Longrightarrow> 
  set ts \<subseteq> partial_states \<Longrightarrow> 
  fst (x) = (t, a)\<close>
  using privates_gen_constr by blast

lemma set_snd_upd_weights_iter:
  assumes 
    \<open>inv_constr (snd xscs)\<close> 
    \<open>fst ta \<in> partial_states\<close> 
    \<open>snd ta \<in> actions\<close> 
    \<open>set (fst xscs) \<subseteq> partial_states\<close>
    \<open>\<And>pos p. ((ta, pos)) \<notin> privates (snd xscs)\<close>
  shows \<open>constr_set (snd (update_weights_iter ta xscs)) = 
      constr_set (gen_constr (fst ta) (snd ta) (fst xscs)) \<inter> constr_set (snd xscs)\<close>
  unfolding update_weights_iter_def
  using assms
  by (auto simp: case_prod_unfold inv_gen_constrI disj_priv_gen_constr)

lemma constrs_list_snoc:
  assumes 
    \<open>fst ` set xs \<subseteq> partial_states\<close> 
    \<open>distinct xs\<close> 
    \<open>snd ` set xs \<subseteq> actions\<close> 
    \<open>a \<in> actions\<close> 
    \<open>t \<in> partial_states\<close> 
    \<open>(t, a) \<notin> set xs\<close>
  shows 
    \<open>constr_set (constrs_list (xs @ [(t, a)])) = 
  constr_set (gen_constr t a (map fst xs)) \<inter> constr_set (constrs_list xs)\<close>
proof -
  have \<open>constr_set (constrs_list (xs @ [(t, a)])) = 
  constr_set (snd (update_weights_iter (t, a) (fold update_weights_iter xs ([], empty_constr))))\<close>
    unfolding constrs_list_def by simp
  also have \<open>\<dots> = constr_set (gen_constr t a (rev (map fst xs))) \<inter> constr_set (constrs_list xs)\<close>
    using privs_fold_update_weights_iter[of "[]" empty_constr xs] assms 
    by (subst set_snd_upd_weights_iter) (auto simp: constrs_list_def inv_constr_fold_update_weights_iter)
  also have \<open>\<dots> = constr_set (gen_constr t a (map fst xs)) \<inter> constr_set (constrs_list xs)\<close>
    using assms ge_gen_constr_def gen_constr_correct gen_constr_spec_def 
    by auto
  finally show ?thesis .
qed

lemma constrs_list_snoc':
  assumes 
    \<open>fst ` set xs \<subseteq> partial_states\<close> 
    \<open>distinct xs\<close> 
    \<open>snd ` set xs \<subseteq> actions\<close> 
    \<open>a \<in> actions\<close> 
    \<open>t \<in> partial_states\<close> 
    \<open>(t, a) \<notin> set xs\<close>
  shows 
    \<open>(\<phi>, w) \<in> constr_set (constrs_list (xs @ [(t, a)])) \<longleftrightarrow>
  (\<phi>, w) \<in> constr_set (gen_constr t a (map fst xs)) \<inter> constr_set (constrs_list xs)\<close>
  using assms constrs_list_snoc 
  by blast

lemma gen_constr_set:
  assumes \<open>set xs \<subseteq> partial_states\<close> \<open>a \<in> actions\<close> \<open>t \<in> partial_states\<close>
  shows 
    \<open>constr_set (gen_constr t a xs) = 
    {(\<phi>, w). 
    (\<forall>x \<in> {x. x \<in> states \<and> consistent x t}.
    (list_all (\<lambda>j. \<not>consistent x j) xs) \<longrightarrow>
        \<phi> \<ge> \<bar>reward a x + (\<Sum>j < h_dim. w j * (l * g j a x - h j x))\<bar>)}\<close>
  using gen_constr_correct[unfolded gen_constr_spec_def ge_gen_constr_def] assms
  by auto


lemma gen_constr_set':
  assumes \<open>set xs \<subseteq> partial_states\<close> \<open>a \<in> actions\<close> \<open>t \<in> partial_states\<close>
  shows 
    \<open>(\<phi>, w) \<in> constr_set (gen_constr t a xs) = 
    (\<forall>x \<in> {x. x \<in> states \<and> consistent x t}.
    (list_all (\<lambda>j. \<not>consistent x j) xs) \<longrightarrow>
        \<phi> \<ge> \<bar>reward a x + (\<Sum>j < h_dim. w j * (l * g j a x - h j x))\<bar>)\<close>
  using gen_constr_correct[unfolded gen_constr_spec_def ge_gen_constr_def] assms
  by auto

lemma in_constrs_list_iff:
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> \<open>distinct xs\<close>
  shows \<open>(\<phi>, w) \<in> constr_set (constrs_list xs) \<longleftrightarrow>
    (\<forall>i < length xs. \<forall>x \<in> {x. x \<in> states \<and> consistent x (fst (xs ! i))}.
      (\<forall>j<i. \<not>consistent x (fst (xs ! j))) \<longrightarrow>
        \<phi> \<ge> \<bar>reward (snd (xs ! i)) x + (\<Sum>j < h_dim. w j * (l * g j (snd (xs ! i)) x - h j x))\<bar>)
    \<close>
  using assms
proof (induction xs rule: rev_induct)
  case (snoc a xs)
  then show ?case
    by (cases a) (auto simp add: 
        constrs_list_snoc' gen_constr_set' list_all_length All_less_Suc nth_append)
qed auto

lemma in_constrs_list_iff':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> \<open>distinct xs\<close>
  shows \<open>(\<phi>, w) \<in> constr_set (constrs_list xs) \<longleftrightarrow>
    (\<forall>i < length xs. \<forall>x \<in> {x. x \<in> states \<and> consistent x (fst (xs ! i))}.
      (\<forall>j<i. \<not>consistent x (fst (xs ! j))) \<longrightarrow>
        \<phi> \<ge> \<bar>Q w x (snd (xs ! i)) - \<nu>\<^sub>w w x\<bar>)
    \<close>
  using assms in_constrs_list_iff[OF assms] sum_subtractf sum_distrib_left states_imp_partial
  by (auto simp: \<nu>\<^sub>w_def algebra_simps G\<^sub>a_g Q_def sum_subtractf sum_distrib_left)

lemma in_constrs_list_iff'':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> \<open>distinct xs\<close>
  shows \<open>(\<phi>, w) \<in> constr_set (constrs_list xs) \<longleftrightarrow> (\<forall>x \<in> states.
  
    (\<forall>i < length xs. consistent x (fst (xs ! i)) \<longrightarrow>
      (\<forall>j<i. \<not>consistent x (fst (xs ! j))) \<longrightarrow>
        \<phi> \<ge> \<bar>Q w x (snd (xs ! i)) - \<nu>\<^sub>w w x\<bar>))
    \<close>
  using assms in_constrs_list_iff'[OF assms]
  by auto

lemma in_constrs_list_iff''':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> \<open>distinct xs\<close>
    \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>(\<phi>, w) \<in> constr_set (constrs_list xs) \<longleftrightarrow> (\<forall>x \<in> states.
        \<phi> \<ge> \<bar>Q w x (dec_list_to_pol xs x) - \<nu>\<^sub>w w x\<bar>)
    \<close>
proof (safe, goal_cases)
  case (1 x)

  obtain i where i: \<open>(find (\<lambda>(t, a). consistent x t) xs) = Some (xs ! i)\<close> \<open>i < length xs\<close>
    \<open>(\<forall>j<i. \<not> consistent x (fst (xs ! j)))\<close>
    \<open>consistent x (fst (xs ! i))\<close>
    apply (cases \<open>(find (\<lambda>(t, a). consistent x t) xs)\<close>)
    using Some_ex_find_iff assms(4)[of x] 1
    by (auto simp: find_None_iff find_Some_iff case_prod_unfold)
 
  then show ?case
    using 1 assms i
    unfolding in_constrs_list_iff''[OF assms(1,2,3)] dec_list_to_pol_def
    by auto
next
  case 2
  
  hence 3: \<open>\<bar>Q w x (dec_list_to_pol xs x) - \<nu>\<^sub>w w x\<bar> \<le> \<phi>\<close> if \<open>x \<in> states\<close> for x
    using that by auto
   
  have *: \<open>\<exists>i. (find (\<lambda>(t, a). consistent x t) xs) = Some (xs ! i) \<and> i < length xs \<and> 
    (\<forall>j<i. \<not> consistent x (fst (xs ! j))) \<and> consistent x (fst (xs ! i))\<close> if \<open>x \<in> states\<close> for x
    using Some_ex_find_iff assms(4)[of x] that
    by (cases \<open>(find (\<lambda>(t, a). consistent x t) xs)\<close>) (auto simp: find_None_iff find_Some_iff case_prod_unfold)

  have 4: \<open>i<length xs \<Longrightarrow> consistent x (fst (xs ! i)) \<Longrightarrow> (\<forall>j<i. \<not> consistent x (fst (xs ! j))) \<Longrightarrow> \<bar>Q w x (snd (xs ! i)) - \<nu>\<^sub>w w x\<bar> \<le> \<phi>\<close>
    if \<open>x \<in> states \<close>for i x
    using *[of x] 3[of x] that 
    unfolding dec_list_to_pol_def
    by (auto simp: not_less_iff_gr_or_eq) (metis linorder_neqE_nat)
    
  thus ?case
    unfolding in_constrs_list_iff''[OF assms(1,2,3)]
    by auto
qed

lemma is_policy_dec_list_to_pol:
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> 
    \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>is_policy (dec_list_to_pol xs)\<close>
proof -
  have \<open>dec_list_to_pol xs x \<in> actions\<close> if \<open>x \<in> states\<close> for x
    unfolding dec_list_to_pol_def
    using  assms that
    by (cases \<open>find (\<lambda>(t, a). consistent x t) xs\<close>) 
      (force simp: comp_def subset_iff image_iff find_None_iff dest: find_Some_in_set)+
  thus ?thesis
    unfolding is_policy_def 
    by auto
qed

lemma in_constrs_list_iff'''':
  assumes 
    \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> \<open>distinct xs\<close>
    \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close> 
  shows 
    \<open>(\<phi>, w) \<in> constr_set (constrs_list xs) \<longleftrightarrow> \<phi> \<ge> proj_err_w (dec_list_to_pol xs) w\<close>
  using proj_err_w_factored assms is_policy_dec_list_to_pol states_ne fin_states
  by (subst in_constrs_list_iff'''[OF assms]) (auto intro!: cSUP_least simp: dist_real_def cSUP_le_iff)

lemma in_constrs_iff:
  shows  \<open>(\<phi>, w) \<in> constr_set constrs \<longleftrightarrow> \<phi> \<ge> proj_err_w (dec_list_to_pol dec_pol) w\<close>
  unfolding constrs_def
  using dec_pol_spec dec_pol_spec_def
  by (intro in_constrs_list_iff'''') auto

lemma proj_err_pol_eq_w: 
  assumes \<open>is_policy p\<close> \<open>\<And>w'. proj_err_w p w \<le> proj_err_w p w'\<close>
  shows \<open>proj_err_pol p = proj_err_w p w\<close>
  unfolding proj_err_pol_def
  using assms
  by (auto intro!: bdd_belowI cINF_lower antisym cINF_greatest)

lemma distinct_dec_pol: \<open>distinct dec_pol\<close>
  using dec_pol_spec dec_pol_spec_def by blast

lemma inv_constrs: \<open>inv_constr constrs\<close>
  using constrs_def constrs_list_def dec_pol_spec dec_pol_spec_def 
  by (auto intro!: inv_constr_fold_update_weights_iter)

lemma norm_blinfun_scaleR_right: \<open>norm ((f :: _ \<Rightarrow>\<^sub>L _) (c *\<^sub>R v)) = \<bar>c\<bar> * norm (f v)\<close>
  by (subst blinfun.scaleR_right) auto

lemma proj_err_w_eq_norm: \<open>is_policy p \<Longrightarrow> proj_err_w p w = 
  norm ((id_blinfun - l *\<^sub>R E.\<P>\<^sub>1 (E.mk_dec_det (expl_pol p))) (\<nu>\<^sub>w_expl w) - E.r_dec\<^sub>b (E.mk_dec_det (expl_pol p)))\<close>
  using dist_norm 
  by (auto simp: E.L_def proj_err_w_eq blinfun.diff_left blinfun.scaleR_left algebra_simps)

lemma proj_err_0_le: \<open>is_policy p \<Longrightarrow> proj_err_w p (\<lambda>_. 0) \<le> reward_bound\<close> 
  using fin_states actions_fin reward_bound
  by (subst proj_err_w_eq) 
    (auto simp: r\<^sub>M_factored actions_ne states_ne intro!: order.trans[OF E.norm_r_dec_le] cSUP_least)

lemma proj_err_w_le: \<open>is_policy p \<Longrightarrow> \<exists>w. proj_err_w p w \<le> reward_bound\<close>
  using proj_err_0_le
  by auto

end

locale ValueDet_API = 
  ValueDet_API' +
    ValueDet_API_Consts +
assumes
    minimize_spec: \<open>is_arg_min' constrs min_sol\<close>
begin

lemma minimize_spec_eq:
  assumes \<open>inv_constr constrs\<close> \<open>(\<phi>, w) \<in> constr_set constrs\<close> \<open>(\<And>\<phi>' w'. (\<phi>', w') \<in> constr_set constrs \<longrightarrow> \<phi> \<le> \<phi>')\<close>
  shows\<open>\<And>\<phi>. \<phi> \<in> fst ` constr_set constrs \<Longrightarrow> fst min_sol \<le> \<phi>\<close> \<open>min_sol \<in> constr_set constrs\<close>
  using minimize_spec assms
  by (auto simp: case_prod_unfold Let_def is_arg_min'_def)

lemma minimize_spec_fst:
  assumes \<open>inv_constr constrs\<close> \<open>(\<phi>, w) \<in> constr_set constrs\<close> \<open>(\<And>\<phi>' w'. (\<phi>', w') \<in> constr_set constrs \<Longrightarrow> \<phi> \<le> \<phi>')\<close>
  shows\<open>fst (min_sol) = \<phi>\<close>
  using assms minimize_spec_eq[of \<phi> w] 
  by (fastforce simp: image_iff intro!: antisym intro!: assms(3)[of \<open>fst min_sol\<close> \<open>snd min_sol\<close>])

lemma fst_minimize_constrs:
  shows
    \<open>fst (min_sol) = proj_err_pol (dec_list_to_pol dec_pol)\<close> and
    \<open>fst (min_sol) = proj_err_w (dec_list_to_pol dec_pol) (snd (min_sol))\<close>
proof goal_cases
  obtain \<phi>_opt 
      where *: \<open>\<And>\<phi> w. proj_err_w (dec_list_to_pol dec_pol) w \<ge> \<phi>_opt\<close>
      and **: \<open>\<exists>w. proj_err_w (dec_list_to_pol dec_pol) w = \<phi>_opt\<close>
    using proj_err_w_min_ex
    by (metis dec_pol_spec dec_pol_spec_def is_policy_dec_list_to_pol)

  hence \<open>\<exists>w_opt. (\<phi>_opt, w_opt) \<in> constr_set constrs\<close> 
    by (subst in_constrs_iff) auto
  then obtain w_opt where ***: \<open>(\<phi>_opt, w_opt) \<in> constr_set constrs\<close>
    by auto

  have 4: \<open>(\<phi>', w') \<in> constr_set constrs \<longrightarrow> \<phi>_opt \<le> \<phi>'\<close> for \<phi>' w'
    using * ** order.trans in_constrs_iff by blast

  hence fst_opt[simp]: \<open>fst (min_sol) = \<phi>_opt\<close>
    using minimize_spec_fst inv_constrs *** by auto
  hence \<open>fst (min_sol) = proj_err_pol (dec_list_to_pol dec_pol)\<close>
    by (metis "*" "**" dec_pol_spec dec_pol_spec_def is_policy_dec_list_to_pol proj_err_pol_eq_w)
  case 1
  then show ?case
    using \<open>fst (min_sol) = proj_err_pol (dec_list_to_pol dec_pol)\<close>
    by blast
  case 2
  then show ?case
    using * "***" fst_opt inv_constrs minimize_spec_eq(2) in_constrs_iff
    by (smt (verit, best) prod.collapse)
qed

lemma proj_err_upd_eq_pol: \<open>proj_err_w (dec_list_to_pol dec_pol) update_weights = 
  proj_err_pol (dec_list_to_pol dec_pol)\<close>
  using fst_minimize_constrs  update_weights_def 
  by force
end
end