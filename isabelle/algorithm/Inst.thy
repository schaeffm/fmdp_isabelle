section \<open>Linear Program for a Single Branch\<close>
theory Inst
  imports 
    ValueDet
    Constr
begin

locale Process_Branch_Consts =
  Constr_Consts where privates = privates +
  Factored_MDP_Default_Consts where rewards = rewards
for
  privates :: \<open>'c \<Rightarrow> ((('x::{countable, linorder} state \<times> 'a::{countable, linorder}) \<times> bool)) set\<close> and
  rewards :: \<open>'a \<Rightarrow> nat \<Rightarrow> ('x state) \<Rightarrow> real\<close> +
fixes
  t :: \<open>'x state\<close> and
  a :: \<open>'a\<close> and
  ts :: \<open>'x state list\<close> and
  factored_lp :: \<open>
      bool \<Rightarrow>
      (('x state \<Rightarrow> real) \<times> (nat set)) list \<Rightarrow> \<comment> \<open>C\<close>
      (('x state \<Rightarrow> ereal) \<times> (nat set)) list \<Rightarrow> \<comment> \<open>b\<close>
      'c\<close>
begin

text \<open>
Here we define the specification of the Factored LP algorithm: 
- it needs to create a set of constraints that minimize |(Cw + b)x| over all states x 
- the private variables that are created are of the form @{term \<open>((t, a), pos)\<close>} 
\<close>
definition \<open>factored_lp_constrs pos C b \<longleftrightarrow>
 constr_set (factored_lp pos C b) = {(\<phi>, w). \<forall>x \<in> states. 
    ereal \<phi> \<ge> ereal (\<Sum>i < length C. w i * (fst (C ! i) x)) + (\<Sum>i < length b. fst (b ! i) x)}\<close>

definition \<open>factored_lp_inv pos C b \<longleftrightarrow>
 inv_constr (factored_lp pos C b)\<close>

definition \<open>factored_lp_privs pos C b \<longleftrightarrow>
 privates (factored_lp pos C b) \<subseteq> {((t, a), pos)}\<close>

definition \<open>inv_b b \<longleftrightarrow>
  (\<forall>(b, scope_b) \<in> set b. has_scope_on b partial_states scope_b \<and> scope_b \<subseteq> vars \<and> (\<forall>x. b x \<noteq> \<infinity>))\<close>

definition \<open>inv_C b \<longleftrightarrow>
  (\<forall>(b, scope_b) \<in> set b. has_scope_on b partial_states scope_b \<and> scope_b \<subseteq> vars)\<close>

definition \<open>factored_lp_spec \<longleftrightarrow>
  (\<forall>pos C b. inv_C C \<longrightarrow> inv_b b \<longrightarrow>
  factored_lp_constrs pos C b \<and> factored_lp_inv pos C b \<and> factored_lp_privs pos C b)\<close>

definition \<open>instantiate f t' x = (f (x++t'))\<close>

definition \<open>neg_scoped = (\<lambda>(f, s). (-f, s))\<close>

\<comment> \<open>the functions h - l * g, instantiated with t become C\<close>
definition \<open>hg_scope i = h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i) - dom t\<close>
definition \<open>hg_inst i = instantiate (\<lambda>x. h i x - l * g' i a x) t\<close>

definition \<open>C = (map (\<lambda>i. (hg_inst i, hg_scope i)) [0..<h_dim])\<close>
definition \<open>neg_C = map neg_scoped C\<close>

\<comment> \<open>the function @{term \<open>r - \<I>\<close>} becomes @{term b}\<close>
definition \<open>r_act_dim = reward_dim a - reward_dim d\<close>

definition \<open>r_scope i = reward_scope a i - dom t\<close>
definition \<open>r_inst i = instantiate (rewards a i) t\<close>

definition \<open>b = (map (\<lambda>i. (r_inst i, r_scope i)) [0..<reward_dim a])\<close>
definition \<open>neg_b = map neg_scoped b\<close>

definition \<open>\<I> t' x = (if consistent x t' then -\<infinity>::ereal else 0)\<close>

definition \<open>\<I>' = map (\<lambda>t'. (instantiate (\<I> t') t, dom t' - dom t)) ts\<close>
definition \<open>scope_\<I>' = \<Union>(set (map snd (\<I>')))\<close>
definition \<open>b' = b @  \<I>'\<close>

definition \<open>neg_b' = neg_b @ \<I>'\<close>

\<comment> \<open>Create factored LPs for (C - b) and -(C - b), effectively minimizing the absolute value of C - b\<close>
definition \<open>\<Omega>_pos = factored_lp True C neg_b'\<close>
definition \<open>\<Omega>_neg = factored_lp False neg_C b'\<close>
definition \<open>\<Omega> = union_constr \<Omega>_pos \<Omega>_neg\<close>
lemmas refl[of \<Omega>, cong]
end

locale Process_Branch =
  Process_Branch_Consts +
  Factored_MDP_Default +
  Constr_API +
  assumes
    factored_lp_spec: \<open>factored_lp_spec\<close> and
    t: \<open>t \<in> partial_states\<close> and
    a: \<open>a \<in> actions\<close> and
    ts: \<open>set ts \<subseteq> partial_states\<close>
begin
lemma not_consistent_\<I>[simp]: \<open>\<not>consistent x t' \<Longrightarrow> \<I> t' x = 0\<close>
  unfolding \<I>_def by auto

lemma consistent_\<I>[simp]: \<open>consistent x t' \<Longrightarrow> \<I> t' x = -\<infinity>\<close>
  unfolding \<I>_def by auto

lemma scope_\<I>'_eq: \<open>scope_\<I>' = (\<Union>t \<in> set ts. dom t) - dom t\<close>
  by (auto simp: \<I>'_def scope_\<I>'_def)

lemma factored_lp_set:
  fixes Cs :: \<open>(((nat \<Rightarrow> 'b option) \<Rightarrow> real) \<times> nat set) list\<close>
  assumes
    \<open>inv_C (Cs :: (((nat \<Rightarrow> 'b option) \<Rightarrow> real) \<times> nat set) list)\<close>
    \<open>inv_b (bs :: (((nat \<Rightarrow> 'b option) \<Rightarrow> ereal) \<times> nat set) list)\<close>
  shows \<open>constr_set (factored_lp pos Cs bs) =
     {(\<phi>, w). \<forall>x\<in>states. ereal (\<Sum>i<length Cs. w i * fst (Cs ! i) x) + (\<Sum>i<length bs. fst (bs ! i) x) \<le> \<phi>}\<close>
  using assms factored_lp_spec unfolding factored_lp_spec_def factored_lp_constrs_def
  by auto

lemmas instantiate_def[simp]

lemma consistent_add[simp]: \<open>consistent x t' \<Longrightarrow> x ++ t' = x\<close>
  unfolding consistent_def by (metis map_add_restr')

lemma map_add_eq_iff: \<open>((m ++ t') i = (m' ++ t') i) \<longleftrightarrow> (i \<in> dom t' \<or> (m i = m' i))\<close>
  by (auto split: option.splits simp: map_add_def)

lemma has_scope_on_instantiate: 
  \<open>(\<And>d. d \<in> D \<Longrightarrow> d ++ t' \<in> D) \<Longrightarrow> 
  has_scope_on f D (R \<union> dom t') \<Longrightarrow> 
  has_scope_on (instantiate f t') D (R - dom t')\<close>
  apply (intro has_scope_onI)
  apply (drule has_scope_on_eq)
  by (auto simp: map_add_eq_iff)

lemma has_scope_on_instantiateI: 
  \<open>t' \<in> partial_states \<Longrightarrow> 
  R \<subseteq> vars \<Longrightarrow> 
  has_scope_on f partial_states (R \<union> dom t') \<Longrightarrow> 
  has_scope_on (instantiate f t') partial_states R\<close>
  apply (rule has_scope_on_subs[of _ _  \<open>R - dom t'\<close> R])
   apply (rule has_scope_on_instantiate)
  by blast+

lemma has_scope_on_addI: 
  \<open>t' \<in> partial_states \<Longrightarrow> 
  R \<subseteq> vars \<Longrightarrow> 
  has_scope_on f partial_states (R \<union> dom t') \<Longrightarrow> 
  has_scope_on (\<lambda>x. f (x ++ t')) partial_states R\<close>
  apply (intro has_scope_onI)
  apply (drule has_scope_on_eq)
  by (auto simp: map_add_eq_iff) blast+

lemma snd_neg_scoped [simp]: \<open>snd (neg_scoped fs) = snd fs\<close>
  unfolding neg_scoped_def by (auto simp: case_prod_unfold)

lemma fst_neg_scoped [simp]: \<open>fst (neg_scoped fs) = -fst fs\<close>
  unfolding neg_scoped_def by (auto simp: case_prod_unfold)

lemma scope_inv_C: \<open>inv_C C\<close>
  unfolding inv_C_def C_def hg_inst_def hg_scope_def 
  using scope_g' \<Gamma>\<^sub>a_D2 h_scope_dims t a
  by (auto intro!: has_scope_on_compose[of _ _ _ ereal] has_scope_on_addI has_scope_on_diff 
      has_scope_on_scale has_scope_on_instantiateI)+

lemma scope_inv_neg_C: \<open>inv_C neg_C\<close>
  using scope_inv_C
  unfolding neg_C_def inv_C_def neg_scoped_def
  by (auto simp: case_prod_unfold simp flip: uminus_ereal.simps(1) intro!: has_scope_on_compose[of _ _ _ \<open>\<lambda>x. - x\<close>]) 

lemma has_scope_on_if:
  assumes \<open>has_scope_on fb X R\<close> \<open>has_scope_on f1 X R\<close> \<open>has_scope_on f2 X R\<close>
  shows \<open>has_scope_on (\<lambda>x. if fb x then f1 x else f2 x) X R\<close>
  using assms unfolding has_scope_on_def
  by metis

lemma has_scope_on_consistent: \<open>
  dom t' \<subseteq> X \<Longrightarrow> 
  t' \<in> partial_states \<Longrightarrow> 
  has_scope_on (\<lambda>x. consistent x t') partial_states X\<close>
  by (auto intro!: has_scope_onI simp: consistent_iff in_mono domI)

lemma scope_inv_b': \<open>inv_b b'\<close>
  using t a ts
  unfolding b'_def inv_b_def b_def r_inst_def r_scope_def \<I>'_def \<I>_def
  by (auto intro!: has_scope_on_compose[of _ _ _ ereal] has_scope_on_addI has_scope_on_consistent split: if_splits)+

lemma scope_inv_neg_b': \<open>inv_b neg_b'\<close>
  using t a ts
  using scope_inv_b'
  unfolding neg_b'_def neg_b_def b'_def inv_b_def b_def r_inst_def r_scope_def
  by (auto intro!: has_scope_on_compose[of _ _ _ ereal] has_scope_on_compose[of _ _ _ \<open>\<lambda>x. - x\<close>] has_scope_on_addI 
      simp: scope_rewardI reward_scopeD case_prod_unfold)
  
lemma sum_neg_infty: \<open>finite X \<Longrightarrow> (\<exists>y \<in> X. f y = (-\<infinity>::ereal)) \<Longrightarrow> (\<forall>y \<in> X. f y \<noteq> \<infinity>) \<Longrightarrow> sum f X = -\<infinity>\<close>
  by (induction X rule: finite_induct) (auto simp: sum_Pinfty)

lemma sum_\<I>'_eq: \<open>(\<Sum>p\<leftarrow>\<I>'. fst p x) = (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
  unfolding \<I>'_def \<I>_def
  by (force split: if_splits simp: sum_list_sum_nth in_set_conv_nth intro!: sum.neutral sum_neg_infty)

lemma sum_neg_b'_eq:
    \<open>(\<Sum>i<length neg_b'. fst (neg_b' ! i) x) = 
  -reward a (x ++ t) + (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
proof -
  have \<open>(\<Sum>i<length (neg_b'). fst (neg_b' ! i) x) = (\<Sum>b \<leftarrow> (neg_b'). fst b x)\<close>
    by (auto simp: sum_list_sum_nth atLeast0LessThan)
  also have \<open>\<dots> = (\<Sum>xa\<leftarrow>neg_b. fst xa x) + (\<Sum>p\<leftarrow>\<I>'. fst p x)\<close>
    unfolding neg_b'_def by (auto simp: comp_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>xa\<leftarrow>neg_b. fst xa x) + (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
    unfolding sum_\<I>'_eq ..
  finally show ?thesis
    unfolding neg_b_def neg_scoped_def b_def r_inst_def reward_def
    by (auto simp: interv_sum_list_conv_sum_set_nat atLeast0LessThan sum_negf)
qed

lemma sum_b'_eq:
  shows
    \<open>(\<Sum>i<length (b'). fst (b' ! i) x) = 
  reward a (x ++ t) + (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
proof -
  have \<open>(\<Sum>i<length (b'). fst (b' ! i) x) = (\<Sum>b \<leftarrow> b'. fst b x)\<close>
    by (auto simp: sum_list_sum_nth atLeast0LessThan)
  also have \<open>\<dots> = (\<Sum>xa\<leftarrow>b. fst xa x) + (\<Sum>p\<leftarrow>\<I>'. fst p x)\<close>
    unfolding b'_def by (auto simp: comp_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>xa\<leftarrow>b. fst xa x) + (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
    unfolding sum_\<I>'_eq ..
  finally show ?thesis
    unfolding b_def r_inst_def reward_def
    by (auto simp: interv_sum_list_conv_sum_set_nat atLeast0LessThan)
qed

lemma sum_C_eq: \<open>(\<Sum>i<length (C). (w i) * fst (C ! i) x) = 
  (\<Sum>j < h_dim. w j * (h j (x++t) - l * g' j a (x++t)))\<close>
  unfolding C_def hg_inst_def 
  by auto

lemma sum_neg_C_eq: \<open>(\<Sum>i<length (neg_C). (w i) * fst (neg_C ! i) x) = 
  - (\<Sum>j < h_dim. w j * (h j (x++t) - l * g' j a (x++t)))\<close>
  unfolding C_def neg_C_def neg_scoped_def hg_inst_def
  by (auto simp: sum_negf[symmetric] algebra_simps)

lemma states_add: \<open>
  x \<in> states \<Longrightarrow> 
  t' \<in> partial_states \<Longrightarrow> 
  x ++ t' \<in> states\<close>
  by blast

lemma consistent_addI: \<open>
  x \<in> states \<Longrightarrow> 
  t' \<in> partial_states \<Longrightarrow> 
  consistent (x ++ t') t'\<close>
  by auto

lemma P_add_iff: \<open>t' \<in> partial_states \<Longrightarrow> 
  (\<forall>x \<in> states. P (x ++ t')) \<longleftrightarrow> (\<forall>x \<in> {x. x \<in> states \<and> consistent x t'}. P x)\<close>
  using consistent_addI states_add by fastforce

lemma set_\<Omega>_pos_neg_ereal:
  shows \<open>constr_set (\<Omega>_pos) = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t}. 
      \<phi> \<ge> - reward a x + (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) + (if \<forall>t'\<in>set ts. \<not> consistent x t' then 0 else - \<infinity>)}\<close>
    \<open>constr_set (\<Omega>_neg) = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t}. 
      \<phi> \<ge> reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) + (if \<forall>t'\<in>set ts. \<not> consistent x t' then 0 else - \<infinity>)}\<close>
  unfolding \<Omega>_neg_def \<Omega>_pos_def
     using t a ts scope_inv_C scope_inv_neg_C scope_inv_b' scope_inv_neg_b'
     by (auto simp: g_restr factored_lp_set P_add_iff sum_b'_eq sum_neg_b'_eq sum_neg_C_eq sum_C_eq states_add 
      intro: consistent_addI)

lemma set_\<Omega>_pos_neg:
  shows \<open>constr_set (\<Omega>_pos) = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      \<phi> \<ge> -reward a x + (\<Sum>j < h_dim. w j * (h j x - l * g j a x))}\<close>
    \<open>constr_set (\<Omega>_neg) = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      \<phi> \<ge> reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x))}\<close>
  unfolding set_\<Omega>_pos_neg_ereal
  by auto

lemma set_\<Omega>_pos_neg':
  shows \<open>constr_set \<Omega>_pos = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      \<phi> \<ge> -reward a x - (\<Sum>j < h_dim. w j * (l * g j a x - h j x))}\<close>
    \<open>constr_set \<Omega>_neg = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      \<phi> \<ge> reward a x + (\<Sum>j < h_dim. w j * (l * g j a x - h j x))}\<close>
  unfolding set_\<Omega>_pos_neg
  by (auto simp: algebra_simps sum_subtractf)

lemma factored_lp_inv:
  assumes \<open>inv_C Cs\<close> \<open>inv_b bs\<close> 
  shows \<open>inv_constr (factored_lp pos Cs bs)\<close>
  using assms factored_lp_spec
  unfolding factored_lp_spec_def factored_lp_inv_def
  by auto

lemma inv_\<Omega>_pos_neg:
  shows \<open>inv_constr \<Omega>_pos\<close> \<open>inv_constr \<Omega>_neg\<close>
  unfolding \<Omega>_pos_def \<Omega>_neg_def
  using t t ts scope_inv_C scope_inv_neg_C scope_inv_neg_b' scope_inv_b'
  by (auto intro!: factored_lp_inv)

lemma privs_factored_lp: \<open>inv_C Cs \<Longrightarrow> inv_b bs \<Longrightarrow> 
  privates (factored_lp pos Cs bs) \<subseteq> {((t, a), pos)}\<close>
  using factored_lp_spec unfolding factored_lp_spec_def factored_lp_privs_def by auto

lemma privs_\<Omega>_pos_neg:
  shows \<open>privates (\<Omega>_pos) \<subseteq> {((t, a), True)}\<close> \<open>privates (\<Omega>_neg) \<subseteq> {((t, a), False)}\<close>
  unfolding \<Omega>_pos_def \<Omega>_neg_def
  using privs_factored_lp scope_inv_C scope_inv_neg_C scope_inv_b' scope_inv_neg_b'
  by auto

lemma disj_privs_\<Omega>_pos_neg:
  shows \<open>disj_priv (\<Omega>_pos) (\<Omega>_neg)\<close>
  using privs_\<Omega>_pos_neg
  by (fastforce simp: disj_priv_def disjnt_def)

lemma inv_\<Omega>:
  shows \<open>inv_constr \<Omega>\<close>
  unfolding \<Omega>_def
  using inv_\<Omega>_pos_neg privs_\<Omega>_pos_neg
  by (fastforce simp: disj_priv_def disjnt_def intro!: inv_constr_union)

lemma privs_\<Omega>:
  shows \<open>fst ` privates \<Omega> \<subseteq> {(t, a)}\<close>
  unfolding \<Omega>_def
  using inv_\<Omega>_pos_neg privs_\<Omega>_pos_neg
  by (subst privs_constr_union) (auto simp: disj_priv_def disjnt_def)

lemma \<Omega>_set_correct:
  shows \<open>constr_set \<Omega> = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      \<phi> \<ge> \<bar> reward a x + (\<Sum>j < h_dim. w j * (l * g j a x - h j x)) \<bar>}\<close>
  unfolding \<Omega>_def
  using inv_\<Omega>_pos_neg set_\<Omega>_pos_neg' disj_privs_\<Omega>_pos_neg
  by (auto intro!: abs_leI)

lemma \<Omega>_set_correct':
  shows \<open>constr_set \<Omega> = {(\<phi>, w). 
    \<forall>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      \<phi> \<ge> \<bar> Q w x a - \<nu>\<^sub>w w x \<bar>}\<close>
  unfolding \<Omega>_set_correct
  using states_imp_partial t a
  by (auto simp: Q_g \<nu>\<^sub>w_def algebra_simps sum_subtractf sum_distrib_left)
end

end