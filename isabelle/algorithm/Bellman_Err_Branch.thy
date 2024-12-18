theory Bellman_Err_Branch
  imports 
    Util 
    Factored_MDP_Util 
    Factored_MDP_Thy 
    Decision_List_Policy 
    Variable_Elim
begin

section \<open>Bellman Error of a Branch\<close>

locale Bellman_Err_Branch_Consts =
  Factored_MDP_Default_Consts
  where 
    rewards = rewards
  for
    rewards :: \<open>'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> ('x::{countable, linorder} state) \<Rightarrow> real\<close> +
  fixes
    variable_elim :: \<open>(('x state \<Rightarrow> ereal) \<times> (nat set)) list \<Rightarrow> ereal\<close>
    \<comment> \<open>Variable elimination algorithm, maximizes sum of input functions\<close>
begin

text \<open>Specification of the variable elimination algorithm.\<close>
definition \<open>variable_elim_correct fs \<longleftrightarrow> 
  variable_elim fs = (MAX x \<in> states. sum_list (map (\<lambda>(f, s). f x) fs))\<close>

text \<open>Valid input functions: don't take (positive) infinite values + scopes are valid.\<close>
definition \<open>scope_inv b \<longleftrightarrow> (\<forall>(b, scope_b) \<in> set b. 
  (\<forall>x. b x \<noteq> \<infinity>) \<and> scope_b \<subseteq> vars \<and> has_scope_on b partial_states scope_b)\<close>

definition \<open>scope_inv' b \<longleftrightarrow> (\<forall>(b, scope_b) \<in> set b. 
  (\<forall>x. b x \<noteq> -\<infinity> \<and> b x \<noteq> \<infinity>) \<and> scope_b \<subseteq> vars \<and> has_scope_on b partial_states scope_b)\<close>

definition \<open>variable_elim_spec \<longleftrightarrow> (\<forall>fs. scope_inv fs \<longrightarrow> variable_elim_correct fs)\<close>

text \<open>Apply part of a state to a function.\<close>
definition \<open>instantiate f t x = f (x ++ t)\<close>

text \<open>Function negation\<close>
definition \<open>neg_scoped = (\<lambda>(f, s). (-f, s))\<close>

text \<open>Functions to maximize that depend on the weights.\<close>
definition \<open>hg_scope t a i = h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i) - dom t\<close>
definition \<open>hg_inst w t a i = instantiate (\<lambda>x. w i * (h i x - l * g' i a x)) t\<close>

definition \<open>C w t a = (map (\<lambda>i. (hg_inst w t a i, hg_scope t a i)) [0..<h_dim])\<close>
definition \<open>neg_C w t a = map neg_scoped (C w t a)\<close>

text \<open>Functions to maximize that independent of the weights.\<close>
definition \<open>r_act_dim a = reward_dim a - reward_dim d\<close>

definition \<open>r_scope t a i = reward_scope a i - dom t\<close>
definition \<open>r_inst t a i = instantiate (rewards a i) t\<close>

definition \<open>b t a = (map (\<lambda>i. (r_inst t a i, r_scope t a i)) [0..<reward_dim a])\<close>
definition \<open>neg_b t a = map neg_scoped (b t a)\<close>

text \<open>Indicator functions that make us ignore states that choose earlier branches.\<close>
definition \<open>\<I> t x = (if consistent x t then -\<infinity>::ereal else 0)\<close>

definition \<open>\<I>' ts t' = map (\<lambda>t. (instantiate (\<I> t) t', dom t - dom t')) ts\<close>
definition \<open>scope_\<I>' ts t' = \<Union>(set (map snd (\<I>' ts t')))\<close>

definition \<open>b' t a ts = (b t a) @  \<I>' ts t\<close>

definition \<open>neg_b' t a ts = (neg_b t a) @  \<I>' ts t\<close>

text \<open>The maximum of the negative + positive error is the absolute error.\<close>
definition \<open>\<epsilon>_pos w t a ts = variable_elim (C w t a @ neg_b' t a ts)\<close>
definition \<open>\<epsilon>_neg w t a ts = variable_elim (neg_C w t a @ b' t a ts)\<close>

definition \<open>\<epsilon>_max w t a ts = max (\<epsilon>_pos w t a ts) (\<epsilon>_neg w t a ts)\<close>
declare refl[of \<epsilon>_max, cong]

end

locale Bellman_Err_Branch =
  Bellman_Err_Branch_Consts +
  Factored_MDP_Default +
  assumes
    variable_elim_spec: \<open>variable_elim_spec\<close>
begin

lemma not_consistent_\<I>[simp]: \<open>\<not>consistent x t \<Longrightarrow> \<I> t x = 0\<close>
  unfolding \<I>_def by auto

lemma consistent_\<I>[simp]: \<open>consistent x t \<Longrightarrow> \<I> t x = -\<infinity>\<close>
  unfolding \<I>_def by auto


lemma scope_\<I>'_eq: \<open>scope_\<I>' ts t' = (\<Union>t \<in> set ts. dom t) - dom t'\<close>
  by (auto simp: \<I>'_def scope_\<I>'_def)

lemma variable_elim_eq_Max:
  assumes
    \<open>scope_inv fs\<close>
  shows 
    \<open>variable_elim fs = (MAX x \<in> states. sum_list (map (\<lambda>(f, s). f x) fs))\<close>
  using assms variable_elim_spec 
  unfolding variable_elim_spec_def variable_elim_correct_def 
  by auto

lemmas instantiate_def[simp]

lemma consistent_add[simp]: \<open>consistent x t \<Longrightarrow> x ++ t = x\<close>
  unfolding consistent_def by (metis map_add_restr')

lemma instantiate_consistent: \<open>consistent x t \<Longrightarrow> instantiate f t x = f x\<close>
  by simp

lemma map_add_eq_iff: \<open>((m ++ t) i = (m' ++ t) i) \<longleftrightarrow> (i \<in> dom t \<or> (m i = m' i))\<close>
  by (auto split: option.splits simp: map_add_def)

lemma has_scope_on_instantiate: 
  assumes \<open>(\<And>d. d \<in> D \<Longrightarrow> d ++ t \<in> D)\<close>
  assumes \<open>has_scope_on f D (R \<union> dom t)\<close>
  shows \<open>has_scope_on (instantiate f t) D (R - dom t)\<close>
  using assms
  by (auto simp: map_add_eq_iff intro!: has_scope_onI has_scope_on_eq[OF assms(2)])

lemma has_scope_on_instantiateI: 
  \<open>t \<in> partial_states \<Longrightarrow> 
  R \<subseteq> vars \<Longrightarrow> 
  has_scope_on f partial_states (R \<union> dom t) \<Longrightarrow> 
  has_scope_on (instantiate f t) partial_states R\<close>
  by (blast intro!: has_scope_on_subs[of _ _  \<open>R - dom t\<close> R] has_scope_on_instantiate)

lemma has_scope_on_addI: 
  assumes \<open>t \<in> partial_states\<close> \<open>R \<subseteq> vars\<close> 
    \<open>has_scope_on f partial_states (R \<union> dom t)\<close> 
  shows \<open>has_scope_on (\<lambda>x. f (x ++ t)) partial_states R\<close>
  using assms
  by (auto simp: map_add_eq_iff intro!: has_scope_onI has_scope_on_eq[OF assms(3)]) blast+

lemma snd_neg_scoped [simp]: \<open>snd (neg_scoped fs) = snd fs\<close>
  unfolding neg_scoped_def by (auto simp: case_prod_unfold)

lemma fst_neg_scoped [simp]: \<open>fst (neg_scoped fs) = -fst fs\<close>
  unfolding neg_scoped_def by (auto simp: case_prod_unfold)

lemma scope_inv_C: 
  \<open>t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow> 
  scope_inv' (C w t a)\<close>
  unfolding scope_inv'_def C_def hg_inst_def hg_scope_def 
  using scope_g' \<Gamma>\<^sub>a_D2 h_scope_dims 
  by (auto intro!: has_scope_on_compose[of _ _ _ ereal] has_scope_on_addI has_scope_on_diff 
      has_scope_on_scale has_scope_on_instantiateI)+

lemma scope_inv_neg_C: \<open>t \<in> partial_states \<Longrightarrow> a \<in> actions \<Longrightarrow> scope_inv' (neg_C w t a)\<close>
  using scope_inv_C[of t a w] 
  unfolding neg_C_def scope_inv'_def neg_scoped_def
  by (auto intro!: has_scope_onI dest!: has_scope_on_eq)

lemma has_scope_on_if:
  assumes \<open>has_scope_on fb X R\<close> \<open>has_scope_on f1 X R\<close> \<open>has_scope_on f2 X R\<close>
  shows \<open>has_scope_on (\<lambda>x. if fb x then f1 x else f2 x) X R\<close>
  using assms unfolding has_scope_on_def
  by metis

lemma has_scope_on_consistent: \<open>
  dom t \<subseteq> X \<Longrightarrow> 
  t \<in> partial_states \<Longrightarrow> 
  has_scope_on (\<lambda>x. consistent x t) partial_states X\<close>
  by (auto intro!: has_scope_onI simp: consistent_iff in_mono domI)

lemma scope_inv_b: \<open>
  t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow> 
  scope_inv' (b t a)\<close>
  unfolding b'_def scope_inv'_def b_def r_inst_def r_scope_def \<I>'_def \<I>_def set_map
    by safe (auto intro!: has_scope_on_compose[of _ _ _ ereal] has_scope_on_addI has_scope_on_consistent split: if_splits)+

lemma scope_inv_b': \<open>
  t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow> 
  set ts \<subseteq> partial_states \<Longrightarrow> 
  scope_inv (b' t a ts)\<close>
  unfolding b'_def scope_inv_def b_def r_inst_def r_scope_def \<I>'_def \<I>_def
  by (auto intro!: has_scope_on_compose[of _ _ _ ereal] has_scope_on_addI has_scope_on_consistent split: if_splits)+


lemma scope_inv_b'': \<open>
  t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow> 
  set ts \<subseteq> partial_states \<Longrightarrow> 
  scope_inv (b t a)\<close>
  unfolding  scope_inv_def b_def r_inst_def r_scope_def
  by (auto intro!:  has_scope_on_addI has_scope_on_consistent )+


lemma b_has_scope_on: \<open>
  t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow>
  (f, s) \<in> set (b t a) \<Longrightarrow> 
  set ts \<subseteq> partial_states \<Longrightarrow> 
  has_scope_on f partial_states s\<close>
  unfolding  scope_inv_def b_def r_inst_def r_scope_def
  by (auto intro!:  has_scope_on_addI has_scope_on_consistent )+


lemma b_scope_in_vars: \<open>
  t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow>
  (f, s) \<in> set (b t a) \<Longrightarrow> 
  s \<subseteq> vars\<close>
  unfolding  scope_inv_def b_def r_inst_def r_scope_def
  by (auto intro!:  has_scope_on_addI has_scope_on_consistent )+


lemma scope_inv'D[dest]: \<open>scope_inv' X \<Longrightarrow> scope_inv X\<close>
  unfolding scope_inv_def scope_inv'_def by auto  

lemma scope_inv_neg_b: \<open>
  t \<in> partial_states \<Longrightarrow> 
  a \<in> actions \<Longrightarrow> 
  scope_inv' (neg_b t a)\<close>
  using scope_inv_b[of t a]
  unfolding neg_b_def scope_inv'_def neg_scoped_def
  by (auto intro!: has_scope_onI dest!: has_scope_on_eq)

lemma scope_inv_\<I>': \<open>t \<in> partial_states \<Longrightarrow> 
  set ts \<subseteq> partial_states \<Longrightarrow> 
  scope_inv (\<I>' ts t)\<close>
  unfolding  \<I>'_def \<I>_def scope_inv_def
  by (auto intro!: has_scope_onI simp: domIff consistent_iff map_add_def split: option.splits)

lemma scope_inv'_neg[intro!]: 
  \<open>scope_inv' (xs :: (((nat \<Rightarrow> 'a option) \<Rightarrow> ereal) \<times> nat set) list) \<Longrightarrow> scope_inv' (map neg_scoped xs)\<close>
  unfolding neg_scoped_def scope_inv'_def
  using ereal_uminus_eq_reorder
  by (fastforce simp:   ereal_uminus_uminus intro!: has_scope_on_compose[of _ _ _ \<open>\<lambda>x. - x\<close>])

lemma scope_inv'_app[simp]: 
  \<open>scope_inv' (xs @ ys) \<longleftrightarrow> scope_inv' xs \<and> scope_inv' ys\<close>
  unfolding scope_inv'_def 
  by (auto simp add: case_prod_unfold)
  
lemma scope_inv_app[simp]: 
  \<open>scope_inv (xs @ ys) \<longleftrightarrow> scope_inv xs \<and> scope_inv ys\<close>
  unfolding scope_inv_def 
  by (auto simp add: case_prod_unfold)
  
lemma scope_inv_neg_b': 
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
    shows \<open>scope_inv (neg_b' t a ts)\<close>
proof -
  have \<open>scope_inv (map (\<lambda>(x, y). (\<lambda>xa. ereal (x xa), y)) (neg_b t a))\<close>
  using assms b_has_scope_on b_scope_in_vars
  unfolding scope_inv_def neg_b_def
  by (auto simp: subset_iff case_prod_unfold)

  thus ?thesis
    unfolding neg_b'_def
    using scope_inv_\<I>'[of t ts] assms
    by simp
qed

lemma sum_\<I>'_eq: \<open>(\<Sum>p\<leftarrow>\<I>' ts t. fst p x) = (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
  by (induction ts arbitrary: t x) (auto simp: \<I>'_def \<I>_def)

lemma sum_neg_b'_eq:
  shows
    \<open>sum_list (map (\<lambda>f. fst f x) (neg_b' t a ts)) = 
  -reward a (x ++ t) + (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
  unfolding neg_b'_def reward_def neg_b_def
  by (auto simp: case_prod_unfold b_def sum_\<I>'_eq interv_sum_list_conv_sum_set_nat sum_negf atLeast0LessThan r_inst_def)

lemma sum_b'_eq:
  shows
    \<open>sum_list (map (\<lambda>f. fst f x) (b' t a ts)) = 
  reward a (x ++ t) + (if \<forall>t' \<in> set ts. \<not>consistent (x ++ t) t' then 0 else -\<infinity>)\<close>
  unfolding b'_def reward_def
  by (auto simp: case_prod_unfold b_def sum_\<I>'_eq interv_sum_list_conv_sum_set_nat sum_negf atLeast0LessThan r_inst_def)

lemma sum_C_eq: \<open>sum_list (map (\<lambda>fs. fst fs x) (C w t a)) = 
  (\<Sum>j < h_dim. w j * (h j (x++t) - l * g' j a (x++t)))\<close>
  unfolding C_def hg_inst_def
  by (auto simp: atLeast_upt comp_def interv_sum_list_conv_sum_set_nat)

lemma sum_neg_C_eq: \<open>sum_list (map (\<lambda>fs. fst fs x) (neg_C w t a)) = 
  - (\<Sum>j < h_dim. w j * (h j (x++t) - l * g' j a (x++t)))\<close>
  unfolding C_def neg_C_def neg_scoped_def hg_inst_def
  by (auto simp: sum_negf[symmetric] algebra_simps atLeast_upt comp_def interv_sum_list_conv_sum_set_nat)

lemma states_add: \<open>
  x \<in> states \<Longrightarrow> 
  t \<in> partial_states \<Longrightarrow> 
  x ++ t \<in> states\<close>
  by blast

lemma consistent_addI: \<open>
  x \<in> states \<Longrightarrow> 
  t \<in> partial_states \<Longrightarrow> 
  consistent (x ++ t) t\<close>
  by auto

lemma P_add_iff: \<open>t \<in> partial_states \<Longrightarrow> 
  (\<forall>x \<in> states. P (x ++ t)) \<longleftrightarrow> (\<forall>x \<in> {x. x \<in> states \<and> consistent x t}. P x)\<close>
  using consistent_addI states_add by fastforce

lemma scope_inv_append: \<open>scope_inv xs \<Longrightarrow> scope_inv ys \<Longrightarrow> scope_inv (xs @ ys)\<close>
  unfolding scope_inv_def
  by auto


lemma \<epsilon>_pos_neg_ereal:
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows \<open>\<epsilon>_pos w t a ts = (MAX x \<in> {x. x \<in> states \<and> consistent x t}. 
      - reward a x + (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) + 
        (if \<forall>t'\<in>set ts. \<not> consistent x t' then 0 else - \<infinity>))\<close>
    \<open>\<epsilon>_neg w t a ts = (MAX x \<in> {x. x \<in> states \<and> consistent x t}.
      reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) + (if \<forall>t'\<in>set ts. \<not> consistent x t' then 0 else - \<infinity>))\<close>
proof goal_cases
  case 1

  have \<open>\<epsilon>_pos w t a ts = (MAX x\<in>states. \<Sum>(f, s)\<leftarrow>map (\<lambda>(x, y). (\<lambda>xa. ereal (x xa), y)) (C w t a) @ neg_b' t a ts. f x)\<close>
    unfolding \<epsilon>_pos_def
    using scope_inv_C assms scope_inv_neg_b' 
    by (subst variable_elim_eq_Max) auto
  also have \<open>\<dots> = (MAX x\<in>states. ereal ((\<Sum>j<h_dim. w j * (h j (x ++ t) - l * g' j a (x ++ t)))) + (-ereal (reward a (x ++ t)) + (if \<forall>t'\<in>set ts. \<not> consistent (x ++ t) t' then 0 else - \<infinity>)))\<close>
    using sum_C_eq
    by (simp add: sum_neg_b'_eq comp_def case_prod_unfold)
  also have \<open>\<dots> = (MAX x\<in> {x. x \<in> states \<and> consistent x t}. ereal ((\<Sum>j<h_dim. w j * (h j (x) - l * g' j a (x)))) + (-ereal (reward a (x)) + (if \<forall>t'\<in>set ts. \<not> consistent (x) t' then 0 else - \<infinity>)))\<close>
    apply (rule Max_eq_if)
    subgoal using fin_states states_ne assms by auto
    subgoal using fin_states states_ne assms by auto
    subgoal using fin_states states_ne assms by (auto simp: consistent_add intro!: states_add exI[of _ \<open>_ ++ t\<close>])
    subgoal by (auto simp: image_iff intro!: bexI)
    done
  also have \<open>\<dots> = (MAX x \<in> {x. x \<in> states \<and> consistent x t}.
      - reward a x + (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) + (if \<forall>t'\<in>set ts. \<not> consistent x t' then 0 else - \<infinity>))\<close>
    using assms states_ne consistent_addI[of _ t] states_add[of _ t] fin_states
    by (auto simp: g_restr algebra_simps intro!: Max_cong consistent_addI)
  finally show ?case .
next
  case 2
  have \<open>\<epsilon>_neg w t a ts = (MAX x\<in>states. \<Sum>(f, s)\<leftarrow>map (\<lambda>(x, y). (\<lambda>xa. ereal (x xa), y)) (neg_C w t a) @ b' t a ts. f x)\<close>
    unfolding \<epsilon>_neg_def
    using scope_inv_neg_C assms scope_inv_b' 
    by (subst variable_elim_eq_Max) auto
  also have \<open>\<dots> = (MAX x\<in>states. ereal (- (\<Sum>j<h_dim. w j * (h j (x ++ t) - l * g' j a (x ++ t)))) + (ereal (reward a (x ++ t)) + (if \<forall>t'\<in>set ts. \<not> consistent (x ++ t) t' then 0 else - \<infinity>)))\<close>
    using sum_neg_C_eq
    by (simp add: sum_b'_eq sum_neg_C_eq comp_def case_prod_unfold)
  also have \<open>\<dots> = (MAX x\<in> {x. x \<in> states \<and> consistent x t}. ereal (- (\<Sum>j<h_dim. w j * (h j (x) - l * g' j a (x)))) + (ereal (reward a (x)) + (if \<forall>t'\<in>set ts. \<not> consistent (x) t' then 0 else - \<infinity>)))\<close>
    apply (rule Max_eq_if)
    subgoal using fin_states states_ne assms by auto
    subgoal using fin_states states_ne assms by auto
    subgoal using fin_states states_ne assms by (auto simp: consistent_add intro!: states_add exI[of _ \<open>_ ++ t\<close>])
    subgoal by (auto simp: image_iff intro!: bexI)
    done
  also have \<open>\<dots> = (MAX x \<in> {x. x \<in> states \<and> consistent x t}.
      reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) + (if \<forall>t'\<in>set ts. \<not> consistent x t' then 0 else - \<infinity>))\<close>
    using assms states_ne consistent_addI[of _ t] states_add[of _ t] fin_states
    by (auto simp: g_restr algebra_simps intro!: Max_cong consistent_addI)
  finally show ?case .
qed

definition \<open>not_cons_upt ts t = {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}\<close>

lemma Max_ex: \<open>finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> X \<and> (MAX x\<in> X. f x) = f x\<close>
  by (metis (mono_tags, lifting) Max_in empty_is_image finite_imageI image_iff)

lemma \<epsilon>_pos_neg:
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows 
\<open>\<epsilon>_pos w t a ts = (if not_cons_upt ts t = {} then -\<infinity> else (MAX x \<in> not_cons_upt ts t. 
   ereal (- reward a x + (\<Sum>j < h_dim. w j * (h j x - l * g j a x)))))\<close>

\<open>\<epsilon>_neg w t a ts = 
  (if not_cons_upt ts t = {} then -\<infinity> else (MAX x \<in> not_cons_upt ts t.
      ereal (reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x)))))\<close>
  subgoal
    unfolding \<epsilon>_pos_neg_ereal[OF assms]
    apply (cases \<open>not_cons_upt ts t = {}\<close>)
    subgoal
      using fin_states states_ne states_add[OF _ assms(1)] assms(1) consistent_addI[of _ t]
      by (auto intro!: Max_eqI intro: exI[of _ \<open>t\<close>] simp: not_cons_upt_def algebra_simps image_iff) metis
    using fin_states finite_imageI
    by (auto simp: not_cons_upt_def intro!: Max_eq_if)
  subgoal
    unfolding \<epsilon>_pos_neg_ereal[OF assms]
    apply (cases \<open>not_cons_upt ts t = {}\<close>)
    subgoal
      using fin_states states_ne states_add[OF _ assms(1)] assms(1) consistent_addI[of _ t]
      by (auto intro!: Max_eqI intro: exI[of _ \<open>t\<close>] simp: not_cons_upt_def algebra_simps image_iff) metis
    using fin_states finite_imageI 
    by (auto simp: not_cons_upt_def intro!: Max_eq_if)
  done

lemma \<epsilon>_pos_neg':
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows \<open>\<epsilon>_pos w t a ts = (\<Squnion>x \<in> not_cons_upt ts t. 
      ereal (- reward a x + (\<Sum>j < h_dim. w j * (h j x - l * g j a x))))\<close>

\<open>\<epsilon>_neg w t a ts = (\<Squnion>x \<in> not_cons_upt ts t.
      ereal (reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x))))\<close>
  unfolding \<epsilon>_pos_neg[OF assms]
  using bot_ereal_def
  by (auto intro!: Max_Sup simp add: fin_states not_cons_upt_def)

lemma \<epsilon>_pos_neg'':
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows \<open>\<epsilon>_pos w t a ts = (\<Squnion>x \<in> not_cons_upt ts t. 
  ereal (-reward a x - (\<Sum>j < h_dim. w j * (l * g j a x - h j x))))\<close>
    and \<open>\<epsilon>_neg w t a ts = (\<Squnion>x \<in> not_cons_upt ts t.  
  ereal (reward a x + (\<Sum>j < h_dim. w j * (l * g j a x - h j x))))\<close>
  unfolding \<epsilon>_pos_neg'[OF assms]
  using not_cons_upt_def
  by (auto simp: algebra_simps sum_subtractf)

lemma \<epsilon>_max_correct:
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows \<open>\<epsilon>_max w t a ts =
    (\<Squnion>x \<in> not_cons_upt ts t. ereal 
      \<bar> reward a x - (\<Sum>j < h_dim. w j * (h j x - l * g j a x)) \<bar>)\<close>
  unfolding \<epsilon>_max_def \<epsilon>_pos_neg'[OF assms] sup_max[symmetric]
  apply (cases \<open>not_cons_upt ts t = {}\<close>)
  subgoal by auto
  subgoal
    by (subst SUP_sup_distrib) (auto intro!: SUP_cong image_Un split: if_splits simp: abs_real_def)
  done

lemma \<epsilon>_max_correct':
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows \<open>\<epsilon>_max w t a ts = (\<Squnion> x \<in> not_cons_upt ts t. ereal \<bar> Q w x a - \<nu>\<^sub>w w x\<bar>)\<close>
  unfolding \<epsilon>_max_correct[OF assms]
  using assms states_imp_partial
  by (auto simp: not_cons_upt_def Q_g \<nu>\<^sub>w_def algebra_simps sum_subtractf sum_distrib_left)

lemma \<epsilon>_max_correct'':
  assumes \<open>t \<in> partial_states\<close> \<open>a \<in> actions\<close> \<open>set ts \<subseteq> partial_states\<close>
  shows \<open>\<epsilon>_max w t a ts =
  (\<Squnion>x \<in> {x. x \<in> states \<and> consistent x t \<and> (\<forall>t' \<in> set ts. \<not> consistent x t')}. 
      ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
  unfolding \<epsilon>_max_correct'[OF assms]
  by (auto simp: not_cons_upt_def dist_real_def)

end

context Factored_MDP_Default
begin

interpretation Variable_Elimination_Consts \<open>\<F> :: (((nat \<Rightarrow> _ option) \<Rightarrow> ereal) \<times> nat set) list\<close> dims id doms
  for \<F> .

interpretation 
  Bellman_Err_Branch_Consts
  where 
    rewards = rewards and
    transitions = transitions and
    doms = doms and
    variable_elim = elim_max
  by unfold_locales

sublocale 
  Bellman_Err_Branch
  where 
    rewards = rewards and
    transitions = transitions and
    doms = doms and
    variable_elim = elim_max
  apply unfold_locales
  unfolding variable_elim_spec_def variable_elim_correct_def scope_inv_def
  apply safe
  subgoal for fs
  proof -
    assume \<open>\<forall>(b, scope_b)\<in>set fs. (\<forall>x. b x \<noteq> \<infinity>) \<and> scope_b \<subseteq> vars \<and> has_scope_on b partial_states scope_b\<close>
    then interpret Variable_Elimination fs dims id doms
      using doms_ne  partial_states_def
      by unfold_locales (fastforce simp:partial_states_def cong del: has_scope_on_cong)+
    show \<open>elim_max fs = (MAX x\<in>states. \<Sum>(f, s)\<leftarrow>fs. f x)\<close>
      unfolding elim_max_correct expl_max_def expl_max_\<F>_def
      unfolding full_vecs_def states_def vecs_on_def partial_vecs_def partial_states_def
      by (auto simp: Int_commute case_prod_unfold)
  qed
  done

end


end