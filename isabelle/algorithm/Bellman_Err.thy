section \<open>Factored Bellman Error\<close>
theory Bellman_Err
  imports Factored_MDP_Util Decision_List_Policy
begin

locale Bellman_Err_Branch =
  Factored_MDP_Default where rewards = rewards for
  rewards :: "'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> 'x::{countable, linorder} state \<Rightarrow> real" + 
fixes
  error_branch :: \<open>weights \<Rightarrow>'x state \<Rightarrow> 'a \<Rightarrow> ('x state) list \<Rightarrow> ereal\<close>
begin

definition \<open>error_branch_spec = (\<forall>w t a ts. 
  a \<in> actions \<longrightarrow> t \<in> partial_states \<longrightarrow> set ts \<subseteq> partial_states \<longrightarrow>
  error_branch w t a ts = 
    (\<Squnion> x \<in> {x. x \<in> states \<and> consistent x t \<and> list_all (\<lambda>t'. \<not>consistent x t') ts}.
      ereal (dist (Q w x a) (\<nu>\<^sub>w w x))))\<close>

end

locale Bellman_Err_Consts =
  Factored_MDP_Default_Consts where rewards = rewards for
  rewards :: "'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> 'x::{countable, linorder} state \<Rightarrow> real" + 
fixes
  error_branch :: \<open>'x state \<Rightarrow> 'a \<Rightarrow> ('x state) list \<Rightarrow> ereal\<close> and
  dec_pol :: \<open>('x state \<times> 'a) list\<close> and
  w :: \<open>weights\<close>
begin

(* ensure dec_pol is greedy wrt w *)
definition \<open>greedy_spec = (\<forall>x \<in> states. is_greedy_act w x (dec_list_to_pol dec_pol x))\<close>

definition \<open>dec_pol_spec \<longleftrightarrow> is_dec_list_pol dec_pol \<and> greedy_spec\<close>

definition \<open>\<pi> = dec_list_to_pol dec_pol\<close>

definition \<open>error_branch_spec = (\<forall>t a ts. 
  a \<in> actions \<longrightarrow> t \<in> partial_states \<longrightarrow> set ts \<subseteq> partial_states \<longrightarrow>
  error_branch t a ts = 
    (\<Squnion> x \<in> {x. x \<in> states \<and> consistent x t \<and> list_all (\<lambda>t'. \<not>consistent x t') ts}.
      ereal (dist (Q w x a) (\<nu>\<^sub>w w x))))\<close>

definition \<open>update_err_iter = (\<lambda>(t, a) (ts, err). (t#ts, sup (error_branch t a ts) err))\<close>

definition \<open>err_list xs = snd (fold update_err_iter xs ([], 0))\<close>

definition \<open>factored_bellman_err = real_of_ereal (err_list dec_pol)\<close>

end

locale Bellman_Err =
  Bellman_Err_Consts +
  Factored_MDP_Default +
  assumes
    dec_pol_spec: dec_pol_spec and
    error_branch_spec: error_branch_spec
begin

lemma is_greedy_actI:
assumes \<open>x \<in> states\<close>
shows \<open>is_greedy_act w x (dec_list_to_pol dec_pol x)\<close>
  using assms dec_pol_spec unfolding dec_pol_spec_def greedy_spec_def
  by auto

lemma dec_list_pol:
shows \<open>is_dec_list_pol dec_pol\<close>
  using  dec_pol_spec unfolding dec_pol_spec_def greedy_spec_def
  by auto

lemma dec_pol:
shows \<open>is_policy (dec_list_to_pol dec_pol)\<close>
  using  dec_pol_spec unfolding dec_pol_spec_def greedy_spec_def
  by auto

lemma is_opt_act: \<open>s \<in> states_expl \<Longrightarrow> 
  E.is_opt_act (apply_bfun (\<nu>\<^sub>w_expl w)) s (dec_list_to_pol dec_pol (from_expl s))\<close>
  using is_greedy_actI[unfolded is_greedy_act_def Q_def, of \<open>from_expl s\<close>] dec_pol in_states_expl'
  by (auto simp add: G\<^sub>a_expl E.is_opt_act_def is_arg_max_linorder)
  
lemma is_greedy:
  \<open>E.is_greedy (\<nu>\<^sub>w_expl w) (\<lambda>x. dec_list_to_pol dec_pol (if x \<in> states_expl then from_expl x else some_state))\<close>
  using  dec_pol is_opt_act_no_state some_in_states is_opt_act
  unfolding E.is_greedy_def
  by auto

lemma err_nil[simp]: \<open>err_list [] = 0\<close>
  unfolding err_list_def
  by auto

lemma set_fst_fold_update_err_iter[simp]: 
  \<open>set (fst (fold update_err_iter xs tscs)) = fst ` set xs \<union> set (fst tscs)\<close>
  by (induction xs arbitrary: tscs ) (auto simp: update_err_iter_def case_prod_unfold)

lemma fst_fold_update_err_iter[simp]: 
  \<open>(fst (fold update_err_iter xs tscs)) = rev (map fst xs) @ (fst tscs)\<close>
  by (induction xs arbitrary: tscs ) (auto simp: update_err_iter_def case_prod_unfold)

lemma snd_upd_err_iter:
  \<open>(snd (update_err_iter ta xscs)) = sup (error_branch (fst ta) (snd ta) (fst xscs)) (snd xscs)\<close>
  unfolding update_err_iter_def
  by (auto simp: case_prod_unfold)

lemma constrs_list_snoc:
  assumes 
    \<open>fst ` set xs \<subseteq> partial_states\<close> 
    \<open>a \<in> actions\<close> 
    \<open>t \<in> partial_states\<close> 
  shows 
    \<open>(err_list (xs @ [(t, a)])) = sup (error_branch t a (map fst xs)) (err_list xs)\<close>
  unfolding err_list_def
  using assms error_branch_spec error_branch_spec_def
  by (auto simp: snd_upd_err_iter)


definition \<open>cands_snoc xs t a = {(x, a :: 'b) | x .(x \<in> states \<and> consistent x t \<and> (\<forall>i \<in> set xs. \<not> consistent x (i)))}\<close>

lemma error_branch_eq_MAX:
  assumes \<open>set xs \<subseteq> partial_states\<close> \<open>a \<in> actions\<close> \<open>t \<in> partial_states\<close>
  shows 
    \<open>error_branch t a xs = 
    (\<Squnion> x \<in> {x. x \<in> states \<and> consistent x t \<and> list_all (\<lambda>j. \<not>consistent x j) xs}.
      ereal(dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
  using assms error_branch_spec error_branch_spec_def by blast

lemma error_branch_eq_MAX':
  assumes \<open>set xs \<subseteq> partial_states\<close> \<open>a \<in> actions\<close> \<open>t \<in> partial_states\<close>
  shows 
    \<open>error_branch t a xs = (\<Squnion> (x, a) \<in> cands_snoc xs t a. ereal(dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
  using assms error_branch_eq_MAX
  unfolding cands_snoc_def
  by (auto simp: case_prod_unfold list_all_iff intro!: antisym SUP_mono)

definition \<open>state_act_cands xs = 
  {(x, a) | x i a. a = snd (xs ! i) \<and> x \<in> states \<and> i < length xs \<and> consistent x (fst (xs ! i)) \<and> (\<forall>j<i. \<not>consistent x (fst (xs ! j)))}\<close>

lemma state_act_cands_nil[simp]: \<open>state_act_cands [] = {}\<close>
  unfolding state_act_cands_def
  by auto

lemma state_act_cands_snoc_sup: \<open>state_act_cands (xs @ [(t, a)]) \<supseteq> state_act_cands xs\<close>
  unfolding state_act_cands_def
  by (auto simp: List.nth_append)

lemma state_act_cands_snoc: \<open>state_act_cands (xs @ [(t, a)]) =
   state_act_cands xs \<union> {(x, a) | x. x \<in> states \<and> consistent x t \<and> (\<forall>b \<in> set xs. \<not>consistent x (fst b))}\<close>
  unfolding state_act_cands_def
proof (safe, goal_cases)
  case (1 a b)
  then show ?case 
  by (auto simp add: less_Suc_eq List.nth_append in_set_conv_nth)+
next
  case (2 a b)
  then show ?case 
  by (auto simp add: less_Suc_eq List.nth_append in_set_conv_nth)+
next
  case (3 a b x)
  then show ?case 
  by (auto simp add: less_Suc_eq List.nth_append)
qed

lemma cands_snoc_state_cands_eq: \<open>cands_snoc (map fst xs) t a' \<union> state_act_cands xs = state_act_cands (xs @ [(t, a')])\<close>
  unfolding state_act_cands_snoc cands_snoc_def
  by auto

lemma err_list_eq_SUP:                   
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> 
  shows \<open>err_list xs = max 0 (\<Squnion> (x, a) \<in> state_act_cands xs. ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
  using assms
proof (induction xs rule: rev_induct)
  case (snoc a xs)
  thus ?case
proof (cases a)
  case (Pair t a')
  let ?selected = \<open>\<lambda>x. x \<in> states \<and> consistent x t \<and> list_all (\<lambda>j. \<not> consistent x j) (map fst xs)\<close>

  have \<open>err_list (xs @ [(t, a')]) = error_branch t a' (map fst xs) \<squnion> err_list xs\<close>
    using snoc Pair  by (subst constrs_list_snoc) auto
  also have \<open>\<dots> = (\<Squnion>(x, a)\<in>cands_snoc (map fst xs) t a'. ereal (dist (Q w x a) (\<nu>\<^sub>w w x))) \<squnion> err_list xs\<close>
    using snoc Pair by (subst error_branch_eq_MAX') auto
  also have \<open>\<dots> = (\<Squnion>(x, a)\<in>cands_snoc (map fst xs) t a'. ereal (dist (Q w x a) (\<nu>\<^sub>w w x))) \<squnion>
    max 0 (\<Squnion>(x, a)\<in>state_act_cands xs. ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
    using snoc by (auto simp: Pair)
  also have \<open>\<dots> = max 0 ((\<Squnion>(x, a)\<in>cands_snoc (map fst xs) t a'. ereal (dist (Q w x a) (\<nu>\<^sub>w w x))) \<squnion>
     (\<Squnion>(x, a)\<in> state_act_cands xs. ereal (dist (Q w x a) (\<nu>\<^sub>w w x))))\<close>
    using snoc
    by (auto simp: max.assoc max.commute)
  also have \<open>\<dots> = max 0 (\<Squnion>(x, a)\<in> cands_snoc (map fst xs) t a' \<union> state_act_cands xs. ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
    by (simp add: SUP_union)
  also have \<open>\<dots> = max 0 (\<Squnion>(x, a)\<in> state_act_cands (xs @ [(t, a')]). ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
    using cands_snoc_state_cands_eq by auto
  finally show ?thesis
    using Pair 
    by simp
qed
qed auto

lemma cands_ne:
  assumes ex_consistent: \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>state_act_cands xs \<noteq> {}\<close>
  using assms states_ne
  apply (induction xs rule: rev_induct)
  by (auto simp: state_act_cands_snoc) meson

lemma err_list_eq_SUP':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> 
  and ex_consistent: \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>err_list xs = (\<Squnion> (x, a) \<in> state_act_cands xs. ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
  unfolding err_list_eq_SUP[OF assms(1,2)]
  using cands_ne[OF assms(3)]
  by (auto intro!: max_absorb2 intro: SUP_upper2)

lemma find_append: \<open>find p (xs @ ys) = (case find p xs of None \<Rightarrow> find p ys | Some y \<Rightarrow> Some y)\<close>
  by (induction xs arbitrary: ys) auto

lemma singletonE: \<open>P 0 x \<Longrightarrow> (\<And>i. P (Suc i) ([] ! i)) \<Longrightarrow> P i ([x] ! i)\<close>
  by (cases i) auto


lemma dec_list_to_pol_ex_state_act_cands:
  assumes \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  assumes \<open>x \<in> states\<close>
  shows \<open>a = dec_list_to_pol xs x \<longleftrightarrow> (x, a) \<in> state_act_cands xs\<close>
  apply (cases \<open>(find (\<lambda>(t, a). consistent x t) xs)\<close>)
  subgoal
    using assms(1)[of x] assms(2)
    unfolding state_act_cands_def dec_list_to_pol_def
    by (auto simp: find_None_iff eq_fst_iff set_conv_nth)
  subgoal
    unfolding state_act_cands_def dec_list_to_pol_def
    using assms
    apply (simp only:)
    apply (simp add: case_prod_unfold find_Some_iff)
    by (metis not_less_iff_gr_or_eq)
  done

lemma dec_list_to_pol_eq_state_act_cands:
  assumes ex_consistent: \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>{(x, a) | x a. x \<in> states \<and> a = dec_list_to_pol xs x} = state_act_cands xs\<close>
  using assms states_ne dec_list_to_pol_ex_state_act_cands[OF assms]
  by (auto simp: state_act_cands_def)+

lemma err_list_eq_SUP'':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> 
  and ex_consistent: \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>err_list xs = (
      \<Squnion> (x, a) \<in> {(x, a) | x a. x \<in> states \<and> a = dec_list_to_pol xs x}.
      ereal (dist (Q w x a) (\<nu>\<^sub>w w x)))\<close>
  using assms
  by (simp add: err_list_eq_SUP'[OF assms] dec_list_to_pol_eq_state_act_cands[symmetric])

lemma err_list_eq_SUP''':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> 
  and ex_consistent: \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
  shows \<open>err_list xs = (\<Squnion>x \<in> states. ereal (dist (Q w x (dec_list_to_pol xs x)) (\<nu>\<^sub>w w x)))\<close>
  apply (simp only: err_list_eq_SUP''[OF assms])
  by (simp add: case_prod_beta setcompr_eq_image image_image)

lemma finite_Sup_ereal_infty: 
  assumes \<open>finite X\<close> \<open>X \<noteq> {}\<close> 
  shows \<open>\<bar>(\<Squnion>(ereal ` X))\<bar> \<noteq> \<infinity>\<close>
proof -
  have \<open>\<Squnion> (ereal ` X) \<in> ereal ` X\<close>
    using assms Max_in[of \<open>ereal ` X\<close>]
    by (simp add: Max_Sup)
  thus ?thesis
    by auto
qed


lemma finite_SUP_ereal_infty: \<open>finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<bar>(\<Squnion>x \<in> X. ereal (f x))\<bar> \<noteq> \<infinity>\<close>
  using finite_Sup_ereal_infty[of \<open>f ` X\<close>]
  by (auto simp: image_image)

lemma err_list_eq_SUP'''':
  assumes \<open>fst ` set xs \<subseteq> partial_states\<close> \<open>snd ` set xs \<subseteq> actions\<close> 
  and ex_consistent: \<open>\<And>x. x \<in> states \<Longrightarrow> \<exists>y \<in> fst ` set xs. consistent x y\<close>
shows \<open>err_list xs = (\<Squnion>x \<in> states. dist (Q w x (dec_list_to_pol xs x)) (\<nu>\<^sub>w w x))\<close>
proof -
  have \<open>err_list xs = (\<Squnion>x\<in>states. ereal (dist (Q w x (dec_list_to_pol xs x)) (\<nu>\<^sub>w w x)))\<close>
    using err_list_eq_SUP'''[OF assms ] .
  also have \<open>\<dots> = (\<Squnion>x\<in>states. (dist (Q w x (dec_list_to_pol xs x)) (\<nu>\<^sub>w w x)))\<close>
  using fin_states states_ne
  by (intro ereal_SUP[symmetric] finite_SUP_ereal_infty) auto
  finally show ?thesis .
qed

lemma bellman_err_w_eq_Q:
  shows \<open>bellman_err_w w = (\<Squnion>x\<in>states. dist (Q w x (dec_list_to_pol dec_pol x)) (\<nu>\<^sub>w w x))\<close>
proof -
  have *: \<open>dist (apply_bfun (\<nu>\<^sub>w_expl w) n) (apply_bfun (E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w)) n) = 0\<close> if \<open>n \<notin>  states_expl\<close> for n
    using that
    by auto

  have dec_list_to_pol_is_greedy: \<open>E.is_greedy (\<nu>\<^sub>w_expl w) (\<lambda>x. dec_list_to_pol dec_pol (if x \<in> states_expl then from_expl x else some_state))\<close>
    using is_greedy by auto

  have dec_pol_in_act: \<open>x \<in> states \<Longrightarrow> dec_list_to_pol dec_pol x \<in> actions\<close> for x
    using dec_pol by blast

  have \<open>bellman_err_w w = (\<Squnion>x. dist ((\<nu>\<^sub>w_expl w) x) ((E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w)) x))\<close>
    unfolding bellman_err_w_eq_expl E.bellman_err\<^sub>b_def dist_bfun.rep_eq by auto
  also have \<open>\<dots> = (\<Squnion>x. if x \<in> states_expl then dist ((\<nu>\<^sub>w_expl w) x) ((E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w)) x) else 0)\<close>
    using * by meson
  also have \<open>\<dots> = (\<Squnion>x \<in> states_expl. dist ((\<nu>\<^sub>w_expl w) x) ((E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w)) x))\<close> 
    using finite_states_expl states_expl_ne
    by (intro antisym cSUP_mono) auto
  also have \<open>\<dots> = (\<Squnion>x \<in> states. dist ((\<nu>\<^sub>w_expl w) (to_expl x)) ((E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w)) (to_expl x)))\<close>
    by (auto simp: states_expl_def image_image)
  also have \<open>\<dots> = (\<Squnion>x \<in> states. dist ((\<nu>\<^sub>w w) x) ((E.\<L>\<^sub>b (\<nu>\<^sub>w_expl w)) (to_expl x)))\<close>
    by (auto simp: states_expl_def \<nu>\<^sub>w_expl.rep_eq)
  also have \<open>\<dots> = (\<Squnion>x \<in> states. dist ((\<nu>\<^sub>w w) x) (E.L\<^sub>a (dec_list_to_pol dec_pol x) (\<nu>\<^sub>w_expl w) (to_expl x)))\<close>
    by (auto intro!: SUP_cong simp: E.is_greedy_L\<^sub>a_eq_\<L>\<^sub>b[OF dec_list_to_pol_is_greedy, symmetric])
  also have \<open>\<dots> = (\<Squnion>x \<in> states. dist ((\<nu>\<^sub>w w) x) (Q w x (dec_list_to_pol dec_pol x)))\<close>
    using dec_pol_in_act
    by (auto simp: Q_r_G\<^sub>a intro!: SUP_cong)
  finally show ?thesis
    by (auto simp: dist_commute)
qed

lemma err_list_eq_SUP''''':
  shows \<open>err_list dec_pol = E.bellman_err\<^sub>b (\<nu>\<^sub>w_expl w)\<close>
  using dec_list_pol is_dec_list_pol_def bellman_err_w_eq_Q
  by (auto simp: err_list_eq_SUP'''' case_prod_unfold bellman_err_w_eq_expl)
end

locale Bellman_Err_API' =
  Bellman_Err_Branch where rewards = rewards for
  rewards :: "'a::{countable, linorder} \<Rightarrow> nat \<Rightarrow> 'x::{countable, linorder} state \<Rightarrow> real" + 
assumes error_branch_spec: \<open>error_branch_spec\<close>
begin

definition \<open>err_list p w = Bellman_Err_Consts.err_list (error_branch w) p\<close>

lemma proj_err_upd_eq_pol:
  assumes \<open>is_dec_list_pol dec_pol\<close> \<open>\<forall>x \<in> states. is_greedy_act w x (dec_list_to_pol dec_pol x)\<close> 
  shows \<open>err_list dec_pol w = E.bellman_err\<^sub>b (\<nu>\<^sub>w_expl w)\<close>
proof -
  interpret U: Bellman_Err_Consts where error_branch = \<open>error_branch w\<close>
    by unfold_locales

  interpret U: Bellman_Err where error_branch = \<open>error_branch w\<close>
    apply unfold_locales
    using error_branch_spec assms
    unfolding error_branch_spec_def U.dec_pol_spec_def U.error_branch_spec_def U.greedy_spec_def
    by auto

  show ?thesis
    by (simp add: U.err_list_eq_SUP''''' err_list_def)
qed

end
end