theory Bellman_Err_Code
  imports 
    "../algorithm/Bellman_Err" 
    Code_Setup 
    Bellman_Err_Branch_Code
begin

section \<open>Bellman Error Code equations\<close>

subsection \<open>Util\<close>

lemma fold_relI:
  assumes \<open>length xs = length ys\<close>
  assumes \<open>\<And>x y x' y'. R_inv x y \<Longrightarrow> (x', y') \<in> set (zip xs ys) \<Longrightarrow> R_inv (f x' x) (f' y' y)\<close>
  assumes \<open>R_inv x_init y_init\<close>
  shows \<open>R_inv (fold f xs x_init) (fold f' ys y_init)\<close>
  using assms
  by (induction xs ys arbitrary: x_init y_init rule: list_induct2) auto

subsection \<open>Definitions\<close>

locale BellmanErrCodeDefs =
  MDPCodeDefs
  where
    sr_ops = sr_ops and
    vec_ops = vec_ops and
    set_ops = set_ops and
    sp_ops = sp_ops and
    sp_pmf_ops = sp_pmf_ops
    + 
    STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops
for 
  sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" 
  and sp_ops :: \<open>('sp, 'state, 'pmf, 'natset) scoped_fn_basic_ops\<close>
  and vec_ops 
  and set_ops
  and sp_pmf_ops ::  "('pmf, nat, 'pmf_set) pmf_ops" 
  and ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" 
  and er_ops +
  fixes
    w_code :: \<open>weights\<close> and
    g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'f\<close> and
    dec_pol_code :: \<open>('state \<times> nat) list\<close>
begin

print_locale BellmanErrBranchCodeDefs
sublocale BellmanErrBranchCodeDefs
  where 
    w_code = w_code and
    ereal_ops = er_ops and
    to_ereal_ops = ste_ops
  for ts_code t_code a_code 
  by unfold_locales

definition \<open>error_branch_code t a ts = \<epsilon>_max_code ts t a\<close>
lemmas refl[of error_branch_code, cong]

definition \<open>update_err_iter_code = 
  (\<lambda>(t, a) (ts, err). (t#ts, sup (error_branch_code t a ts) err))\<close>
lemmas refl[of update_err_iter_code, cong]

definition \<open>err_list_code = snd (fold update_err_iter_code dec_pol_code ([], 0))\<close>
lemmas refl[of err_list_code, cong]

definition \<open>factored_bellman_err_code = real_of_ereal err_list_code\<close>
lemmas refl[of factored_bellman_err_code, cong]

end

subsection \<open>Instantiations + Correctness of Code Equations\<close>
locale BellmanErrCode = 
  BellmanErrCodeDefs +
  MDPCode +
  STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops

locale Bellman_Err_Code_Transfer =
  MDP_Code_Transfer
  where 
    actions = actions +
  BellmanErrCodeDefs
where 
  ste_ops = ste_ops and 
  er_ops = er_ops +
  STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops
for
    er_ops and
    ste_ops :: "(_, _) scoped_fn_to_ereal_ops" and
    actions :: \<open>nat set\<close> +
fixes 
  w :: \<open>nat \<Rightarrow> real\<close> and
  dec_pol :: \<open>((nat \<rightharpoonup> nat) \<times> nat) list\<close>
begin

sublocale Bellman_Err_Branch_Code_Transfer 
  where to_ereal_ops = ste_ops and ereal_ops = er_ops
  for ts_code t_code a_code t a ts
  by unfold_locales

definition \<open>error_branch t a ts = \<epsilon>_max t a ts\<close>
lemmas refl[of error_branch, cong]

sublocale Bellman_Err_Consts
  where error_branch = \<open>error_branch w\<close>
  by unfold_locales

end

locale Bellman_Err_Code_Transfer_Rel =
  MDP_Code_Transfer_Rel +
  Bellman_Err_Code_Transfer
  where 
    dec_pol_code = dec_pol_code and
    dec_pol = dec_pol +
  BellmanErrCode
  where
    dec_pol_code = dec_pol_code 
for dec_pol_code dec_pol
   +
assumes 
dec_pol_rel: \<open>pol_rel dec_pol_code dec_pol\<close> and
w_rel: \<open>w_rel w_code w\<close> and
g_cache[simp]: \<open>g_cache = g_code\<close>
begin

context 
  fixes a_code a t_code t ts_code ts
  assumes assms: \<open>a_code = a\<close> \<open>a \<in> actions\<close> \<open>state_rel t_code t\<close> \<open>w_rel w_code w\<close> \<open>list_all2 state_rel ts_code ts\<close>
begin

interpretation Bellman_Err_Branch_Code_Transfer_Rel
  where 
    to_ereal_ops = ste_ops and 
    ereal_ops = er_ops
  using assms
  by unfold_locales (auto simp: nat_rel_def bellman_err_branch_rel_def w_rel'_def t_rel_def ts_rel_def a_rel_def g_rel_def)

lemma error_branch_rel:
  \<open>error_branch_code t_code a ts_code = error_branch w t a ts\<close>
  unfolding error_branch_code_def error_branch_def
  using \<epsilon>_max_code_eq a_code_eq 
  by blast

end

context 
  assumes assms: \<open>is_dec_list_pol dec_pol\<close> \<open>greedy_spec\<close>
begin

interpretation Bellman_Err
  where error_branch = \<open>error_branch w\<close>
  using assms
  by unfold_locales
    (auto simp: dec_pol_spec_def error_branch_spec_def error_branch_def \<epsilon>_max_correct'' list_all_iff)

lemma dec_list_to_pol_is_opt: \<open>E.is_opt_act (\<nu>\<^sub>w_expl w) s (expl_pol (dec_list_to_pol dec_pol) s)\<close>
  using is_opt_act_no_state is_greedy expl_pol_eq expl_pol_no_state
  unfolding E.is_greedy_def
  by (cases \<open>s \<in> states_expl\<close>) presburger+

lemma factored_bellman_err_eq: \<open>factored_bellman_err = proj_err_w (dec_list_to_pol dec_pol) w\<close>
  unfolding factored_bellman_err_def err_list_eq_SUP'''''
  unfolding  E.bellman_err\<^sub>b_def
  using proj_err_w_eq dec_list_to_pol_is_opt E.is_greedy_L_eq_\<L>\<^sub>b E.is_greedy_def dec_pol
  by (auto simp: expl_pol_eq)
end

lemma dec_pol_code_len[simp]: \<open>length dec_pol_code = length dec_pol\<close>
  using dec_pol_rel 
  by auto

lemma update_err_iter_rel: \<open>
  rel_fun 
    (rel_prod state_rel (rel_on (=) actions)) 
    (rel_fun (rel_prod (list_all2 state_rel) (=)) (rel_prod (list_all2 state_rel) (=))) 
    update_err_iter_code update_err_iter\<close>
  unfolding update_err_iter_code_def update_err_iter_def
  using w_rel error_branch_rel
  by (auto intro!: rel_funI)

lemma err_list_rel: \<open>err_list_code = err_list dec_pol\<close>
proof -
  have \<open>rel_prod (list_all2 state_rel) (=) (fold update_err_iter_code dec_pol_code ([], 0)) ((fold update_err_iter dec_pol ([], 0)))\<close> 
    by (rule fold_relI) (insert dec_pol_rel, auto intro!: update_err_iter_rel[THEN rel_funD, THEN rel_funD])
  thus ?thesis
  unfolding err_list_code_def err_list_def
  by auto
qed

lemma factored_bellman_err_rel:
  \<open>factored_bellman_err_code = factored_bellman_err\<close>
  unfolding factored_bellman_err_code_def factored_bellman_err_def
  using err_list_rel
  by auto

lemma factored_bellman_err_eq':
  assumes \<open>is_dec_list_pol dec_pol\<close> \<open>greedy_spec\<close>
  shows 
    \<open>factored_bellman_err = proj_err_w (dec_list_to_pol dec_pol) w\<close>
  using assms factored_bellman_err_eq 
  by blast

end

end