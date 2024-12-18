theory API_Code
  imports 
    "../algorithm/API" 
    Code_Setup 
    Bellman_Err_Code
    Dec_List_Code
    ValueDet_Code
begin

locale APICodeDefs =
  MDPCodeDefs
  where
    sr_ops = sr_ops and
    vec_ops = vec_ops and
    set_ops = set_ops and
    sp_ops = sp_ops and
    sp_pmf_ops = sp_pmf_ops +
 STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops +
 Coeffs: Coeffs constr_map_ops +
  LP_Cert_Defs
where
  minimize = minimize and
  constr_map_ops = constr_map_ops
for 
  sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" and 
  sp_ops :: \<open>('sp, 'state, 'pmf, 'natset) scoped_fn_basic_ops\<close> and 
  vec_ops and 
  set_ops and 
  sp_pmf_ops ::  "('pmf, nat, 'pmf_set) pmf_ops" and 
  ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
  constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> and
  er_ops :: "('ef, 'state, 'natset) scoped_fn_ereal_ops" and
  minimize :: \<open>'m LP_Code \<Rightarrow> 'm lp_res\<close> +
fixes
  t_max_code :: \<open>nat\<close> and
  \<epsilon>_code :: \<open>real\<close>
begin


print_locale DecListPolCodeDefs
sublocale DecListPolCodeDefs for g_cache w_code
  by unfold_locales

definition update_dec_list_code :: \<open>(nat \<Rightarrow> nat \<Rightarrow> 'f) \<Rightarrow> weights \<Rightarrow> ('state \<times> nat) list\<close> where
  \<open>update_dec_list_code = dec_list_pol_code\<close>
lemmas refl[of update_dec_list_code, cong]

print_locale ValueDetCodeDefs
sublocale ValueDetCodeDefs
  where
    minimize = minimize
  for dec_pol_code g_cache
  by unfold_locales

definition update_weights_code :: \<open>(nat \<Rightarrow> nat \<Rightarrow> 'f) \<Rightarrow> ('state \<times> nat) list \<Rightarrow> weights\<close> where
\<open>update_weights_code g pol = upd_weights_code pol g\<close>
lemmas refl[of update_weights_code, cong]

print_locale BellmanErrCodeDefs
sublocale BEC?: BellmanErrCodeDefs for g_cache w_code dec_pol_code
  by unfold_locales

definition bellman_err_code :: 
  \<open>(nat \<Rightarrow> nat \<Rightarrow> 'f) \<Rightarrow> ('state \<times> nat) list \<Rightarrow> weights \<Rightarrow> real\<close> where
\<open>bellman_err_code g p w = factored_bellman_err_code w g p\<close>
lemmas refl[of bellman_err_code, cong]

definition body_code :: \<open>_ \<Rightarrow> ('state \<times> nat) list \<Rightarrow> ('state \<times> nat) list \<times> weights\<close> where
  \<open>body_code g p =
    (let 
        w' = update_weights_code g p;
        p' = update_dec_list_code g w' in (p', w'))\<close>
lemmas refl[of body_code, cong]

definition \<open>w0_code = (\<lambda>_. 0)\<close>
definition \<open>p0_code = update_dec_list_code g_code (\<lambda>_. 0)\<close>

definition \<open>pol_code_i i = ((fst o body_code g_code) ^^ i) p0_code\<close>
lemmas refl[of pol_code_i, cong]

lemma pol_code_i_0: \<open>pol_code_i 0 = p0_code\<close>
  unfolding pol_code_i_def by auto

lemma pol_code_i_Suc: \<open>pol_code_i (Suc i) = fst (body_code g_code (pol_code_i i))\<close>
  unfolding pol_code_i_def by auto

lemma pol_code_i_Suc': \<open>pol_code_i (Suc i) = update_dec_list_code g_code (update_weights_code g_code (pol_code_i i))\<close>
  unfolding pol_code_i_Suc body_code_def Let_def
  by auto

definition \<open>api_aux_code_step g pw t = (
  let 
    (p, w) = pw;
    (p', w') = body_code g p;
    err = bellman_err_code g p' w';
    t' = t + 1;
    w_eq = (\<forall>i < h_dim_code. w' i = w i);
    err_le = (err \<le> \<epsilon>_code);
    timeout = (t' \<ge> t_max_code) in
    (w', p', err, t', w_eq, err_le, timeout))\<close>
lemmas refl[of api_aux_code_step, cong]

function api_aux_code where
\<open>api_aux_code g pw t = (
  let
    (p, w) = pw;
    (p', w') = body_code g p;
    err = bellman_err_code g p' w';
    t' = t + 1;
    w_eq = (\<forall>i < h_dim_code. w' i = w i);
    err_le = (err \<le> \<epsilon>_code);
    timeout = (t' \<ge> t_max_code) in
    (if w_eq \<or> err_le \<or> timeout then (w', p', err, t, w_eq, err_le, timeout)
     else api_aux_code g (p', w') t'))\<close>
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(g, w, t). t_max_code - t)") auto
lemmas refl[of \<open>api_aux_code\<close>, cong]

lemmas api_aux_code.simps[simp del]

definition \<open>api_code =
  (let 
    ga = g_arr;
    gc = IArray.sub ga;
    w0 = (\<lambda>_. 0);
    p0 = update_dec_list_code gc w0;
    res = api_aux_code gc (p0, w0) 0 in 
  res)\<close>

lemma api_aux_code': \<open>api_aux_code g pw t =
  (
    let (w', p', err, t', w_eq, err_le, timeout) = api_aux_code_step g pw t in
    (if w_eq \<or> err_le \<or> timeout then (w', p', err, t, w_eq, err_le, timeout)
     else api_aux_code g (p', w') t')
  )\<close>
  unfolding api_aux_code.simps[of g pw t] Let_def api_aux_code_step_def case_prod_unfold
  by auto

end

locale APICode =
  APICodeDefs 
  where
    sr_ops = sr_ops and
    vec_ops = vec_ops and
    set_ops = set_ops and
    sp_ops = sp_ops and
    sp_pmf_ops = sp_pmf_ops and
    constr_map_ops = constr_map_ops and
    minimize = minimize and
    ste_ops = ste_ops and
    er_ops = er_ops +
  LP_Cert 
  where
    constr_map_ops = constr_map_ops and
    minimize = minimize +
  MDPCode
  where
    sr_ops = sr_ops and
    vec_ops = vec_ops and
    set_ops = set_ops and
    sp_ops = sp_ops and
    sp_pmf_ops = sp_pmf_ops +
 STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops +
 Coeffs: Coeffs constr_map_ops
for 
  sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" and 
  sp_ops :: \<open>('sp, 'state, 'pmf, 'natset) scoped_fn_basic_ops\<close> and 
  vec_ops and 
  set_ops and 
  sp_pmf_ops ::  "('pmf, nat, 'pmf_set) pmf_ops" and 
  ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
  (* lp_ops :: \<open>('lp, 'pmf_set, 'm) lp_ops\<close> and *)
  (* constr_ops :: \<open>('pmf_set, 'm, var_code_ty) constr_ops\<close> and  *)
  constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> and
  er_ops :: "('ef, 'state, 'natset) scoped_fn_ereal_ops" and
  minimize :: \<open>'m LP_Code \<Rightarrow> 'm lp_res\<close> +
assumes \<epsilon>_code_pos: \<open>\<epsilon>_code > 0\<close>

locale APICodeTransfer =
  APICodeDefs
  where doms = doms and
    vec_ops = vec_ops and
      sr_ops = sr_ops +
  MDP_Code_Transfer
where doms = doms and d = d and
    vec_ops = vec_ops +
  STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops dims doms
  for 
    doms :: "nat \<Rightarrow> nat set" and
    d :: nat and
    t_max :: nat and
    \<epsilon> :: real and
    vec_ops :: \<open>('f, nat, 'd) vec_ops\<close>
begin

sublocale VDCT?: ValueDetCode_Transfer
  where
    minimize = minimize
  for dec_pol dec_pol_code g_cache
  by unfold_locales

definition \<open>update_weights' = (\<lambda>i p. 
    (if pol_rel (pol_code_i i) p 
  then 
    update_weights (pol_code_i i) g_code 
  else 
    VDA'.update_weights p))\<close>
lemmas refl[of update_weights', cong]

print_locale API_Interface_Consts
sublocale AIC?: API_Interface_Consts
  where 
    doms = doms and
    actions = actions and
    update_dec_list = \<open>dec_list_pol_filter o dec_list_pol\<close> and
    update_weights = update_weights'
  
  by unfold_locales

unbundle lifting_syntax

definition \<open>api_rels \<longleftrightarrow> \<epsilon>_code = \<epsilon> \<and> t_max_code = t_max\<close>

abbreviation \<open>body_rel \<equiv> rel_fun (pol_rel) (rel_prod pol_rel w_rel)\<close>

abbreviation \<open>update_dec_list_rel \<equiv> (w_rel ===> pol_rel) (update_dec_list_code g_code) dec_list_pol\<close>

abbreviation \<open>bellman_err_rel \<equiv>
  (pol_rel ===> w_rel ===> (=)) (\<lambda>p w. bellman_err_code g_code p w) (\<lambda>p w. proj_err_w (dec_list_to_pol p) w)\<close>

abbreviation "api_rel \<equiv> rel_prod w_rel (rel_prod pol_rel (=))"

end

locale APICodeTransferRel =
  APICodeTransfer +
  APICode +
  MDP_Code_Transfer_Rel +
  assumes
    api_rels: \<open>api_rels\<close>
begin

context
  fixes g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'b\<close> and  dec_pol_code :: \<open>('e \<times> nat) list\<close> and dec_pol
  assumes h: \<open>g_cache = g_code\<close> \<open>dec_pol_spec' dec_pol\<close>
begin

interpretation VDCT?: ValueDetCode_Transfer_Rel'
  where            
    minimize = minimize and
    g_cache = g_cache
  using h
  by unfold_locales auto

lemmas fst_minimize_constrs =  VDA'.fst_minimize_constrs
lemmas ex_is_arg_min'_constrs = ex_is_arg_min'_constrs
end

context
  fixes g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'b\<close> and  dec_pol_code :: \<open>('e \<times> nat) list\<close> and dec_pol
  assumes h: \<open>g_cache = g_code\<close> \<open>dec_pol_spec' dec_pol\<close> \<open>pol_rel dec_pol_code dec_pol\<close>
begin

interpretation VDCT?: ValueDetCode_Transfer_Rel
  where            
    minimize = minimize and
    g_cache = g_cache
  using h
  by unfold_locales auto

lemmas upd_w_rel = VDCT.upd_weights_rel
lemmas arg_min'_minimize' = VDCT.minimize_spec
lemmas constr_set_eq = VDCT.VDA'.in_constrs_iff

end



print_locale Bellman_Err_Code_Transfer
sublocale BECT?: Bellman_Err_Code_Transfer
  where g_cache = g_cache
  for dec_pol_code dec_pol w_code w g_cache
  by unfold_locales

lemma \<epsilon>_eq[simp]: \<open>\<epsilon>_code = \<epsilon>\<close>
  using api_rels unfolding api_rels_def by auto

lemma t_max_eq[simp]: \<open>t_max_code = t_max\<close>
  using api_rels unfolding api_rels_def by auto

lemma update_weights_code_eq[simp]: \<open>pol_rel p_code p \<Longrightarrow> i < h_dim \<Longrightarrow>
  update_weights_code g_code p_code i = update_weights p_code g_code i\<close>
  unfolding update_weights_def
  unfolding minimize'_def
  unfolding update_weights_code_def upd_weights_code_def
  unfolding Let_def case_prod_unfold snd_conv
  by auto

definition \<open>api_aux'_step pw t = (
  let 
    (p, w) = pw;
    w' = update_weights' t p;
    p' = dec_list_pol_filter (dec_list_pol w');
    err = proj_err_w (dec_list_to_pol p') w';
    t' = t + 1;
    w_eq = (\<forall>i < h_dim. w' i = w i);
    err_le = (err \<le> \<epsilon>);
    timeout = (t' \<ge> t_max) in
    (w', p', err, t', w_eq, err_le, timeout))\<close>
lemmas refl[of api_aux'_step, cong]

lemma api_aux_code': \<open>api_aux pw t =
  (
    let (w', p', err, t', w_eq, err_le, timeout) = api_aux'_step pw t in
    (if w_eq \<or> err_le \<or> timeout then (w', p', err, t, w_eq, err_le, timeout)
     else api_aux (p', w') t')
  )\<close>
  unfolding Let_def api_aux.simps[of pw t]
  unfolding Let_def api_aux'_step_def case_prod_unfold case_prod_unfold
  by auto

lemmas rel_funD[dest]

lemmas api_aux.simps[simp del]


sublocale Dec_List_Pol_Code_Transfer
  where g_cache = g_code
  for w_code w
  by unfold_locales
 
context 
  fixes g_cache w_code w
  assumes 
    g_rel: \<open>g_cache = g_code\<close> and
    w_rel: \<open>w_rel (w_code :: nat \<Rightarrow> real) w\<close>
begin

interpretation Dec_List_Pol_Code_Transfer_Rel
  using w_rel g_rel
  by unfold_locales blast

lemma dec_list_pol_in_acts: \<open>snd ` (set (dec_list_pol w)) \<subseteq> actions\<close>
  unfolding dec_list_pol_def dec_list_act_def by (auto simp: set_insort_key)
  
lemma dec_list_pol_filter_in_acts: \<open>snd ` (set (dec_list_pol_filter (dec_list_pol w))) \<subseteq> actions\<close>
  using dec_list_pol_in_acts dec_list_pol_filter_aux_subs
  unfolding dec_list_pol_filter_def
  by blast


lemma update_dec_list_rel[intro!]: 
  \<open>pol_rel (update_dec_list_code g_cache w_code) (dec_list_pol_filter (dec_list_pol w))\<close>
  unfolding update_dec_list_code_def
  using dec_list_pol_filter_in_acts
  by (intro list.rel_mono_strong[OF dec_list_pol_impl_correct]) auto

end


context 
  fixes w_code :: \<open>nat \<Rightarrow> real\<close> and  w dec_pol_code dec_pol g_cache
  assumes h: \<open>w_rel w_code w\<close> \<open>pol_rel dec_pol_code dec_pol\<close> \<open>g_cache = g_code\<close>
begin

interpretation Bellman_Err_Code_Transfer_Rel
  where 
    g_cache = g_cache and
    w_code = w_code and
    w = w and
    dec_pol_code = dec_pol_code and
    dec_pol = dec_pol
  using h 
  by unfold_locales blast+

lemmas factored_bellman_err_rel = factored_bellman_err_rel

lemmas factored_bellman_err_eq' = factored_bellman_err_eq'

lemma factored_bellman_err_code_eq_proj_err:
  \<open>is_dec_list_pol dec_pol \<Longrightarrow> greedy_spec dec_pol w \<Longrightarrow> factored_bellman_err_code w_code g_cache dec_pol_code = proj_err_w (dec_list_to_pol dec_pol) w\<close>
  using factored_bellman_err_rel factored_bellman_err_eq'
  by auto
end

lemma update_weights_code_rel[intro]:
  assumes \<open>pol_rel p_code p\<close> \<open>p_code = pol_code_i t\<close>
  shows \<open>w_rel (update_weights_code g_code p_code) (update_weights p_code g_code)\<close>
  unfolding update_weights'_def update_weights_def
  using assms
  unfolding update_weights_code_def upd_weights_code_def Let_def minimize'_def
  unfolding case_prod_unfold snd_conv
  by (auto simp: w_rel_def)

lemma update_weights_code_rel'[intro]:
  assumes \<open>pol_rel p_code p\<close> and \<open>p_code = pol_code_i t\<close>
  shows \<open>w_rel (update_weights_code g_code p_code) (update_weights' t p)\<close>
  unfolding update_weights'_def update_weights_def
  using assms
  unfolding update_weights_code_def upd_weights_code_def Let_def minimize'_def
  unfolding case_prod_unfold snd_conv
  by (auto simp: w_rel_def)

lemma dec_list_pol_in_acts': \<open>snd ` set (dec_list_pol w) \<subseteq> actions\<close>
  unfolding dec_list_pol_def dec_list_act_def
  by (auto simp: set_insort_key)

lemma dec_list_pol_in_states: \<open>fst ` set (dec_list_pol w) \<subseteq> partial_states\<close>
  unfolding dec_list_pol_def dec_list_act_def
  by (auto simp: set_insort_key set_assignments_abs T\<^sub>a_dims)+

lemma dec_list_pol_correct: \<open>is_dec_list_pol (dec_list_pol w)\<close>
  using distinct_dec_list_pol ex_consistent_dec_list_pol dec_list_pol_in_acts' dec_list_pol_in_states
  unfolding is_dec_list_pol_def 
  by (auto simp: case_prod_unfold find_Some_iff) (meson nth_mem)

lemma w_relD: \<open>w_rel w_code w \<Longrightarrow> i < h_dim \<Longrightarrow> w_code i = w i\<close>
  unfolding w_rel_def by blast

lemma bellman_err_code_eq_proj_err_w:
  assumes \<open>pol_rel p_code p\<close> and \<open>w_rel w_code w\<close> \<open>greedy_spec p w\<close> \<open>is_dec_list_pol p\<close>
  shows \<open>bellman_err_code g_code p_code w_code = proj_err_w (dec_list_to_pol p) w\<close>
  unfolding bellman_err_code_def
  using assms 
  by (subst factored_bellman_err_code_eq_proj_err) auto

lemma body_code_simps[simp]: 
  \<open>snd (body_code g_code pw) = update_weights_code g_code pw\<close>
  \<open>fst (body_code g_code pw) = update_dec_list_code g_code (update_weights_code g_code pw)\<close>
  unfolding body_code_def Let_def 
  by auto

lemma api_aux_code_step_simps[simp]:
  \<open>fst (api_aux_code_step g_code pw_code t) = update_weights_code g_code (fst pw_code)\<close>
  unfolding api_aux_code_step_def Let_def case_prod_unfold snd_conv fst_conv
  by auto

lemma greedy_spec_self[intro!]: \<open>greedy_spec (dec_list_pol_filter (dec_list_pol w)) w\<close>
      using dec_list_pol_sel_greedy
      unfolding greedy_spec_def dec_list_pol_sel_def
      unfolding update_weights'_def greedy_spec_def
      by auto

lemmas dec_list_pol_correct[intro!]

lemma api_aux_step_rel:
  assumes 
    \<open>pol_rel p_code p\<close> and \<open>w_rel w_code w\<close> \<open>p_code = pol_code_i t\<close>
  shows \<open>api_rel (api_aux_code_step g_code (p_code, w_code) t) (api_aux'_step (p, w) t)\<close>
  unfolding api_aux'_step_def Let_def api_aux_code_step_def
  apply (simp add: case_prod_unfold)
  apply safe
  subgoal unfolding body_code_def Let_def using update_weights_code_rel' assms by auto
  subgoal unfolding body_code_def Let_def fst_conv
    using assms update_weights_code_rel'
    by (auto intro!: update_dec_list_rel)
  subgoal 
    apply (rule bellman_err_code_eq_proj_err_w)
    using assms update_weights_code_rel' dec_list_pol_filter_is_pol
    by auto
  subgoal
    unfolding body_code_def Let_def snd_conv update_weights'_def
    using assms w_relD
    by auto
  subgoal
    unfolding body_code_def Let_def snd_conv update_weights'_def
    using assms w_relD
    by fastforce
  subgoal
    apply (subst (asm) bellman_err_code_eq_proj_err_w)
    using assms dec_list_pol_filter_is_pol
    by auto
  subgoal 
    using assms dec_list_pol_filter_is_pol     
    by (subst bellman_err_code_eq_proj_err_w) auto
  done

lemma api_rel_snd_snd[simp]: \<open>api_rel constr a \<Longrightarrow> snd (snd constr) = snd (snd a)\<close>
  by auto

lemma api_aux_code'':
    \<open>api_aux_code g_code pw t =
    (let (w', p', err, t', w_eq, err_le, timeout) = api_aux_code_step g_code pw t
     in if w_eq \<or> err_le \<or> timeout then (w', p', err, t, w_eq, err_le, timeout) else api_aux_code g_code (p', w') t')\<close>
  by (subst api_aux_code.simps) (auto simp: case_prod_unfold Let_def body_code_def api_aux_code_step_def)

lemmas pol_code_i_Suc'[simp]

lemma api_aux_correct: 
  assumes \<open>rel_prod pol_rel w_rel pw_code pw\<close> \<open>pol_code_i t = fst pw_code\<close>
  shows \<open>api_rel ((api_aux_code g_code) pw_code t) (api_aux pw t)\<close>
  using assms
proof  (induction pw t arbitrary: pw_code rule: api_aux.induct)
  case (1 pw t)

  have rel_step: \<open>api_rel (api_aux_code_step g_code pw_code t) (api_aux'_step pw t)\<close>
    apply (cases \<open>pw_code\<close>; cases pw)
    apply hypsubst
    apply (rule api_aux_step_rel)
    using 1(2,3)
    by auto

  have w_rel_step: \<open>w_rel (update_weights_code g_code (fst pw_code)) (update_weights' t (fst pw))\<close>
    using rel_step  
    by (auto simp: api_aux'_step_def case_prod_unfold Let_def)

  have pol_rel_step: \<open>pol_rel 
  (update_dec_list_code g_code (update_weights_code g_code (fst pw_code))) 
  (dec_list_pol_filter (dec_list_pol (update_weights' t (fst pw))))\<close>
    using rel_step dec_list_pol_filter_is_pol
    by (auto simp: api_aux'_step_def case_prod_unfold Let_def api_aux_code_step_def)

  have err_eq: \<open>bellman_err_code g_code (update_dec_list_code g_code (update_weights_code g_code (fst pw_code))) (update_weights_code g_code (fst pw_code)) =
    proj_err_w (dec_list_to_pol (dec_list_pol_filter (dec_list_pol (update_weights' t (fst pw))))) (update_weights' t (fst pw))\<close>
    apply (rule bellman_err_code_eq_proj_err_w)
    using assms w_rel_step dec_list_pol_filter_is_pol 
    by auto
  note "1.IH"[OF refl _ refl refl refl refl refl refl refl, of \<open>fst pw\<close> \<open>snd pw\<close>]
  show ?case
  proof (cases \<open>
    (t_max \<le> t + 1) \<or> 
    (proj_err_w (dec_list_to_pol (dec_list_pol_filter (dec_list_pol (update_weights' t (fst pw))))) (update_weights' t (fst pw)) \<le> \<epsilon>) \<or>
    (\<forall>i<h_dim. update_weights' t (fst pw) i = snd pw i)\<close>)
    case True
    then show ?thesis
      apply (subst api_aux_code')
      apply (subst api_aux_code'')
      apply (simp del: api_aux.simps add: err_eq w_rel_step Let_def case_prod_unfold api_aux_code_step_def api_aux'_step_def pol_rel_step)
      apply safe
        using "1.prems" w_rel_step
        by (auto dest!: w_relD simp del: api_aux.simps)
    next
      case False

      have pol_code_Suc_i_eq: \<open>pol_code_i (Suc t) = update_dec_list_code g_code (update_weights_code g_code (fst pw_code))\<close>
        using 1 by auto

      let ?w_code' = \<open>update_weights_code g_code (fst pw_code)\<close>
      let ?p_code' = \<open>update_dec_list_code g_code ?w_code'\<close>
      let ?code_ret = \<open>api_aux_code g_code (?p_code', ?w_code')\<close>

      let ?w' = \<open>update_weights' t (fst pw)\<close>
      let ?p' = \<open>dec_list_pol_filter (dec_list_pol ?w')\<close>
      let ?ret = \<open>api_aux (?p', ?w')\<close>
      have *: \<open>api_rel (?code_ret (t + 1)) (?ret (t + 1))\<close>
        apply (rule "1.IH"[of _ \<open>fst pw\<close> \<open>snd pw\<close>])
        using False 
        using rel_step[unfolded api_aux_code_step_def api_aux'_step_def body_code_def Let_def]
        by (auto simp: case_prod_unfold "1.prems")

      show ?thesis
      apply (subst api_aux_code')
        apply (subst api_aux_code'')
        unfolding Let_def
        using "1.prems" False
        using * w_rel_step
        by (auto simp add: err_eq  Let_def case_prod_unfold api_aux_code_step_def api_aux'_step_def dest!: w_relD)
    qed
  qed

lemma g_arr_eq_code[simp]: \<open>IArray.sub g_arr = g_code\<close>
  unfolding g_arr_def g_code_def
  by auto

lemma api_rel: \<open>api_rel api_code api\<close>
  unfolding api_code_def api_def Let_def g_arr_eq_code
  using p0_code_def pol_code_i_0
  by (intro api_aux_correct) (auto simp: w_rel_def)

lemma dec_pol_spec'_iff: \<open>dec_pol_spec' p \<longleftrightarrow> is_dec_list_pol p\<close>
  unfolding dec_pol_spec'_def is_dec_list_pol_def
  by (auto simp: case_prod_unfold)

sublocale AIC?: API_Interface
  where 
    doms = doms and
    actions = actions and
    update_dec_list = \<open>dec_list_pol_filter o dec_list_pol\<close> and
    update_weights = update_weights'
  apply unfold_locales
  subgoal
    unfolding update_weights_spec_def
    unfolding update_weights'_def
    apply safe
    apply auto
    subgoal for p i
      unfolding opt_weights_pol_def update_weights_def 
      using arg_min'_minimize'[OF refl, of p \<open>(pol_code_i i)\<close>]
      using constr_set_eq[OF refl, of p \<open>(pol_code_i i)\<close>]
      apply (simp add: dec_pol_spec'_iff )
      unfolding is_arg_min'_def case_prod_unfold is_arg_min_linorder
      apply auto
      by (smt (z3) prod.exhaust_sel)
    subgoal for p
      unfolding opt_weights_pol_def VDA'.update_weights_def 
      using fst_minimize_constrs[OF refl, of p] ex_is_arg_min'_constrs[OF refl, of p]
      unfolding dec_pol_spec'_iff
      apply (auto simp add: )
      unfolding is_arg_min'_def case_prod_unfold is_arg_min_def
      apply auto
      by (smt (z3) dec_list_to_pol proj_err_pol_le_w)
    done
  subgoal unfolding dec_list_pol_spec_def is_greedy_dec_list_pol_def
    using dec_list_pol_sel_greedy dec_list_to_pol dec_list_pol_filter_is_pol
      unfolding dec_list_pol_sel_def is_greedy_pol_iff is_greedy_act_def
      apply (auto simp: is_greedy_w_def is_arg_max_linorder)
      by blast
    done

end
end