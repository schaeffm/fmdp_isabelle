theory ValueDet_Code
  imports 
    Code_Setup 
    Inst_Code
begin

locale LP_Cert_Defs =
  Coeffs: Coeffs constr_map_ops 
  for
    constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> +
  fixes
    minimize :: \<open>('m) LP_Code \<Rightarrow> 'm lp_res\<close>
begin

definition \<open>lp_cert_spec = (\<forall>lp.
  case lp of LP_Code c cs \<Rightarrow>
  Coeffs.invar c \<and> (\<forall>c \<in> set cs. Coeffs.invar (constr_code_poly c)) \<longrightarrow>
  (case minimize (LP_Code c cs) of
    Opt sol val \<Rightarrow> 
    Coeffs.invar sol \<and> 
    Coeffs.cross_prod_code sol c = val \<and> 
    sol \<in> Coeffs.sol_space_code cs \<and>
    (\<forall>sol' \<in> Coeffs.sol_space_code cs. val \<le> Coeffs.cross_prod_code sol' c)
    | _ \<Rightarrow> True))\<close>

end

locale LP_Cert =
  LP_Cert_Defs +
  assumes
  lp_cert_spec: \<open>lp_cert_spec\<close>
begin

end

locale ValueDetCodeDefs =
  MDPCodeDefs 
  where sr_ops = sr_ops +
    STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops +
  LP_Cert_Defs constr_map_ops minimize 
  for 
    constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> and
    minimize :: \<open>('m) LP_Code \<Rightarrow> 'm lp_res\<close> and
    er_ops and
    ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
    sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" +
  fixes
    dec_pol_code :: \<open>('state \<times> nat) list\<close> and
    g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'f\<close>
begin

sublocale InstCodeDefs
  for  
    ts_code and
    t_code and
    a_code
  by unfold_locales

definition gen_constr_code :: \<open>'state \<Rightarrow> nat \<Rightarrow> 'state list \<Rightarrow> 'm Constr_Code list\<close> where
  \<open>gen_constr_code s a ts = \<Omega>_code ts s a\<close>
lemmas refl[of gen_constr_code, cong]

definition \<open>update_weights_iter_code = (\<lambda>(t, a) (ts, cs). (t#ts, gen_constr_code t a ts @ cs))\<close>
lemmas refl[of update_weights_iter_code, cong]

definition \<open>constrs_list_code xs = snd (fold (update_weights_iter_code) xs ([], []))\<close>
lemmas refl[of constrs_list_code, cong]

definition \<open>constrs_code = constrs_list_code dec_pol_code\<close>
lemmas refl[of constrs_code, cong]

definition \<open>obj_code = Coeffs.to_map [(var_phi, 1)]\<close>
lemmas refl[of obj_code, cong]

definition \<open>lp_code = LP_Code obj_code (constrs_code)\<close>
lemmas refl[of lp_code, cong]

definition \<open>default_sol = (SOME (sol, val). 
    val = Coeffs.cross_prod_code sol obj_code  \<and>
    sol \<in> Coeffs.sol_space_code constrs_code \<and>
    ( (\<forall>sol' \<in> Coeffs.sol_space_code constrs_code. val \<le> Coeffs.cross_prod_code sol' obj_code)) \<and> 
    (Coeffs.invar sol))\<close>
lemmas refl[of default_sol, cong]

definition \<open>lp_sol_code = (case
  minimize lp_code of
  Opt vars val \<Rightarrow> (vars, val)
  | _ \<Rightarrow> default_sol)\<close> 

(* without the let, the solution might have to be recomputed multiple times *)
definition \<open>upd_weights_code = (
  let 
    sol = fst (lp_sol_code);
    w_arr = IArray.of_fun (\<lambda>i. real_of_ereal (Coeffs.lookup0_code (var_w i) sol)) h_dim_code
  in
    IArray.sub w_arr)\<close>

end

locale ValueDetCode = 
  ValueDetCodeDefs
  where
    er_ops = er_ops and
    ste_ops = ste_ops and
    sr_ops = sr_ops +
    MDPCodeDefs
  where sr_ops = sr_ops +
    STE: ScopedFnToEreal ste_ops sr_ops er_ops vec_ops set_ops +
    LP_Cert
  for 
    er_ops and
    ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
    sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" + 
  assumes g_cache: \<open>g_cache = g_code\<close>

locale ValueDetCode_Transfer =
  MDP_Code_Transfer
  where
    sr_ops = sr_ops and
    rewards = rewards and
    transitions = transitions and
    doms = doms +
ValueDetCodeDefs 
where doms = doms +
STE: ScopedFnToEreal
where 
  doms = doms and
  ops = ste_ops and real_ops = sr_ops and ereal_ops = er_ops
for
  doms :: \<open>nat \<Rightarrow> nat set\<close> and
  rewards :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> real\<close> and 
  transitions :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat pmf" + 
fixes
  dec_pol :: \<open>((nat \<rightharpoonup> nat) \<times> nat) list\<close>
begin


print_locale InstCodeDefs
interpretation InstCodeDefs for ts_code t_code a_code 
  by unfold_locales

definition \<open>minimize' =
  (let (w_code, phi_code) = lp_sol_code in
     (phi_code, \<lambda>i. real_of_ereal (Coeffs.lookup0_code ((var_w i)) w_code)))\<close>
lemmas refl[of minimize', cong]

definition \<open>dec_pol_spec' \<longleftrightarrow>
  fst ` set dec_pol \<subseteq> partial_states \<and> snd ` set dec_pol \<subseteq> actions \<and> distinct dec_pol \<and> (\<forall>x\<in>states. Bex (fst ` set dec_pol) (consistent x))\<close>

print_locale InstCode_Transfer
sublocale InstCode_Transfer for ts_code t_code a_code t a ts
  by unfold_locales

sublocale ValueDet_API_Consts
  where
    inv_constr = inv_constr and
    union_constr = union_constr and
    empty_constr = empty_constr and 
    constr_set = constr_set and
    privates = privates and
    min_sol = minimize' and
    gen_constr = \<open>\<Omega>\<close> and
    dec_pol = dec_pol
  using union_spec empty_constr_spec 
  by unfold_locales

sublocale VDA': ValueDet_API_Consts
  where
    inv_constr = inv_constr and
    union_constr = union_constr and
    empty_constr = empty_constr and 
    constr_set = constr_set and
    privates = privates and
    min_sol = \<open>SOME x. is_arg_min' constrs x\<close> and
    gen_constr = \<open>\<Omega>\<close> and
    dec_pol = dec_pol
  by unfold_locales

end

locale ValueDetCode_Transfer_Rel' =
  ValueDetCode_Transfer
  where
    rewards = rewards and
    doms = doms and
    transitions = transitions
    +
    MDP_Code_Transfer_Rel
  where
    rewards = rewards and
    transitions = transitions and
    doms = doms +
    ValueDetCode where doms = doms + 
    ValueDetCode
  where 
    doms = doms
  for
    doms :: \<open>nat \<Rightarrow> nat set\<close> and
    rewards :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> real\<close> and 
    transitions :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat pmf" +
  assumes 
    dec_pol_spec: \<open>dec_pol_spec'\<close>
begin

print_locale InstCode_Transfer
interpretation InstCode_Transfer for ts_code t_code a_code t a ts
  by unfold_locales

print_locale Factored_LP_Inst
sublocale Factored_LP_Inst \<open>TYPE(((nat \<Rightarrow> nat option) \<times> nat) \<times> bool)\<close> \<open>TYPE(nat)\<close>.

context
  fixes a t ts
  assumes h: \<open>a \<in> actions\<close> \<open>t \<in> partial_states\<close> \<open>set ts \<subseteq> partial_states\<close>
begin

interpretation InstCode_Transfer'
  using h by unfold_locales auto

lemmas inv_\<Omega> = inv_\<Omega>
lemmas \<Omega>_set_correct = \<Omega>_set_correct
lemmas privs_\<Omega> = privs_\<Omega>
end

lemma g_rel: \<open>g_rel\<close>
  using g_cache unfolding g_rel_def by auto

context
  fixes a_code a t_code t ts_code ts
  assumes h: \<open>t_rel t_code t\<close> \<open>ts_rel ts_code ts\<close> \<open>a_rel a_code a\<close>
begin

interpretation InstCode_Transfer_Rel
  using h g_rel inst_rel_def by unfold_locales auto

lemmas \<Omega>_rel = \<Omega>_rel

end

definition \<open>sat_lp_code cs sol \<longleftrightarrow> (\<forall>c \<in> set cs. Coeffs.eval_constr_code c sol)\<close>

definition \<open>constr_inv constr_code = (case constr_code of
  Constr_Le p rhs \<Rightarrow> Coeffs.invar p | Constr_Eq p rhs \<Rightarrow> Coeffs.invar p)\<close>

lemma invar_obj_code: \<open>Coeffs.invar obj_code\<close>
  unfolding obj_code_def using Coeffs.correct by fast

lemma cross_prod_obj_code[simp]:
  assumes \<open>Coeffs.invar sol\<close>
  shows \<open>cross_prod (lookup0 (Coeffs.\<alpha> obj_code)) (lookup0 (Coeffs.\<alpha> sol)) = lookup0 (Coeffs.\<alpha> sol) var_phi\<close>
  using assms
  unfolding cross_prod_def obj_code_def
  by (auto simp: card_1_singleton_iff Coeffs.correct lookup0_def split: option.splits)

lemma constrs_rel_appendI[intro]:
  assumes \<open>constrs_rel cs_code (fst cs)\<close>
  assumes \<open>constrs_rel cs_code' (fst cs')\<close>
  shows \<open>constrs_rel (cs_code @ cs_code') (fst (union_constr cs cs'))\<close>
  using assms Lifting_Set.union_transfer rel_funD
  unfolding constrs_rel_def union_constr_def
  by fastforce

lemma update_weights_iter_code_fold_rel:
  assumes \<open>constrs_rel cs_code (fst cs)\<close> \<open>pol_rel p_code p\<close> \<open>list_all2 Vec.state_rel ts_code ts\<close>
  shows \<open>constrs_rel (snd (fold update_weights_iter_code p_code (ts_code, cs_code))) (fst (snd (fold update_weights_iter p (ts, cs))))\<close>
  using assms
proof (induction p arbitrary: p_code cs_code cs ts_code ts )
  case Nil
  then show ?case by auto
next
  case (Cons sa p)
  then show ?case
  proof (cases \<open>p_code\<close>)
    case Nil
    then show ?thesis using Cons by auto
  next
    case (Cons sa_code p_code)
    then show ?thesis
      apply simp
      apply (subst (2) update_weights_iter_code_def)
      apply (subst (2) update_weights_iter_def)
      unfolding gen_constr_code_def
        using Cons t_rel_def Cons.prems ts_rel_def
        by (auto intro!: constrs_rel_appendI \<Omega>_rel Cons.IH[of _ _ p_code] simp: case_prod_unfold nat_rel_def a_rel_def)
  qed
qed

lemma obj_code_rel: \<open>poly_rel obj_code (\<lambda>i. case i of var_name.var_phi \<Rightarrow> 1 | _ \<Rightarrow> 0)\<close>
  unfolding obj_code_def poly_rel_def
  by (auto simp: Coeffs.correct map_fn_rel_def var_invar_def lookup0_def split: var_name.splits)

lemma gen_constr_spec: \<open>gen_constr_spec\<close>
  subgoal
    unfolding gen_constr_spec_def
    apply safe
    subgoal
      using inv_\<Omega>
      unfolding gen_constr_spec_def inv_gen_constr_def a_rel_def
      apply safe
      by auto
    subgoal
      unfolding ge_gen_constr_def
      apply safe
      subgoal for t \<phi> w a ts
        apply (subst (asm) \<Omega>_set_correct[of a t ts])
        unfolding list_all_iff
        by blast+
      subgoal for t phi w a ts
        apply (subst \<Omega>_set_correct[of a t ts])
        unfolding list_all_iff
        by blast+
      done
    subgoal
      unfolding privs_constr_def
      using privs_\<Omega> by blast
    done
  done

lemma dec_pol_spec': \<open>dec_pol_spec\<close>
  using dec_pol_spec unfolding dec_pol_spec_def dec_pol_spec'_def by blast 

sublocale VDA': ValueDet_API'
  where
    inv_constr = Factored_LP_Inst.inv_constr and
    union_constr = Factored_LP_Inst.union_constr and
    empty_constr = Factored_LP_Inst.empty_constr and 
    constr_set = Factored_LP_Inst.constr_set and
    privates = Factored_LP_Inst.privates and
    gen_constr = \<open>\<Omega>\<close> and
    dec_pol = dec_pol
  using dec_pol_spec' gen_constr_spec empty_constr_spec union_spec
  by unfold_locales auto

lemma is_dec_pol: \<open>is_policy (dec_list_to_pol dec_pol)\<close>
  apply (rule dec_list_to_pol)
  using dec_pol_spec
  unfolding dec_pol_spec_def is_dec_list_pol_def dec_pol_spec'_def
  by (auto simp: case_prod_unfold)

lemma proj_err_w_arg_min_le: \<open>proj_err_w (dec_list_to_pol dec_pol) (arg_min (proj_err_w (dec_list_to_pol dec_pol)) (\<lambda>_. True)) \<le> proj_err_pol (dec_list_to_pol dec_pol)\<close>
proof -
  obtain w where w: \<open>\<And>w'. proj_err_w (dec_list_to_pol dec_pol) w \<le> proj_err_w (dec_list_to_pol dec_pol) w'\<close>
    using proj_err_w_min_ex is_dec_pol
    by blast

  show ?thesis
    unfolding proj_err_pol_def
    apply (rule cInf_greatest)
    subgoal by auto
    apply (subst arg_min_equality[where f = \<open>proj_err_w (dec_list_to_pol dec_pol)\<close>])
    using w by fastforce+
qed


lemma ex_is_arg_min'_constrs: \<open>\<exists>sol. is_arg_min' constrs sol\<close>
  unfolding is_arg_min'_def case_prod_unfold
  unfolding VDA'.in_constrs_iff
  apply simp
  apply (rule exI[of _ \<open>proj_err_pol (dec_list_to_pol dec_pol)\<close>])
  using is_dec_pol
  apply safe
  subgoal using proj_err_w_arg_min_le by blast
  subgoal
    using proj_err_pol_le_w[OF is_dec_pol]
    by (smt (verit, best))
  done

sublocale VDA': ValueDet_API
  where
    inv_constr = Factored_LP_Inst.inv_constr and
    union_constr = Factored_LP_Inst.union_constr and
    empty_constr = Factored_LP_Inst.empty_constr and 
    constr_set = Factored_LP_Inst.constr_set and
    min_sol = \<open>SOME x. is_arg_min' constrs x\<close> and
    privates = Factored_LP_Inst.privates and
    gen_constr = \<open>\<Omega>\<close> and
    dec_pol = dec_pol
  apply unfold_locales
  using ex_is_arg_min'_constrs
  using dec_pol_spec' gen_constr_spec
  by (auto intro!: someI2)
end

locale ValueDetCode_Transfer_Rel =
  ValueDetCode_Transfer_Rel' +
  assumes 
    dec_pol_rel: \<open>pol_rel dec_pol_code dec_pol\<close>
begin

lemma map_fn_relI[intro]: \<open>map_fn_rel m_code m\<close> if \<open>dom m_code \<subseteq> {v. var_invar v}\<close> 
    and \<open>\<And>i. i \<in> dom m_code \<Longrightarrow> m_code i = Some (m (var_code_\<alpha> i))\<close>
    and \<open>\<And>i. i \<notin> var_code_\<alpha> ` dom m_code \<Longrightarrow> m i = 0\<close> for m m_code
    unfolding map_fn_rel_def lookup0_def
    using that
    by auto

lemma minimize_Opt_specs:
  assumes \<open>minimize (LP_Code obj cs) = Opt sol val\<close>
    \<open>Coeffs.invar obj\<close> \<open>\<And>c. c\<in>set cs \<Longrightarrow> Coeffs.invar (constr_code_poly c)\<close>
  shows 
    \<open>Coeffs.invar sol\<close> 
    \<open>Coeffs.cross_prod_code sol obj = val\<close> 
    \<open>sol \<in> Coeffs.sol_space_code cs\<close> 
    \<open>(\<forall>sol'\<in>Coeffs.sol_space_code cs. val \<le> Coeffs.cross_prod_code sol' obj)\<close>
  using assms lp_cert_spec unfolding lp_cert_spec_def
  by (smt (verit, best) LP_Code.case lp_res.simps(8))+

lemma constrs_rel: \<open>constrs_rel constrs_code (fst constrs)\<close>
  unfolding constrs_code_def constrs_def
  unfolding constrs_list_code_def constrs_list_def
  apply (rule update_weights_iter_code_fold_rel)
  using dec_pol_rel
  by (auto simp: constrs_rel_def empty_constr_def Lifting_Set.empty_transfer)

lemma var_code_\<alpha>_phi_iff[simp]: \<open>var_code_\<alpha> v = var_name.var_phi \<longleftrightarrow> v = var_code.var_phi\<close>
  by (cases v) auto

lemma var_code_\<alpha>_w_iff[simp]: \<open>var_code_\<alpha> v = var_name.var_w i \<longleftrightarrow> v = var_code.var_w i\<close>
  by (cases v) auto

lemma var_phi_inv[simp, intro!]: \<open>var_invar var_phi\<close>
  unfolding var_invar_def
  by auto

lemma var_w_inv[simp, intro!]: \<open>var_invar (var_w i)\<close>
  unfolding var_invar_def
  by auto

lemma poly_\<alpha>'_phi[simp]: \<open>poly_\<alpha>' m var_name.var_phi = lookup0 m var_code.var_phi\<close>
proof -
  have [simp]: \<open>var_code.var_phi \<in> dom m \<Longrightarrow> 
  (SOME v. v \<in> dom m \<and> var_invar v \<and> v = var_code.var_phi) = var_code.var_phi\<close>
    by auto
  thus ?thesis
  by (auto simp: poly_\<alpha>'_def lookup0_def split: option.splits)
qed

lemma poly_\<alpha>'_w[simp]: \<open>poly_\<alpha>' m (var_name.var_w i) = lookup0 m (var_code.var_w i)\<close>
proof -
  have [simp]: \<open>var_code.var_w i \<in> dom m \<Longrightarrow> 
  (SOME v. v \<in> dom m \<and> var_invar v \<and> v = var_code.var_w i) = var_code.var_w i\<close>
    by auto
  thus ?thesis
  by (auto simp: poly_\<alpha>'_def lookup0_def split: option.splits)
qed

lemma lookup0_dom[simp]: \<open>i \<in> dom m \<Longrightarrow> lookup0 m i = the (m i)\<close>
  unfolding lookup0_def
  by auto

lemma vec_\<alpha>_some_show_state[simp]: \<open>Vec.invar x_code \<Longrightarrow> (Vec.\<alpha> (SOME v'. Vec.invar v' \<and> show_state v' = show_state x_code)) = Vec.\<alpha> x_code\<close>
  by (rule someI2[of _ x_code]) (auto simp: show_state_correct)

definition \<open>prefix_invar p \<longleftrightarrow> (case p of (t, a, pos) \<Rightarrow> length t = dims)\<close>
definition \<open>prefix_\<alpha> = (\<lambda>(t, a, pos). ((\<lambda>i. if i < dims then t ! i else None, a), pos))\<close>

lemma var_code_\<alpha>_f[simp]:
  assumes \<open>Vec.invar v\<close>
  shows \<open>var_code_\<alpha> (var_code.var_f p_code f (show_state v)) = var_name.var_f (prefix_\<alpha> p_code) (f_name_code_\<alpha> f) (Vec.\<alpha> v)\<close>
  unfolding prefix_\<alpha>_def
  by (auto simp: assms)

lemmas has_scope_on_cong[cong del]
lemmas Coeffs.correct(5)[simp]
lemmas Coeffs.correct(28)[intro]
lemmas Coeffs.to_map_correct(1)[simp]
lemmas Vec.vec_rel_in_vars[simp del]

lemma lookup0_nodom[simp]: \<open>i \<notin> dom  m \<Longrightarrow> lookup0 m i = 0\<close>
  unfolding lookup0_def
  by (auto split: option.splits)

lemmas var_code_\<alpha>.simps(2)[simp del]

lemma vec_\<alpha>_some_show_state'[simp]: \<open>Vec.invar x_code \<Longrightarrow> (Vec.\<alpha> (SOME v'. Vec.invar v' \<and> show_state v' = show_state x_code)) = Vec.\<alpha> x_code\<close>
  by (rule someI2[of _ x_code]) (auto simp: show_state_correct)

lemma f_name_rel_self[simp, intro]: \<open>f_name_rel f_code (f_name_code_\<alpha> f_code)\<close>
  by (cases \<open>f_code\<close>) (auto simp: f_name_rel_def)


lemma var_code_\<alpha>_phi[simp]: \<open>var_code_\<alpha> x = var_name.var_phi \<longleftrightarrow> x = var_phi\<close>
  by (cases \<open>x\<close>) (auto simp: var_code_\<alpha>.simps)

lemma var_code_\<alpha>_w[simp]: \<open>var_code_\<alpha> x = var_name.var_w i \<longleftrightarrow> x = var_w i\<close>
  by (cases \<open>x\<close>) (auto simp: var_code_\<alpha>.simps)

lemma lookup0_map_fn_rel_var_phi: \<open>map_fn_rel m f \<Longrightarrow> lookup0 m (var_phi) = f (var_name.var_phi)\<close>
  unfolding map_fn_rel_def
  by (auto simp: image_iff) (metis(no_types, lifting) var_code_\<alpha>_phi lookup0_dom lookup0_nodom)

lemma lookup0_map_fn_rel_var_w: \<open>map_fn_rel m f \<Longrightarrow> lookup0 m (var_w i) = f ((var_name.var_w i))\<close>
  unfolding map_fn_rel_def
  by (auto simp: image_iff) (metis(no_types, lifting) var_code_\<alpha>_w lookup0_dom lookup0_nodom)

lemma var_invar_prefix_invarD[dest]: \<open>var_invar (var_f p f x) \<Longrightarrow> prefix_invar p\<close>
  unfolding  prefix_invar_def var_invar_def
  by auto

lemma f_name_code_\<alpha>_eqD[dest]: \<open>f_name_code_\<alpha> x = f_name_code_\<alpha> y \<Longrightarrow> x = y\<close>
  by (cases x; cases y) auto

lemma var_code_\<alpha>_eqD[dest]: 
  assumes \<open>var_code_\<alpha> v = var_code_\<alpha> v'\<close> \<open>var_invar v\<close> \<open>var_invar v'\<close> 
  shows \<open>v = v'\<close>
proof -
  {
    fix p f v p' f' v'
    let ?f = \<open>(var_f p f v) :: (nat option list \<times> nat \<times> bool, nat option list) var_code\<close>
    let ?f' = \<open>(var_f p' f' v') :: (nat option list \<times> nat \<times> bool, nat option list) var_code\<close>
    assume h: \<open>var_code_\<alpha> ?f = var_code_\<alpha> ?f'\<close>
      \<open>var_invar ?f\<close> \<open>var_invar ?f'\<close>

    hence \<open>p = p'\<close>
      by (auto simp: var_code_\<alpha>.simps prefix_invar_def case_prod_unfold dest!: var_invar_prefix_invarD intro!: prod_eqI nth_equalityI)
        meson+

    moreover have \<open>f = f'\<close>
      using h
      by (auto simp: var_code_\<alpha>.simps)

    moreover have \<open>v = v'\<close>
      using show_state_correct h var_code_\<alpha>_f
      unfolding var_invar_def
      by (force simp del: var_code_\<alpha>_f)
      
    ultimately have \<open>?f = ?f'\<close>
      by auto
    }
    thus ?thesis
      using assms var_code_\<alpha>_phi[of v'] var_code_\<alpha>_w[of v'] var_code_\<alpha>_w[of v]
      by (cases v; cases v') force+
  qed

lemma some_var_eq[simp]: \<open>var_invar i \<Longrightarrow> i \<in> dom s \<Longrightarrow> (SOME v. v \<in> dom s \<and> var_invar v \<and> var_code_\<alpha> v = var_code_\<alpha> i) = i\<close> for i s
  by auto

lemma poly_\<alpha>_eq_lookup0[simp]: 
  \<open>v\<in>dom m \<Longrightarrow> var_invar v \<Longrightarrow> var_code_\<alpha> v = i \<Longrightarrow> 
  poly_\<alpha>' m i = lookup0 m v\<close>
  unfolding poly_\<alpha>'_def
  by (auto simp: some_equality var_code_\<alpha>_eqD)

lemma \<open>Some (poly_\<alpha>' sol_inv (var_code_\<alpha> i)) = sol_inv i\<close> if \<open>i \<in> dom sol_inv\<close> \<open>var_invar i\<close>
  using that
  poly_\<alpha>_eq_lookup0
  by auto
lemma map_fn_relE: 
  assumes \<open>map_fn_rel m f\<close>
  obtains \<open>\<And>i. i \<in> dom m \<Longrightarrow> var_invar i\<close>
    \<open>\<And>i. i \<in> dom m \<Longrightarrow> lookup0 m i = f (var_code_\<alpha> i)\<close>
    \<open>\<And>i. i \<notin> var_code_\<alpha> ` dom m \<Longrightarrow> f i = 0\<close>
  using assms 
    unfolding map_fn_rel_def
  by auto


lemma poly_\<alpha>'_nodom[simp]: \<open>i \<notin> var_code_\<alpha> ` dom s \<Longrightarrow> poly_\<alpha>' s i = 0\<close> for s i
    unfolding poly_\<alpha>'_def
    by auto

  lemma poly_\<alpha>_var_code[simp]: \<open>var_invar i \<Longrightarrow> i \<in> dom s \<Longrightarrow> poly_\<alpha>' s (var_code_\<alpha> i) = lookup0 s i\<close> for s i
    by (cases \<open>i \<in> dom s\<close>) auto


lemma poly_\<alpha>_var_code_inv[simp]: \<open>var_invar i \<Longrightarrow> dom s \<subseteq> Collect var_invar \<Longrightarrow> poly_\<alpha>' s (var_code_\<alpha> i) = lookup0 s i\<close> for s i
    by (cases \<open>i \<in> dom s\<close>) (auto simp: poly_\<alpha>'_def)



fun eval_constr_code_\<alpha> where
  \<open>eval_constr_code_\<alpha> (Constr_Le cs rhs) a \<longleftrightarrow> cross_prod (lookup0 (Coeffs.\<alpha> cs)) a \<le> rhs\<close> |
  \<open>eval_constr_code_\<alpha> (Constr_Eq cs rhs) a \<longleftrightarrow> cross_prod (lookup0 (Coeffs.\<alpha> cs)) a = rhs\<close>

definition \<open>constr_space_\<alpha> c_code = {v. eval_constr_code_\<alpha> c_code v}\<close>

definition \<open>sol_space_code_\<alpha> cs_code = {v. \<forall>c \<in> set cs_code. v \<in> constr_space_\<alpha> c}\<close>

lemma lookup0_nzE: \<open>lookup0 m x = y \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> m x = Some y\<close>
  unfolding lookup0_def
  by (auto split: option.splits)


lemma lookup0_nzE': 
  assumes \<open>lookup0 m x \<noteq> 0\<close> 
  obtains y where \<open>m x = Some y\<close> \<open>y \<noteq> 0\<close> 
  using assms
  unfolding lookup0_def
  by (auto split: option.splits)

lemma lookup0_nz_iff: \<open>lookup0 m x \<noteq> 0 \<longleftrightarrow> x \<in> dom m \<and> the (m x) \<noteq> 0\<close>
  unfolding lookup0_def
  by (auto split: option.splits)


lemma poly_rel_eval_eq:
  assumes constr_rel: \<open>poly_rel p_code p\<close>
  and sol_rel: \<open>map_fn_rel sol_code sol\<close>
shows \<open>cross_prod (lookup0 (Coeffs.\<alpha> p_code)) (lookup0 sol_code) = (\<Sum>i\<in>vars_poly p. p i * sol i)\<close>
proof -
  have *: \<open>Coeffs.invar p_code\<close>
    using assms unfolding poly_rel_def by auto

  hence \<open>finite (dom (Coeffs.\<alpha> p_code))\<close>
    by auto

  hence **: \<open>finite (var_code_\<alpha> ` dom (Coeffs.\<alpha> p_code))\<close>
    by auto

  have fin_vars: \<open>finite (vars_poly p)\<close>
    using constr_rel
    by (intro finite_subset[OF _ **]) 
      (auto simp: image_iff poly_rel_def elim!: map_fn_relE simp: vars_poly_def)

  have lookup_p_nz: \<open>\<And>i. i \<in> vars_poly p \<Longrightarrow> \<exists>i'. (var_code_\<alpha> i') = i \<and> lookup0 (Coeffs.\<alpha> p_code) i' \<noteq> 0\<close>
    using constr_rel
    unfolding poly_rel_def vars_poly_def
    by (auto elim!: map_fn_relE simp: image_iff) (metis (no_types, lifting) lookup0_dom)

  have lookup_sol_nz: \<open>\<And>i. i \<in> vars_poly sol \<Longrightarrow> \<exists>i'. (var_code_\<alpha> i') = i \<and> lookup0 sol_code i' \<noteq> 0\<close>
    using sol_rel
    unfolding poly_rel_def vars_poly_def
    by (auto elim!: map_fn_relE  simp: lookup0_nz_iff image_iff) (metis (no_types, lifting))

  have \<open>cross_prod (lookup0 (Coeffs.\<alpha> p_code)) (lookup0 sol_code) = 
  (\<Sum>i | lookup0 (Coeffs.\<alpha> p_code) i \<noteq> 0 \<and> lookup0 sol_code i \<noteq> 0. p (var_code_\<alpha> i) * sol (var_code_\<alpha> i))\<close>
    unfolding cross_prod_def
    apply (intro sum.cong[OF refl] arg_cong2[where f = \<open>(*)\<close>])
    using sol_rel * assms
    by (auto elim!: map_fn_relE lookup0_nzE' simp: poly_rel_def)
  also have \<open>\<dots> = (\<Sum> i \<in> (var_code_\<alpha>) ` {i.  lookup0 (Coeffs.\<alpha> p_code) i \<noteq> 0 \<and> lookup0 sol_code i \<noteq> 0}.  p i * sol i)\<close>
    apply (subst sum.reindex)
    using var_code_\<alpha>_eqD assms
    by (auto intro!: inj_onI elim!: map_fn_relE lookup0_nzE')
  also have \<open>\<dots> = (\<Sum>i\<in>vars_poly p \<inter> vars_poly sol. p i * sol i)\<close>
    apply (rule sum.mono_neutral_cong_left)
    subgoal using fin_vars by auto
    subgoal
      using constr_rel assms(2)
      by (auto simp: poly_rel_def vars_poly_def lookup0_nz_iff elim!: map_fn_relE )+
    subgoal
      using constr_rel sol_rel var_code_\<alpha>_eqD
      by (auto simp: image_iff poly_rel_def lookup0_nz_iff elim!: map_fn_relE) (metis (no_types, lifting))
    subgoal by auto
    done
  also have \<open>\<dots> = (\<Sum>i\<in>vars_poly p. p i * sol i)\<close>
    using fin_vars
    by (auto simp: vars_poly_def intro!: sum.mono_neutral_cong_left)
  finally show ?thesis
    .
qed

lemma constr_rel_sat_iff: 
  assumes constr_rel: \<open>constr_rel cs_code cs\<close>
  and sol_rel: \<open>map_fn_rel sol_code sol\<close>
shows \<open>sat_constr sol cs \<longleftrightarrow> lookup0 sol_code \<in> constr_space_\<alpha> cs_code\<close>
  unfolding constr_space_\<alpha>_def
  unfolding sat_constr_def
  using assms poly_rel_def
  by (cases \<open>cs_code\<close>; cases \<open>cs\<close>) (auto simp: poly_rel_eval_eq vars_constr_def)
  
lemma constrs_rel_sat_iff: 
  assumes constrs_rel: \<open>constrs_rel cs_code cs\<close>
  and sol_rel: \<open>map_fn_rel sol_code sol\<close>
shows \<open>sat_lp sol cs \<longleftrightarrow> lookup0 sol_code \<in> sol_space_code_\<alpha> cs_code\<close>
  using assms constr_rel_sat_iff[OF _ sol_rel]
  unfolding sat_lp_def constrs_rel_def sol_space_code_\<alpha>_def
  by (auto dest: rel_setD1 rel_setD2)

definition \<open>list_of_map m = map (\<lambda>i. (i, the (m i))) (SOME xs. set xs = (dom m) \<and> distinct xs)\<close>

lemma finite_list_of_map: 
  assumes \<open>finite (dom m)\<close> 
  shows \<open>map_of (list_of_map m) = m\<close>
proof -
  have \<open> set (SOME xs. set xs = dom m \<and> distinct xs) = dom m\<close>
    using someI2_ex[OF finite_distinct_list] assms
    by fast

  thus ?thesis
    unfolding list_of_map_def
    by fastforce
qed

lemma finite_map_has_code: \<open>finite (dom m) \<Longrightarrow> \<exists>m_code. Coeffs.invar m_code \<and> Coeffs.\<alpha> m_code = m\<close>
  using finite_list_of_map
  by (intro exI[of _ \<open>Coeffs.to_map (list_of_map m)\<close>]) auto

lemma sol_space_code_\<alpha>_correct:
  assumes \<open>Coeffs.invar v\<close>
  shows \<open>v \<in> Coeffs.sol_space_code cs_code \<longleftrightarrow> lookup0 (Coeffs.\<alpha> v) \<in> sol_space_code_\<alpha> cs_code\<close>
  unfolding Coeffs.sol_space_code_def sol_space_code_\<alpha>_def constr_space_\<alpha>_def Coeffs.sol_space_code_constr_def
  using assms
  by (auto elim!: Coeffs.eval_constr_code.elims eval_constr_code_\<alpha>.elims)

definition \<open>constr_code_vars c_code = (case c_code of Constr_Le p _ \<Rightarrow> dom (Coeffs.\<alpha> p) | Constr_Eq p _ \<Rightarrow> dom (Coeffs.\<alpha> p))\<close>
definition \<open>constrs_code_vars cs_code = (\<Union>c \<in> set cs_code. constr_code_vars c)\<close>


lemma vars_lp_subs:
  assumes          
    cs_rel: \<open>constrs_rel cs_code cs\<close>
  shows \<open>vars_lp cs \<subseteq> var_code_\<alpha> ` constrs_code_vars cs_code\<close>
  using assms
  unfolding constrs_rel_def vars_lp_def
  by (fastforce simp: vars_constr_def image_iff constrs_code_vars_def constr_code_vars_def poly_rel_def vars_poly_def 
      elim!: map_fn_relE constr_rel.elims dest!: rel_setD2 split: constr.splits Constr_Code.splits)

lemma constr_code_vars_fin:
  assumes          
    cs_rel: \<open>constrs_rel cs_code cs\<close>
  shows \<open>finite (constrs_code_vars cs_code)\<close>
  using assms
  unfolding constrs_rel_def vars_lp_def
  by (auto simp: vars_constr_def image_iff constrs_code_vars_def constr_code_vars_def poly_rel_def vars_poly_def  
      elim!: map_fn_relE constr_rel.elims dest!: rel_setD1 split: constr.splits Constr_Code.splits)

lemma finite_vars_lp[intro]:
  assumes \<open>constrs_rel cs_code cs\<close>
  shows \<open>finite (vars_lp cs)\<close>
  using vars_lp_subs constr_code_vars_fin assms
  by (meson finite_surj)

lemmas lookup0_map_fn_rel_var_phi[simp] lookup0_map_fn_rel_var_w[simp]

lemma in_var_code_\<alpha>_dom_iff: \<open>map_fn_rel m f \<Longrightarrow> var_invar i \<Longrightarrow> var_code_\<alpha> i \<in> var_code_\<alpha> ` dom m \<longleftrightarrow> i \<in> dom m\<close>
  by (auto elim!: map_fn_relE dest!: var_code_\<alpha>_eqD)
  

lemma map_fn_abs_zero[simp]: \<open>map_fn_rel m f \<Longrightarrow> var_invar i \<Longrightarrow> i \<notin> dom m \<Longrightarrow> f (var_code_\<alpha> i) = 0\<close>
  using in_var_code_\<alpha>_dom_iff[of m f i]
  by (auto elim!: map_fn_relE)

lemma lookup0_map_fn_rel[simp]: \<open>map_fn_rel m f \<Longrightarrow> var_invar i \<Longrightarrow> lookup0 m i = f (var_code_\<alpha> i)\<close>
  apply (cases i)
  subgoal by auto
  subgoal 
    apply (cases \<open>i \<in> dom m\<close>)
      using map_fn_abs_zero[of m f i]
      by (auto elim!: map_fn_relE)+
    subgoal by auto
    done


lemma lookup0_map_fn_rel_no_inv[simp]: \<open>map_fn_rel m f \<Longrightarrow> \<not>var_invar i \<Longrightarrow> lookup0 m i = 0\<close>
  apply (cases i)
  subgoal by auto
  subgoal 
    apply (cases \<open>i \<in> dom m\<close>)
      using map_fn_abs_zero[of m f i]
      by (auto elim!: map_fn_relE)+
    subgoal by auto
    done

lemma cross_prod_indep: \<open>cross_prod (lookup0 (Coeffs.\<alpha> c)) (lookup0 s) = cross_prod (lookup0 (Coeffs.\<alpha> c)) (lookup0 s')\<close> 
    if \<open>(\<And>i. i \<in> dom (Coeffs.\<alpha> (c)) \<Longrightarrow> s i = s' i)\<close> \<open>Coeffs.invar c\<close>
    for c s s'
  proof -
    have *: \<open>finite (dom (Coeffs.\<alpha> c))\<close>
      using that by auto
    have \<open>finite {x. lookup0 (Coeffs.\<alpha> c) x \<noteq> 0}\<close>
      by (auto intro: finite_subset[OF _ *] simp: lookup0_def split: option.splits)
    thus ?thesis
      unfolding cross_prod_def
      apply (intro sum.mono_neutral_cong)
      using that by (auto simp: lookup0_def domIff split: option.splits)
  qed


lemma constr_space_indep: \<open>lookup0 s \<in> constr_space_\<alpha> c \<longleftrightarrow> lookup0 s' \<in> constr_space_\<alpha> c\<close>
    if \<open>(\<And>i. i \<in> dom (Coeffs.\<alpha> (constr_code_poly c)) \<Longrightarrow> s i = s' i)\<close> \<open>(Coeffs.invar (constr_code_poly c))\<close>
    for c s s'
  unfolding constr_space_\<alpha>_def
  using that  cross_prod_indep[of _ s s']
  by (auto simp: constr_code_poly_def elim!: eval_constr_code_\<alpha>.elims)


lemma constr_rel_vars_invar: 
  \<open>constr_rel c_code c' \<Longrightarrow> dom (Coeffs.\<alpha> (constr_code_poly c_code)) \<subseteq> Collect var_invar\<close>
  by (auto elim!: constr_rel.elims simp: domIff poly_rel_def constr_code_poly_def elim!: map_fn_relE)

lemma constrs_rel_vars_invar: 
  \<open>constrs_rel cs_code c' \<Longrightarrow> c_code \<in> set cs_code \<Longrightarrow> dom (Coeffs.\<alpha> (constr_code_poly c_code)) \<subseteq> Collect var_invar\<close>
  unfolding constrs_rel_def
  using constr_rel_vars_invar
  by (auto dest!: rel_setD1)

lemma minimize_correct:
  assumes          
    cs_rel: \<open>constrs_rel cs_code (fst cs)\<close> and
    obj_rel: \<open>poly_rel obj_code' (\<lambda>i. case i of var_name.var_phi \<Rightarrow> 1 | _ \<Rightarrow> 0)\<close> and
    \<open>minimize (LP_Code obj_code' cs_code ) = Opt sol_code \<phi>_code\<close>
  shows
    \<open>Coeffs.invar sol_code\<close>
    \<open>is_arg_min' cs (\<phi>_code, (\<lambda>i. lookup0 (Coeffs.\<alpha> sol_code) (var_w i)))\<close>
proof (goal_cases)
  have inv_obj: \<open>Coeffs.invar obj_code'\<close>
    using assms
    unfolding poly_rel_def constrs_rel_def
    by auto
  moreover have inv_constr: \<open>Coeffs.invar (constr_code_poly c)\<close> if \<open>c \<in> set cs_code\<close> for c
  proof -
    obtain c' where \<open>constr_rel c c'\<close>
      using assms \<open>c \<in> set cs_code\<close>
      unfolding constrs_rel_def
      by (auto dest!: rel_setD1)
    thus ?thesis
      by (cases c; cases c') (auto simp: poly_rel_def constr_code_poly_def)
  qed

  hence fin_vars_lp: \<open>finite (vars_lp (fst cs))\<close>
    using assms 
    by auto
  
  case 1
  thus ?case
    using assms inv_obj inv_constr minimize_Opt_specs(1) by auto
  case 2

  have 
    inv_sol: \<open>Coeffs.invar sol_code\<close> and
    cross_prod_sol: \<open>Coeffs.cross_prod_code sol_code obj_code' = \<phi>_code\<close> and
    sol_space_sol: \<open>sol_code \<in> Coeffs.sol_space_code cs_code\<close> and
    opt_sol: \<open>\<And>sol'. sol'\<in>Coeffs.sol_space_code cs_code \<Longrightarrow> \<phi>_code \<le> Coeffs.cross_prod_code sol' obj_code'\<close>
    using assms(3) calculation inv_constr minimize_Opt_specs by auto
  
  define sol_inv where \<open>sol_inv = (Coeffs.\<alpha> sol_code |` {v. var_invar v})\<close>

  define sol where \<open>sol = poly_\<alpha>' sol_inv\<close>

  have dom_sol_inv[intro]: \<open>i \<in> dom sol_inv \<Longrightarrow> var_invar i\<close> for i
    unfolding sol_inv_def by auto


  have sol_rel: \<open>map_fn_rel sol_inv sol\<close>
    using dom_sol_inv
    by (auto simp: sol_def domIff)

  have poly_rel_lookup0[simp]: \<open>poly_rel p_code p \<Longrightarrow> var_invar i \<Longrightarrow> lookup0 (Coeffs.\<alpha> p_code) i = p (var_code_\<alpha> i)\<close> for p_code p i
    unfolding poly_rel_def by auto

  have poly_rel_lookup_nz[simp]: \<open>poly_rel p_code p \<Longrightarrow> i \<in> dom (Coeffs.\<alpha> p_code) \<Longrightarrow> 
    lookup0 (Coeffs.\<alpha> p_code) i = p (var_code_\<alpha> i)\<close> for p_code p i
    unfolding poly_rel_def
    by (auto elim!: map_fn_relE)+

  hence poly_rel_lookup_nz[simp]: \<open>poly_rel p_code p \<Longrightarrow> i \<in> dom (Coeffs.\<alpha> p_code) \<Longrightarrow> 
    lookup0 (Coeffs.\<alpha> p_code) i = p (var_code_\<alpha> i)\<close> for p_code p i
    unfolding poly_rel_def
    by auto

  have lookup0_obj_code: \<open>var_invar i \<Longrightarrow> lookup0 (Coeffs.\<alpha> obj_code') i = (\<lambda>i. case i of var_name.var_phi \<Rightarrow> 1 | _ \<Rightarrow> 0) (var_code_\<alpha> i)\<close> for i
    using obj_rel
    by auto

  have obj_code_phi[simp]: \<open>lookup0 (Coeffs.\<alpha> obj_code') var_code.var_phi = 1\<close>
    using obj_rel
    by auto

  have obj_code'_nz_iff[simp]: \<open>lookup0 (Coeffs.\<alpha> obj_code') x \<noteq> 0 \<longleftrightarrow> x = var_code.var_phi\<close> for x
    apply (cases \<open>var_invar x\<close>)
    using obj_rel poly_rel_def
    by (auto split: var_name.splits)


  have cross_prod_sol_obj[simp]: \<open>Coeffs.cross_prod_code sol_code obj_code' = lookup0 (Coeffs.\<alpha> sol_code) var_code.var_phi\<close>
    unfolding cross_prod_def
    using lookup0_obj_code
    by (subst sum.cong[of _ \<open>if lookup0 (Coeffs.\<alpha> sol_code) var_code.var_phi = 0 then {} else {var_code.var_phi}\<close>])
      auto

  hence sol_code_phi[simp]: \<open>lookup0 (Coeffs.\<alpha> sol_code) var_code.var_phi = \<phi>_code\<close>
    using cross_prod_sol
    by auto

  have \<phi>_code_sol: \<open>\<phi>_code = sol var_name.var_phi\<close>
    unfolding sol_def sol_inv_def
    using sol_code_phi
    by (auto simp: restrict_map_def lookup0_def split: option.splits simp del: sol_code_phi)
  
  have *: \<open>lookup0 (Coeffs.\<alpha> sol_code) \<in> sol_space_code_\<alpha> cs_code\<close>
    using assms
    using inv_sol sol_space_code_\<alpha>_correct sol_space_sol by blast


  hence \<open>lookup0 sol_inv \<in> constr_space_\<alpha> c\<close> if \<open>c \<in> set cs_code\<close> for c 
    apply (subst constr_space_indep[of _ _ \<open>(Coeffs.\<alpha> sol_code)\<close>])
    using that  inv_constr constrs_rel_vars_invar[OF assms(1) that]
    unfolding sol_inv_def sol_space_code_\<alpha>_def
    by auto

  hence \<open>lookup0 sol_inv \<in> sol_space_code_\<alpha> cs_code\<close>
    using assms(1) sol_space_code_\<alpha>_def
    by auto

  hence sat_lp: \<open>sat_lp sol (fst cs)\<close>
    apply (subst constrs_rel_sat_iff[OF assms(1) sol_rel])
    using sol_space_sol
    by blast

  have \<open>(\<phi>_code, \<lambda>i. lookup0 sol_inv (var_code.var_w i)) \<in> constr_set cs\<close>
    unfolding constr_set_def
    using \<phi>_code_sol sat_lp
    by (auto intro!: exI[of _ sol] ext simp: sol_def)

  moreover have \<open>\<phi>_code \<le> \<phi>'\<close> if 
      is_sol: \<open>(\<phi>', w') \<in> constr_set cs\<close>
      for \<phi>' w'
  proof -
    obtain full_sol 
      where full_sol: \<open>sat_lp full_sol (fst cs)\<close>
       \<open>full_sol var_name.var_phi = \<phi>'\<close> 
       \<open>\<And>i. full_sol (var_name.var_w i) = w' i\<close>
      using that is_sol unfolding constr_set_def
      by auto

    let ?sol = \<open>\<lambda>i. if i \<in> insert var_name.var_phi (vars_lp (fst cs)) then full_sol i else 0\<close>

    have \<open>vars_poly ?sol \<subseteq> insert var_name.var_phi (vars_lp (fst cs))\<close>
      unfolding vars_poly_def
      by auto

    have sol_sat: \<open>sat_lp ?sol (fst cs)\<close>
      using full_sol fin_vars_lp
      unfolding sat_lp_def sat_constr_def vars_lp_def
      apply (auto split: constr.splits)
      by (smt (verit, best) sum.cong)+
    
    have sol_phi: \<open>?sol var_name.var_phi = \<phi>'\<close>
      using full_sol
      by (auto split: if_splits)

    define sol_code_\<alpha> where sol_code_\<alpha>: \<open>sol_code_\<alpha> = (\<lambda>i. if var_invar i \<and> ?sol (var_code_\<alpha> i) \<noteq> 0 then Some (?sol (var_code_\<alpha> i)) else None)\<close>

    have "var_code_\<alpha> ` (dom sol_code_\<alpha>) \<subseteq> insert var_name.var_phi  (vars_lp (fst cs))"
      unfolding sol_code_\<alpha>
      using fin_vars_lp
      by (auto simp: domIff split: if_splits)

    have "finite (var_code_\<alpha> ` (dom sol_code_\<alpha>))"
      using \<open>var_code_\<alpha> ` dom sol_code_\<alpha> \<subseteq> insert var_name.var_phi (vars_lp (fst cs))\<close> fin_vars_lp finite_subset 
      by auto

    hence \<open>finite (dom sol_code_\<alpha>)\<close>
      apply (subst (asm) finite_image_iff)
      by (auto simp: inj_on_def sol_code_\<alpha> split: if_splits)
     
    then obtain sol' where inv_sol': \<open>Coeffs.invar sol'\<close> and [simp]: \<open>Coeffs.\<alpha> sol' = sol_code_\<alpha>\<close>
      using finite_map_has_code
      by auto

    have vars_cs_have_code: \<open>i \<in> vars_lp (fst cs) \<Longrightarrow> \<exists>v. var_invar v \<and> var_code_\<alpha> v = i\<close> for i
      apply (cases i)
      subgoal
        unfolding vars_lp_def vars_constr_def vars_poly_def
        using assms(1)
      unfolding constrs_rel_def vars_lp_def
      apply (auto dest!: rel_setD2 simp: image_iff poly_rel_def elim!: map_fn_relE constr_rel.elims)
      by (metis (no_types, lifting))+
      subgoal by auto
      subgoal by auto
      done
    hence sol'_rel: \<open>poly_rel sol' ?sol\<close>
      unfolding poly_rel_def
      using inv_sol'
      by (auto simp: sol_code_\<alpha> image_iff Ball_def domIff intro!: map_fn_relI split: if_splits)+

    have \<open>Coeffs.cross_prod_code sol' obj_code' = \<phi>'\<close>
      apply (subst poly_rel_eval_eq[OF sol'_rel, of \<open>(Coeffs.\<alpha> obj_code')\<close> \<open>(\<lambda>i. case i of var_name.var_phi \<Rightarrow> 1 | _ \<Rightarrow> 0)\<close>])
      subgoal
        using obj_rel
        by (auto simp: poly_rel_def)
      subgoal
      unfolding vars_poly_def
      apply (subst sum.mono_neutral_cong_right[where S = \<open>if  full_sol var_name.var_phi = 0 then {} else {var_name.var_phi}\<close>, OF _ _ _ refl])
      subgoal using fin_vars_lp by auto
      subgoal by simp
      subgoal by (auto split: var_name.splits)
      subgoal using full_sol by fastforce+
      done
    done

  moreover have \<open>sol' \<in> Coeffs.sol_space_code cs_code\<close>
    apply (subst sol_space_code_\<alpha>_correct)
    subgoal using poly_rel_def sol'_rel by blast
    subgoal
    using sol'_rel sol_sat
    unfolding poly_rel_def
    by (subst constrs_rel_sat_iff[symmetric, OF assms(1)]) auto
    done
    
  ultimately show ?thesis
      using opt_sol
      by blast

  qed

  ultimately show ?case
    unfolding is_arg_min'_def sol_inv_def
    by (auto simp: restrict_map_def lookup0_def)
qed

lemma minimize_lp_code_in_constr_set:
  assumes \<open>minimize lp_code = Opt m v\<close>
  shows \<open>(v, \<lambda>i. lookup0 (Coeffs.\<alpha> m) (var_code.var_w i)) \<in> constr_set constrs\<close>
  using minimize_correct constrs_rel obj_code_rel assms
  unfolding is_arg_min'_def lp_code_def
  by auto

lemma lp_code_opt_invar: \<open>minimize lp_code = Opt sol val \<Longrightarrow> Coeffs.invar sol\<close>
  apply (rule minimize_correct[of \<open>constrs_code\<close> _ obj_code])
  using constrs_rel obj_code_rel
  by (auto simp: lp_code_def)

lemma is_arg_min_constrs_opt_lp_code: 
  assumes \<open>minimize lp_code = Opt sol v\<close>
  shows \<open>is_arg_min' constrs (v, (\<lambda>i. lookup0 (Coeffs.\<alpha> sol) (var_code.var_w i)))\<close>
  using minimize_correct constrs_rel obj_code_rel assms
  unfolding is_arg_min'_def lp_code_def
  by simp


lemma default_sol: \<open>Coeffs.invar (fst default_sol)\<close>
    \<open>fst default_sol \<in> Coeffs.sol_space_code constrs_code\<close>
    \<open>snd default_sol = Coeffs.cross_prod_code (fst default_sol) obj_code\<close>
    \<open>(\<forall>sol'\<in>Coeffs.sol_space_code constrs_code. snd default_sol \<le> Coeffs.cross_prod_code sol' obj_code)\<close>
proof -
  have fin_vars_constr: \<open>finite (vars_lp (fst constrs))\<close>
    using constrs_rel by auto

  obtain sol_opt where is_sol: \<open>is_arg_min' constrs sol_opt\<close>
    using ex_is_arg_min'_constrs .. 
  
    obtain full_sol 
      where full_sol: 
        \<open>sat_lp full_sol (fst constrs)\<close>
       \<open>full_sol var_name.var_phi = fst sol_opt\<close>
       \<open>\<And>i. full_sol (var_name.var_w i) = snd sol_opt i\<close>
      \<open>\<And>full_sol'. sat_lp full_sol' (fst constrs) \<Longrightarrow> full_sol var_name.var_phi \<le> full_sol' var_name.var_phi\<close>
      using that is_sol unfolding constr_set_def is_arg_min'_def
      by fastforce

    let ?sol = \<open>\<lambda>i. if i \<in> insert var_name.var_phi (vars_lp (fst constrs)) then full_sol i else 0\<close>

    have \<open>vars_poly ?sol \<subseteq> insert var_name.var_phi (vars_lp (fst constrs))\<close>
      unfolding vars_poly_def
      by auto

    have \<open>\<And>c. c \<in> fst constrs \<Longrightarrow> sat_constr full_sol c \<Longrightarrow> sat_constr ?sol c\<close>
      using  fin_vars_constr
      unfolding sat_lp_def sat_constr_def vars_lp_def
      apply (auto split: constr.splits simp: intro!: sum.cong)
      by (smt (verit, best) sum.cong)+

    hence sol_sat: \<open>sat_lp ?sol (fst constrs)\<close>
      using full_sol fin_vars_constr
      unfolding sat_lp_def sat_constr_def vars_lp_def
      by (auto split: constr.splits simp:  if_distrib elim!: ballE intro!: sum.cong)

    have sol_phi: \<open>?sol var_name.var_phi = fst sol_opt\<close>
      using full_sol
      by (auto split: if_splits)

    define sol_code_\<alpha> where sol_code_\<alpha>: 
      \<open>sol_code_\<alpha> = (\<lambda>i. if var_invar i \<and> ?sol (var_code_\<alpha> i) \<noteq> 0 then Some (?sol (var_code_\<alpha> i)) else None)\<close>

    have "var_code_\<alpha> ` (dom sol_code_\<alpha>) \<subseteq> insert var_name.var_phi  (vars_lp (fst constrs))"
      unfolding sol_code_\<alpha>
      by (auto simp: domIff split: if_splits)

    have "finite (var_code_\<alpha> ` (dom sol_code_\<alpha>))"
      using \<open>var_code_\<alpha> ` dom sol_code_\<alpha> \<subseteq> insert var_name.var_phi (vars_lp (fst constrs))\<close> 
        fin_vars_constr finite_subset by auto

    hence \<open>finite (dom sol_code_\<alpha>)\<close>
      apply (subst (asm) finite_image_iff)
      by (auto simp: inj_on_def sol_code_\<alpha> split: if_splits)
     
    then obtain sol' where inv_sol': \<open>Coeffs.invar sol'\<close> and [simp]: \<open>Coeffs.\<alpha> sol' = sol_code_\<alpha>\<close>
      using finite_map_has_code
      by auto

    have vars_cs_have_code: \<open>i \<in> vars_lp (fst constrs) \<Longrightarrow> \<exists>v. var_invar v \<and> var_code_\<alpha> v = i\<close> for i
      using  constrs_rel
      unfolding constrs_rel_def vars_lp_def
      apply (auto dest!: rel_setD2 simp: image_iff vars_constr_def vars_poly_def poly_rel_def elim!: map_fn_relE constr_rel.elims)
      by (metis (no_types, lifting))+

    hence sol'_rel: \<open>poly_rel sol' ?sol\<close>
      unfolding poly_rel_def map_fn_rel_def 
      using vars_cs_have_code inv_sol' var_phi_inv
      by (auto simp: image_iff domIff sol_code_\<alpha> Ball_def split: if_splits)
      
    have \<open>Coeffs.cross_prod_code sol' obj_code = fst sol_opt\<close>
      apply (subst poly_rel_eval_eq[OF sol'_rel, of \<open>(Coeffs.\<alpha> obj_code)\<close> 
            \<open>(\<lambda>i. case i of var_name.var_phi \<Rightarrow> 1 | _ \<Rightarrow> 0)\<close>])
      subgoal using obj_code_rel poly_rel_def by auto
      apply (subst sum.mono_neutral_cong_right[where S = 
            \<open>if  full_sol var_name.var_phi = 0 then {} else {var_name.var_phi}\<close>])
      using fin_vars_constr full_sol unfolding vars_poly_def
      by (auto split: var_name.splits)

  moreover have \<open>sol' \<in> Coeffs.sol_space_code constrs_code\<close>
    apply (subst sol_space_code_\<alpha>_correct)
    using poly_rel_def sol'_rel
    subgoal by blast
    apply (subst constrs_rel_sat_iff[symmetric, OF constrs_rel])
    using sol'_rel sol_sat
    unfolding poly_rel_def
    by auto

  ultimately have \<open>Coeffs.cross_prod_code sol' obj_code \<le> Coeffs.cross_prod_code sol'' obj_code\<close>
    if \<open>Coeffs.invar sol''\<close> \<open>sol'' \<in> Coeffs.sol_space_code constrs_code\<close> for sol''
  proof -
  
  define sol_inv where \<open>sol_inv = (Coeffs.\<alpha> sol'' |` {v. var_invar v})\<close>

  define sol where \<open>sol = poly_\<alpha>' sol_inv\<close>


  have dom_sol_inv[intro]: \<open>i \<in> dom sol_inv \<Longrightarrow> var_invar i\<close> for i
    unfolding sol_inv_def by auto

  have sol_rel: \<open>map_fn_rel sol_inv sol\<close>
      unfolding sol_def   
      by (auto simp: domIff dom_sol_inv )  

  have lookup0_obj_code: \<open>lookup0 (Coeffs.\<alpha> obj_code) i \<noteq> 0 \<Longrightarrow> i = var_code.var_phi\<close> for i
    using obj_code_rel 
    unfolding poly_rel_def cross_prod_def  lookup0_def obj_code_def
    by (auto split: option.splits var_name.splits elim!: map_fn_relE)
  

  have obj_code_phi[simp]: \<open>lookup0 (Coeffs.\<alpha> obj_code) var_code.var_phi = 1\<close>
    using obj_code_rel
    unfolding poly_rel_def cross_prod_def  lookup0_def obj_code_def
    by (auto split: option.splits var_name.splits elim!: map_fn_relE)

  have cross_prod_sol''_obj: \<open> Coeffs.cross_prod_code sol'' obj_code = lookup0 (Coeffs.\<alpha> sol'') var_code.var_phi\<close>
    unfolding cross_prod_def
    using lookup0_obj_code
    apply (subst sum.cong[of _ \<open>if lookup0 (Coeffs.\<alpha> sol'') var_code.var_phi = 0 then {} else {var_code.var_phi}\<close>])
    by auto


  have cross_prod_sol''_sol[simp]: \<open> Coeffs.cross_prod_code sol'' obj_code = sol var_name.var_phi\<close>
    unfolding cross_prod_sol''_obj
    by (auto simp: lookup0_def sol_def sol_inv_def split: option.splits)
   

  have cross_prod_sol_obj[simp]: \<open>Coeffs.cross_prod_code sol' obj_code = 
    lookup0 (Coeffs.\<alpha> sol') var_code.var_phi\<close>
    unfolding cross_prod_def
    using lookup0_obj_code
    apply (subst sum.cong[of _ \<open>if lookup0 (Coeffs.\<alpha> sol') var_code.var_phi = 0 then {} else {var_code.var_phi}\<close>])
    by auto

  hence sol_code_phi[simp]: \<open>lookup0 (Coeffs.\<alpha> sol') var_code.var_phi = fst sol_opt\<close>
    using \<open>Coeffs.cross_prod_code sol' obj_code = fst sol_opt\<close>
    by auto

  have constr_code_poly_inv[intro]: \<open>Coeffs.invar (constr_code_poly c)\<close> if \<open>c \<in> set constrs_code\<close> for c
    using that constrs_rel
    unfolding constrs_rel_def 
    by (auto dest!: rel_setD1 elim!: constr_rel.elims simp: constr_code_poly_def poly_rel_def)
    

  have *: \<open>lookup0 (Coeffs.\<alpha> sol'') \<in> sol_space_code_\<alpha> constrs_code\<close>
    apply (subst sol_space_code_\<alpha>_correct[symmetric])
    using that
    by auto

  hence \<open>lookup0 sol_inv \<in> constr_space_\<alpha> c\<close> if \<open>c \<in> set constrs_code\<close> for c
      apply (subst constr_space_indep[of _ _ \<open>(Coeffs.\<alpha> sol'')\<close>])
      using * that that constrs_rel constrs_rel_vars_invar unfolding sol_inv_def sol_space_code_\<alpha>_def
      by fastforce+

  hence \<open>lookup0 sol_inv \<in> sol_space_code_\<alpha> constrs_code\<close>
    using sol_space_code_\<alpha>_def
    by auto

  hence sat_lp: \<open>sat_lp sol (fst constrs)\<close>
    apply (subst constrs_rel_sat_iff[OF constrs_rel sol_rel])
    by blast

  hence \<open>fst sol_opt \<le>  sol var_name.var_phi\<close>
    using is_sol
    unfolding is_arg_min'_def constr_set_def
    by auto


  then show \<open>Coeffs.cross_prod_code sol' obj_code \<le> Coeffs.cross_prod_code sol'' obj_code\<close>
    unfolding cross_prod_sol_obj sol_code_phi  
    by simp
qed

  moreover have sol'_sat: \<open>sol' \<in> Coeffs.sol_space_code constrs_code\<close>
    apply (subst sol_space_code_\<alpha>_correct[OF inv_sol'])
    apply (subst constrs_rel_sat_iff[symmetric, OF constrs_rel])
    using sol'_rel sol_sat
    unfolding poly_rel_def
    by auto
    
  ultimately have ex_opt_code: \<open>\<exists>vs.
    snd vs = Coeffs.cross_prod_code (fst vs) obj_code \<and>
    fst vs \<in>Coeffs.sol_space_code constrs_code \<and>
      (\<forall>sol'\<in>Coeffs.sol_space_code constrs_code. snd vs \<le> Coeffs.cross_prod_code sol' obj_code) \<and>
 Coeffs.invar (fst vs)\<close>
    unfolding Coeffs.sol_space_code_def 
    using sol'_rel
    by (auto intro!: exI[of _ sol'])

  thus 
    \<open>Coeffs.invar (fst default_sol)\<close>
    \<open>fst default_sol \<in> Coeffs.sol_space_code constrs_code\<close>
    \<open>snd default_sol = Coeffs.cross_prod_code (fst default_sol) obj_code\<close>
    \<open>(\<forall>sol'\<in>Coeffs.sol_space_code constrs_code. snd default_sol \<le> Coeffs.cross_prod_code sol' obj_code)\<close>
    unfolding default_sol_def case_prod_unfold
    using someI_ex[OF ex_opt_code]
    by blast+
qed

lemma default_sol_opt: 
  shows \<open>is_arg_min' constrs (snd default_sol, \<lambda>i. lookup0 (Coeffs.\<alpha> (fst default_sol)) (var_code.var_w i))\<close>
proof -

  define sol_inv where \<open>sol_inv = (Coeffs.\<alpha> (fst default_sol) |` {v. var_invar v})\<close>

  define sol where \<open>sol = poly_\<alpha>' sol_inv\<close>

  have map_fn_relI[intro!]: \<open>map_fn_rel m_code m\<close> if \<open>dom m_code \<subseteq> {v. var_invar v}\<close> 
    and \<open>\<And>i. i \<in> dom m_code \<Longrightarrow> m_code i = Some (m (var_code_\<alpha> i))\<close>
    and \<open>\<And>i. i \<notin> var_code_\<alpha> ` dom m_code \<Longrightarrow> m i = 0\<close> for m m_code
    unfolding map_fn_rel_def lookup0_def
    using that
    by auto

  have dom_sol_inv[intro]: \<open>i \<in> dom sol_inv \<Longrightarrow> var_invar i\<close> for i
    unfolding sol_inv_def by auto

  hence sol_rel: \<open>map_fn_rel sol_inv sol\<close>
    by (auto simp: domIff sol_def)

  have lookup0_obj_code: \<open>lookup0 (Coeffs.\<alpha> obj_code) i \<noteq> 0 \<Longrightarrow> i = var_code.var_phi\<close> for i
    using obj_code_rel
    unfolding poly_rel_def cross_prod_def  lookup0_def obj_code_def
    by (auto split: option.splits var_name.splits elim!: map_fn_relE)
   

  have obj_code_phi[simp]: \<open>lookup0 (Coeffs.\<alpha> obj_code) var_code.var_phi = 1\<close>
    using obj_code_rel
    unfolding poly_rel_def cross_prod_def  lookup0_def obj_code_def
    by (auto split: option.splits var_name.splits elim!: map_fn_relE)
   
  have cross_prod_sol_obj[simp]: \<open>Coeffs.cross_prod_code (fst default_sol) obj_code = lookup0 (Coeffs.\<alpha> (fst default_sol)) var_code.var_phi\<close>
    unfolding cross_prod_def
    using lookup0_obj_code
    apply (subst sum.cong[of _ \<open>if lookup0 (Coeffs.\<alpha> (fst default_sol)) var_code.var_phi = 0 then {} else {var_code.var_phi}\<close>])
    by auto

  hence sol_code_phi[simp]: \<open>lookup0 (Coeffs.\<alpha> (fst default_sol)) var_code.var_phi = snd default_sol\<close>
    using default_sol(3) 
    by presburger

  have \<phi>_code_sol: \<open>snd default_sol = sol var_name.var_phi\<close>
    unfolding sol_def sol_inv_def
    using sol_code_phi
    by (auto simp: restrict_map_def lookup0_def split: option.splits simp del: sol_code_phi)
  
  have constr_code_poly_inv[intro]: \<open>Coeffs.invar (constr_code_poly c)\<close> if \<open>c \<in> set constrs_code\<close> for c
    using that constrs_rel
    unfolding constrs_rel_def 
    by (auto dest!: rel_setD1 elim!: constr_rel.elims simp: constr_code_poly_def poly_rel_def)
    
  have *: \<open>lookup0 (Coeffs.\<alpha> (fst default_sol)) \<in> sol_space_code_\<alpha> constrs_code\<close>
    using constrs_rel default_sol
    using  sol_space_code_\<alpha>_correct  by blast

  hence \<open>lookup0 sol_inv \<in> constr_space_\<alpha> c\<close> if \<open>c \<in> set constrs_code\<close> for c 
      apply (subst constr_space_indep[of _ _ \<open>(Coeffs.\<alpha> (fst default_sol))\<close>])
    using * that  constrs_rel constrs_rel_vars_invar unfolding sol_inv_def sol_space_code_\<alpha>_def
    by (fastforce intro!: constr_code_poly_inv)+

  hence \<open>lookup0 sol_inv \<in> sol_space_code_\<alpha> (constrs_code)\<close>
    using sol_space_code_\<alpha>_def
    by auto

  hence sat_lp: \<open>sat_lp sol (fst constrs)\<close>
    apply (subst constrs_rel_sat_iff[OF constrs_rel sol_rel])
    by blast

  hence \<open>(fst (snd default_sol, \<lambda>i. lookup0 (Coeffs.\<alpha> (fst default_sol)) (var_code.var_w i)), snd (snd default_sol, \<lambda>i. lookup0 (Coeffs.\<alpha> (fst default_sol)) (var_code.var_w i))) \<in> constr_set constrs\<close>
    unfolding constr_set_def
    using default_sol
    by (auto intro!: ext exI[of _ sol] simp: sol_def sol_inv_def lookup0_def)

  moreover have \<open>snd default_sol \<le> \<phi>'\<close> if is_sol: \<open>(\<phi>', w') \<in> constr_set constrs\<close> for \<phi>' w'
  proof -
    obtain full_sol 
      where full_sol: \<open>sat_lp full_sol (fst constrs)\<close>
       \<open>full_sol var_name.var_phi = \<phi>'\<close> 
       \<open>\<And>i. full_sol (var_name.var_w i) = w' i\<close>
      using that is_sol unfolding constr_set_def
      by auto

    let ?sol = \<open>\<lambda>i. if i \<in> insert var_name.var_phi (vars_lp (fst constrs)) then full_sol i else 0\<close>

    have \<open>vars_poly ?sol \<subseteq> insert var_name.var_phi (vars_lp (fst constrs))\<close>
      unfolding vars_poly_def
      by auto

    have sol_sat: \<open>sat_lp ?sol (fst constrs)\<close>
      using full_sol 
      unfolding sat_lp_def sat_constr_def vars_lp_def
      apply (auto split: constr.splits)
      by (smt (verit, best) sum.cong)+
    
    have sol_phi: \<open>?sol var_name.var_phi = \<phi>'\<close>
      using full_sol
      by (auto split: if_splits)

    define sol_code_\<alpha> where sol_code_\<alpha>: \<open>sol_code_\<alpha> = (\<lambda>i. if var_invar i \<and> ?sol (var_code_\<alpha> i) \<noteq> 0 then Some (?sol (var_code_\<alpha> i)) else None)\<close>

    have *: "var_code_\<alpha> ` (dom sol_code_\<alpha>) \<subseteq> insert var_name.var_phi  (vars_lp (fst constrs))"
      unfolding sol_code_\<alpha>
      by (auto simp: domIff split: if_splits)

    have "finite (var_code_\<alpha> ` (dom sol_code_\<alpha>))"
      apply (rule finite_subset[OF *])
      using constrs_rel
      by auto

    hence \<open>finite (dom sol_code_\<alpha>)\<close>
      apply (subst (asm) finite_image_iff)
      by (auto simp: inj_on_def sol_code_\<alpha> split: if_splits)
     
    then obtain sol' where inv_sol': \<open>Coeffs.invar sol'\<close> and [simp]: \<open>Coeffs.\<alpha> sol' = sol_code_\<alpha>\<close>
      using finite_map_has_code
      by auto

    have vars_cs_have_code: \<open>i \<in> vars_lp (fst constrs) \<Longrightarrow> \<exists>v. var_invar v \<and> var_code_\<alpha> v = i\<close> for i
      using constrs_rel
      unfolding constrs_rel_def vars_lp_def
      apply (auto dest!: rel_setD2 simp: image_iff vars_constr_def vars_poly_def poly_rel_def elim!: map_fn_relE constr_rel.elims)
      by (metis (no_types, lifting))+

    hence sol'_rel: \<open>poly_rel sol' ?sol\<close>
      unfolding poly_rel_def
      using vars_cs_have_code inv_sol'
      by (auto simp: sol_code_\<alpha> image_iff Ball_def domIff split: if_splits)+

    have \<open>Coeffs.cross_prod_code sol' obj_code = \<phi>'\<close>
      apply (subst poly_rel_eval_eq[OF sol'_rel, of \<open>(Coeffs.\<alpha> obj_code)\<close> \<open>(\<lambda>i. case i of var_name.var_phi \<Rightarrow> 1 | _ \<Rightarrow> 0)\<close>])
      subgoal using  obj_code_rel unfolding poly_rel_def by auto
      subgoal
      apply (subst sum.mono_neutral_cong_right[where S = \<open>if  full_sol var_name.var_phi = 0 then {} else {var_name.var_phi}\<close>, OF _ _ _ refl])
      subgoal using constrs_rel unfolding vars_poly_def by fastforce
      subgoal unfolding vars_poly_def by simp
      subgoal by (auto split: var_name.splits)
      subgoal using full_sol by fastforce+
      done
    done

  moreover have \<open>sol' \<in> Coeffs.sol_space_code constrs_code\<close>
    apply (subst sol_space_code_\<alpha>_correct)
    using poly_rel_def sol'_rel apply blast
    apply (subst constrs_rel_sat_iff[symmetric, OF constrs_rel])
    using sol'_rel sol_sat
    unfolding poly_rel_def
    by auto
    
  ultimately show ?thesis
    using default_sol(4) by blast
  qed
  
  ultimately show ?thesis
    unfolding is_arg_min'_def sol_inv_def
    by (auto simp: restrict_map_def lookup0_def)
qed

lemma lp_sol_code_opt: 
  \<open>is_arg_min' constrs (snd lp_sol_code, \<lambda>i. lookup0 (Coeffs.\<alpha> (fst lp_sol_code)) (var_code.var_w i))\<close>
  unfolding lp_sol_code_def default_sol_opt
  using is_arg_min_constrs_opt_lp_code default_sol_opt 
  by (cases \<open>minimize lp_code\<close>) auto

lemma invar_lp_sol_code: \<open>Coeffs.invar (fst lp_sol_code)\<close>
  using lp_code_opt_invar default_sol default_sol_opt
  unfolding lp_sol_code_def case_prod_unfold
  by (cases \<open>minimize lp_code\<close>) auto
 
lemma minimize'_correct: \<open>is_arg_min' constrs minimize'\<close>
  using lp_sol_code_opt invar_lp_sol_code
  unfolding minimize'_def Let_def case_prod_unfold real_of_ereal.simps lookup0_def Coeffs.lookup0_code_def
  by (subst Coeffs.lookup_correct) auto

sublocale ValueDet_API
  where
    inv_constr = Factored_LP_Inst.inv_constr and
    union_constr = Factored_LP_Inst.union_constr and
    empty_constr = Factored_LP_Inst.empty_constr and 
    constr_set = Factored_LP_Inst.constr_set and
    min_sol = minimize' and
    privates = Factored_LP_Inst.privates and
    gen_constr = \<open>\<Omega>\<close> and
    dec_pol = dec_pol
  using minimize'_correct dec_pol_spec' gen_constr_spec 
  by unfold_locales auto

lemma upd_weights_rel: \<open>w_rel (upd_weights_code) update_weights\<close>
  unfolding upd_weights_code_def Let_def update_weights_def
  unfolding minimize'_def Let_def
  by (auto simp add: case_prod_unfold w_rel_def)

end

end