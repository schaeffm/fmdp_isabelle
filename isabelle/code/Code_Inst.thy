theory Code_Inst
  imports 
    "HOL-Library.IArray"
    API_Code
    "collections/Scoped_Fn_Inst"
    "collections/Vec_Inst"
    "collections/Set_Inst"
    "Collections.RBTSetImpl"
    "Collections.ArrayMapImpl"
    "collections/Pmf_Inst"
    "lp_cert/LP_Cert_Code"
begin

subsection "Definitions"

locale APIInstDefs =
  MDPCodeDefs
  where
    sr_ops = sr_ops and
    sp_ops = sp_ops and
    pmf_set_ops = pmf_set_ops +
    STE: ScopedFnToEreal ste_ops sr_ops er_ops +
    Coeffs: Coeffs constr_map_ops
  for
    constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> and
    ste_ops :: \<open>('f, 'ef) scoped_fn_to_ereal_ops\<close> and
    sr_ops :: \<open>('f, 'state, 'natset) scoped_fn_real_ops\<close> and
    sp_ops :: \<open>('pf, 'state, 'pmf, 'natset) scoped_fn_basic_ops\<close> and
    er_ops and 
    pmf_set_ops :: "(nat, 'pmf_set) oset_ops" +
  fixes
    t_max_code :: \<open>nat\<close> and
    \<epsilon>_code :: \<open>real\<close> and
    lp_oracle :: \<open>nat \<Rightarrow> sparse_vec_ty \<Rightarrow> sparse_mat_ty \<Rightarrow> sparse_vec_ty \<Rightarrow> sparse_vec_ty LP_Cert option\<close>
begin

print_locale LP_Cert_Inst_Defs
sublocale LPC: LP_Cert_Inst_Defs
  where 
    doms = doms_code and
    dims = dims_code and
    map_ops = constr_map_ops and
    lp_oracle = lp_oracle
  by unfold_locales

print_locale APICodeDefs
sublocale API_Code_Interp: APICodeDefs
  where
    pmf_set_ops = pmf_set_ops and
    dims = dims and
    doms = doms and
    dims_code = dims_code and
    doms_code = doms_code and
    minimize = LPC.minimize and
    constr_map_ops = constr_map_ops and
    t_max_code = t_max_code
  by unfold_locales

subsection \<open>API interpretation\<close>

definition \<open>api_code = API_Code_Interp.api_code\<close>

print_locale LP_Cert_Inst
sublocale LPC: LP_Cert_Inst
  where              
    doms = doms_code and
    dims = dims_code and
    map_ops = constr_map_ops and
    lp_oracle = lp_oracle
  by unfold_locales

print_locale APICodeDefs
sublocale API_Code_Interp: APICodeDefs
  where
    pmf_set_ops = pmf_set_ops and
    dims = dims and
    doms = doms and
    dims_code = dims_code and
    doms_code = doms_code and
    minimize = LPC.minimize and
    constr_map_ops = constr_map_ops and
    t_max_code = t_max_code
  by unfold_locales
end

locale APIInst =
  APIInstDefs
  where
    constr_map_ops = constr_map_ops and
    ste_ops = ste_ops and
    sr_ops = sr_ops and
    sp_ops = sp_ops and
    er_ops = er_ops and
    pmf_set_ops = pmf_set_ops +
  MDPCode
  where
    sr_ops = sr_ops and
    sp_ops = sp_ops and
    pmf_set_ops = pmf_set_ops +
    STE: ScopedFnToEreal ste_ops sr_ops er_ops +
    Coeffs: Coeffs constr_map_ops
  for
    constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> and
    ste_ops :: \<open>('f, 'ef) scoped_fn_to_ereal_ops\<close> and
    sr_ops :: \<open>('f, 'state, 'natset) scoped_fn_real_ops\<close> and
    sp_ops :: \<open>('pf, 'state, 'pmf, 'natset) scoped_fn_basic_ops\<close> and
    er_ops and 
    pmf_set_ops :: "(nat, 'pmf_set) oset_ops" +
  assumes \<epsilon>_code_pos: \<open>\<epsilon>_code > 0\<close>
begin


lemma lpc_min_opt_correct:
  assumes \<open>LPC.minimize (Factored_LP_Code.LP_Code.LP_Code c cs) = Opt x obj_val\<close> 
    \<open>Coeffs.invar c\<close>
    \<open>((\<And>i. i \<in> set cs \<Longrightarrow> Coeffs.invar (constr_code_poly i)))\<close>
  shows 
    \<open>Coeffs.invar x\<close> 
    \<open>Coeffs.cross_prod_code x c = obj_val\<close> 
    \<open>x \<in> Coeffs.sol_space_code cs\<close> \<open>\<forall>sol'\<in>Coeffs.sol_space_code cs. obj_val \<le> Coeffs.cross_prod_code sol' c\<close>
  subgoal
    using assms Coeffs.to_map_correct
    unfolding LPC.minimize_def LPC.lp_minimize_def 
    by (auto split: option.splits LP_Cert.splits if_splits simp: case_prod_unfold LPC.solve_lp_def)
      using LPC.lp_minimize_sound[of cs c x obj_val] assms 
      unfolding LPC.minimize_def
      by auto

lemma lp_cert_spec: \<open>API_Code_Interp.lp_cert_spec\<close>
  unfolding API_Code_Interp.lp_cert_spec_def
  using lpc_min_opt_correct
  by (auto split: LP_Code.splits lp_res.splits)

find_theorems  LPC.minimize
sublocale API_Code_Interp: APICode
  where
    pmf_set_ops = pmf_set_ops and
    dims = dims and
    doms = doms and
    dims_code = dims_code and
    doms_code = doms_code and
    minimize = LPC.minimize and
    constr_map_ops = constr_map_ops and
    t_max_code = t_max_code
  using \<epsilon>_code_pos lp_cert_spec
  by unfold_locales auto
end

type_synonym dom_set_ty = nat

type_synonym set_ty = \<open>nat\<close>

setup \<open>Locale_Code.open_block\<close>

interpretation IAM: StdMap iam_basic.dflt_ops
  using iam_basic.dflt_ops_impl.

interpretation Pmf: PmfNat_Inst
  where
    set_ops = bs_ops and
    map_ops = iam_basic.dflt_ops
  by unfold_locales

setup \<open>Locale_Code.close_block\<close>

type_synonym state_ty = \<open>nat iarray \<times> set_ty\<close>
type_synonym lp_var_ty = \<open>(state_ty \<times> nat \<times> bool, state_ty) var_code\<close>
type_synonym pmf_ty = \<open>real option array \<times> dom_set_ty\<close>
end