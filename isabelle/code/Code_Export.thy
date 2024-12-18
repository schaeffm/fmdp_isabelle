theory Code_Export
  imports Input_Validation
begin

type_synonym 'vm_ty lp_ty = 
  \<open>(bool \<times> nat \<times> (nat \<times> real) list \<times> ((nat \<times> real) list \<times> sense \<times> real) list \<times> nat bound list) \<times> 'vm_ty\<close>

fun show_min where
  \<open>show_min True = ''Min''\<close>
| \<open>show_min False = ''Max''\<close>

definition \<open>show_n_vars n = show n\<close>

definition \<open>endl = [CHR 10]\<close>

definition [icf_rec_def]: \<open>rm_basic_ops' \<equiv> map_basic_ops.truncate rm_basic_ops\<close>

setup Locale_Code.open_block

interpretation VM: Var_Map_Inst where
  map_ops = \<open>ahm_basic_ops\<close>
  by unfold_locales

setup Locale_Code.close_block

setup Locale_Code.open_block

locale Factored_API_Input_DS =
  fixes api_input :: \<open>(set_ty, pmf_ty) api_input\<close>
begin

abbreviation \<open>dims \<equiv> api_input_dims api_input\<close>
abbreviation \<open>doms \<equiv> api_input_doms api_input\<close>

definition [icf_rec_def]: \<open>constr_map_ops = ahm_ops\<close>

sublocale Coeffs constr_map_ops
  unfolding constr_map_ops_def
  by unfold_locales

definition [icf_rec_def]: \<open>set_ops = bs_ops\<close>

interpretation S: NatSet set_ops
  unfolding set_ops_def
  using SetCode.NatSet_axioms.

sublocale Vec: Vec_Inst
  where set_ops = set_ops
    and dims = dims
    and doms = doms
  by unfold_locales

definition [icf_rec_def]: \<open>vec_ops = Vec.vec_ops\<close>

interpretation V: Vec vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close> 
  using vec_ops_def set_ops_def Vec.Vec_axioms set_ops_def 
  by force

sublocale SF_Real: Scoped_Fn_Impl_Real
  where
    vec_ops = vec_ops and
    set_ops = set_ops and
    doms = \<open>\<lambda>i. {..<doms i}\<close> and doms_fn = doms and
    out = \<open>TYPE(real)\<close> and
    dims = dims
  by standard auto

sublocale SF_Ereal: Scoped_Fn_Impl_Ereal
  where
    vec_ops = vec_ops and
    set_ops = set_ops and
    dims = dims and
    doms = \<open>\<lambda>i. {..<doms i}\<close> and 
    doms_fn = doms and
    out = \<open>TYPE(ereal)\<close>
  by standard

sublocale SF_Pmf: Scoped_Fn_Impl
  where
    vec_ops = vec_ops and
    set_ops = set_ops and
    dims = dims and
    doms = \<open>\<lambda>i. {..<doms i}\<close> and 
    doms_fn = doms and
    out = \<open>TYPE(pmf_ty)\<close>
  by standard

definition [icf_rec_def]: \<open>(scoped_real_ops :: (_, _, _) scoped_fn_real_ops) = 
  scoped_fn_basic_ops.extend (SF_Real.scoped_fn_ops)
  \<lparr>scoped_fn_real_op_scale = scoped_scale,
      scoped_fn_real_op_diff = SF_Real.scoped_diff \<rparr>\<close>

definition [icf_rec_def]: \<open>(scoped_ereal_ops :: (_, _, _) scoped_fn_ereal_ops) = 
  scoped_fn_basic_ops.extend (SF_Ereal.scoped_fn_ops)
  \<lparr>scoped_fn_ereal_op_ind = SF_Ereal.scoped_ind \<rparr>\<close>

definition [icf_rec_def]: \<open>(scoped_pmf_ops :: (_, _, pmf_ty, _) scoped_fn_basic_ops) = 
  SF_Pmf.scoped_fn_ops\<close>                                       

definition [icf_rec_def]: \<open>(ste_ops :: (_, _) scoped_fn_to_ereal_ops) = \<lparr>
  scoped_fn_to_ereal_op_to_ereal = SF_Ereal.scoped_to_ereal \<rparr>\<close>

sublocale SR: ScopedStateRealDefs scoped_real_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close> .

sublocale SR: ScopedFn scoped_real_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
  using SF_Real.SF.ScopedFn_axioms
  unfolding ScopedFn_def scoped_real_ops_def ScopedFn_axioms_def
  unfolding scoped_fn_basic_ops.defs unfolding Scoped_Fn_Code.scoped_fn_basic_ops.simps
  by blast

sublocale SR: ScopedStateReal scoped_real_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
  using SF_Real.scoped_diff_invar SF_Real.scoped_scale_invar SF_Real.scoped_scale_scope SF_Real.scoped_scale_apply
  by unfold_locales 
    (simp_all add: scoped_real_ops_def scoped_fn_basic_ops.defs SF_Real.scoped_fn_ops_def)

sublocale SE: ScopedStateERealDefs scoped_ereal_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close> .

sublocale SE: ScopedFn scoped_ereal_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
  using SF_Ereal.SF.ScopedFn_axioms
  unfolding ScopedFn_def scoped_ereal_ops_def ScopedFn_axioms_def
  unfolding scoped_fn_basic_ops.defs unfolding Scoped_Fn_Code.scoped_fn_basic_ops.simps
  by blast

sublocale SE: ScopedStateEReal scoped_ereal_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
  using SF_Ereal.scoped_ind_cons SF_Ereal.scoped_ind_ncons
  by unfold_locales 
    (simp_all add: SF_Ereal.scoped_fn_ops_def scoped_ereal_ops_def scoped_fn_basic_ops.defs)
  
sublocale SSP: ScopedStatePmf scoped_pmf_ops Pmf.pmf_ops vec_ops set_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
    using SF_Pmf.SF.ScopedFn_axioms
    by (auto simp add: Pmf.Pmf_axioms ScopedStatePmf_axioms_def ScopedStatePmf_def scoped_pmf_ops_def set_ops_def)

definition \<open>doms_code' i = bs.from_list [0..<doms i]\<close>


sublocale STE: ScopedFnToErealDefs ste_ops scoped_real_ops scoped_ereal_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
  by unfold_locales

lemma to_ereal_invar: \<open>SR.invar f \<Longrightarrow> SE.invar (STE.to_ereal f)\<close>
  using SF_Real.scoped_to_ereal_invar[of f]
  unfolding Record_Intf.icf_rec_unf scoped_fn_to_ereal_ops.defs scoped_fn_basic_ops.defs
  by auto

lemma to_ereal_scope: \<open>SR.invar f \<Longrightarrow> SE.scoped_scope_\<alpha> (STE.to_ereal f) = SR.scoped_scope_\<alpha> f\<close>
  using SF_Real.scoped_to_ereal_scope[of f]
  unfolding Record_Intf.icf_rec_unf scoped_fn_to_ereal_ops.defs scoped_fn_basic_ops.defs
  by auto

lemma to_ereal_apply: \<open>SR.invar f \<Longrightarrow> SR.scoped_scope_\<alpha> f \<subseteq> dom (V.\<alpha> x) \<Longrightarrow> V.invar x \<Longrightarrow> SE.scoped_\<alpha> (STE.to_ereal f) x = ereal (SR.scoped_\<alpha> f x)\<close>
  using SF_Real.scoped_to_ereal_apply[of f x]
  unfolding Record_Intf.icf_rec_unf scoped_fn_to_ereal_ops.defs scoped_fn_basic_ops.defs
  by auto

sublocale STE: ScopedFnToEreal ste_ops scoped_real_ops scoped_ereal_ops vec_ops set_ops dims \<open>\<lambda>i. {..<doms i}\<close>
  using to_ereal_invar to_ereal_scope to_ereal_apply
  by unfold_locales blast+

sublocale Factored_API_Input_Defs
  where
    sr_ops = scoped_real_ops and
    ste_ops = ste_ops and
    er_ops = scoped_ereal_ops and
    sp_ops = scoped_pmf_ops and
    constr_map_ops = constr_map_ops and
    vec_ops = vec_ops and
    set_ops = set_ops and
    sp_pmf_ops = Pmf.pmf_ops and
    pmf_set_ops = set_ops and
    doms = \<open>\<lambda>i. {..<doms i}\<close> and
    dims = dims and
    api_input = api_input and
    lp_oracle = lp_oracle 
  for lp_oracle
  by unfold_locales metis+
end

interpretation Global_Code_Inst: Factored_API_Input_DS api_input for api_input
  by unfold_locales

setup Locale_Code.close_block

declare [[code abort: scoped_invar_vec_ops_uu_set_opsb]]
declare [[code abort: pmf_\<alpha>_impl_dflt_ops_iam_basic_ops]]
declare [[code abort: default_sol_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu]]
definition \<open>solver = Global_Code_Inst.solver_checked\<close>

type_synonym constr_ty = \<open>((nat \<times> real) \<times> RBT_Def.color) tree\<close>
type_synonym actions_ty = \<open>dom_set_ty\<close>
type_synonym state_ty = \<open>nat iarray \<times> set_ty\<close>
type_synonym real_scoped = \<open>(state_ty, real, set_ty) scoped_fn\<close>
type_synonym h_ty = \<open>nat \<Rightarrow> real_scoped\<close>
type_synonym effects_ty = \<open>nat \<Rightarrow> set_ty\<close>
type_synonym rewards_ty = \<open>nat \<Rightarrow> nat \<Rightarrow> real_scoped\<close>
type_synonym transitions_ty = \<open>nat \<Rightarrow> nat \<Rightarrow> (state_ty, real option array \<times> set_ty, set_ty) scoped_fn\<close>
type_synonym oracle_ty = \<open>nat \<Rightarrow> constr_ty \<Rightarrow> ((nat \<times> constr_ty) \<times> RBT_Def.color) tree \<Rightarrow> constr_ty \<Rightarrow> constr_ty LP_Cert option\<close>
type_synonym input_ty = \<open>(set_ty, pmf_ty) api_input\<close>

definition \<open>show_weights solver_input w = 
  (''Weights:'' @ endl @ concat (
    map 
      (\<lambda>i. ''  w'' @ show i @ '': '' @ show (w i) @ endl) 
      [0..<api_input_h_dim_code solver_input]))\<close>

definition \<open>show_state solver_input s =
  concat (map (\<lambda>i. case i of None \<Rightarrow> ''_'' | Some i \<Rightarrow> show i) 
    (Global_Code_Inst.Vec.vec_to_list solver_input (s)))\<close>

definition \<open>k solver_input = Global_Code_Inst.Vec.vec_to_list solver_input\<close>

definition \<open>show_pol solver_input p =
  ''Policy:'' @ endl @ concat (
  map 
    (\<lambda>(s,a). ''  '' @ show_state solver_input s @ '' -> '' @ show a @  endl) 
    p)\<close>

definition \<open>show_err e = 
  ''Error: '' @ show e @ endl\<close>

definition \<open>show_steps steps = 
  ''Iterations: '' @ show steps @ endl\<close>

definition \<open>show_status w_eq err_le timeout = 
  ''Status: '' @ endl @
  ''  '' @ ''Weights converged: '' @ show w_eq @ endl @ 
  ''  '' @ ''Error bound reached: '' @ show err_le @ endl @ 
  ''  '' @ ''Timeout: '' @ show timeout @ endl\<close>

type_synonym out_ty = 
  \<open>(nat \<Rightarrow> real) \<times> (state_ty \<times> nat) list \<times> real \<times> nat \<times> bool \<times> bool \<times> bool\<close>

fun show_res :: \<open>(set_ty, pmf_ty) api_input \<Rightarrow> out_ty \<Rightarrow> _\<close> where
  \<open>show_res solver_input (w, p, err, steps, w_eq, err_le, timeout) = 
  String.implode (
  ''Result:'' @ endl @
  show_weights solver_input w @ 
  show_pol solver_input p @
  show_err err @
  show_steps steps @
  show_status w_eq err_le timeout
  )\<close>

code_printing
  constant IArray.tabulate \<rightharpoonup> (SML) 
    "case _ of (n, f) => Vector.tabulate (IntInf.toInt n, fn i => f ((IntInf.fromInt i)))"
  | constant IArray.sub' \<rightharpoonup> (SML) 
    "case _ of (arr, i) => Vector.sub (arr, IntInf.toInt i)"
  | constant IArray.length' \<rightharpoonup> (SML) 
    "IntInf.fromInt (Vector.length _)"

code_reserved Scala Vector

code_printing
  type_constructor iarray \<rightharpoonup> (Scala) "Array.T[_]"
  | constant IArray \<rightharpoonup> (Scala) "Array.init'_list"
  | constant IArray.tabulate \<rightharpoonup> (Scala) "_ match { case (a,b) => Array.make(a)(b) }"
  | constant IArray.sub' \<rightharpoonup> (Scala) "_ match { case (a,b) => Array.nth(a,b) }"
  | constant IArray.length' \<rightharpoonup> (Scala) "Array.len"

definition vec_lookup :: \<open>((nat \<times> 'b)) list \<Rightarrow> nat \<Rightarrow> 'b option\<close> where
  \<open>vec_lookup = am_lookup\<close>

(*
definition vec_from_list :: "(nat \<times> 'b) list \<Rightarrow> ((nat \<times> 'b) \<times> RBT_Def.color) tree" where
  "vec_from_list = M.from_list2"
lemmas vec_from_list_def[unfolded M.from_list2_def, code]
*)

definition \<open>pmf_from_list xs = (iam.to_map xs, bs.from_list(map fst xs))\<close>
definition \<open>set_from_list = bs.from_list\<close>

definition \<open>show_nat (n :: nat) = String.implode (show n)\<close>
definition \<open>show_rat (n :: rat) = String.implode (show n)\<close>
definition \<open>show_vec v = Tree2.inorder v\<close>
definition \<open>show_mat m = map (\<lambda>(i, v). (i, Tree2.inorder v)) (Tree2.inorder m)\<close>

lemma upd_list_greatest: \<open>(\<And>i. i \<in> fst ` set xs \<Longrightarrow> (y :: nat) > i) \<Longrightarrow> upd_list y x xs = xs @ [(y, x)]\<close>
  apply (induction xs arbitrary:  y x)
   apply (auto simp: enumerate_append_eq image_iff)
   apply blast
  subgoal for a xs y
    apply (cases \<open>\<forall>i. i \<in> fst ` set xs \<longrightarrow>  y > i\<close>)
    apply (auto simp: image_iff)
    using order.asym by blast
  done

lemma from_list2_enum[code_unfold]: \<open>Global_Code_Inst.Code_Inst.LPC.Map_am.from_list2 (List.enumerate 0 x) = (List.enumerate 0 x)\<close>
  unfolding Global_Code_Inst.Code_Inst.LPC.Map_am.from_list2_def
  apply (induction x  rule: rev_induct)
   apply (auto simp: case_prod_unfold am_empty_def am_update_def)
  using Map_by_Ordered.from_list2_def[OF am_Map_by_Ordered] 
  apply (auto simp: enumerate_append_eq   Map_by_Ordered.from_list2_def Global_Code_Inst.Code_Inst.LPC.Map_am.from_list2_def am_update_def)
  apply (subst upd_list_greatest)
   by (auto simp: in_set_enumerate_eq in_set_enumerate_eq)

lemma from_list2_enum'[code_unfold]: \<open>Global_Code_Inst.Code_Inst.LPC.Map_am'.from_list2 (List.enumerate 0 x) = (List.enumerate 0 x)\<close>
  using from_list2_enum
  unfolding Global_Code_Inst.Code_Inst.LPC.Map_am'.from_list2_def
    Global_Code_Inst.Code_Inst.LPC.Map_am.from_list2_def
  unfolding am_empty'_def am_update'_def am_update_def am_empty_def
  by auto

lemma from_list2_enum_gen'[code_unfold]: \<open>from_list2_am_empty'_am_update' (List.enumerate 0 x) = (List.enumerate 0 x)\<close>
  unfolding from_list2_am_empty'_am_update'_def
  using from_list2_enum' 
  by auto

lemma from_list2_enum_gen[code_unfold]: \<open>from_list2_am_empty_am_update (List.enumerate 0 x) = (List.enumerate 0 x)\<close>
  unfolding from_list2_am_empty_am_update_def
  using from_list2_enum 
  by auto

lemmas comp_apply[code_unfold]

definition \<open>sorted1_code x = sorted1 x\<close>
lemmas sorted1_code_def[code del]

lemma sorted1_code[code]: 
  \<open>sorted1_code = (\<lambda>xs. case xs of (x#y#ys) \<Rightarrow> fst x < fst y \<and> sorted1_code (y#ys) | _ \<Rightarrow> True)\<close>
  by (fastforce simp: sorted1_code_def split: list.splits intro!: ext)

lemmas sorted1_code_def[symmetric, code_unfold]
lemmas id_apply[code_unfold]

subsection \<open>IArray Setup for usage in sets\<close>
instantiation  iarray :: (ceq) ceq
begin
 
 
definition ceq_iarray :: \<open>('a::ceq iarray \<Rightarrow> 'a::ceq iarray \<Rightarrow> bool) option\<close> where
  \<open>ceq_iarray = Some (\<lambda>x y. (x = y))\<close>
 
instance
  apply standard
  unfolding ceq_iarray_def
  by auto

end
 
instantiation  iarray :: (ccompare) ccompare
 begin


definition ccompare_iarray :: \<open>('a::ccompare iarray \<Rightarrow> 'a::ccompare iarray \<Rightarrow> order) option\<close> where
  \<open>ccompare_iarray = None\<close>

instance
  apply standard
  unfolding ccompare_iarray_def
  by auto

end

derive (dlist) set_impl iarray

subsection \<open>Code Export\<close>

export_code
  solver
rat_of_real
IArray.tabulate

vec_lookup
set_from_list 
pmf_from_list
Cert_Opt

Leq Geq Eq

Tree2.inorder

show_rat
show_nat
  show_vec
  show_mat

(* aux for parsing *)
Some None
Lb Ub Betw Beq Free
Rat.Fract

integer_of_nat nat_of_integer int_of_integer integer_of_int
times_rat_inst.times_rat uminus_rat_inst.uminus_rat minus_rat_inst.minus_rat one_rat_inst.one_rat
divide_rat_inst.divide_rat Rat.of_int quotient_of 

show_res

in Scala
module_name Solver
file_prefix factored_solver
(* file factored_solver.scala *)

end