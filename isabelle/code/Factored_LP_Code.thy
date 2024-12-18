theory Factored_LP_Code
  imports 
    "../algorithm/Factored_LP"
    "collections/Scoped_Fn_Rel"
    Code_Setup 
    Variable_Elim_Code
    "Show.Show_Instances"
begin                                                                  

definition \<open>lookup0 m x = (case m x of Some y \<Rightarrow> y | _ \<Rightarrow> 0)\<close>

datatype 'coeffs Constr_Code = 
  Constr_Le 'coeffs real | 
  Constr_Eq 'coeffs real

datatype 'm LP_Code = LP_Code 'm \<open>'m Constr_Code list\<close>

definition \<open>cross_prod f f' = (\<Sum> i \<in> {i. f i \<noteq> 0 \<and> f' i \<noteq> 0}. f i * f' i)\<close>
definition \<open>constr_code_poly c = (case c of Constr_Le cs b \<Rightarrow> cs | Constr_Eq cs b \<Rightarrow> cs)\<close>

locale CoeffsDefs =
  StdMapDefs \<open>constr_op_map_ops :: ('k, real, 'm) map_ops\<close>
  for constr_op_map_ops
begin

definition \<open>lookup0_code k m = (case lookup k m of None \<Rightarrow> 0 | Some y \<Rightarrow> y)\<close>

abbreviation \<open>cross_prod_code a b \<equiv> cross_prod (lookup0 (\<alpha> a)) (lookup0 (\<alpha> b))\<close>

fun eval_constr_code where
  \<open>eval_constr_code (Constr_Le cs rhs) a \<longleftrightarrow> cross_prod_code cs a \<le> rhs\<close> |
  \<open>eval_constr_code (Constr_Eq cs rhs) a \<longleftrightarrow> cross_prod_code cs a = rhs\<close>

definition \<open>sol_space_code_constr constr = {sol. invar sol \<and> eval_constr_code constr sol }\<close>
definition \<open>sol_space_code lp = { sol. (invar sol) \<and> (\<forall>c \<in> set lp. sol \<in> sol_space_code_constr c) }\<close>

end

setup \<open>Locale_Code.open_block\<close>

context StdMapDefs
begin

definition \<open>lookup' m k = the (lookup m k)\<close>

end

setup \<open>Locale_Code.close_block\<close>

locale Coeffs = 
  CoeffsDefs constr_op_map_ops + 
  StdMap constr_op_map_ops
  for constr_op_map_ops

datatype 'id lp_res = Opt 'id real | Infeasible | Unbounded

datatype f_name_code = 
  f_c_code nat | 
  f_b_code nat | 
  f_e_code nat

instantiation f_name_code :: linorder
begin

definition \<open>less_eq_f_name_code f1 f2 = (
  case (f1, f2) of
    (f_e_code i, f_e_code j) \<Rightarrow> i \<le> j
  | (f_e_code _, _) \<Rightarrow> True
  | (f_b_code i, f_b_code j) \<Rightarrow> i \<le> j
  | (f_b_code _, f_c_code _) \<Rightarrow> True
  | (f_c_code i, f_c_code j) \<Rightarrow> i \<le> j
  | (_, _) \<Rightarrow> False)\<close>

definition less_f_name_code :: "f_name_code \<Rightarrow> f_name_code \<Rightarrow> bool" where
  \<open>less_f_name_code f1 f2 \<longleftrightarrow> f1 \<le> f2 \<and> f1 \<noteq> f2\<close>

instance
  by standard (auto simp: less_eq_f_name_code_def less_f_name_code_def split: f_name_code.splits)

end

datatype ('x, 'v) var_code = 
  var_phi | 
  var_f 'x f_name_code 'v |
  var_w nat

locale FactoredLPCodeDefs =
  MDPCodeDefs
  where sr_ops = sr_ops and sp_ops = sp_ops +
    STE: ScopedFnToErealDefs to_ereal_ops +
    Coeffs: CoeffsDefs constr_map_ops
  for 
    sr_ops :: "('f, 'v, 'natset) scoped_fn_real_ops" and
    sp_ops and
    to_ereal_ops :: \<open>('f, 'ef) scoped_fn_to_ereal_ops\<close> and
    constr_map_ops :: \<open>(('x_str, 'v_str) var_code, real, _) map_ops\<close>+
  fixes
    C_code :: \<open>'f list\<close> and
    B_code :: \<open>'ef list\<close> and
    prefix_code :: \<open>'x_str\<close> and
    show_state :: \<open>'v \<Rightarrow> 'v_str\<close>
begin

definition \<open>showl i = String.implode (show i)\<close>

fun show_f where
  \<open>show_f (f_c_code i) = ''c'' @ show i\<close>
| \<open>show_f (f_b_code i) = ''b'' @ show i\<close>
| \<open>show_f (f_e_code i) = ''e'' @ show i\<close>

definition \<open>constr_le_from_list xs rhs = Constr_Le (Coeffs.to_map xs) rhs\<close>

definition \<open>constr_eq_from_list xs rhs = Constr_Eq (Coeffs.to_map xs) rhs\<close>

definition \<open>constr_c_code z i c = (
  let var_c = var_f prefix_code (f_c_code i) (show_state z) in
    constr_eq_from_list [(var_c, -1), (var_w i, SR.scoped_\<alpha> c z)] 0)\<close>

definition \<open>constrs_c_single_code i c =
  map (\<lambda>z. constr_c_code z i c) (assignments_impl (SR.scope c))\<close>

definition \<open>constrs_c_code =
 concat (map (\<lambda>(i, c). constrs_c_single_code i c) (List.enumerate 0 C_code))\<close>

definition \<open>constr_b_code z j rhs =
  constr_eq_from_list [((var_f prefix_code (f_b_code j) (show_state z)), 1)] rhs\<close>

definition \<open>constrs_b_single_code i b =
  List.map_filter (\<lambda>z. 
    let rhs = STE.SE.scoped_\<alpha> b z in
      if rhs = -\<infinity> then None
      else Some (constr_b_code z i (real_of_ereal rhs))) (assignments_impl (STE.SE.scope b))\<close>

definition \<open>constrs_b_code =
  concat (map (\<lambda>(i, b). constrs_b_single_code i b) (List.enumerate 0 B_code))\<close>

definition \<open>\<F>_init_code =
  map (\<lambda>(i, f). (f_c_code i, SR.scope f)) (List.enumerate 0 C_code) @
  map (\<lambda>(i, f). (f_b_code i, STE.SE.scope f)) (List.enumerate 0 B_code)
\<close>

definition \<open>constrs_init_code = 
  constrs_c_code @ constrs_b_code\<close>

definition \<open>vec_from_idx X f =
  Scope.iterate X (\<lambda>j v. (Vec.update v j (f j))) Vec.empty\<close>

definition \<open>constr_max_code E i z xi = 
  constr_le_from_list 
  (((var_f prefix_code (f_e_code i) (show_state z)), -1) # map (\<lambda>(f, s). 
  ((var_f prefix_code f (show_state (vec_from_idx s (\<lambda>j. if j = i then xi else Vec.idx z j)))), 1)) E) 0\<close>

definition \<open>constrs_max_code E i scope_e =
  map (\<lambda>(z, xi). constr_max_code E i z xi) 
  (List.product (assignments_impl scope_e) ([0..<doms_code i]))\<close>

definition \<open>elim_step_code \<Omega> \<F> i = (let
  l = i;
  (E, not_E) = partition (\<lambda>(f, s). Scope.memb l s) \<F>;
  scope_e = Scope.delete l (Scope.Union_sets (map snd E));
  \<Omega>' = \<Omega> @ constrs_max_code E l scope_e
  in         
  (\<Omega>', (f_e_code l, scope_e) # not_E, i + 1)
)
\<close>
lemmas refl[of elim_step_code, cong]

definition \<open>elim_vars_aux_code = 
  ((\<lambda>(\<Omega>, \<F>, i). elim_step_code \<Omega> \<F> i) ^^ dims_code) 
  (constrs_init_code, \<F>_init_code, 0)\<close>

definition \<open>gen_constrs_code arg = (
  case arg of (\<Omega>, \<F>, i) \<Rightarrow>
    constr_le_from_list
      (((var_phi, -1) # map (\<lambda>(f, _). ((var_f prefix_code f (show_state Vec.empty)), 1)) \<F>)) 
      0 # \<Omega>)\<close>

definition \<open>elim_vars_code = gen_constrs_code elim_vars_aux_code\<close>

end

locale FactoredLPCode =
  FactoredLPCodeDefs +
  MDPCode
  where sr_ops = sr_ops and sp_ops = sp_ops +
    STE: ScopedFnToEreal to_ereal_ops +
    Coeffs: Coeffs constr_map_ops +
  assumes 
    show_state_correct: \<open>Vec.invar x \<Longrightarrow> Vec.invar y \<Longrightarrow> Vec.\<alpha> x = Vec.\<alpha> y \<longleftrightarrow> show_state x = show_state y\<close>
begin
end

locale Factored_LP_Code_Transfer =
  FactoredLPCodeDefs
  where
    constr_map_ops = constr_map_ops and 
    doms = doms and
    sr_ops = sr_ops and
    pmf_set_ops = pmf_set_ops and
    prefix_code = prefix_code +
    Coeffs: CoeffsDefs constr_map_ops +
    MDP_Code_Transfer
  where 
    doms = doms and
    sr_ops = sr_ops and 
    pmf_set_ops = pmf_set_ops +
    STE: ScopedFnToEreal 
  where doms = doms and
    ops = to_ereal_ops
  for 
    prefix_code :: "'p_str" and
    doms :: "nat \<Rightarrow> nat set" and 
    sr_ops :: \<open>('f, 'v, 'natset) scoped_fn_real_ops\<close> and
    ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
    er_ops and
    pmf_set_ops :: "(nat, 'pmf_set) oset_ops" and
    constr_map_ops :: \<open>(('p_str, 'v_str) var_code, real, 'm) map_ops\<close> and

C :: \<open>(((nat \<Rightarrow> nat option) \<Rightarrow> real) \<times> nat set) list\<close> and
B :: \<open>(((nat \<Rightarrow> nat option) \<Rightarrow> ereal) \<times> nat set) list\<close> and

prefix :: \<open>'p\<close> +
fixes
  prefix_\<alpha> :: \<open>'p_str \<Rightarrow> 'p\<close> and
  prefix_invar :: \<open>'p_str \<Rightarrow> bool\<close>
assumes prefix_\<alpha>_inj: \<open>inj_on prefix_\<alpha> {p. prefix_invar p}\<close>
begin

sublocale
  factored_lp_consts
  where
    dims = dims and
    doms = doms and 
    order = id and
    C = C and B = B and
    prefix = prefix
  by unfold_locales

sublocale STE.SE: States_Code_Transfer dims doms doms_code dims_code
  by unfold_locales

definition \<open>C_rel \<longleftrightarrow>
  list_all2 (SR.scoped_fn_state_rel (=)) C_code C \<and> 
  (\<forall>c \<in> set C. snd c \<subseteq> vars) \<and>
  (\<forall>c \<in> set C. has_scope_on (fst c) partial_states (snd c))\<close>

definition \<open>B_rel \<longleftrightarrow>
  list_all2 (STE.SE.scoped_fn_state_rel (=)) B_code B \<and> 
  (\<forall>c \<in> set B. snd c \<subseteq> vars) \<and>
  (\<forall>c \<in> set B. \<forall>x. fst c x \<noteq> \<infinity>) \<and>
  (\<forall>c \<in> set B. has_scope_on (fst c) partial_states (snd c))\<close>

definition \<open>f_name_rel v_code v \<longleftrightarrow> (
  case (v_code, v) of
    (f_e_code i, f_e j) \<Rightarrow> i = j
  | (f_c_code i, f_c j) \<Rightarrow> i = j
  | (f_b_code i, f_b j) \<Rightarrow> i = j
  | _ \<Rightarrow> False)\<close>

definition \<open>var_invar v = (case v of var_f p f_code v_code \<Rightarrow> 
prefix_invar p \<and> (\<exists>v_code'. Vec.invar v_code' \<and> show_state v_code' = v_code) | _ \<Rightarrow> True)\<close>
lemmas refl[of var_invar, cong]

definition \<open>var_prefix_code v = (case v of var_f p f_code v_code \<Rightarrow> p = prefix_code | _ \<Rightarrow> True)\<close>
lemmas refl[of var_prefix_code, cong]

fun f_name_code_\<alpha> :: \<open>f_name_code \<Rightarrow> f_name\<close> where
  \<open>f_name_code_\<alpha> (f_c_code i) = f_c i\<close> |
  \<open>f_name_code_\<alpha> (f_b_code i) = f_b i\<close> |
  \<open>f_name_code_\<alpha> (f_e_code i) = f_e i\<close>
lemmas refl[of f_name_code_\<alpha>, cong]

fun var_code_\<alpha> :: \<open>(_, _) var_code \<Rightarrow> (_, nat) var_name\<close> where
  \<open>var_code_\<alpha> var_code.var_phi = var_name.var_phi\<close> |
  \<open>var_code_\<alpha> (var_code.var_f p_code f_name_code v) =
  (var_name.var_f (prefix_\<alpha> p_code) (f_name_code_\<alpha> f_name_code) (Vec.\<alpha> (SOME v'. Vec.invar v' \<and> show_state v' = v)))\<close> |
  \<open>var_code_\<alpha> (var_code.var_w i) = (var_name.var_w i)\<close>
lemmas refl[of var_code_\<alpha>, cong]

definition \<open>map_fn_rel m f \<longleftrightarrow>
  (dom m \<subseteq> {v. var_invar v}) \<and>
  (\<forall>i_code \<in> dom m. lookup0 m i_code = f (var_code_\<alpha> i_code)) \<and>
  (\<forall>i. i \<notin> var_code_\<alpha> ` dom m \<longrightarrow> f i = 0)\<close>
lemmas refl[of map_fn_rel, cong]

definition \<open>poly_rel cs_code cs \<longleftrightarrow> Coeffs.invar cs_code \<and> map_fn_rel (Coeffs.\<alpha> cs_code) cs\<close>
lemmas refl[of poly_rel, cong]

fun constr_rel where
  \<open>constr_rel (Constr_Le cs_code rhs_code) (Le cs rhs) \<longleftrightarrow> rhs_code = rhs \<and> poly_rel cs_code cs\<close> |
  \<open>constr_rel (Constr_Eq cs_code rhs_code) (Eq cs rhs) \<longleftrightarrow> rhs_code = rhs \<and> poly_rel cs_code cs\<close> |
  \<open>constr_rel _ _ \<longleftrightarrow> False\<close>
lemmas refl[of constr_rel, cong]

definition \<open>poly_\<alpha> m i = (
  if \<exists>v \<in> dom (Coeffs.\<alpha> m). var_code_\<alpha> v = i 
  then lookup0 (Coeffs.\<alpha> m) (SOME v. v \<in> dom (Coeffs.\<alpha> m) \<and> var_invar v \<and> var_code_\<alpha> v = i) 
  else 0)\<close>
lemmas refl[of poly_\<alpha>, cong]


definition \<open>poly_\<alpha>' m i = (
  if \<exists>v \<in> dom m. var_code_\<alpha> v = i 
  then lookup0 m (SOME v. v \<in> dom m \<and> var_invar v \<and> var_code_\<alpha> v = i) 
  else 0)\<close>
lemmas refl[of poly_\<alpha>', cong]

fun constr_\<alpha> where
  \<open>constr_\<alpha> (Constr_Le cs_code rhs_code) = (Le (poly_\<alpha> cs_code) rhs_code)\<close> |
  \<open>constr_\<alpha> (Constr_Eq cs_code rhs_code) = (Eq (poly_\<alpha> cs_code) rhs_code)\<close>
lemmas refl[of constr_\<alpha>, cong]

definition \<open>constrs_\<alpha> cs = constr_\<alpha> ` set cs\<close>
lemmas refl[of constrs_\<alpha>, cong]

definition \<open>constrs_rel cs_code cs = rel_set constr_rel (set cs_code) cs\<close>
lemmas refl[of constrs_rel, cong]

definition \<open>\<F>_rel f_code f scopes \<longleftrightarrow>
  distinct (map fst f_code) \<and>
  (\<forall>g \<in> f. scopes g \<subseteq> vars) \<and>
  rel_set (rel_prod f_name_rel Scope.set_rel) (set f_code) ((\<lambda>c. (c, scopes c)) ` f)\<close>
lemmas refl[of \<F>_rel, cong]

definition \<open>config_rel = (\<lambda>(cs_code, \<F>_code, i_code) (cs, \<F>, scopes, i).
  invar_lp cs \<F> scopes i \<and> 
    constrs_rel cs_code cs \<and>
      \<F>_rel \<F>_code \<F> scopes \<and> i_code = i)\<close>
lemmas refl[of config_rel, cong]
end

locale Factored_LP_Code_Transfer_Rel =
  Factored_LP_Code_Transfer +
  FactoredLPCode +
  MDP_Code_Transfer_Rel +     
  assumes 
    prefix_rel[simp]: \<open>prefix_\<alpha> prefix_code = prefix\<close> and
    prefix_inv[intro]: \<open>prefix_invar prefix_code\<close>
begin
lemmas has_scope_on_cong[cong del]
lemmas Coeffs.correct(5)[simp]
lemmas Coeffs.correct(28)[intro]
lemmas Coeffs.to_map_correct(1)[simp]
lemmas Vec.vec_rel_in_vars[simp del]

definition \<open>vec_rep v = Vec.insert_list Vec.empty (sorted_key_list_of_set fst (Map.graph v))\<close>

lemma finite_graph_states: \<open>v \<in> partial_states \<Longrightarrow> finite (Map.graph v)\<close>
  by (auto intro!: finite_subset[of \<open>(\<lambda>i. (i, the (v i))) ` {..<dims}\<close>])

lemma finite_graph_states': \<open>v \<in> partial_states \<Longrightarrow> finite (set_of_map v)\<close>
  using set_of_map_def finite_graph_states Map.graph_def by metis

lemma vec_rep_invar[intro]: \<open>v \<in> partial_states \<Longrightarrow> Vec.invar (vec_rep v)\<close>
  unfolding vec_rep_def
  using finite_graph_states[of v] 
  by (auto simp: folding_Map_graph.set_sorted_key_list_of_set[of \<open>Map.graph v\<close>, of v] 
      elim!: partial_statesE dest!: in_graphD)

lemma vec_rep_idx[simp]: 
  assumes \<open>v \<in> partial_states\<close> 
  shows \<open>Vec.\<alpha> (vec_rep v) = v\<close>
proof (rule ext)
  fix i

  have \<open>finite (dom v)\<close>
    using assms 
    by auto

  thus \<open>Vec.\<alpha> (vec_rep v) i = v i\<close>
    unfolding vec_rep_def
    using folding_Map_graph.sorted_key_list_of_set[of \<open>Map.graph v\<close>, of v] assms
    by (cases \<open>v i\<close>) (auto simp: subset_iff partial_states_def case_prod_unfold map_upds_def map_of_eq_None_iff dest!: in_graphD intro!: in_graphI)
qed

lemma state_rel_rep:
  assumes \<open>v \<in> partial_states\<close>
  shows \<open>state_rel (vec_rep v) v\<close>
  using vec_rep_idx vec_rep_invar assms by blast

lemma partial_states_onD[dest]: \<open>v \<in> partial_states_on X \<Longrightarrow> v \<in> partial_states\<close>
  by blast

lemma has_scope_on_rel:
  assumes \<open>SR.scoped_fn_state_rel (=) f_code f\<close>
  shows \<open>has_scope_on (fst f) (partial_states_on (snd f)) (snd f)\<close>
proof (rule has_scope_onI, goal_cases)
  case (1 d d')
  then show ?case 
    using assms
    using SR.scoped_fn_state_relE'(1)[OF assms state_rel_rep[of d], symmetric, subst]
    using SR.scoped_fn_state_relE'(1)[OF assms state_rel_rep[of d'], symmetric, subst]
    by (auto intro!: SR.scoped_\<alpha> simp: partial_states_onD iff del: domIff)+
qed

sublocale States_Code_Transfer
  dims
  doms
  doms_code
  dims_code
  .

sublocale PmfSet: StdOSet pmf_set_ops
  using SP.Pmf.set .


lemma vec_\<alpha>_some_show_state[simp]: \<open>Vec.invar x_code \<Longrightarrow> (Vec.\<alpha> (SOME v'. Vec.invar v' \<and> show_state v' = show_state x_code)) = Vec.\<alpha> x_code\<close>
  by (rule someI2[of _ x_code]) (auto simp: show_state_correct)

lemma var_code_\<alpha>_f[simp]:
  assumes \<open>Vec.invar v\<close>
  shows \<open>var_code_\<alpha> (var_code.var_f p_code f (show_state v)) = var_name.var_f (prefix_\<alpha> p_code) (f_name_code_\<alpha> f) (Vec.\<alpha> v)\<close>
  by (auto simp: assms)

lemma lookup0_nodom[simp]: \<open>i \<notin> dom  m \<Longrightarrow> lookup0 m i = 0\<close>
  unfolding lookup0_def
  by (auto split: option.splits)

lemmas var_code_\<alpha>.simps(2)[simp del]

lemma f_name_rel_self[simp, intro]: \<open>f_name_rel f_code (f_name_code_\<alpha> f_code)\<close>
  by (cases \<open>f_code\<close>) (auto simp: f_name_rel_def)

lemma var_code_\<alpha>_phi[simp]: \<open>var_code_\<alpha> x = var_name.var_phi \<longleftrightarrow> x = var_phi\<close>
  by (cases \<open>x\<close>) (auto simp: var_code_\<alpha>.simps)

lemma var_code_\<alpha>_w[simp]: \<open>var_code_\<alpha> x = var_name.var_w i \<longleftrightarrow> x = var_w i\<close>
  by (cases \<open>x\<close>) (auto simp: var_code_\<alpha>.simps)

lemma lookup0_map_fn_rel_var_phi: \<open>map_fn_rel m f \<Longrightarrow> lookup0 m (var_phi) = f (var_name.var_phi)\<close>
  unfolding map_fn_rel_def
  by (auto simp:   image_iff subset_iff split: option.splits iff del: domIff) (metis lookup0_nodom var_code_\<alpha>_phi)

lemma lookup0_map_fn_rel_var_w: \<open>map_fn_rel m f \<Longrightarrow> lookup0 m (var_w i) = f ((var_name.var_w i))\<close>
  unfolding map_fn_rel_def
  using var_code_\<alpha>_w
  by (auto simp: image_iff iff del: domIff) (metis var_code_\<alpha>_w lookup0_nodom)

lemma bi_unique_f_name_rel: \<open>bi_unique f_name_rel\<close>
  by (auto intro!: bi_uniqueI left_uniqueI right_uniqueI simp: f_name_rel_def split: f_name_code.splits f_name.splits)

lemma fn_name_rel_imp_eq: \<open>f_name_rel x_code (f_name_code_\<alpha> x_code') \<Longrightarrow> x_code' = x_code\<close>
  by (meson bi_uniqueDl bi_unique_f_name_rel f_name_rel_self)

definition \<open>list_fn_rel xs f \<longleftrightarrow> 
  distinct (map fst xs) \<and>
  map_fn_rel (map_of xs) f\<close>

lemma lookup0_map_of: \<open>(k, v) \<in> set xs \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> lookup0 (map_of xs) k = v\<close>
  unfolding lookup0_def
  by auto

lemma list_fn_relI:
  assumes 
    \<open>distinct (map fst cs_code)\<close>
    \<open>\<And>c. c \<in> set cs_code \<Longrightarrow> var_invar (fst c)\<close>
    \<open>\<And>c. c \<in> set cs_code \<Longrightarrow> snd c = cs (var_code_\<alpha> (fst c))\<close>
    \<open>\<And>v. v \<notin> var_code_\<alpha> ` fst ` set cs_code \<Longrightarrow> cs v = 0\<close>
  shows \<open>list_fn_rel cs_code cs\<close>
  unfolding list_fn_rel_def map_fn_rel_def
  using assms
  by (auto simp: dom_map_of_conv_image_fst intro: lookup0_map_of)

lemma var_invar_basic[intro]: \<open>var_invar var_code.var_phi\<close> \<open>var_invar (var_code.var_w i)\<close>
  by (auto simp: var_invar_def)

lemma var_invar_fI[intro!]:
  assumes \<open>Vec.invar x\<close>
  shows \<open>var_invar (var_code.var_f prefix_code a (show_state x))\<close>
  using assms prefix_rel
  unfolding var_invar_def
  by auto

lemma f_name_rel_unique[simp]: \<open>f_name_rel a c' \<Longrightarrow> f_name_code_\<alpha> a = c'\<close>
  unfolding f_name_rel_def f_name_code_\<alpha>.simps
  by (auto split: f_name_code.splits f_name.splits)

lemma f_name_f_rel_self[intro]: \<open>f_name_rel (f_e_code i) (f_e i)\<close>
  by (auto simp: f_name_rel_def)

lemma invar_\<F>_rel_set:  
  assumes \<open>\<F>_rel F_code F_abs scopes\<close> \<open>f \<in> set F_code\<close>
  shows \<open>Scope.invar (snd f)\<close>
  using assms 
  unfolding \<F>_rel_def
  by (auto dest!: rel_setD1)

lemma map_fn_rel_lookup_var_invar: 
  assumes \<open>map_fn_rel cs_code cs\<close> \<open>cs_code x = Some y\<close>
  shows \<open>var_invar x\<close>
  using assms
  unfolding map_fn_rel_def
  by auto

lemma map_fn_rel_no_invar: \<open>map_fn_rel cs_code cs \<Longrightarrow> \<not>var_invar x \<Longrightarrow> cs_code x = None\<close>
  by (meson domD domIff map_fn_rel_lookup_var_invar)

lemma lookup0_nz_dom: \<open>lookup0 cs x \<noteq> 0 \<Longrightarrow> x \<in> dom cs\<close>
  by (auto simp: lookup0_def split: option.splits)

lemma dom_list_fn_rel: \<open>list_fn_rel cs_code cs \<Longrightarrow> dom (map_of cs_code) \<subseteq> {x. var_invar x}\<close>
  unfolding list_fn_rel_def by (auto simp add: map_fn_rel_lookup_var_invar)

lemma constr_from_list_le_rel:
  assumes \<open>list_fn_rel cs_code cs\<close>
  shows \<open>constr_rel (constr_le_from_list cs_code rhs) (Le cs rhs)\<close>
  using assms Coeffs.to_map_correct
  unfolding constr_le_from_list_def list_fn_rel_def poly_rel_def
  by (auto simp: poly_rel_def)

lemma constr_from_list_eq_rel:
  assumes \<open>list_fn_rel cs_code cs\<close>
  shows \<open>constr_rel (constr_eq_from_list cs_code rhs) (Eq cs rhs)\<close>
  using assms Coeffs.to_map_correct
  unfolding constr_eq_from_list_def list_fn_rel_def
  by (auto simp: poly_rel_def)

lemmas Coeffs.correct(28)[simp]

lemma invar_from_idx[intro!]: 
  assumes \<open>Scope.invar X\<close> \<open>Scope.\<alpha> X \<subseteq> {..<dims}\<close> \<open>\<And>i. i \<in> Scope.\<alpha> X \<Longrightarrow> f i \<in> doms i\<close>
  shows \<open>Vec.invar (vec_from_idx X f)\<close>
  unfolding vec_from_idx_def
  by (rule Scope.iterate_rule_insert_P) (insert assms, auto)

lemma idx_from_idx[simp]: 
  assumes \<open>Scope.invar X\<close> \<open>Scope.\<alpha> X \<subseteq> {..<dims}\<close> \<open>\<And>i. i \<in> Scope.\<alpha> X \<Longrightarrow> f i \<in> doms i\<close>
  shows \<open>Vec.\<alpha> (vec_from_idx X f) i = (if i \<in> Scope.\<alpha> X then Some (f i) else None)\<close>
  unfolding vec_from_idx_def  
  by (rule Scope.iterate_rule_insert_P[where S = X, where I = 
        \<open>\<lambda>R v. Vec.invar v \<and> Vec.\<alpha> v = (\<lambda>i. if i \<in> R then Some (f i) else None)\<close>]) 
    (insert assms, auto intro!: ext)


lemma idx_from_idx'[simp]: 
  assumes \<open>Scope.invar X\<close> \<open>Scope.\<alpha> X \<subseteq> {..<dims}\<close> \<open>\<And>i. i \<in> Scope.\<alpha> X \<Longrightarrow> f i \<in> doms i\<close>
  shows \<open>Vec.\<alpha> (vec_from_idx X f) = (\<lambda>i. Some (f i)) |` Scope.\<alpha> X\<close>
  using idx_from_idx[OF assms]
  by auto

lemma \<F>_rel_\<alpha>: \<open>(f, s) \<in> set \<F>_code \<Longrightarrow> \<F>_rel \<F>_code \<F> scopes \<Longrightarrow> f_name_code_\<alpha> f \<in> \<F>\<close>
  unfolding \<F>_rel_def
  by (auto dest!: rel_setD1)

lemma \<F>_relE:
  assumes \<open>fs \<in> set \<F>_code\<close> \<open>\<F>_rel \<F>_code \<F> scopes\<close>
  obtains \<open>f_name_code_\<alpha> (fst fs) \<in> \<F>\<close> \<open>Scope.\<alpha> (snd fs) = scopes (f_name_code_\<alpha> (fst fs))\<close> \<open>Scope.invar (snd fs)\<close> \<open>Scope.\<alpha> (snd fs) \<subseteq> vars\<close>
  using assms
  unfolding \<F>_rel_def
  by (auto dest!: rel_setD1)

lemma \<F>_rel_scope_eq[simp]: 
  assumes \<open>(f, s) \<in> set \<F>_code\<close> \<open>\<F>_rel \<F>_code \<F> scopes\<close>
  shows \<open>Scope.\<alpha> s = scopes (f_name_code_\<alpha> f)\<close>
  using assms
  unfolding \<F>_rel_def
  by (auto dest!: rel_setD1)

lemma \<F>_rel_scopes_vars: \<open>\<F>_rel \<F>_code \<F> scopes \<Longrightarrow> (f, s) \<in> set \<F>_code \<Longrightarrow> Scope.\<alpha> s \<subseteq> vars\<close>
  using invar_\<F>_rel_set 
  unfolding \<F>_rel_def
  by (fastforce dest: rel_setD1)

lemma \<F>_rel_scopes_vars': \<open>\<F>_rel \<F>_code \<F> scopes \<Longrightarrow> f \<in> \<F> \<Longrightarrow> scopes f \<subseteq> vars\<close>
  using invar_\<F>_rel_set 
  unfolding \<F>_rel_def
  by (auto dest!: rel_setD1)

lemma \<F>_eq_\<F>_code: 
  assumes \<open>\<F>_rel \<F>_code \<F> scopes\<close> 
  shows \<open>\<F> = (\<lambda>f. f_name_code_\<alpha> (fst f)) `  set \<F>_code\<close>
proof (standard, goal_cases)
  case 1
  then show ?case 
    using assms
    unfolding \<F>_rel_def
    by (auto simp:  image_iff dest!: rel_setD2) force

next
  case 2
  then show ?case
    using assms \<F>_rel_\<alpha>
    by auto
qed

lemma list_fn_relI':
  assumes 
    \<open>distinct (map fst xs)\<close>
    \<open>(\<And>c. c \<in> set xs \<Longrightarrow> var_invar (fst c))\<close>
    \<open>\<And>i_code y. (i_code, y) \<in> set xs \<Longrightarrow> y = f (var_code_\<alpha> i_code)\<close>
    \<open>\<And>i. i \<notin> var_code_\<alpha> ` dom (map_of xs) \<Longrightarrow> f i = 0\<close>
  shows \<open>list_fn_rel xs f\<close>
  unfolding list_fn_rel_def map_fn_rel_def lookup0_def
  using assms
  by auto

lemma \<F>_rel_distinctD[dest]: \<open>\<F>_rel \<F>_code \<F> scopes \<Longrightarrow> distinct (map fst \<F>_code)\<close>
  unfolding \<F>_rel_def by auto

lemma constr_max_rel:
  assumes \<open>\<F>_rel \<F>_code \<F> scopes\<close> \<open>state_rel x_code x\<close>  
    \<open>f_e_code i \<notin> fst ` set \<F>_code\<close> \<open>f_e i \<notin> \<F>\<close> \<open>xl \<in> doms i\<close> \<open>\<And>f. f \<in> \<F> \<Longrightarrow> scopes f - {i} \<subseteq> dom x\<close> \<open>i < dims\<close>
  shows \<open>constr_rel (constr_max_code \<F>_code i x_code xl) (constr_max \<F> i scopes x xl)\<close>
proof -
  {
    fix f s
    assume f: \<open>(f, s) \<in> set \<F>_code\<close>

    have \<open>(f_name_code_\<alpha> f) \<in> \<F>\<close>
      using \<F>_rel_\<alpha> assms(1) f by blast


    have scopes_subs: \<open>scopes (f_name_code_\<alpha> f) - {i} \<subseteq> dom x\<close>  \<open>scopes (f_name_code_\<alpha> f) \<subseteq> vars\<close>
      using assms \<open>f_name_code_\<alpha> f \<in> \<F>\<close> 
      by blast+


    have eq_scopes[simp]: \<open>Scope.\<alpha> s = scopes (f_name_code_\<alpha> f)\<close>
      using \<F>_rel_\<alpha> assms(1) f
      by auto

    have [simp, intro]: 
      \<open>Scope.invar s\<close> and \<open>Scope.\<alpha> s \<subseteq> vars\<close> and \<open>Scope.\<alpha> s - {i} \<subseteq> dom x\<close>
      using f assms assms invar_\<F>_rel_set scopes_subs
      by auto

    have not_f_e_i: \<open>f_name_code_\<alpha> f \<noteq> f_e i\<close>
      using f assms 
      by (auto elim!: \<F>_relE[OF _ assms(1)])

    have scopes_imp_x: \<open>j \<in> scopes (f_name_code_\<alpha> f) \<Longrightarrow> j \<noteq> i \<Longrightarrow>  j \<in> dom x\<close> for j
      using assms scopes_subs
      unfolding subset_iff
      by auto

    let ?x_code = \<open>vec_from_idx s (\<lambda>j. if j = i then xl else Vec.idx x_code j)\<close>

    have 
      \<open>i \<in> scopes (f_name_code_\<alpha> f) \<Longrightarrow>
        (\<lambda>ia. Some (if ia = i then xl else Vec.idx x_code ia)) |` scopes (f_name_code_\<alpha> f) = (x |` (scopes (f_name_code_\<alpha> f) - {i}))(i \<mapsto> xl)\<close>
      \<open>i \<notin> scopes (f_name_code_\<alpha> f) \<Longrightarrow> 
        (\<lambda>ia. Some (if ia = i then xl else Vec.idx x_code ia)) |` scopes (f_name_code_\<alpha> f) = x |` scopes (f_name_code_\<alpha> f)\<close>
      using assms(2) scopes_imp_x Vec.some_idx
      by (auto elim!: Vec.state_relE' simp:restrict_map_def)

    hence [simp]: \<open>Vec.\<alpha> ?x_code = x(i \<mapsto> xl) |` Scope.\<alpha> s\<close>
      using scopes_subs assms
      by (subst idx_from_idx') auto

    have v_\<alpha>: \<open>var_code_\<alpha> (var_code.var_f prefix_code f (show_state ?x_code))
        = var_name.var_f prefix (f_name_code_\<alpha> f) (x(i \<mapsto> xl) |` Scope.\<alpha> s)\<close>
      using scopes_subs assms
      by (subst var_code_\<alpha>_f) (intro invar_from_idx, auto)

    note v_\<alpha>  not_f_e_i  eq_scopes
  }
  note aux[simp] = this

  have [simp]: \<open>var_code_\<alpha> (var_code.var_f prefix_code (f_e_code i) (show_state x_code)) = var_name.var_f prefix (f_e i) x\<close>
    using assms prefix_rel 
    by auto

  show ?thesis
    unfolding constr_max_code_def constr_max_def
  proof(intro constr_from_list_le_rel list_fn_relI', goal_cases)
    case 1
    then show ?case 
      using assms by (auto simp: distinct_map intro!: inj_onI dest: eq_key_imp_eq_value)
  next
    case (2 c)
    have \<open>var_invar (var_code.var_f prefix_code f (show_state (vec_from_idx s (\<lambda>j. if j = i then xl else Vec.idx x_code j))))\<close>
      if \<open>(f, s) \<in> set \<F>_code \<close> for f s
    proof -
      have \<open>j \<in> scopes (f_name_code_\<alpha> f) \<Longrightarrow> j \<in> dom x \<or> j = i\<close> for j
        using assms that
        by (elim \<F>_relE[OF _ \<open>\<F>_rel \<F>_code \<F> scopes\<close>]) (auto simp add: subset_iff)
      thus ?thesis
      using that assms(2) 
        apply (intro invar_from_idx var_invar_fI)
      subgoal by (elim \<F>_relE[OF _ \<open>\<F>_rel \<F>_code \<F> scopes\<close>]) auto
      subgoal by (elim \<F>_relE[OF _ \<open>\<F>_rel \<F>_code \<F> scopes\<close>]) auto
      subgoal for j
        apply (cases \<open>i = j\<close>)
        subgoal using \<open>xl \<in> doms i\<close> by auto
        subgoal
          using \<open>state_rel x_code x\<close>
          apply (subst Vec.state_idx_eq)
          apply (elim \<F>_relE[OF _ \<open>\<F>_rel \<F>_code \<F> scopes\<close>])
          by (auto dest!: state_rel_partialD elim!: partial_statesE2)
        done
      done
  qed
  then show ?case
    using 2 assms(2)
    by auto
  next
    case (3 i_code y)
    thus ?case
      using \<F>_relE[OF _ assms(1)]
      by auto
  next
    case (4 v)
    thus ?case
      by (auto split: var_name.splits simp: \<F>_eq_\<F>_code[OF assms(1)] dom_map_of_conv_image_fst case_prod_unfold image_iff)
  qed
qed

lemma vecs_on_eq_partial[simp]: \<open>vecs_on X = partial_states_on_eq X\<close>
  unfolding vecs_on_def partial_states_on_eq_def partial_states_def partial_vecs_def
  by auto

lemma lt_doms[simp]: \<open>i < dims \<Longrightarrow> {..<card (doms i)} = doms i\<close>
  using doms_code by auto

lemma constrs_max_rel: 
  assumes \<open>\<F>_rel \<F>_code \<F> scopes\<close>  \<open>i < dims\<close>
    \<open>f_e_code i \<notin> fst ` set \<F>_code\<close> 
    \<open>f_e i \<notin> \<F>\<close>
    \<open>Scope.set_rel scope_e_code scope_e\<close>
    \<open>scope_e \<subseteq> vars\<close>
    \<open>\<And>f. f \<in> \<F> \<Longrightarrow> scopes f - {i} \<subseteq> scope_e\<close>
  shows \<open>constrs_rel
  (constrs_max_code \<F>_code i scope_e_code) 
  (constrs_max \<F> i scopes scope_e)\<close>
proof -

  note card_doms_in_doms[simp del]

  have \<open>z_code \<in> set (assignments_impl scope_e_code) \<Longrightarrow>
           xl \<in> doms i \<Longrightarrow>
           \<exists>x. (\<exists>xl z. x = constr_max \<F> i scopes z xl \<and> z \<in> partial_states_on_eq (Scope.\<alpha> scope_e_code) \<and> xl \<in> doms i) \<and>
               constr_rel (constr_max_code \<F>_code i z_code xl) x\<close> for z_code xl
    using assignments_impl_set[OF assms(5) assms(6)] assms(1,2,3,4,5,7)
    by (auto dest!: rel_setD1 intro!:  exI[of _ \<open>constr_max \<F> i scopes z xl\<close> for z] constr_max_rel)+

  moreover have \<open>z \<in> partial_states_on_eq (Scope.\<alpha> scope_e_code) \<Longrightarrow>
       xl \<in> doms i \<Longrightarrow> \<exists>x\<in>set (assignments_impl scope_e_code). 
  \<exists>y\<in>doms i. constr_rel (constr_max_code \<F>_code i x y) (constr_max \<F> i scopes z xl)\<close> for z xl
    using assms assignments_impl_set[OF assms(5) assms(6)] constr_max_rel[OF assms(1) _ assms(3) assms(4) ]
    by (auto dest!: rel_setD2 intro!: bexI[of _ xl]) (metis  partial_states_on_eq_domD) 

  ultimately show ?thesis
    unfolding constrs_max_code_def constrs_max_def 
    using assms
    by (auto intro!: rel_setI simp: constrs_rel_def atLeast0LessThan)
qed

lemma prefix_\<alpha>_eqD[dest]: \<open>prefix_\<alpha> x = prefix_\<alpha> y \<Longrightarrow> prefix_invar x \<Longrightarrow> prefix_invar y \<Longrightarrow> x = y\<close>
  using prefix_\<alpha>_inj by (auto dest!: inj_onD)

lemma var_invar_prefix_invarD[dest]: \<open>var_invar (var_f p f x) \<Longrightarrow> prefix_invar p\<close>
  unfolding var_invar_def by auto

lemma f_name_code_\<alpha>_eqD[dest]: \<open>f_name_code_\<alpha> x = f_name_code_\<alpha> y \<Longrightarrow> x = y\<close>
  by (cases x; cases y) auto

lemma var_code_\<alpha>_eqD[dest]: \<open>var_code_\<alpha> v = var_code_\<alpha> v' \<Longrightarrow> var_invar v \<Longrightarrow> var_invar v' \<Longrightarrow> v = v'\<close>
  using show_state_correct var_invar_def 
  by (cases v; cases v') auto

lemma map_fn_relE: 
  assumes \<open>map_fn_rel m f\<close>
  obtains \<open>\<And>i. i \<in> dom m \<Longrightarrow> var_invar i\<close>
    \<open>\<And>i. i \<in> dom m \<Longrightarrow> lookup0 m i = f (var_code_\<alpha> i)\<close>
    \<open>\<And>i. i \<notin> var_code_\<alpha> ` dom m \<Longrightarrow> f i = 0\<close>
  using assms 
  unfolding map_fn_rel_def
  by auto

lemma poly_\<alpha>_eq_lookup0[simp]: \<open>v\<in>dom (Coeffs.\<alpha> m) \<Longrightarrow> var_invar v \<Longrightarrow> var_code_\<alpha> v = i \<Longrightarrow> 
  poly_\<alpha> m i = lookup0 (Coeffs.\<alpha> m) v\<close>
  unfolding poly_\<alpha>_def
  by (auto intro!: some_equality[symmetric] arg_cong2[where f = lookup0] iff del: domIff)

lemma poly_\<alpha>_0[simp]: \<open>(\<And>v. v \<in> dom (Coeffs.\<alpha> m) \<Longrightarrow> \<not>var_code_\<alpha> v = i) \<Longrightarrow> 
  poly_\<alpha> m i = 0\<close>
  unfolding poly_\<alpha>_def
  by auto

lemma lookup0_coeffs[simp]: \<open>var_invar v \<Longrightarrow> dom (Coeffs.\<alpha> m) \<subseteq> {v. var_invar v} \<Longrightarrow> 
  lookup0 (Coeffs.\<alpha> m) v = poly_\<alpha> m (var_code_\<alpha> v)\<close>
  by (cases \<open>\<exists>v'\<in>dom (Coeffs.\<alpha> m). var_code_\<alpha> v' = var_code_\<alpha> v\<close>) (auto iff del: domIff)

lemma poly_rel_imp_\<alpha>_eq[simp]: 
  assumes \<open>poly_rel p_code p\<close> 
  shows \<open>poly_\<alpha> p_code i = p i\<close>
  using assms
  unfolding poly_rel_def
  by (cases \<open>\<exists>v\<in>dom (Coeffs.\<alpha> p_code). var_code_\<alpha> v = i\<close>) 
    (auto iff del: domIff elim!: map_fn_relE simp: image_iff, metis)

lemma constr_rel_imp_\<alpha>_eq[simp]:\<open>constr_rel constr_code constr \<Longrightarrow> constr_\<alpha> constr_code = constr\<close>
  by (cases constr_code; cases constr) auto

lemma constrs_rel_imp_\<alpha>_eq[simp]:\<open>constrs_rel constrs_code constrs \<Longrightarrow> constrs_\<alpha> constrs_code = constrs\<close>
  unfolding constrs_rel_def constrs_\<alpha>_def
  by (fastforce dest: rel_setD1 rel_setD2 constr_rel_imp_\<alpha>_eq simp: image_iff)

lemma rel_setE: 
  assumes "rel_set R X Y"
  obtains f f' where \<open>\<And>x. x \<in> X \<Longrightarrow> R x (f x)\<close> \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y\<close> \<open>\<And>y. y \<in> Y \<Longrightarrow> R (f' y) y\<close> \<open>\<And>y. y \<in> Y \<Longrightarrow> f' y \<in> X\<close>
  using assms
  unfolding rel_set_def
  by metis

lemmas rel_prod_sel[simp]

lemma f_name_relI[intro]: 
  \<open>f_name_rel (f_b_code i) (f_b i)\<close>
  \<open>f_name_rel (f_c_code i) (f_c i)\<close>
  \<open>f_name_rel (f_e_code i) (f_e i)\<close>
  unfolding f_name_rel_def 
  by auto

lemma f_name_relI'[iff, simp]: 
  \<open>f_name_rel (f_b_code i) (f_b j) \<longleftrightarrow> i = j\<close>
  \<open>f_name_rel (f_c_code i) (f_c j) \<longleftrightarrow> i = j\<close>
  \<open>f_name_rel (f_e_code i) (f_e j) \<longleftrightarrow> i = j\<close>
  unfolding f_name_rel_def 
  by auto

lemma rel_set_unI[intro]: \<open>rel_set R X Y \<Longrightarrow> rel_set R X' Y' \<Longrightarrow> rel_set R (X \<union> X') (Y \<union> Y')\<close>
  using union_transfer[THEN rel_funD, THEN rel_funD].

lemma insert_constrs_rel:
  assumes \<open>constrs_rel cs_code cs\<close> \<open>constr_rel constr_code constr\<close>
  shows \<open>constrs_rel (constr_code#cs_code) (insert constr cs)\<close>
  using assms
  unfolding constrs_rel_def rel_set_def
  by simp

lemma config_imp_constrs_rel:
  assumes \<open>config_rel cfg_code cfg\<close>
  shows \<open>constrs_rel (fst cfg_code) (fst cfg)\<close>
  using assms unfolding config_rel_def by auto


lemma config_rel_fst:
  assumes \<open>config_rel cfg_code cfg\<close>
  assumes \<open>(a, s) \<in> set (fst (snd cfg_code))\<close>
  shows \<open>f_name_code_\<alpha> a \<in> fst (snd cfg)\<close>
  using assms unfolding config_rel_def
  using \<F>_rel_\<alpha> by force

lemma config_fst_snd: 
  assumes \<open>config_rel cfg_code cfg\<close>
  shows \<open>f_name_code_\<alpha> ` fst ` (set (fst (snd cfg_code))) = fst (snd cfg)\<close>
  using  \<F>_eq_\<F>_code[of \<open>(fst (snd cfg_code))\<close>] config_rel_fst[OF assms] assms
  unfolding config_rel_def
  by (auto simp: image_iff)+

lemma config_rel_distinct: \<open>config_rel cfg_code cfg \<Longrightarrow> distinct (fst (snd cfg_code))\<close>
  unfolding config_rel_def \<F>_rel_def
  by (auto dest!: distinct_mapI)

lemma var_code_\<alpha>_f'[simp]:
  assumes \<open>Vec.invar x_code\<close>
  shows \<open>var_code_\<alpha> (var_code.var_f prefix_code f (show_state x_code)) = var_name.var_f prefix (f_name_code_\<alpha> f) (Vec.\<alpha> x_code)\<close>
  using assms prefix_rel var_code_\<alpha>_f 
  by auto

lemma lookup0_poly_rel: \<open>poly_rel p_code p \<Longrightarrow> i \<in> dom (Coeffs.\<alpha> p_code) \<Longrightarrow> lookup0 (Coeffs.\<alpha> p_code) i = p (var_code_\<alpha> i)\<close>
  unfolding poly_rel_def map_fn_rel_def
  by auto
end


locale Factored_LP_Code_Transfer_Rel' =
  Factored_LP_Code_Transfer_Rel +
  assumes 
    C_valid: \<open>C_rel\<close> and
    B_valid: \<open>B_rel\<close>
begin

lemma B_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) B_code B\<close>
  using B_valid unfolding B_rel_def by auto

lemma C_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) C_code C\<close>
  using C_valid unfolding C_rel_def by auto

lemma b_subs_vars: \<open>b' \<in> set B \<Longrightarrow> snd b' \<subseteq> vars\<close>
  using B_valid unfolding B_rel_def by auto

lemma c_subs_vars: \<open>c' \<in> set C \<Longrightarrow> snd c' \<subseteq> vars\<close>
  using C_valid unfolding C_rel_def by auto

sublocale factored_lp
  where doms = doms and
    prefix = prefix and
    order = id
  using B_valid[unfolded B_rel_def] C_valid[unfolded C_rel_def]  doms_ne
  by unfold_locales (auto simp: partial_states_def partial_vecs_def subset_iff elim!: sndE[rotated])+

abbreviation \<open>C_code' \<equiv> map (\<lambda>(i, f). (f_c_code i, SR.scope f)) (List.enumerate 0 C_code)\<close>
abbreviation \<open>B_code' \<equiv> map (\<lambda>(i, f). (f_b_code i, STE.SE.scope f)) (List.enumerate 0 B_code)\<close>

lemma len_B_code[simp]: \<open>length B_code = num_b\<close>
  using B_rel
  unfolding num_b_def by auto

lemma len_C_code[simp]: \<open>length C_code = num_c\<close>
  using C_rel
  unfolding num_c_def by auto

lemma rel_set_B_code': \<open>rel_set (rel_prod f_name_rel Scope.set_rel) 
  (set B_code') ({(f_b i, scope_b i) |i. i < num_b})\<close>
proof (rule rel_setI, goal_cases)
  case (1 x)
  then show ?case 
    using B_rel 
    by (intro bexI[of _ \<open>case fst x of f_b_code i \<Rightarrow> (f_b i, scope_b i)\<close>]) 
      (auto simp: case_prod_unfold scope_b_def in_set_enumerate_eq)
next
  case (2 y)
  then show ?case 
    using B_rel
    by (intro bexI[of _ \<open>case fst y of f_b i \<Rightarrow> (B_code' ! i)\<close>])
      (auto simp: in_set_enumerate_eq nth_enumerate_eq scope_b_def image_iff Bex_def)
qed

lemma rel_set_C_code': \<open>rel_set (rel_prod f_name_rel Scope.set_rel) 
  (set C_code') ({(f_c i, scope_c i) |i. i < num_c})\<close>
proof (rule rel_setI, goal_cases)
  case (1 x)
  then show ?case 
    using C_rel 
    by (intro bexI[of _ \<open>case fst x of f_c_code i \<Rightarrow> (f_c i, scope_c i)\<close>]) 
      (auto simp: case_prod_unfold scope_c_def in_set_enumerate_eq)
next
  case (2 y)
  then show ?case 
    using C_rel
    by (intro bexI[of _ \<open>case fst y of f_c i \<Rightarrow> (C_code' ! i)\<close>])
      (auto simp: in_set_enumerate_eq nth_enumerate_eq scope_c_def image_iff Bex_def)
qed

lemma \<F>_init_rel: \<open>\<F>_rel \<F>_init_code \<F>_init scopes_init\<close>
  unfolding \<F>_init_code_def \<F>_init_def \<F>_rel_def
  apply safe
  subgoal by (auto simp: comp_def distinct_map in_set_enumerate_eq intro!: inj_onI)
  subgoal using scope_c_subs scopes_init_def by auto
  subgoal using scope_b_subs scopes_init_def by auto
  subgoal
    unfolding set_append image_Un
    apply (rule union_transfer[THEN rel_funD, THEN rel_funD])
    subgoal
      unfolding scopes_init_def  Setcompr_eq_image[symmetric]
      using rel_set_C_code'
      by (smt (verit, best) Collect_cong f_name.case(1) mem_Collect_eq)
    subgoal
      unfolding scopes_init_def  Setcompr_eq_image[symmetric]
      using rel_set_B_code'
      by (smt (verit, best) Collect_cong f_name.case(2) mem_Collect_eq)
    done
  done

lemma constrs_c_eq: \<open>constrs_c = (\<Union>i < num_c. {constr_c z i |z. z \<in> vecs_on (scope_c i)})\<close>
  unfolding constrs_c_def by auto

lemma set_constrs_c_single_code: \<open>set (constrs_c_single_code i (C_code ! i)) = 
  {constr_c_code z i (((C_code ! i))) | z.
  z \<in> set (assignments_impl (SR.scope (C_code ! i)))}\<close>
  unfolding constrs_c_single_code_def Let_def
  by auto

lemma set_constrs_c_code: \<open>set constrs_c_code = (\<Union>i < num_c. set (constrs_c_single_code i (C_code ! i)))\<close>
  by (auto simp: constrs_c_code_def in_set_enumerate_eq algebra_simps in_set_enumerate_eq Bex_def)

lemma scope_C[simp]: \<open>i < num_c \<Longrightarrow> SR.scope_\<alpha> (C_code ! i) = scope_c i\<close>
  using C_rel scope_c_def by auto

lemma scoped_C_code[simp]:
  assumes \<open>state_rel x_code x\<close> \<open>i < num_c\<close> \<open>x \<in> partial_states_on_eq (scope_c i)\<close>
  shows \<open>SR.scoped_\<alpha> (C_code ! i) x_code = c_r i x\<close>
  using assms C_rel c_def partial_states_on_eq_domD scope_c_def
  by (auto dest!: list_all2_nthD[of _ _ _ i])

lemma constr_c_rel:
  assumes \<open>state_rel x_code x\<close> \<open>x \<in> partial_states_on_eq (scope_c i)\<close> \<open>i < num_c\<close>
  shows \<open>constr_rel (constr_c_code x_code i (C_code ! i)) (constr_c x i)\<close>
  unfolding constr_c_code_def constr_c_def Let_def
  using assms prefix_rel
  by  (intro constr_from_list_eq_rel list_fn_relI) auto

lemma constr_c_rel':
  assumes \<open>i < num_c\<close>
  shows 
    \<open>(rel_on state_rel (partial_states_on_eq (scope_c i)) ===> constr_rel) 
      (\<lambda>x_code. (constr_c_code x_code i ((C_code ! i))))
      (\<lambda>x. constr_c x i)\<close>
  using constr_c_rel assms
  by auto

lemma C_code_inv[intro!]: \<open>i < num_c \<Longrightarrow> SR.invar (C_code ! i)\<close>
  by (metis C_rel SR.scoped_fn_state_relE'(3) len_C_code list_rel_nthE')

lemma rel_C_scope_states: \<open>i < num_c \<Longrightarrow> 
  rel_set state_rel (set (assignments_impl (SR.scope (C_code ! i)))) (vecs_on (scope_c i))\<close>
  using scope_c_subs 
  by (auto intro!: assignments_impl_set)

lemma rel_C'_scope_states': \<open>i < num_c \<Longrightarrow> 
  rel_set (rel_on state_rel (partial_states_on_eq (scope_c i)))
    {z. z \<in> set (assignments_impl (SR.scope (C_code ! i)))}
    {z. z \<in> (vecs_on (scope_c i))}\<close>
  using rel_C_scope_states[of i]
  by (auto intro!: rel_setI dest: rel_setD1 rel_setD2)

lemma constrs_rel_c_single_i:
  assumes \<open>i < num_c\<close>
  shows \<open>constrs_rel (constrs_c_single_code i (C_code ! i)) {constr_c z i |z j. z \<in> vecs_on (scope_c i)}\<close>
  unfolding Let_def constrs_rel_def set_constrs_c_single_code
  using assms image_transfer[THEN rel_funD, THEN rel_funD, OF constr_c_rel' rel_C'_scope_states'[OF assms]]
  by (auto simp: Setcompr_eq_image)

lemma constrs_C_rel: \<open>constrs_rel constrs_c_code constrs_c\<close>
  unfolding constrs_rel_def constrs_c_eq set_constrs_c_code
  apply (rule Union_transfer[THEN rel_funD])
  apply (rule image_transfer[THEN rel_funD, THEN rel_funD, of \<open>\<lambda>i j. i = j \<and> i < num_c\<close>])
  using constrs_rel_c_single_i 
  by (auto intro!: rel_funI intro: rel_setI simp: constrs_rel_def)

lemma constr_b_rel:
  assumes \<open>state_rel x_code x\<close>
  shows \<open>constr_rel (constr_b_code x_code i (real_of_ereal (b_r i x))) (constr_b x i)\<close>
  unfolding constr_b_code_def constr_b_def
  using assms prefix_rel
  by (intro constr_from_list_eq_rel list_fn_relI) auto

lemma scope_B[simp]: \<open>i < num_b \<Longrightarrow> STE.SE.scope_\<alpha> (B_code ! i) = scope_b i\<close>
  using B_rel scope_b_def by auto

lemma scoped_B_code[simp]:
  assumes \<open>state_rel x_code x\<close> \<open>i < num_b\<close> \<open>x \<in> partial_states_on_eq (scope_b i)\<close>
  shows \<open>STE.SE.scoped_\<alpha> (B_code ! i) x_code = b_r i x\<close>
  using assms B_rel b_def partial_states_on_eq_domD scope_b_def
  by (auto dest!: list_all2_nthD[of _ _ _ i])

lemma constr_b_rel':
  assumes \<open>i < num_b\<close>
  shows \<open>(rel_on state_rel (partial_states_on_eq (scope_b i)) ===> constr_rel) 
  (\<lambda>x_code. (constr_b_code x_code i (real_of_ereal (STE.SE.scoped_\<alpha> (B_code ! i) x_code))))
  (\<lambda>x. constr_b x i)\<close>
  using constr_b_rel assms
  by auto

lemma constrs_b_eq: \<open>constrs_b = (\<Union>i < num_b. {constr_b z i |z. z \<in> vecs_on (scope_b i) \<and> b_r i z \<noteq> - \<infinity>})\<close>
  unfolding constrs_b_def by auto

lemma B_code_inv[intro!]: \<open>i < num_b \<Longrightarrow> STE.SE.invar (B_code ! i)\<close>
  by (metis B_rel STE.SE.scoped_fn_state_relE'(3) len_B_code list_rel_nthE')

lemma rel_B_scope_states: \<open>i < num_b \<Longrightarrow> rel_set state_rel (set (assignments_impl (STE.SE.scope (B_code ! i)))) (vecs_on (scope_b i))\<close>
  using scope_b_subs by (auto intro!: assignments_impl_set)


lemma rel_B'_scope_states: \<open>i < num_b \<Longrightarrow> rel_set state_rel 
  {z. STE.SE.scoped_\<alpha> (B_code ! i) z \<noteq> - \<infinity> \<and> z \<in> set (assignments_impl (STE.SE.scope (B_code ! i)))}
  {z. z \<in> (vecs_on (scope_b i)) \<and> b_r i z \<noteq> - \<infinity>}\<close>
  apply (rule rel_setI)
  subgoal for x 
  using rel_setD1[OF rel_B_scope_states[of i ], of x] scoped_B_code[of x _ i]
    by (fastforce intro!: exI[of _ \<open>Vec.\<alpha> x\<close>])
  subgoal for y
    using rel_setD2[OF rel_B_scope_states[of i], of y]
    by auto (metis scoped_B_code)
  done


lemma rel_B'_scope_states': \<open>i < num_b \<Longrightarrow> rel_set (rel_on state_rel (partial_states_on_eq (scope_b i))) 
  {z. STE.SE.scoped_\<alpha> (B_code ! i) z \<noteq> - \<infinity> \<and> z \<in> set (assignments_impl (STE.SE.scope (B_code ! i)))}
  {z. z \<in> (vecs_on (scope_b i)) \<and> b_r i z \<noteq> - \<infinity>}\<close>
  apply (rule rel_setI)
  subgoal for x 
  using rel_setD1[OF rel_B_scope_states[of i ], of x] scoped_B_code[of x _ i]
    by (fastforce intro!: exI[of _ \<open>Vec.\<alpha> x\<close>])
  subgoal for y
    using rel_setD2[OF rel_B_scope_states[of i], of y]
    by auto (metis rel_onI scoped_B_code)
  done


lemma set_constrs_b_single_code: \<open>set (constrs_b_single_code i (B_code ! i)) = 
  {constr_b_code z i (real_of_ereal (STE.SE.scoped_\<alpha> (B_code ! i) z)) | z. 
  STE.SE.scoped_\<alpha> (B_code ! i) z \<noteq> - \<infinity> \<and> 
  z \<in> set (assignments_impl (STE.SE.scope (B_code ! i)))}\<close>
  unfolding constrs_b_single_code_def Let_def
  apply safe
  subgoal by (auto simp: set_map_filter image_iff)
  subgoal for x z
    by (auto 
        simp: set_map_filter image_iff 
        intro!: bexI[of _  \<open>Some (constr_b_code z i (real_of_ereal (STE.SE.scoped_\<alpha> (B_code ! i) z)))\<close>])
  done


lemma constrs_rel_b_single_i:
  assumes \<open>i < num_b\<close>
  shows \<open>constrs_rel (constrs_b_single_code i (B_code ! i)) {constr_b z i |z j. z \<in> vecs_on (scope_b i) \<and> b_r i z \<noteq> - \<infinity>}\<close>
  unfolding Let_def constrs_rel_def set_constrs_b_single_code
  using assms image_transfer[THEN rel_funD, THEN rel_funD, OF constr_b_rel' rel_B'_scope_states'[OF assms]]
  by (auto simp: set_map_filter image_image image_Un image_Int Setcompr_eq_image[symmetric])

lemma set_constrs_b_code: \<open>set constrs_b_code = (\<Union>i < num_b. set (constrs_b_single_code i (B_code ! i)))\<close>
  by (auto simp: constrs_b_code_def in_set_enumerate_eq Bex_def)

lemma constrs_B_rel: \<open>constrs_rel constrs_b_code constrs_b\<close>
  unfolding constrs_b_eq
  unfolding constrs_rel_def set_constrs_b_code
  apply (rule Union_transfer[THEN rel_funD])
  apply (rule image_transfer[THEN rel_funD, THEN rel_funD, of \<open>\<lambda>i j. i = j \<and> i < num_b\<close>])
  using constrs_rel_b_single_i constrs_rel_def
  by (auto intro: rel_setI)

lemma constrs_init_rel: \<open>constrs_rel constrs_init_code constrs_init\<close>
  using constrs_B_rel constrs_C_rel
  unfolding constrs_init_code_def constrs_init_def constrs_rel_def
  by auto

lemma config_rel_init: \<open>config_rel (constrs_init_code, \<F>_init_code, 0) (constrs_init, \<F>_init, scopes_init, 0)\<close>
  unfolding config_rel_def
  using constrs_init_rel invar_init \<F>_init_rel
  by auto

lemma elim_step_ith: \<open>snd (snd (snd (((\<lambda>p. elim_step (fst p) (fst (snd p)) (fst (snd (snd p))) (snd (snd (snd p)))) ^^ i) (\<Omega>, \<F>, x, y)))) = y + i\<close>
  apply (induction i arbitrary: x y \<Omega> \<F>)
  unfolding funpow_Suc_right elim_step_def
  by (auto simp: Let_def)

lemma config_rel_step: 
  assumes \<open>i < dims\<close> \<open>config_rel (cs_code, \<F>_code, i_code) (cs, \<F>, scopes, i)\<close>
  shows \<open>config_rel (elim_step_code cs_code \<F>_code i_code) (elim_step cs \<F> scopes i)\<close>
proof-
  have [simp]: \<open>i_code = i\<close>
    using assms unfolding config_rel_def by auto

  have invar_lp: \<open>invar_lp cs \<F> scopes i\<close>
    using assms unfolding config_rel_def by auto

  note elim_step_def
  note elim_step_code_def

  let ?l = i
  let ?E = \<open>{e |e. e \<in> \<F> \<and> ?l \<in> scopes e}\<close>
  let ?E_code = \<open>fst (partition (\<lambda>(f, s). Scope.memb ?l s) \<F>_code)\<close>
  let ?notE_code = \<open>snd (partition (\<lambda>(f, s). Scope.memb ?l s) \<F>_code)\<close>
  let ?scope_e_code = \<open>Scope.delete ?l (Scope.Union_sets (map snd ?E_code))\<close>

  have \<F>_rel[intro]: \<open>\<F>_rel \<F>_code \<F> scopes\<close>
    using assms unfolding config_rel_def by auto

  have not_f_e_l[simp]: \<open>f \<in> \<F> \<Longrightarrow> f \<noteq> f_e ?l\<close> for f
    using assms 
    unfolding invar_lp_def config_rel_def \<F>_init_def
    by auto

  hence not_f_e_code_l[simp]: \<open>f \<in> set \<F>_code \<Longrightarrow> fst f \<noteq> f_e_code ?l\<close> for f
    using f_name_code_\<alpha>.simps(3)
    by (metis \<F>_rel \<F>_relE)

  have distinct: \<open>distinct (map fst (filter (\<lambda>p. Scope.memb i (snd p)) \<F>_code))\<close>
    using distinct_map_filter \<F>_rel_distinctD
    by blast

  moreover have scopes_lt_dim: \<open>x \<in> scopes g \<Longrightarrow> g \<in> \<F> \<Longrightarrow> x < dims\<close> for x g
    using assms
    unfolding config_rel_def \<F>_rel_def
    by (auto elim!: rel_setE)+

  ultimately have \<F>_rel_fst: \<open>\<F>_rel (filter (\<lambda>p. Scope.memb i (snd p)) \<F>_code) {f \<in> \<F>. i \<in> scopes f} scopes\<close>
    using assms
    unfolding config_rel_def \<F>_rel_def case_prod_unfold
    by (fastforce intro!: rel_setI simp: image_iff rel_set_def)


  have \<open>rel_set (rel_prod f_name_rel Scope.set_rel) (set (snd (partition (\<lambda>(f, y). Scope.memb i y) \<F>_code)))
     ((\<lambda>c. (c, (scopes(f_e i := \<Union> (scopes ` {e |e. e \<in> \<F> \<and> i \<in> scopes e}) - {i})) c)) ` (\<F> - {e |e. e \<in> \<F> \<and> i \<in> scopes e}))\<close>    
    using assms
    unfolding config_rel_def \<F>_rel_def case_prod_unfold rel_set_def
    by (fastforce intro!: rel_setI)

  hence \<F>_rel_E: \<open>\<F>_rel ?notE_code (\<F> - ?E) (scopes(f_e ?l := \<Union> (scopes ` ?E) - {?l}))\<close>
    unfolding \<F>_rel_def
    using distinct_map_fst_filterI \<F>_rel_distinctD  scopes_lt_dim
    by (force simp: comp_def case_prod_unfold)+

  have \<F>_scope_inv: \<open>(f, s) \<in> set \<F>_code \<Longrightarrow> Scope.invar s\<close> for f s
    by (auto intro!: Scope.set_relI elim!: \<F>_relE[OF _ \<F>_rel])

  have scopes_\<alpha>: \<open>scopes (f_name_code_\<alpha> (fst f)) = Scope.\<alpha> (snd f)\<close> if \<open>f \<in> set \<F>_code\<close> for f
    using that f_name_rel_self[of \<open>fst f\<close>] \<F>_relE
    by blast

  hence scopes_\<alpha>': \<open>scopes (f_name_code_\<alpha> f) = Scope.\<alpha> s\<close> if \<open>(f,s) \<in> set \<F>_code\<close> for f s
    using that by auto

  have \<open>Scope.set_rel 
    ((Scope.Union_sets (map snd (filter (\<lambda>(f, y). Scope.memb i y) \<F>_code))))
    (\<Union> (scopes ` {f \<in> \<F>. i \<in> scopes f}))\<close>
      unfolding \<F>_eq_\<F>_code[OF \<F>_rel]
      using scopes_\<alpha> \<F>_scope_inv
      by (intro Scope.set_relI) (auto simp add: Scope.Union_sets_correct[subst] case_prod_unfold)

    hence *: \<open>Scope.set_rel ?scope_e_code
    (\<Union> (scopes ` {f \<in> \<F>. i \<in> scopes f}) - {i})\<close>
      by auto

  have \<F>_rel': \<open>\<F>_rel ((f_e_code ?l, ?scope_e_code) # ?notE_code) (\<F> - ?E \<union> {f_e ?l}) (scopes(f_e ?l := \<Union> (scopes ` ?E) - {?l}))\<close>
    unfolding \<F>_rel_def
    apply safe
    subgoal using \<F>_rel_E not_f_e_code_l by force
    subgoal using \<F>_rel_E unfolding \<F>_rel_def by auto
    subgoal using assms \<F>_rel \<F>_rel_def config_rel_def by auto
    subgoal
      apply auto
    apply (rule Lifting_Set.insert_transfer[THEN rel_funD, THEN rel_funD])
      subgoal
        using *
        by auto
      subgoal
        using \<F>_rel  
      by (fastforce simp: \<F>_eq_\<F>_code[OF \<F>_rel] \<F>_scope_inv \<F>_rel_\<alpha> intro!: rel_setI)
    done
  done

  have \<open>constrs_rel
     (constrs_max_code (filter (\<lambda>p. Scope.memb i (snd p)) \<F>_code) i
       (Scope.delete i (Scope.Union_sets (map snd (filter (\<lambda>p. Scope.memb i (snd p)) \<F>_code)))))
     (constrs_max {f \<in> \<F>. i \<in> scopes f} i scopes (\<Union> (scopes ` {f \<in> \<F>. i \<in> scopes f}) - {i}))\<close>
    apply (rule constrs_max_rel)
    subgoal using \<F>_rel_fst by blast
    subgoal using assms by blast
    subgoal using assms by (meson filter_is_subset in_fst_imageE not_f_e_code_l prod.sel(1) subset_code(1))
    subgoal using not_f_e_l by fastforce
      using * invar_lp
      unfolding invar_lp_def partition_filter1 case_prod_unfold
      by force+

  moreover have \<open>constrs_rel cs_code cs\<close> 
    using assms unfolding config_rel_def by auto
  ultimately have c_rel: \<open>constrs_rel (fst (elim_step_code cs_code \<F>_code i_code)) (fst (elim_step cs \<F> scopes i))\<close>
    unfolding elim_step_code_def elim_step_def Let_def case_prod_unfold constrs_rel_def
    by (auto intro!: union_transfer[THEN rel_funD, THEN rel_funD])

  show ?thesis
    unfolding config_rel_def elim_step_def elim_step_code_def Let_def
    apply safe
    subgoal using assms invar_lp_step[of i] unfolding config_rel_def by (auto simp: elim_step_def Let_def)
    subgoal using c_rel unfolding elim_step_def elim_step_code_def by (simp add: Let_def)
    subgoal using \<F>_rel' by simp
    subgoal by simp
    done
qed

lemma config_rel_pow: 
  assumes \<open>i \<le> dims\<close>
  shows \<open>config_rel (((\<lambda>(\<Omega>, x, y). elim_step_code \<Omega> x y) ^^ i) (constrs_init_code, \<F>_init_code, 0))
     (((\<lambda>(\<Omega>, \<F>, x, y). elim_step \<Omega> \<F> x y) ^^ i) (constrs_init, \<F>_init, scopes_init, 0))\<close>
  using assms
  apply (induction i)
  subgoal using config_rel_init by auto
  subgoal
    unfolding case_prod_unfold
    using invar_lp_elim_step_iter
    supply elim_step_ith[where y = 0, subst]
    by (auto simp: config_rel_step)
  done

lemma elim_vars_aux_rel: \<open>config_rel elim_vars_aux_code elim_vars_aux\<close>
  unfolding elim_vars_aux_code_def elim_vars_aux_def
  using config_rel_pow
  by auto

lemma gen_constrs_rel:
  assumes \<open>config_rel cfg_code cfg\<close>
  shows \<open>constrs_rel (gen_constrs_code cfg_code) (gen_constrs cfg)\<close>
proof -
  let ?gen_code = \<open>constr_le_from_list ((var_code.var_phi, - 1) # map (\<lambda>p. (var_code.var_f prefix_code (fst p) (show_state Vec.empty), 1)) (fst (snd cfg_code))) 0\<close>
  let ?gen = \<open>Le (case_var_name (\<lambda>p f z. if p = prefix \<and> f \<in> fst (snd cfg) \<and> z = Map.empty then 1 else 0) (\<lambda>nat. 0) (- 1)) 0\<close>
  have 1: \<open>constr_rel ?gen_code ?gen\<close>
    apply (intro constr_from_list_le_rel list_fn_relI)
    subgoal 
      using assms config_rel_distinct[OF assms]
      unfolding config_rel_def \<F>_rel_def
      by (fastforce simp: distinct_map inj_on_def)
    using assms
    unfolding \<F>_rel_def
    by (auto split: var_name.splits simp: image_iff config_fst_snd[symmetric])
  thus ?thesis
    unfolding gen_constrs_code_def gen_constrs_def case_prod_unfold
    using insert_constrs_rel 1 assms  
    by (auto dest!: config_imp_constrs_rel)
qed

lemma elim_vars_rel: \<open>constrs_rel elim_vars_code elim_vars\<close>
  using elim_vars_aux_rel gen_constrs_rel
  unfolding elim_vars_code_def elim_vars_def
  by blast

lemma constrs_rel_append: \<open>constrs_rel cs_code cs \<Longrightarrow> constrs_rel cs_code' cs' \<Longrightarrow>
  constrs_rel (cs_code @ cs_code') (cs \<union> cs')\<close>
  unfolding constrs_rel_def by auto

definition \<open>sol_space_constr constr = { sol. sat_constr sol constr }\<close>

definition \<open>sol_\<alpha> sol = (\<lambda>v. Coeffs.lookup0_code sol v)\<close>

end
end