theory LP_File_Certification
  imports LP_Code
begin

section \<open>LP file format\<close>
datatype sense = Leq | Geq | Eq
datatype 'a bound = Lb 'a "real option" | Ub 'a "real option" | Betw "real option" 'a "real option" | Beq 'a real | Free 'a

type_synonym 'a constraint_expr = "('a \<times> real) list"
type_synonym 'a constraint = "'a constraint_expr \<times> sense \<times> real"
type_synonym 'a constraint_sect = "'a constraint list"
type_synonym 'a bounds = "'a bound list"

type_synonym 'a LP = "
  bool \<times>                 \<comment> \<open>minimize?\<close>
  nat \<times> \<comment> \<open>dimension\<close>
  'a constraint_expr \<times>        \<comment> \<open>objective function\<close>
  'a constraint list \<times>   \<comment> \<open>constraints\<close>
  'a bounds"                  \<comment> \<open>bounds\<close>

fun var_bound where
  "var_bound (Lb v _) = v"
| "var_bound (Ub v _) = v"
| "var_bound (Free v) = v"
| "var_bound (Betw _ v _) = v"
| "var_bound (Beq v _) = v"

definition "vars_bounds bs = set (map var_bound bs)"

definition "vars_constrexpr ce = set (map snd ce)"

fun vars_constraint where "vars_constraint (c, _, _) = vars_constrexpr c"

definition "vars_constraint_sect (cs :: string constraint_sect) = \<Union> (set (map vars_constraint cs))"

fun vars_LP where
  "vars_LP (_, c,cs, bds) = vars_constrexpr c \<union> vars_constraint_sect cs \<union> vars_bounds bds"

fun to_nat_LP :: "string LP \<Rightarrow> nat LP" where
  "to_nat_LP (minimize, cost, cs, bds) = (
  let vars = {} :: string set in
  (minimize, undefined, undefined, undefined)
)"

derive "show" bound
derive "show" sense

context LP_Code
begin

fun vec_init where
"vec_init x 0 v = v" |
"vec_init x (Suc n) v = vec_init x n (v_update n x v)"

definition "neg_constraint_expr = map (\<lambda>(i :: nat, x :: real). (i, -x))"

fun constraint_to_le where
  "constraint_to_le (p, Leq, b) = [(p,b)]" |
  "constraint_to_le (p, Geq, b) = [(neg_constraint_expr p, -b)]" |
  "constraint_to_le (p, Eq, b) = [(neg_constraint_expr p, - b), (p,b)]"

definition "constraints_to_le cs = concat (map constraint_to_le cs)"
definition "constraints_to_map cs =
  (let (A, b) = unzip (constraints_to_le cs) in
   (map Sparse_Vec.from_list2 A, b))"

definition "from_file' m n c cs = (
    n,
    Sparse_Vec.from_list2 (if m then c else neg_constraint_expr c),
    let (c2, b2) = constraints_to_map cs in 
      (Sparse_Mat.from_list2 (List.enumerate 0 (c2)), Sparse_Vec.from_list2 (List.enumerate 0 (b2))))"

definition \<open>scalar_prod_list xs m = (sum_list (map (\<lambda>(i, r). r * lookup' m i) xs))\<close>

definition \<open>sat_constr constr x \<longleftrightarrow> (case constr of 
  (p, Leq, r) \<Rightarrow> scalar_prod_list p x \<le> r |
  (p, Geq, r) \<Rightarrow> scalar_prod_list p x \<ge> r |
  (p, Eq, r) \<Rightarrow> scalar_prod_list p x = r)\<close>

definition \<open>sat_lp_list constrs x \<longleftrightarrow> (\<forall>constr \<in> set constrs. sat_constr constr x)\<close>

lemma v_lookup_foldl_upd: \<open>Sparse_Vec.invar v0 \<Longrightarrow> v_lookup (foldl (\<lambda>acc (k, v). v_update k v acc) v0 xs) i = (v_lookup v0 ++ Map.map_of (rev xs)) i\<close>
  apply (induction xs arbitrary: v0 i)
  by (auto simp: Sparse_Vec.invar_update Sparse_Vec.map_update)


lemma m_foldl_invar: \<open>Sparse_Mat.invar v0 \<Longrightarrow> Sparse_Mat.invar (foldl (\<lambda>acc (k, v). m_update k v acc) v0 xs)\<close>
  apply (induction xs arbitrary: v0)
  by (auto simp: Sparse_Mat.invar_update Sparse_Mat.map_update)

lemma v_foldl_invar: \<open>Sparse_Vec.invar v0 \<Longrightarrow> Sparse_Vec.invar (foldl (\<lambda>acc (k, v). v_update k v acc) v0 xs)\<close>
  apply (induction xs arbitrary: v0)
  by (auto simp: Sparse_Vec.invar_update Sparse_Vec.map_update)

lemma m_lookup_foldl_upd: \<open>Sparse_Mat.invar v0 \<Longrightarrow> m_lookup (foldl (\<lambda>acc (k, v). m_update k v acc) v0 xs) i = (m_lookup v0 ++ Map.map_of (rev xs)) i\<close>
  apply (induction xs arbitrary: v0 i)
  by (auto simp: Sparse_Mat.invar_update Sparse_Mat.map_update)

lemmas Sparse_Vec.invar_empty[simp] Sparse_Vec.map_empty[simp]
lemmas Sparse_Mat.invar_empty[simp] Sparse_Mat.map_empty[simp]

lemma v_lookup_from_list[simp]: \<open>v_lookup (Sparse_Vec.from_list2 xs) = Map.map_of (rev xs)\<close>
  unfolding Sparse_Vec.from_list2_def
  apply (rule ext)
  apply (subst v_lookup_foldl_upd)
  by auto

lemma v_from_list_invar[simp]: \<open>Sparse_Vec.invar (Sparse_Vec.from_list2 xs)\<close>
  unfolding Sparse_Vec.from_list2_def
  using v_foldl_invar by auto

lemma m_lookup_from_list[simp]: \<open>m_lookup (Sparse_Mat.from_list2 xs) = Map.map_of (rev xs)\<close>
  unfolding Sparse_Mat.from_list2_def
  apply (rule ext)
  apply (subst m_lookup_foldl_upd)
  by auto

lemma m_from_list_invar[simp]: \<open>Sparse_Mat.invar (Sparse_Mat.from_list2 xs)\<close>
  unfolding Sparse_Mat.from_list2_def
  using m_foldl_invar by auto

lemma scalar_prod_map_empty[simp]: \<open>scalar_prod_map Map.empty x = 0\<close> \<open>scalar_prod_map x Map.empty = 0\<close>
  unfolding scalar_prod_map_def by auto

lemma feasible_map_from_list: 
  \<open>feasible_map (Sparse_Mat.from_list2 (List.enumerate 0 (map (\<lambda>x. Sparse_Vec.from_list2 (fst x)) xs))) (Sparse_Vec.from_list2 (List.enumerate 0 (map snd xs))) x
  \<longleftrightarrow> (\<forall>(v, b) \<in> set xs. scalar_prod_map (v_lookup (Sparse_Vec.from_list2 v)) x \<le> b)\<close>
  unfolding feasible_map_def v_lookup'_def m_lookup'_def
  apply (auto split: option.splits simp: List.in_set_enumerate_eq distinct_map_of_rev map_of_eq_None_iff image_iff)
   apply (metis fst_eqD in_set_conv_nth snd_eqD)
  by (metis (no_types, opaque_lifting) add.right_neutral in_set_enumerate_eq length_map prod.sel(1) snd_eqD zero_order(1))

lemma proj_unzip: 
  \<open>fst (unzip xs) = map fst xs\<close> \<open>snd (unzip xs) = map snd xs\<close>
  by (induction xs) (auto simp: case_prod_unfold)

lemma feasible_map_iff:
  assumes \<open>from_file' True n c cs = (n, c_map, A_map, b_map)\<close>
  shows \<open>feasible_map A_map b_map x \<longleftrightarrow> 
  (\<forall>constr\<in>set cs. \<forall>constr' \<in> set (constraint_to_le constr). scalar_prod_map (Map.map_of (rev (fst constr'))) x \<le> snd constr')\<close> (*sat_lp_list cs x\<close>*)
  using assms
  unfolding from_file'_def
  apply (auto simp: case_prod_unfold  constraints_to_map_def)
  unfolding proj_unzip
  by (fastforce simp: feasible_map_from_list comp_def case_prod_unfold constraints_to_le_def)+

lemma distinct_mapD: \<open>distinct (map f xs) \<Longrightarrow> distinct xs\<close>
  apply (induction xs) by auto

lemma sum_list_lookup[simp]: 
  \<open>distinct (map fst p) \<Longrightarrow> (\<Sum>p\<leftarrow>p. (snd p :: real) * lookup' x (fst p)) = (\<Sum>i \<in> fst ` set p. lookup' (Map.map_of p) i * lookup' x i)\<close>
  apply (induction p)
  by (auto simp: lookup'_def split: option.splits intro!: sum.cong dest: in_fstD)

lemma lookup_mult_sum[simp]: 
  \<open>(\<Sum>i\<in>fst ` set p. lookup' (Map.map_of p) i * lookup' x i :: real) = (\<Sum>i\<in>fst ` set p \<inter> dom x. lookup' (Map.map_of p) i * lookup' x i)\<close>
  apply (rule sum.mono_neutral_right)
  by (auto simp: lookup'_def map_of_eq_None_iff map_of_eq_Some_iff split: option.splits)

lemma lookup_mult_sum'[simp]: \<open>(\<Sum>i\<in>fst ` set p. (lookup' x i :: real) * lookup' (Map.map_of p) i) = (\<Sum>i\<in>fst ` set p \<inter> dom x.  lookup' x i * lookup' (Map.map_of p) i)\<close>
  apply (rule sum.mono_neutral_right)
  by (auto simp: lookup'_def map_of_eq_None_iff map_of_eq_Some_iff split: option.splits)

lemma real_neg_leD: \<open>a \<le> (-b :: real) \<Longrightarrow> -a \<ge> b\<close>
  by auto

lemma lookup'_map_neg[simp]: \<open>lookup' (Map.map_of (map (\<lambda>p. (fst p, - snd p)) p)) i = (- lookup' (Map.map_of p) i :: real)\<close>
    by (auto dest!:  simp: lookup'_def  map_of_map[unfolded case_prod_unfold] split: option.splits)

lemma sat_constr_iff: \<open>distinct (map fst p) \<Longrightarrow> 
  (\<forall>constr' \<in> set (constraint_to_le (p, s, r)). scalar_prod_map (Map.map_of (rev (fst constr'))) x \<le> snd constr') \<longleftrightarrow> sat_constr (p, s, r) x\<close>
  apply (cases \<open>s\<close>)
  using distinct_mapD[of fst p] 
  by (auto intro: real_neg_leD dest!: real_neg_leD[of _ \<open>r\<close>] 
simp: Groups_Big.sum_negf[symmetric] comp_def case_prod_unfold  distinct_map_of_rev sat_constr_def scalar_prod_list_def scalar_prod_map_def neg_constraint_expr_def image_image algebra_simps)
  
lemma feasible_map_iff_sat_lp_list:
  assumes \<open>from_file' True n c cs = (n, c_map, A_map, b_map)\<close>  \<open>\<forall>(p, _, r) \<in> set cs. distinct (map fst p)\<close>
  shows \<open>feasible_map A_map b_map x \<longleftrightarrow> sat_lp_list cs x\<close>
  apply (subst feasible_map_iff[OF assms(1)])
  unfolding sat_lp_list_def
  using assms
  apply (auto simp: sat_constr_iff[symmetric] case_prod_unfold)
  by (metis fst_conv sat_constr_iff snd_conv)


lemma from_file'_invar: 
  assumes \<open>from_file' m n c cs = (n, c_map, A_map, b_map)\<close> 
  shows \<open>Sparse_Vec.invar c_map\<close> \<open>Sparse_Vec.invar b_map\<close> \<open>Sparse_Mat.invar A_map\<close>
  using assms
  unfolding from_file'_def
  by (auto simp: case_prod_unfold)

lemma constr_to_map_fst_inv: \<open>v \<in> set (fst (constraints_to_map cs)) \<Longrightarrow> Sparse_Vec.invar v\<close>
  unfolding constraints_to_map_def
  by (auto simp: case_prod_unfold)

lemma from_file'_mat_code_inv:
  assumes \<open>from_file' True n c cs = (n, c_map, A_map, b_map)\<close>
  shows \<open>mat_code_invar A_map\<close>
  using assms from_file'_invar distinct_enumerate constr_to_map_fst_inv
  unfolding mat_code_invar_def
  apply auto
   apply fastforce
  unfolding from_file'_def
  apply (auto simp: in_set_enumerate_eq distinct_map_of_rev case_prod_unfold map_of_eq_Some_iff)
  using nth_mem 
  by blast

lemma solve_sound:
  assumes 
    \<open>from_file' True n c cs = (n, c_map, A_map, b_map)\<close> 
    \<open>\<forall>(p, _, r) \<in> set cs. distinct (map fst p)\<close>  
    \<open>distinct (map fst c)\<close>
    \<open>solve oracle A_map b_map c_map  n  = Some (Cert_Opt x y)\<close> \<open>Sparse_Vec.invar x\<close>
  shows 
    \<open>sat_lp_list cs (v_lookup x)\<close> \<open>\<And>x'. sat_lp_list cs x' \<Longrightarrow> scalar_prod_list c (v_lookup x) \<le>  scalar_prod_list c x'\<close>
  using assms feasible_map_iff_sat_lp_list[OF assms(1) assms(2)] from_file'_invar from_file'_mat_code_inv 
   apply auto
   apply (auto intro!: feasible_primal_correct simp: case_prod_unfold feasible_map_iff_sat_lp_list[symmetric] solve_def check_cert_def split: option.splits if_splits)
     apply fastforce
    apply fastforce
  using check_feas_def check_opt''_def check_opt'_def apply force
  subgoal for x'
  using check_opt''_opt[of x y A_map b_map c_map x']
  unfolding from_file'_def
  apply (auto simp: Int_commute case_prod_unfold distinct_map_of_rev scalar_prod_map_def scalar_prod_list_def algebra_simps)
  by (meson check_opt''_def)
  done

end
end