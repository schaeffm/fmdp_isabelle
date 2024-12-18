theory Certify_Standard_Form
  imports 
    "HOL.String"
    LP_Duality.LP_Duality 
    Farkas.Matrix_Farkas 
    Linear_Programming.Linear_Programming
begin                 

locale LP =
  fixes 
    A :: \<open>real mat\<close> and 
    b c :: \<open>real vec\<close>
  assumes 
    b_vec [simp]: \<open>b \<in> carrier_vec (dim_row A)\<close> and 
    c_vec [simp]: \<open>c \<in> carrier_vec (dim_col A)\<close>
begin

abbreviation \<open>nvars \<equiv> dim_col A\<close>

text \<open>We first define the semantics of an LP in Standard Form:
max @{term \<open>c \<bullet> x\<close>}, s.t. @{term \<open>A *\<^sub>v x \<le> b\<close>}.
\<close>

datatype LP_Sol = Infeasible | Unbounded | Solution real

definition "feasible_reg =
  {x | x. x \<in> carrier_vec nvars \<and> A *\<^sub>v x \<le> b}"

definition "obj_space = (\<lambda>x. c \<bullet> x) ` feasible_reg"

definition "obj_max = Maximum obj_space"
definition "obj_min = Minimum obj_space"

definition "is_opt x \<longleftrightarrow> x \<in> feasible_reg \<and> (\<forall>y \<in> feasible_reg. c \<bullet> x \<le> c \<bullet> y)"

definition "sol_space = {x \<in> feasible_reg. is_opt x}"

definition "feasible \<longleftrightarrow> feasible_reg \<noteq> {}"

lemma feasible_ex: "feasible \<longleftrightarrow> (\<exists>x \<in> carrier_vec nvars. A *\<^sub>v x \<le> b)"
  unfolding feasible_def feasible_reg_def less_eq_vec_def
  by auto

definition "infeasible \<longleftrightarrow> feasible_reg = {}"

definition "unbounded \<longleftrightarrow> \<not> bdd_below obj_space"

definition "has_sol \<longleftrightarrow> feasible \<and> has_Minimum obj_space"

lemma obj_min_in_obj_space: "has_sol \<Longrightarrow> obj_min \<in> obj_space"
  using has_MinimumD(1)[of obj_space]
  unfolding has_sol_def obj_min_def
  by auto

definition "semantics = 
  (if infeasible then Infeasible else if has_sol then Solution obj_min else Unbounded)"

lemma infeasible_feasible[simp]: "infeasible \<longleftrightarrow> \<not>feasible"
  by (auto simp: infeasible_def feasible_def)

lemma "(\<exists>x. semantics = Solution x) \<longleftrightarrow> has_sol"
  by (auto simp: semantics_def unbounded_def feasible_reg_def has_sol_def)

lemma "semantics = Solution x \<Longrightarrow> x = obj_min"
  by (auto dest: obj_min_in_obj_space split: if_splits simp: semantics_def)

section \<open>Certification\<close>
text \<open>We define certificates for unboundedness, infeasibility and optimality:
- Optimality: via LP duality
- Infeasiblity: via Farkas coefficients
- Unboundedness: feasible vector + unbounded direction
\<close>

datatype Certificate = 
  Cert_Infeasible "real vec" | 
  Cert_Solution (primal_sol: "real vec") (dual_sol: "real vec") |
  Cert_Unbounded "real vec" "real vec"

definition "check_infeasible p \<longleftrightarrow>
  p \<ge> 0\<^sub>v (dim_row A) \<and> 
  mat_of_row p * A = 0\<^sub>m 1 nvars \<and> 
  p \<bullet> b < 0"

lemma check_infeasible_sound:
  assumes "check_infeasible p"
  shows "infeasible"
  oops
(*
proof -
  have"\<not> A *\<^sub>v x \<le> b" if "x \<in> carrier_vec nvars" for x
  using Matrix_Farkas.farkas_lemma_matrix[of A "dim_row A" "dim_col A" b] that assms
  unfolding check_infeasible_def
  by auto
  thus ?thesis
    by (auto simp: feasible_ex less_eq_vec_def)
qed
*)

definition "check_unbounded x d \<longleftrightarrow>
  x \<in> carrier_vec nvars \<and> 
  d \<in> carrier_vec nvars \<and>
  A *\<^sub>v x \<le> b \<and>
  A *\<^sub>v d \<le> 0\<^sub>v (dim_row A) \<and>
  c \<bullet> d < 0"

lemma smult_zero[simp]: "(d :: _ :: trivial_conjugatable_linordered_field) \<cdot>\<^sub>v (0\<^sub>v n) = 0\<^sub>v n"
  by auto

lemma vec_add_right_le:
  fixes x :: "_ :: trivial_conjugatable_linordered_field vec"
  assumes "x \<in> carrier_vec n" "y \<in> carrier_vec n" "z \<in> carrier_vec n" 
  assumes "x \<le> z" "y \<le> 0\<^sub>v n" 
  shows "x + y \<le> z"
  using assms vec_add_mono[of _ "0\<^sub>v n"] by force

lemma check_unbounded_sound:
  assumes "check_unbounded x d"
  shows "unbounded"
proof -
  have "\<exists>l. \<forall>r \<le> l. \<exists>x \<in> carrier_vec nvars.  A *\<^sub>v x \<le> b \<and> c \<bullet> x = r"
  proof -
    have xd_feasible: "A *\<^sub>v (x + e \<cdot>\<^sub>v d) \<le> b" if "e \<ge> 0" for e
    using that assms unfolding check_unbounded_def
    by (auto intro!: vec_add_right_le mult_mat_vec_carrier smult_nneg_npos_vec
        simp: mult_add_distrib_mat_vec[of A "dim_row A" "dim_col A"] 
              mult_mat_vec[of A "dim_row A" "dim_col A"])
   have "\<exists>y \<in> carrier_vec nvars. A *\<^sub>v y \<le> b \<and> c \<bullet> y = r" if "r \<le> c \<bullet> x" for r
    using that xd_feasible b_vec c_vec assms
    unfolding check_unbounded_def
    apply (intro bexI[of _ "x + (r - c \<bullet> x)/(c \<bullet> d)  \<cdot>\<^sub>v d"])
    by  (auto simp: divide_nonpos_neg scalar_prod_add_distrib[of _ "dim_col A"])
  thus ?thesis
    by auto
qed
  then obtain l where **: "\<exists>x \<in> carrier_vec nvars. A *\<^sub>v x \<le> b \<and> c \<bullet> x = r" if "r \<le> l" for r
    by auto
  hence "r \<le> l \<Longrightarrow> r \<in> obj_space" for r
    by (auto simp: obj_space_def feasible_reg_def image_iff)
  thus ?thesis
    unfolding unbounded_def
    by (auto elim!: bdd_below.E) (metis dual_order.trans less_le_not_le lt_ex)
qed

lemma (in -) has_Min_imp_has_Max:
  assumes \<open>has_Minimum (X :: 'a :: trivial_conjugatable_linordered_field set)\<close>
  shows \<open>has_Maximum ((\<lambda>x. - x) ` X)\<close>
  using assms
  unfolding has_Minimum_def has_Maximum_def
  by auto

lemma (in -) has_Max_imp_has_Min:
  assumes \<open>has_Maximum (X :: 'a :: trivial_conjugatable_linordered_field set)\<close>
  shows \<open>has_Minimum ((\<lambda>x. - x) ` X)\<close>
  using assms
  unfolding has_Minimum_def has_Maximum_def
  by auto

lemma (in -) image_compr: \<open>f ` {g x | x. P x} = {f (g x) |x. P x}\<close>
  by auto

lemma (in -) Maximum_neg: \<open>has_Minimum {- f x :: 'a :: trivial_conjugatable_linordered_field |x. P x} \<Longrightarrow> 
  Maximum {f x|x. P x} = - Minimum {- f x|x. P x}\<close>
  by (rule eqMaximumI) (fastforce dest: has_MinimumD)+


lemma (in -) Minimum_neg: \<open>has_Minimum {f x :: 'a :: trivial_conjugatable_linordered_field |x. P x} \<Longrightarrow> 
  Minimum {f x|x. P x} = - Maximum {- f x|x. P x}\<close>
  using Maximum_neg[of \<open>-f\<close>]
  by (fastforce dest: has_MinimumD)+

lemma (in -) le_vec_neg_iff: 
  \<open>a \<in> carrier_vec n \<Longrightarrow> (b :: 'a :: trivial_conjugatable_linordered_field vec) \<in> carrier_vec n \<Longrightarrow> a \<le> -b \<longleftrightarrow> b \<le> -a\<close>
  unfolding less_eq_vec_def
  by auto

lemma (in -) neg_le_0_vec_iff[simp]:
  fixes v :: "'b :: trivial_conjugatable_linordered_field vec" 
  shows \<open>-v \<le> 0\<^sub>v n \<longleftrightarrow> 0\<^sub>v n \<le> v\<close>
  by (auto simp: less_eq_vec_def algebra_simps)

lemma (in -) zero_le_neg_vec_iff[simp]:
  fixes v :: "'b :: trivial_conjugatable_linordered_field vec" 
  shows \<open>0\<^sub>v n \<le> -v \<longleftrightarrow> v \<le> 0\<^sub>v n\<close>
  by (auto simp: less_eq_vec_def algebra_simps)

lemma (in -) dim_vec_le_eq: \<open>v \<le> u \<Longrightarrow> dim_vec v = dim_vec u\<close>
    by (auto simp: less_eq_vec_def algebra_simps)

lemma (in -) neg_mat_eq_iff: \<open>-(A :: 'a :: trivial_conjugatable_linordered_field mat) = B \<longleftrightarrow> A = - B\<close>
  by auto

lemma (in -) neg_vec_eq_iff: \<open>-(A :: 'a :: trivial_conjugatable_linordered_field vec) = B \<longleftrightarrow> A = - B\<close>
  by auto

corollary (in -) strong_duality_theorem_min_max':
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and primal: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
    and dual: "\<exists> y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c"
  shows "Minimum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}
       = Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
    and "has_Minimum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
    and "has_Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
proof -
  have dual': \<open>\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = -c\<close>
  proof -
    obtain y where \<open>y \<le> 0\<^sub>v nr \<and>  A\<^sup>T *\<^sub>v y = c\<close> 
      using assms
      by auto
    moreover then have \<open>y \<in> carrier_vec nr\<close>
      unfolding less_eq_vec_def
      by auto

    ultimately have \<open>-y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v -y = -c\<close>
      using le_vec_neg_iff[of _ nr, OF zero_carrier_vec] A b c
      by (auto simp: transpose_carrier_mat)
    thus ?thesis ..
  qed

  have neg_c: \<open>-c \<in> carrier_vec nc\<close>
    using assms by auto

  have "has_Maximum {-c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
    using  strong_duality_theorem_min_max[OF assms(1) assms(2) _ _ dual'] assms
    by auto
  moreover have \<open>{- (- c \<bullet> x) |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b} = {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}\<close>
    using c
    by force    
  ultimately show has_min: "has_Minimum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}"
    using c
    by (auto dest!: has_Max_imp_has_Min simp: image_compr)

  have \<open>has_Minimum {b \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = - c}\<close>
    using strong_duality_theorem_min_max[OF assms(1) assms(2) _ _ dual'] assms
    by auto

  hence \<open>has_Maximum {- (b \<bullet> y) |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = - c}\<close>
    by (auto dest!: has_Min_imp_has_Max simp: image_compr)

  have neg_vec: \<open>- vec n f = vec n (-f)\<close> for n f
    by auto

  have vec_cong: \<open>n = m \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> f i = g i) \<Longrightarrow> vec n f = vec m g\<close> for n m f g
    by auto

  have mat_vec_mult_neg: \<open>dim_col A = dim_vec v \<Longrightarrow> A *\<^sub>v (- v :: 'b :: ring vec) = - (A *\<^sub>v v)\<close> for A v
    by auto

  have cond_iff: \<open>0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = - c \<longleftrightarrow> -y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v -y = c\<close> for y
    using assms
    by (auto simp: neg_vec_eq_iff  mat_vec_mult_neg dim_vec_le_eq[symmetric] algebra_simps)

  moreover then have sets_eq: \<open>{- (b \<bullet> y) |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = - c} = {b \<bullet> y | y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}\<close>
    unfolding cond_iff
    apply safe
    subgoal for _ y
      using assms
      by (intro exI[of _ \<open>-y\<close>]) (auto simp: dim_vec_le_eq[symmetric])
    subgoal for _ y
      using assms
      by (intro exI[of _ \<open>-y\<close>]) (auto simp add: dim_vec_le_eq)
    done

  thus "has_Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
    using  strong_duality_theorem_min_max[OF assms(1) assms(2) _ _ dual'] assms
    by (auto dest!: has_Min_imp_has_Max simp: image_compr)

  have 1: \<open>Minimum {c \<bullet> x |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b} = - Maximum {- (c \<bullet> x) |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}\<close>
    using assms has_min
    by (subst Minimum_neg) auto
  also have 2: \<open>\<dots> = - Maximum {(- c \<bullet> x) |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}\<close>
    using assms uminus_scalar_prod
    by (auto intro!: arg_cong[where f = \<open>Maximum\<close>])
  also have 3: \<open>\<dots> = -  Minimum {b \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = - c}\<close>
    using strong_duality_theorem_min_max[OF assms(1) assms(2), of \<open>-c\<close>] assms dual'
    by auto
  also have 4: \<open>\<dots> = Maximum {b \<bullet> y |y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}\<close>
    using sets_eq \<open>has_Minimum {b \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = - c}\<close>
    by (subst Minimum_neg) auto

 show \<open>Minimum {c \<bullet> x |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b} = Maximum {b \<bullet> y |y. y \<le> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}\<close> 
   using 1 2 3 4 by auto
qed

corollary strong_duality_theorem_check:
  assumes primal: "x_opt \<in> carrier_vec nvars" "A *\<^sub>v x_opt \<le> b"
    and dual: "y_opt \<le> 0\<^sub>v (dim_row A)" "A\<^sup>T *\<^sub>v y_opt = c"
  shows
    "c \<bullet> x_opt = b \<bullet> y_opt \<longleftrightarrow> (Minimum {c \<bullet> x | x. x \<in> carrier_vec nvars \<and> A *\<^sub>v x \<le> b} = c \<bullet> x_opt 
    \<and> Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v (dim_row A) \<and> A\<^sup>T *\<^sub>v y = c} = b \<bullet> y_opt)"
proof -
  have y: \<open>dim_vec y_opt = dim_row A\<close>
    using assms unfolding less_eq_vec_def by force

  have neg_y_nonneg: \<open>0\<^sub>v (dim_row A) \<le> - y_opt\<close>
    using assms unfolding less_eq_vec_def by force

  have A_y: \<open>A\<^sup>T *\<^sub>v - y_opt = - (A\<^sup>T *\<^sub>v y_opt)\<close>
    using assms y
    by auto
    
  have "Minimum {c \<bullet> x | x. x \<in> carrier_vec nvars \<and> A *\<^sub>v x \<le> b} \<le> c \<bullet> x_opt"
    using assms c_vec
    by (fastforce intro!:has_MinimumD(2)[OF strong_duality_theorem_min_max'(2)])
  moreover have "b \<bullet> y_opt \<le> Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v (dim_row A) \<and> A\<^sup>T *\<^sub>v y = c}"
    using assms  c_vec
    by (fastforce intro!: has_MaximumD[OF strong_duality_theorem_min_max'(3)])
  moreover have "c \<bullet> x_opt \<ge> b \<bullet> y_opt"
    using weak_duality_theorem[where c = \<open>-c\<close> and y = \<open>-y_opt\<close>, of A  \<open>dim_row A\<close> \<open>dim_col A\<close>, of b x_opt]
    using assms b_vec neg_y_nonneg A_y y
    by auto
  moreover have "Minimum {c \<bullet> x | x. x \<in> carrier_vec nvars \<and> A *\<^sub>v x \<le> b} = Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v (dim_row A) \<and> A\<^sup>T *\<^sub>v y = c}"
    using assms c_vec
    by (fastforce intro!:  strong_duality_theorem_min_max')
  ultimately show ?thesis
    using assms by linarith
qed

corollary strong_duality_theorem_check':
  assumes primal: "x_opt \<in> carrier_vec nvars" "A *\<^sub>v x_opt \<le> b" 
    and dual: "y_opt \<le> 0\<^sub>v (dim_row A)" "A\<^sup>T *\<^sub>v y_opt = c"
    and "c \<bullet> x_opt = b \<bullet> y_opt"
  shows
    "Minimum {c \<bullet> x | x. x \<in> carrier_vec nvars \<and> A *\<^sub>v x \<le> b} = c \<bullet> x_opt"
    "Maximum {b \<bullet> y | y. y \<le> 0\<^sub>v (dim_row A) \<and> A\<^sup>T *\<^sub>v y = c} = b \<bullet> y_opt"
  using assms strong_duality_theorem_check
  by blast+

corollary strong_duality_theorem_check'':
  assumes primal: "x_opt \<in> carrier_vec nvars" "A *\<^sub>v x_opt \<le> b" 
    and dual: "y_opt \<le> 0\<^sub>v (dim_row A)" "A\<^sup>T *\<^sub>v y_opt = c"
    and "c \<bullet> x_opt = b \<bullet> y_opt"
  assumes \<open>A *\<^sub>v x \<le> b\<close> \<open>x \<in> carrier_vec nvars\<close>
  shows "c \<bullet> x \<ge> c \<bullet> x_opt"
proof -
  have *: "c \<bullet> x_opt = Minimum {c \<bullet> x | x. x \<in> carrier_vec nvars \<and> A *\<^sub>v x \<le> b}"
    using assms strong_duality_theorem_check
    by auto
  show ?thesis
    unfolding *
    using assms strong_duality_theorem_min_max' b_vec c_vec
    by (intro has_MinimumD(2) strong_duality_theorem_min_max'(2)) blast+
qed

definition check_solution where
  "check_solution p d \<longleftrightarrow> (p \<in> carrier_vec nvars) \<and> (A *\<^sub>v p \<le> b) \<and> (d \<le> 0\<^sub>v (dim_row A)) \<and> (A\<^sup>T *\<^sub>v d = c) \<and> (c \<bullet> p = b \<bullet> d)"

lemma check_solution_sound:
  assumes "check_solution p d"
  shows "(c \<bullet> p) = obj_min"
  using assms 
  unfolding check_solution_def obj_min_def obj_space_def feasible_reg_def
  using strong_duality_theorem_check'(1)[of p d]
  by (auto simp: image_Collect)

definition "check_certificate cert = (
  case cert of
    Cert_Infeasible v   \<Rightarrow> (if check_infeasible v  then Some Infeasible else None) |
    Cert_Solution p d   \<Rightarrow> (if check_solution p d  then Some (Solution (c \<bullet> p)) else None) |
    Cert_Unbounded x d  \<Rightarrow> (if check_unbounded x d then Some Unbounded else None))"

type_synonym oracle_ty = "real mat \<Rightarrow> real vec \<Rightarrow> real vec \<Rightarrow> Certificate option"

definition solve_cert :: "oracle_ty \<Rightarrow> LP_Sol option" where
  "solve_cert f = f A b c \<bind> check_certificate"

lemma solve_cert_sound:
  (* "solve_cert f = Some Infeasible \<Longrightarrow> infeasible" *)
  "solve_cert f = Some Unbounded \<Longrightarrow> unbounded"
  "solve_cert f = Some (Solution x) \<Longrightarrow> x = obj_min"
  (* using check_infeasible_sound  *)
    using check_unbounded_sound check_solution_sound
    by (cases "f A b c"; auto split: Certificate.splits if_splits 
        simp: solve_cert_def check_certificate_def)+
end
end