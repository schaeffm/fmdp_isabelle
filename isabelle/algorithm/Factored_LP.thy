theory Factored_LP
  imports 
    "HOL-Analysis.Analysis" 
    Util 
    Constr
begin

section \<open>Linear Programs\<close>
datatype 'a constr = Eq "'a \<Rightarrow> real" real | Le "'a \<Rightarrow> real" real

definition \<open>vars_poly p = {i. p i \<noteq> 0}\<close>
definition "vars_constr constr = (case constr of Le p b \<Rightarrow> vars_poly p | Eq p b \<Rightarrow> vars_poly p)"
definition "vars_lp lp = (\<Union>c \<in> lp. vars_constr c)"

definition \<open>eval_poly p x = (\<Sum>i \<in> vars_poly p. p i * x i)\<close>

definition "sat_constr x constr = (
  case constr of
    Eq p rhs \<Rightarrow> (\<Sum>i \<in> vars_constr constr. p i * x i) = rhs
  | Le p rhs \<Rightarrow> (\<Sum>i \<in> vars_constr constr. p i * x i) \<le> rhs
)"

lemma sat_constr_Eq: "sat_constr x (Eq p rhs) \<longleftrightarrow> eval_poly p x = rhs"
  unfolding sat_constr_def vars_constr_def eval_poly_def
  by simp

lemma sat_constr_Le: "sat_constr x (Le p rhs) \<longleftrightarrow> eval_poly p x \<le> rhs"
  unfolding sat_constr_def vars_constr_def eval_poly_def
  by simp

definition "sat_lp x lp \<longleftrightarrow> (\<forall>c \<in> lp. sat_constr x c)"

lemma sat_lpD[dest]: "sat_lp x lp \<Longrightarrow> c \<in> lp \<Longrightarrow> sat_constr x c"
  unfolding sat_lp_def by simp

lemma sat_lpI[intro]: "(\<And>c. c \<in> lp \<Longrightarrow> sat_constr x c) \<Longrightarrow> sat_lp x lp"
  unfolding sat_lp_def by simp

lemma satisfying_un[simp]: "sat_lp x (xs \<union> ys) \<longleftrightarrow> sat_lp x xs \<and> sat_lp x ys"
  unfolding sat_lp_def
  by auto

lemma sat_constr_indep[intro]:
  assumes \<open>\<And>v. v \<in> vars_constr constr \<Longrightarrow> x v = y v\<close>
  shows "sat_constr x constr = sat_constr y constr"
  unfolding sat_constr_def
  using assms
  by (auto split: constr.splits)

lemma sat_lp_indep[intro]:
  assumes \<open>\<And>v. v \<in> vars_lp lp \<Longrightarrow> x v = y v\<close>
  shows "sat_lp x lp = sat_lp y lp"
  using assms sat_constr_indep[of _ x y]
  unfolding sat_lp_def vars_lp_def
  by fastforce

definition \<open>opt_lp x c cs \<longleftrightarrow> sat_lp x cs \<and> (\<forall>x'. (sat_lp x' cs \<longrightarrow> eval_poly c x \<le> eval_poly c x'))\<close>

lemma opt_lpI[intro]:
  assumes \<open>sat_lp x cs\<close>
    and \<open>\<And>x'. sat_lp x' cs \<Longrightarrow> eval_poly c x \<le> eval_poly c x'\<close>
  shows \<open>opt_lp x c cs\<close>
  unfolding opt_lp_def
  using assms
  by auto

section \<open>Factored LP\<close>

subsection \<open>Factored LP Variables\<close>
datatype f_name = 
  f_c nat | 
  f_b nat | 
  f_e nat

datatype ('pre ,'a) var_name =
  var_f 'pre "f_name" "nat \<rightharpoonup> 'a" | 
  var_w nat |
  var_phi

locale factored_lp_consts = fixes
  C :: "(((nat \<rightharpoonup> 'a) \<Rightarrow> real) \<times> nat set) list" and
  B :: "(((nat \<rightharpoonup> 'a) \<Rightarrow> ereal) \<times> nat set) list" and

doms :: "nat \<Rightarrow> 'a set" and
\<comment> \<open>Each dimension has a domain\<close>

dims :: nat
\<comment>\<open>for each @{term "i < num_c"}, @{term "c i v"} assigns to each vector @{term "(v :: nat \<Rightarrow> 'a) \<in> Dom num_c"} a real value\<close> and

prefix :: \<open>'x\<close> and
\<comment> \<open>prefixes are added to private LP variables to make them distinct between branches\<close>

order :: "nat \<Rightarrow> nat"
begin

text \<open>(Partial) Vectors.\<close>
definition \<open>partial_vecs = {x. \<forall>(i, j) \<in> Map.graph x. i \<in> {..<dims} \<and> j \<in> doms i}\<close>
definition \<open>vecs_on D = {x. dom x = D} \<inter> partial_vecs\<close>
definition \<open>full_vecs = vecs_on {..<dims}\<close>

text \<open>Consistency between vectors.\<close>
definition \<open>consistent x x' = (x |` dom x' = x')\<close>

abbreviation \<open>scope \<equiv> snd\<close>
abbreviation \<open>fn \<equiv> fst\<close>

definition \<open>num_c = length C\<close>
definition \<open>num_b = length B\<close>

definition scope_c :: \<open>nat \<Rightarrow> nat set\<close>
  where \<open>scope_c i = snd (C ! i)\<close>

definition scope_b :: \<open>nat \<Rightarrow> nat set\<close>
  where \<open>scope_b i = snd (B ! i)\<close>

definition \<open>c i = fst (C ! i)\<close>

definition \<open>b i = fst (B ! i)\<close>

abbreviation \<open>c_r i x \<equiv> c i (x |` ((scope_c i)))\<close>
abbreviation \<open>b_r i x \<equiv> b i (x |` ((scope_b i)))\<close>

text \<open>Evaluation of C and B on weights and a vector.\<close>
definition \<open>eval_c w (x :: nat \<rightharpoonup> 'a) = (\<Sum>i < num_c. w i * c_r i x)\<close>
definition \<open>eval_b x = (\<Sum>j < num_b. b_r j x)\<close>
definition \<open>eval_cb w x = eval_c w x + eval_b x\<close>
definition \<open>eval_max w = (MAX x. eval_cb w x)\<close>

definition \<open>is_ub_max w \<phi> \<longleftrightarrow> (\<phi> \<ge> eval_max w)\<close>

abbreviation \<open>var_f' \<equiv> var_f prefix\<close>

abbreviation "restr_f f x scopes \<equiv> var_f' f (x |` (scopes f))"

text \<open>Enumerate all functions in c + all states with matching scopes.\<close>
definition \<open>vars_c = {var_f' (f_c i) z | z i. z \<in> vecs_on (scope_c i) \<and> i < num_c}\<close>

text \<open>Ensures @{term \<open>f(c,i,z) = w_i * c_i(z)\<close>}\<close>
definition \<open>constr_c z i = Eq (\<lambda>v.
    if v = var_f' (f_c i) z then -1
    else if v = var_w i then c_r i z
    else 0) 0\<close>

definition "constrs_c = 
  {constr_c z i | z i. z \<in> vecs_on (scope_c i) \<and> i < num_c}"

definition "vars_b = { var_f' (f_b j) z | z j. 
  z \<in> vecs_on (scope_b j) \<and> j < num_b}"

text \<open>Ensures @{term \<open>f(b,j,z) = b_j(z)\<close>}\<close>
definition "constr_b z j =
  Eq (\<lambda>v. if v = var_f' (f_b j) z then 1 else 0) (real_of_ereal (b_r j z))"

definition "constrs_b = 
  {constr_b z j | z j. z \<in> vecs_on (scope_b j) \<and> j < num_b \<and> b_r j z \<noteq> -\<infinity>}"

definition "vars_w = {var_w i| i. i < num_c}"

text \<open>Initial set of function to maximize constructed from B and C.\<close>
definition "\<F>_init = {(f_c i) | i. i < num_c} \<union> {(f_b i) | i. i < num_b}"

definition "scopes_init f = (case f of f_b i \<Rightarrow> scope_b i | f_c i \<Rightarrow> scope_c i | _ \<Rightarrow> {})"

definition "constrs_init = constrs_c \<union> constrs_b"

definition "vars_init = vars_c \<union> vars_b \<union> vars_w"

text \<open>Inefficient but simpler constraint set, used to prove correctness.\<close>
definition "constr_\<F> \<F> scopes x = 
  Le (\<lambda>v. 
      case v of 
        var_f p f z \<Rightarrow> if p = prefix \<and> f \<in> \<F> \<and> z = x |` (scopes f) then 1 else 0
      | var_phi \<Rightarrow> -1
      | _ \<Rightarrow> 0) 0"

definition "constrs_\<F> \<F> scopes = constr_\<F> \<F> scopes ` full_vecs"

definition "expl_constr x = Le (\<lambda>v. 
      case v of
        var_w i \<Rightarrow> if i < num_c then c_r i x else 0
      | var_phi \<Rightarrow> - 1
      | _ \<Rightarrow> 0) (-real_of_ereal (eval_b x))"

definition "explicit_lp = expl_constr ` {v. v \<in> full_vecs \<and> eval_b v \<noteq> -\<infinity>}"
  \<comment> \<open>@{verbatim \<open>var_phi \<ge> (\<Sum>i < num_vars. var_w i * c i x)\<close>}\<close>

subsection \<open>Definitions to Handle Negative Infinity\<close>
definition \<open>Max0 X = (if X = {} then 0 else Max X)\<close>

definition \<open>max_w (sol :: _ \<Rightarrow> real) = (if num_c = 0 then 0 else (MAX i \<in> {..<num_c}. \<bar>sol (var_w i)\<bar>))\<close>

definition \<open>max_phi (sol :: _ \<Rightarrow> real) = \<bar>sol var_phi\<bar>\<close>

definition \<open>max_e (sol :: _ \<Rightarrow> real) = (if dims = 0 then 0 else (MAX i \<in> {..<dims}.
    MAX x \<in> partial_vecs. \<bar>sol (var_f prefix (f_e i) x)\<bar>))\<close>

definition \<open>max_c (sol :: _ \<Rightarrow> real) = (if num_c = 0 then 0 else (MAX i \<in> {..<num_c}. 
    MAX x \<in> partial_vecs. \<bar>sol (var_f prefix (f_c i) x)\<bar>))\<close>

definition \<open>max_b (sol :: _ \<Rightarrow> real) = (if num_b = 0 then 0 else (MAX i \<in> {..<num_b}. 
    MAX x \<in> partial_vecs. \<bar>sol (var_f prefix (f_b i) x)\<bar>))\<close>

definition \<open>max_var (sol :: _ \<Rightarrow> real) = Max ((\<lambda>f. f sol) ` {max_phi, max_w, max_c, max_b, max_e})\<close>
definition \<open>dom_max_card = (MAX i \<in> {..<dims}. card (doms i))\<close>

definition unbdd_vars_init where \<open>unbdd_vars_init = {
    var_f prefix (f_b i) z | z i. z \<in> vecs_on (scope_b i) \<and> i < num_b \<and> b_r i z = -\<infinity>}\<close>

definition mk_unbdd_small where 
  "mk_unbdd_small \<F> unbdd sol = 
    (\<lambda>v :: ('x, 'a) var_name. if v \<in> unbdd then -card \<F> * max_var sol else sol v)"

subsection \<open>Valid Variables\<close>
definition \<open>valid_var v \<longleftrightarrow> (
  case v of
    var_phi \<Rightarrow> True | 
    var_w i \<Rightarrow> i < num_c | 
    var_f p f z \<Rightarrow> 
      p = prefix \<and> z \<in> partial_vecs \<and> (case f of f_b i \<Rightarrow> i < num_b | f_c i \<Rightarrow> i < num_c | f_e i \<Rightarrow> i < dims))\<close>

definition \<open>valid_vars = {v. valid_var v}\<close>

subsection \<open>Factored LP Algorithm\<close>

text \<open>Create constraints that ensure @{term \<open>f_e\<close>} is at least the sum of the functions in E:
  sum f in E, @{verbatim \<open>f(z(l := xl) <= f(e, l)\<close>}.\<close>
definition "constr_max E l scopes z xl =
  Le (\<lambda>v.
    case v of
      var_f p f z' \<Rightarrow>
    if p = prefix \<and> f = f_e l \<and> z' = z then -1
    else if p = prefix \<and> f \<in> E \<and> z' = (z(l \<mapsto> xl)) |` (scopes f) then 1
    else 0
    | _ \<Rightarrow> 0) 0"

definition "constrs_max E l scopes scope_e = 
  {constr_max E l scopes z xl | xl z. z \<in> vecs_on scope_e \<and> xl \<in> doms l}"

text \<open>Single iteration step: 
1. select variable to eliminate, 
2. partition functions based on that,
3. create new function (variable) with constraints to ensure maximization.\<close>
definition "elim_step \<Omega> \<F> scopes i = (let
  l = order i;
  E = {e | e. e \<in> \<F> \<and> l \<in> scopes e};
  scope_e = (\<Union>e \<in> E. scopes e) - {l};
  \<Omega>' = \<Omega> \<union> constrs_max E l scopes scope_e in
  (\<Omega>', \<F> - E \<union> {f_e l}, scopes(f_e l := scope_e), i+1)
)"
lemmas refl[of \<open>elim_step\<close>, cong]

definition "elim_vars_aux = 
  ((\<lambda>(\<Omega>, \<F>, scopes, i). elim_step \<Omega> \<F> scopes i) ^^ dims) (constrs_init, \<F>_init, scopes_init, 0)"
lemmas refl[of \<open>elim_vars_aux\<close>, cong]

text \<open>Create final constraints: phi >= sum of functions in F\<close>
definition "gen_constrs arg = (
  case arg of (\<Omega>, \<F>, scopes, i) \<Rightarrow> (\<Omega> \<union> {Le (\<lambda>v.
    case v of
      var_f p f z \<Rightarrow> if p = prefix \<and> f \<in> \<F> \<and> z = Map.empty then 1 else 0
    | var_phi \<Rightarrow> -1
    | _ \<Rightarrow> 0) 0}))"
lemmas refl[of \<open>gen_constrs\<close>, cong]

definition "elim_vars = gen_constrs elim_vars_aux"
lemmas refl[of \<open>elim_vars\<close>, cong]

text \<open>All LP variables possibly created by the algorithm.\<close>
definition \<open>lp_vars =
  {var_phi} \<union> 
  {var_w i |i . i < num_c} \<union> 
  {var_f' (f_c i) x | i x .  i < num_c \<and> x \<in> partial_vecs} \<union>
  {var_f' (f_b i) x | i x .  i < num_b \<and> x \<in> partial_vecs} \<union>
  {var_f' (f_e i) x | i x .  i < dims \<and> x \<in> partial_vecs}\<close>

text \<open>Algorithm invariant used to show correctness:\<close>
definition "invar_lp constrs \<F> scopes i \<longleftrightarrow>
  (\<F> \<subseteq> \<F>_init \<union> (\<lambda>i. f_e (order i)) ` {0..<i}) \<and>
  finite \<F> \<and>
  constrs_init \<subseteq> constrs \<and>
  vars_lp constrs \<subseteq> lp_vars \<and>
  (\<forall>constr \<in> constrs. \<forall>z. \<forall>j \<ge> i. j < dims \<longrightarrow> var_f' (f_e (order j)) z \<notin> vars_constr constr) \<and>
  (\<forall>f \<in> \<F>. scopes f \<subseteq> {0..<dims} - order ` {0..<i}) \<and>
  (\<forall>lp_sol. \<comment> \<open>Equivalence to explicit LP\<close>
    (sat_lp lp_sol (constrs \<union> constrs_\<F> \<F> scopes) \<longrightarrow> sat_lp lp_sol explicit_lp) \<and>
    (sat_lp lp_sol explicit_lp \<longrightarrow> (\<exists>lp_sol'. lp_sol var_phi = lp_sol' var_phi \<and> 
    (\<forall>i. lp_sol (var_w i) = lp_sol' (var_w i)) \<and> sat_lp lp_sol' (constrs \<union> constrs_\<F> \<F> scopes))))"

end

locale factored_lp = factored_lp_consts 
  where
    prefix = prefix
  for prefix :: 'x + 
  assumes fin_dom_dim[simp]: \<open>\<And>i. i < dims \<Longrightarrow> finite (doms i)\<close>
  assumes ne_dom_dim[intro]: \<open>\<And>i. i < dims \<Longrightarrow> doms i \<noteq> {}\<close>
  assumes scope_b: \<open>\<And>c s. (c, s) \<in> set B \<Longrightarrow> s \<subseteq> {..<dims} \<and> has_scope_on c partial_vecs s\<close>
  assumes scope_c: \<open>\<And>c s. (c, s) \<in> set C \<Longrightarrow> s \<subseteq> {..<dims} \<and> has_scope_on c partial_vecs s\<close>

assumes B_notinf: \<open>\<And>c s v. (c, s) \<in> set B \<Longrightarrow> c v \<noteq> \<infinity>\<close>
assumes order: \<open>bij_betw order {0..<dims} {0..<dims}\<close>

begin

lemma fin_vars_subs[dest]: \<open>X \<subseteq> {..<dims} \<Longrightarrow> finite X\<close>
  using finite_nat_iff_bounded 
  by blast

subsection \<open>Vectors\<close>

lemma partial_vecsE[elim]:
  assumes \<open>x \<in> partial_vecs\<close>
  obtains \<open>dom x \<subseteq> {..<dims}\<close> 
    and \<open>\<And>i. i \<in> dom x \<Longrightarrow> \<exists>y. x i = Some y \<and> y \<in> doms i\<close>
  using assms 
  unfolding partial_vecs_def Map.graph_def
  by auto

lemma partial_vecsI[intro]:
  assumes \<open>dom x \<subseteq> {..<dims}\<close> 
    and \<open>\<And>i. i \<in> dom x \<Longrightarrow> the (x i) \<in> doms i\<close>
  shows \<open>x \<in> partial_vecs\<close>
  using assms 
  unfolding partial_vecs_def Map.graph_def
  by fastforce

lemma vecs_on_self[simp]: \<open>x \<in> vecs_on (dom x) \<longleftrightarrow> x \<in> partial_vecs\<close>
  unfolding vecs_on_def
  by auto

lemma vecs_onE[elim]:
  assumes \<open>x \<in> vecs_on X\<close>
  obtains \<open>dom x = X\<close> 
    and \<open>x \<in> partial_vecs\<close>
  using assms 
  unfolding vecs_on_def
  by auto


lemma vecs_onI[intro]:
  assumes \<open>dom x = X\<close> 
    and \<open>x \<in> partial_vecs\<close>
  shows \<open>x \<in> vecs_on X\<close>
  using assms 
  unfolding vecs_on_def
  by auto

lemma partial_vecs_eq_Un: 
  \<open>partial_vecs = (\<Union>x \<in> {x. x \<subseteq> {..<dims}}. vecs_on x)\<close> (is \<open>?L = ?R\<close>)
proof -
  have \<open>x \<in> ?L \<Longrightarrow> x \<in> ?R\<close> for x
    by (auto intro!: exI[of _ \<open>dom x\<close>])
  moreover have \<open>?R \<subseteq> ?L\<close> 
    by auto
  ultimately show ?thesis 
    by auto
qed

lemma fin_partial_states_eq:
  assumes \<open>X \<subseteq> {..<dims}\<close>
  shows \<open>finite (vecs_on X)\<close>
proof -
  have \<open>vecs_on X \<subseteq> {x. dom x \<subseteq> X \<and> ran x \<subseteq> (\<Union>i \<in> X. doms i)}\<close> (is \<open>?L \<subseteq> ?R\<close>)
    by (fastforce elim!: ranE)

  moreover have \<open>finite ?R\<close>
    using assms fin_dom_dim fin_vars_subs
    by (intro finite_set_of_finite_maps') auto      
  ultimately show ?thesis
    using finite_subset 
    by fastforce
qed

lemma fin_partial_vecs: \<open>finite (partial_vecs)\<close>
  using partial_vecs_eq_Un fin_partial_states_eq
  by auto

lemma empty_partial: \<open>Map.empty \<in> partial_vecs\<close>
  unfolding partial_vecs_def by auto

lemma partial_vecs_ne: \<open>partial_vecs \<noteq> {}\<close>
  using empty_partial by auto

lemma partial_vecs_restrI[intro]: \<open>v \<in> partial_vecs \<Longrightarrow> v |` X \<in> partial_vecs\<close>
  by (auto elim!: partial_vecsE intro!: partial_vecsI)


lemma restr_onI[intro]: \<open>x \<in> vecs_on X \<Longrightarrow> X \<inter> Y = Z \<Longrightarrow> x |` Y \<in> vecs_on Z\<close>
  by (auto intro!: vecs_onI)

lemma restr_on_eq[intro]: \<open>x \<in> vecs_on X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> x |` Y \<in> vecs_on Y\<close>
  by auto

lemma full_vecs_dims[intro, dest]: \<open>x \<in> full_vecs \<Longrightarrow> x \<in> vecs_on {..<dims}\<close>
  by (auto simp: full_vecs_def)

lemma full_vecs_partial[dest]: \<open>x \<in> full_vecs \<Longrightarrow> x \<in> partial_vecs\<close>
  by (auto simp: full_vecs_def)

subsection \<open>Scopes\<close>
lemma scope_b': \<open>cs \<in> set B \<Longrightarrow> snd cs \<subseteq> {..<dims} \<and> has_scope_on (fst cs) partial_vecs (snd cs)\<close>
  using scope_b[of \<open>fst cs\<close> \<open>snd cs\<close>]
  by auto

lemma scope_c_subs[intro]: \<open>i < num_c \<Longrightarrow> scope_c i \<subseteq> {..<dims}\<close>
  unfolding num_c_def scope_c_def
  using scope_c[of \<open>fst (C ! i)\<close> \<open>snd (C ! i)\<close>]
  by auto

lemma scope_b_subs[intro]: \<open>i < num_b \<Longrightarrow> scope_b i \<subseteq> {..<dims}\<close>
  using scope_b'
  unfolding num_b_def scope_b_def
  by auto

lemma has_scope_on_b: \<open>i < num_b \<Longrightarrow> has_scope_on (b i) partial_vecs (scope_b i)\<close>
  unfolding num_b_def scope_b_def b_def
  using scope_b
  by auto

lemma has_scope_on_c: \<open>i < num_c \<Longrightarrow> has_scope_on (c i) partial_vecs (scope_c i)\<close>
  unfolding num_c_def scope_c_def c_def
  using scope_c
  by auto

lemma c_r_eq_c: \<open>x \<in> partial_vecs \<Longrightarrow> scope_c i \<subseteq> dom x \<Longrightarrow> i < num_c \<Longrightarrow> c_r i x = c i x\<close>
  by (intro has_scope_on_eq[OF has_scope_on_c]) auto

lemma b_r_eq_b: \<open>x \<in> partial_vecs \<Longrightarrow> (scope_b i) \<subseteq> dom x \<Longrightarrow> i < num_b \<Longrightarrow> 
  b_r i x = b i x\<close>
  by (intro has_scope_on_eq[OF has_scope_on_b]) auto

lemma b_r_notinf: \<open>j < num_b \<Longrightarrow> b_r j x \<noteq> \<infinity>\<close>
  using B_notinf
  unfolding num_b_def b_def
  using B_notinf[of \<open>fst (B ! j)\<close> \<open>snd (B ! j)\<close>]
  by auto

subsection \<open>Initialization\<close>

lemma vars_constr_c: "vars_constr (constr_c z i) =
(if c_r i z = 0
  then {var_f' (f_c i) z}
  else {var_w i, var_f' (f_c i) z})"
  unfolding constr_c_def vars_constr_def vars_poly_def
  by auto

lemma finite_vars_constr_c[simp, intro]: 
  "finite (vars_constr (constr_c z i))"
  using infinite_super vars_constr_c 
  by auto

lemmas if_mult_distrib_right = if_distrib[of \<open>\<lambda>x. x * _\<close>]

lemma sat_constr_c_iff: 
  "sat_constr sol (constr_c z i) \<longleftrightarrow> 
  (sol (var_f' (f_c i) z) = c_r i z * sol (var_w i))"
  unfolding sat_constr_def vars_constr_c
  by (auto simp: constr_c_def)

lemma sat_constrs_c_iff: 
  "sat_lp sol constrs_c \<longleftrightarrow> 
  (\<forall>i < num_c. \<forall>z \<in> vecs_on (scope_c i). 
    sol (var_f' (f_c i) z) = c_r i z * sol (var_w i))"
  unfolding constrs_c_def sat_lp_def
  using sat_constr_c_iff
  by blast

lemma vars_constr_b[simp]: "vars_constr (constr_b z j) = {var_f' (f_b j) z}"
  unfolding vars_constr_def constr_b_def vars_poly_def
  by auto

lemma sat_constr_b_iff: 
  "sat_constr sol (constr_b z j) \<longleftrightarrow> ereal (sol (var_f' (f_b j) z)) = real_of_ereal (b_r j z)"
  using vars_constr_b
  unfolding sat_constr_def constr_b_def
  by simp

lemma real_of_erealD: \<open>x = real_of_ereal y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> y \<noteq> -\<infinity> \<Longrightarrow> ereal x = y\<close>
  by (cases y) auto

lemma sat_constrs_b_iff: 
  "sat_lp sol constrs_b \<longleftrightarrow> (\<forall>i < num_b. 
  \<forall>z \<in> vecs_on (scope_b i). b_r i z = - \<infinity> \<or>
    sol (var_f' (f_b i) z) = b_r i z)"
  unfolding constrs_b_def sat_lp_def
  by simp (metis b_r_notinf sat_constr_b_iff  real_of_erealD)+

lemma vars_expl_constr_eq: 
  "vars_constr (expl_constr x) = insert var_phi {var_w i| i. i \<in> {0..<num_c} \<and> c_r i x \<noteq> 0}"
  unfolding vars_constr_def expl_constr_def vars_poly_def
  by (fastforce split: var_name.splits intro: var_name.exhaust)

lemma vars_expl_constr_subs: "vars_constr (expl_constr x) \<subseteq> insert var_phi (var_w ` {0..<num_c})"
  using vars_expl_constr_eq
  by blast

lemma fin_vars_expl_constr[simp, intro]: "finite (vars_constr (expl_constr x))"
  by (auto simp: vars_expl_constr_eq)

lemma sum_case_var_name: "(\<Sum>x \<in> X. case_var_name e f g x) = 
  (\<Sum>x \<in> X. case_var_name e (\<lambda>_. 0) 0 x) + 
  (\<Sum>x \<in> X. case_var_name (\<lambda>_ _ _. 0) f 0 x) + 
  (\<Sum>x \<in> X. case_var_name (\<lambda>_ _ _. 0) (\<lambda>_. 0) g x)"
  by (auto simp: sum.distrib[symmetric] intro!: sum.cong split: var_name.splits)

lemma eval_b_notinf: \<open>eval_b x \<noteq> \<infinity>\<close>
  unfolding eval_b_def
  using b_r_notinf
  by (auto simp: sum_Pinfty)

lemma sat_expl_constr_iff: 
  assumes \<open>eval_b x \<noteq> - \<infinity>\<close>
  shows "sat_constr lp_sol (expl_constr x) \<longleftrightarrow> 
  lp_sol var_phi \<ge> eval_c (lp_sol o var_w) x + eval_b x"
proof -
  have "(\<Sum>i\<in>vars_constr (expl_constr x).
       (case i of var_f _ f_name fun \<Rightarrow> 0
        | var_w i \<Rightarrow> if i <num_c then c_r i x else 0 | var_phi \<Rightarrow> - 1) *
       lp_sol i) = (\<Sum>i\<in>insert var_phi (var_w ` {0..<num_c}).
       (case i of var_f _ f_name fun \<Rightarrow> 0
        | var_w i \<Rightarrow> if i <num_c then c_r i x else 0 | var_phi \<Rightarrow> - 1) *
       lp_sol i)"
    using vars_expl_constr_eq
    by (auto intro!: sum.mono_neutral_left)
  also have "\<dots> = eval_c (lp_sol o var_w) x - lp_sol var_phi"
    by (subst sum.insert) (auto simp: eval_c_def sum.reindex[unfolded inj_on_def] intro: sum.cong)
  finally show ?thesis
    using assms eval_b_notinf
    by (cases \<open>eval_b x\<close>) (auto simp: if_distrib expl_constr_def sat_constr_def)
qed

lemma sat_explicit_lp_iff:
  shows "sat_lp lp_sol explicit_lp \<longleftrightarrow> 
    (\<forall>x \<in> full_vecs. lp_sol var_phi \<ge> eval_c (lp_sol o var_w) x + eval_b x)"
  unfolding sat_lp_def explicit_lp_def
  using sat_expl_constr_iff
  by auto+

lemma vars_constr_\<F>: 
  "vars_constr (constr_\<F> \<F> scopes x) = insert var_phi {var_f' f z | f z. f \<in> \<F> \<and> z = x |` (scopes f)}"
  unfolding vars_constr_def vars_poly_def constr_\<F>_def
  by (fastforce intro: var_name.exhaust split: var_name.splits)

lemma sat_constr_\<F>:
  assumes "finite \<F>"
  shows "sat_constr sol (constr_\<F> \<F> scopes x) \<longleftrightarrow> 
  (\<Sum>f \<in> \<F>. sol (var_f' f (x |` (scopes f)))) \<le> sol var_phi"
proof -
  have "(\<Sum>i\<in>insert var_phi {var_f' f z | f z. f \<in> \<F> \<and> z = x |` (scopes f)}.
       (case i of 
          var_f p f z \<Rightarrow> if p = prefix \<and> f \<in> \<F> \<and> z = x |` (scopes f) then 1 else 0 | 
          var_w n \<Rightarrow> 0 | 
          var_phi \<Rightarrow> - 1) * sol i) =
      (\<Sum>i\<in> {var_f' f  (x |` (scopes f)) | f. f \<in> \<F>}.
       (case i of 
          var_f p f z \<Rightarrow> if p = prefix \<and> f \<in> \<F> \<and> z = x |` (scopes f) then 1 else 0 | 
          _ \<Rightarrow> 0) * sol i) - sol var_phi"
    using assms
    by (auto intro!: sum.cong)
  also have "\<dots> = (\<Sum>f \<in> \<F>. sol (var_f' f (x |` (scopes f)))) - sol var_phi"
    unfolding Setcompr_eq_image
    by (auto simp: Setcompr_eq_image inj_on_def sum.reindex intro!: sum.cong)

  finally show ?thesis
    unfolding sat_constr_def constr_\<F>_def vars_constr_\<F>[unfolded constr_\<F>_def]
    by simp
qed

lemma finite_\<F>_init: "finite \<F>_init"
  unfolding \<F>_init_def
  by auto

lemma restrict_subset_Dom[intro]: "x \<in> vecs_on Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> x |` X \<in> vecs_on Y"
  unfolding vecs_on_def
  by auto

lemma Dom_imp_dom_dim_c[dest]: \<open>x \<in> vecs_on {..<dims} \<Longrightarrow> i < num_c \<Longrightarrow> 
  j \<in> scope_c i \<Longrightarrow> the (x j) \<in> doms j\<close>
  using scope_c_subs
  by force

lemma Dom_imp_dom_dim_b[dest]: \<open>x \<in> vecs_on {..<dims} \<Longrightarrow> i < num_b \<Longrightarrow> j \<in> scope_b i \<Longrightarrow> 
  the (x j) \<in> doms j\<close>
  using scope_b_subs  
  by force

lemma sum_neg_infty: 
  \<open>finite X \<Longrightarrow> (\<exists>i \<in> X. f i = -\<infinity>) \<Longrightarrow> (\<forall>i \<in> X. f i \<noteq> \<infinity>) \<Longrightarrow> (\<Sum>i \<in> X. f i) = (-\<infinity> :: ereal)\<close>
  by (induction rule: finite_induct) (auto simp: sum_Pinfty)

lemma sum_neg_infty': \<open>finite X \<Longrightarrow> (\<Sum>i \<in> X. f i) = (-\<infinity> :: ereal) \<Longrightarrow> (\<exists>i \<in> X. f i = -\<infinity>) \<close>
  by (induction rule: finite_induct) (auto simp: sum_Pinfty)

lemma eval_b_not_neg_infD: \<open>eval_b x \<noteq> -\<infinity> \<Longrightarrow> i < num_b \<Longrightarrow> b_r i x \<noteq> -\<infinity>\<close>
  unfolding eval_b_def
  by (meson b_r_notinf finite_lessThan lessThan_iff sum_neg_infty)

lemma eval_b_neg_infD: \<open>eval_b x = -\<infinity> \<Longrightarrow> \<exists>i < num_b. b_r i x = -\<infinity>\<close>
  unfolding eval_b_def
  using sum_neg_infty' b_r_notinf
  by (meson b_r_notinf finite_lessThan lessThan_iff sum_neg_infty)

lemma sat_init_impl_sat_expl:              
  assumes "sat_lp lp_sol (constrs_init \<union> constrs_\<F> \<F>_init scopes_init)"
  shows "sat_lp lp_sol explicit_lp"
proof -
  have "sat_lp lp_sol constrs_init"
    using assms
    by auto
  hence "sat_lp lp_sol constrs_c"
    unfolding constrs_init_def
    by auto

  hence f_c_eq_w: "lp_sol (var_f' (f_c i) z) = c_r i z * lp_sol (var_w i)"
    if "i < num_c" "z \<in> vecs_on (scope_c i)" for i z
    using that
    by (simp add: sat_constrs_c_iff)

  have f_b_eq_b: "lp_sol (var_f' (f_b i) z) = b_r i z"
    if "i < num_b" "z \<in> vecs_on (scope_b i)" \<open>b_r i z \<noteq> -\<infinity>\<close>for i z
    using constrs_init_def \<open>sat_lp lp_sol constrs_init\<close> sat_constrs_b_iff that
    by auto

  have eval_c_eq: "(\<Sum>i < num_c. lp_sol (var_f' (f_c i) (x |` (scopes_init (f_c i))))) = eval_c (lp_sol o var_w) x"
    if "x \<in> full_vecs" for x
    using that
    unfolding eval_c_def scopes_init_def full_vecs_def
    by (subst sum.cong[OF refl f_c_eq_w]) 
      (force dest!: scope_c_subs intro!: vecs_onI simp: algebra_simps)+

  have \<open>lp_sol (restr_f (f_b j) x scopes_init) = b_r j (x |` scope_b j)\<close> if \<open>x \<in> full_vecs\<close> \<open>j < num_b\<close> \<open>eval_b x \<noteq> -\<infinity>\<close> for x j
    using scope_b_subs that
    unfolding full_vecs_def scopes_init_def
    by (subst f_b_eq_b[symmetric]) 
      (auto dest!: eval_b_not_neg_infD intro!: partial_vecsI vecs_onI elim!: vecs_onE partial_vecsE)+

  hence eval_b_eq: "(\<Sum>j < num_b. lp_sol (restr_f (f_b j) x scopes_init)) = eval_b x"
    if "x \<in> full_vecs" \<open>eval_b x \<noteq> -\<infinity>\<close> for x
    using that 
    unfolding eval_b_def
    by (auto simp flip: sum_ereal)

  have *: "(\<Sum>f\<in>\<F>_init. lp_sol (restr_f f x scopes_init)) \<le> lp_sol var_phi" if "x \<in> full_vecs"  for x
    using that finite_\<F>_init assms constrs_\<F>_def sat_constr_\<F>
    by blast

  have \<open>{f_c i |i. i < num_c} \<inter> {f_b i |i. i < num_b} = {}\<close>
    by auto

  hence "eval_c (lp_sol o var_w) x + eval_b x \<le> lp_sol var_phi" if "x \<in> full_vecs" for x
    using eval_b_eq[of x] eval_c_eq * that eval_b_notinf
    unfolding \<F>_init_def
    by (cases \<open>eval_b x\<close>) (auto simp: sum.union_disjoint lessThan_def setcompr_eq_image sum.reindex[unfolded inj_on_def])

  thus "sat_lp lp_sol explicit_lp"
    unfolding sat_explicit_lp_iff
    by auto
qed

lemma max_phi_nonneg: \<open>max_phi sol \<ge> 0\<close>
  unfolding max_phi_def
  by auto


lemma max_w_nonneg: \<open>max_w sol \<ge> 0\<close>
  unfolding max_w_def 
  using lessThan_empty_iff
  by (auto simp: Max_ge_iff)

lemma max_e_nonneg: \<open>max_e sol \<ge> 0\<close>
  unfolding max_e_def
  using fin_partial_vecs partial_vecs_ne lessThan_empty_iff
  by (auto simp: Max_ge_iff)

lemma max_c_nonneg: \<open>max_c sol \<ge> 0\<close>
  unfolding max_c_def
  using fin_partial_vecs partial_vecs_ne lessThan_empty_iff
  by (auto simp: Max_ge_iff)

lemma max_b_nonneg: \<open>max_b sol \<ge> 0\<close>
  unfolding max_b_def
  using fin_partial_vecs partial_vecs_ne lessThan_empty_iff
  by (auto simp: Max_ge_iff)

lemma max_var_nonneg: \<open>max_var sol \<ge> 0\<close>
  using max_phi_nonneg max_e_nonneg max_c_nonneg max_b_nonneg max_w_nonneg
  unfolding max_var_def
  by (simp add: le_max_iff_disj)

lemma not_consistent_restrict: \<open>\<not>consistent x y \<Longrightarrow> \<not>consistent (x |` X) y\<close> 
  unfolding consistent_def
  by (metis Map.restrict_restrict dom_restrict restrict_dom)

lemma unbdd_in[simp]: \<open>v \<in> unbdd \<Longrightarrow> mk_unbdd_small \<F> unbdd sol v = -card \<F> * max_var sol\<close>
  unfolding mk_unbdd_small_def 
  by auto

lemma unbdd_notin[simp]: \<open>v \<notin> unbdd \<Longrightarrow> mk_unbdd_small \<F> unbdd sol v = sol v\<close>
  unfolding mk_unbdd_small_def 
  by auto

lemma max_b_ge: \<open>i < num_b \<Longrightarrow> z \<in> partial_vecs \<Longrightarrow> \<bar>sol (var_f prefix (f_b i) z)\<bar> \<le> max_b sol\<close>
  unfolding max_b_def
  using fin_partial_vecs partial_vecs_ne abs_ge_self lessThan_empty_iff
  by (auto simp: Max_ge_iff)

lemma max_c_ge: \<open>i < num_c \<Longrightarrow> z \<in> partial_vecs \<Longrightarrow> \<bar>sol (var_f prefix (f_c i) z)\<bar> \<le> max_c sol\<close>
  unfolding max_c_def
  using fin_partial_vecs partial_vecs_ne abs_ge_self lessThan_empty_iff
  by (auto simp: Max_ge_iff)+

lemma max_e_ge: \<open>i < dims \<Longrightarrow> z \<in> partial_vecs \<Longrightarrow> \<bar>sol (var_f prefix (f_e i) z)\<bar> \<le> max_e sol\<close>
  unfolding max_e_def
  using fin_partial_vecs partial_vecs_ne abs_ge_self lessThan_empty_iff
  by (auto simp: Max_ge_iff)+

lemma max_w_ge: \<open>i < num_c \<Longrightarrow> \<bar>sol (var_w i)\<bar> \<le> max_w sol\<close>
  unfolding max_w_def
  by auto

lemma max_phi_ge: \<open>\<bar>sol var_phi\<bar> \<le> max_phi sol\<close>
  unfolding max_phi_def
  by auto

lemma max_var_ge: \<open>valid_var v \<Longrightarrow> \<bar>sol v\<bar> \<le> max_var sol\<close>
  unfolding valid_var_def max_var_def
  using max_e_ge max_c_ge max_b_ge max_w_ge max_phi_ge
  by (simp split: var_name.splits f_name.splits add:max_phi_ge max_w_ge le_max_iff_disj)

lemma max_var_ge': \<open>valid_var v \<Longrightarrow> sol v \<le> max_var sol\<close>
  using max_var_ge abs_le_D1 by blast

lemma valid_phi: \<open>valid_var (var_phi)\<close>
  unfolding valid_var_def by auto

lemma sat_expl_impl_sat_init:
  assumes "sat_lp (lp_sol :: ('x, 'a) var_name \<Rightarrow> real) explicit_lp"
  shows "\<exists>lp_sol'.
         lp_sol var_phi = lp_sol' var_phi \<and> (\<forall>i. lp_sol (var_w i) = lp_sol' (var_w i))
    \<and> sat_lp lp_sol' (constrs_init \<union> constrs_\<F> \<F>_init scopes_init)"
proof -
  define lp_sol' where "lp_sol' = (\<lambda>v :: ('x, 'a) var_name.
    case v of
      var_f p f z \<Rightarrow>
        (case f of 
    (f_c i) \<Rightarrow>
      if p = prefix \<and> i < num_c then lp_sol (var_w i) * (c_r i z) else lp_sol v 
  | f_b i \<Rightarrow> 
      if p = prefix \<and> i < num_b then 
        real_of_ereal (b_r i z) else lp_sol v
  )
    | _ \<Rightarrow> lp_sol v)"

  define lp_sol'' where "lp_sol'' = mk_unbdd_small \<F>_init unbdd_vars_init lp_sol'"

  have b_c_disj: \<open>{f_c j|j. j < num_c} \<inter> {f_b j |j. j < num_b} = {}\<close>
    by auto

  have abs_inf: \<open>\<bar>x\<bar> = \<infinity> \<longleftrightarrow> x = \<infinity> \<or> x = -\<infinity>\<close> for x :: ereal
    by auto

  have eval_le_phi: "eval_c (lp_sol o var_w) x + eval_b x \<le> lp_sol var_phi"
    if "x \<in> full_vecs" for x
    using assms sat_explicit_lp_iff that by auto

  hence sum_le: "(\<Sum>f\<in>{f_c i |i. i < num_c} \<union> {f_b i |i. i < num_b}. lp_sol'' (var_f' f (x |` (scopes_init f)))) \<le> lp_sol'' var_phi"
    if \<open>x \<in> full_vecs\<close> \<open>eval_b x = -\<infinity>\<close> for x
  proof -

    have *: \<open>lp_sol'' (restr_f (f_b i) x scopes_init) \<le> max_var lp_sol'\<close> if \<open>i < num_b\<close> for i
      unfolding lp_sol''_def mk_unbdd_small_def
      using that \<open>x \<in> full_vecs\<close>
      by (auto intro!: order.trans[OF _ max_var_nonneg] max_var_ge' simp: valid_var_def max_var_nonneg)+


    obtain i where \<open>i < num_b\<close> \<open>b_r i x = -\<infinity>\<close>
      using \<open>eval_b x = - \<infinity>\<close> eval_b_neg_infD by blast
    have f_b_i: \<open>{f_b i |i. i < num_b} = insert (f_b i) {f_b j |j. j \<noteq> i \<and> j < num_b}\<close>
      using \<open>i < num_b\<close> by auto

    have \<open>(\<Sum>f\<in>{f_b i |i. i < num_b}. lp_sol'' (restr_f f x scopes_init)) =
      lp_sol'' (restr_f (f_b i) x scopes_init) + (\<Sum>f\<in>{f_b j |j. j \<noteq> i \<and> j < num_b}. lp_sol'' (restr_f f x scopes_init))\<close>
      using \<open>i < num_b\<close>
      by (subst sum.insert[symmetric]) (auto intro!: sum.cong simp del: sum.insert)
    also have \<open>\<dots> = -card \<F>_init * max_var lp_sol' + (\<Sum>f\<in>{f_b j |j. j \<noteq> i \<and> j < num_b}. lp_sol'' (restr_f f x scopes_init))\<close>
      unfolding lp_sol''_def unbdd_vars_init_def
      using \<open>i < num_b\<close> \<open>b_r i x = - \<infinity>\<close> scope_b_subs that
      by (subst unbdd_in) (auto simp add: scopes_init_def)
    also have \<open>\<dots> \<le> -card \<F>_init * max_var lp_sol' + (\<Sum>f\<in>{f_b j |j. j \<noteq> i \<and> j < num_b}. max_var lp_sol')\<close>
      using * 
      by (auto intro: sum_bounded_above)
    also have \<open>\<dots> = (card {f_b j |j. j \<noteq> i \<and> j < num_b} - real (card \<F>_init)) * max_var lp_sol'\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = (real (card {f_b j |j. j < num_b}) - 1 - real (card \<F>_init)) * max_var lp_sol'\<close>
      by (auto simp: f_b_i)
    also have \<open>\<dots> = -(real (card {f_c j|j. j < num_c}) + 1) * max_var lp_sol'\<close>
      using b_c_disj
      by (auto simp: algebra_simps \<F>_init_def card_Un_disjoint)

    finally have \<open>(\<Sum>f\<in>{f_b i |i. i < num_b}. lp_sol'' (restr_f f x scopes_init)) \<le> -(real (card {f_c j|j. j < num_c}) + 1) * max_var lp_sol'\<close>.
    moreover have \<open>(\<Sum>f\<in>{f_c i |i. i < num_c}. lp_sol' (restr_f f x scopes_init)) \<le> (\<Sum>f\<in>{f_c i |i. i < num_c}. max_var lp_sol')\<close>
      using that max_var_ge
      by (intro sum_mono) (auto intro!: max_var_ge' simp: valid_var_def)+
    moreover then 
    have *: \<open>(\<Sum>f\<in>{f_c i |i. i < num_c}. lp_sol' (restr_f f x scopes_init)) \<le> card {f_c i |i. i < num_c} * max_var lp_sol'\<close>
      by auto
    moreover have \<open>(\<Sum>f\<in>{f_c i |i. i < num_c}. lp_sol'' (restr_f f x scopes_init)) \<le> card {f_c i |i. i < num_c} * max_var lp_sol'\<close>
      unfolding lp_sol''_def mk_unbdd_small_def unbdd_vars_init_def
      by (auto intro!: order.trans[OF _ *] sum_mono)
    ultimately have \<open>(\<Sum>f\<in>{f_c i |i. i < num_c} \<union> {f_b i |i. i < num_b}. lp_sol'' (restr_f f x scopes_init)) \<le> (real (card {f_c j |j. j < num_c})) * max_var lp_sol' + 
  (- real (card {f_c j |j. j < num_c}) - 1) * max_var lp_sol'
      \<close>
      using b_c_disj
      by (auto simp add: sum.union_disjoint)
    hence \<open>(\<Sum>f\<in>{f_c i |i. i < num_c} \<union> {f_b i |i. i < num_b}. lp_sol'' (restr_f f x scopes_init)) \<le>  - max_var lp_sol'\<close>
      by argo
    thus \<open>(\<Sum>f\<in>{f_c i |i. i < num_c} \<union> {f_b i |i. i < num_b}. lp_sol'' (restr_f f x scopes_init)) \<le> lp_sol'' var_phi\<close>
      unfolding lp_sol''_def unbdd_vars_init_def
      using max_var_ge[OF valid_phi, of lp_sol']
      by auto
  qed

  moreover have sum_le: "(\<Sum>f\<in>{f_c i |i. i < num_c} \<union> {f_b i |i. i < num_b}. 
  lp_sol'' (var_f' f (x |` (scopes_init f)))) \<le> lp_sol'' var_phi"
    if \<open>x \<in> full_vecs\<close> \<open>eval_b x \<noteq> -\<infinity>\<close> for x
    using eval_le_phi[of x]
    unfolding eval_c_def eval_b_def scopes_init_def lp_sol''_def lp_sol'_def lessThan_def
    using that b_c_disj b_r_notinf eval_b_not_neg_infD abs_inf
    by (auto simp: unbdd_vars_init_def setcompr_eq_image sum.reindex inj_on_def sum.union_disjoint ereal_real 
        simp flip: ereal_less_eq(3) plus_ereal.simps(1) sum_ereal)

  ultimately have sat_\<F>: "sat_lp lp_sol'' (constrs_\<F> \<F>_init scopes_init)"
    unfolding constrs_\<F>_def sat_lp_def \<F>_init_def
    by (auto simp add: sat_constr_\<F>)


  moreover have sat: \<open>sat_lp lp_sol'' constrs_init\<close>
    unfolding constrs_init_def  
    using b_r_notinf real_of_erealD
    by (auto simp: sat_constrs_c_iff sat_constrs_b_iff 
        lp_sol'_def lp_sol''_def unbdd_vars_init_def mk_unbdd_small_def 
        split: var_name.splits if_splits)


  show ?thesis
    using sat sat_\<F>
    by (auto intro: exI[of _ lp_sol''] simp: unbdd_vars_init_def lp_sol''_def lp_sol'_def)
qed

lemma sat_constr_max_iff:
  assumes "finite E" "f_e l \<notin> E"
  shows "sat_lp lp_sol (constrs_max E l scopes scope_e) \<longleftrightarrow>
   (\<forall>z\<in>vecs_on scope_e. \<forall>xl\<in>doms l. (\<Sum>f \<in> E. lp_sol (var_f' f ((z(l \<mapsto> xl)) |` (scopes f)))) \<le> lp_sol (var_f' (f_e l) z))"
proof -
  have vars_constr_subs: "vars_constr (constr_max E l scopes z xl) = 
  insert (var_f' (f_e l) z) {var_f' f ((z(l \<mapsto> xl)) |` (scopes f) :: nat \<rightharpoonup> 'a) | f. f \<in> E}"
    for xl z
    unfolding constr_max_def vars_poly_def vars_constr_def
    by (auto split: var_name.splits) (metis var_name.exhaust)

  have *: "(\<Sum>i\<in> vars_constr (constr_max E l scopes z xl).
              (case i of var_f p f z' \<Rightarrow> 
      if p = prefix \<and> f = f_e l \<and> z' = z then - 1 else 
      if p = prefix \<and> f \<in> E \<and> z' = (z(l \<mapsto> xl)) |` (scopes f) then 1 else 0 | _ \<Rightarrow> 0) * lp_sol i)
      = - lp_sol (var_f' (f_e l) z) + (\<Sum>f \<in> E. lp_sol (var_f' f ((z(l \<mapsto> xl)) |` (scopes f))))"
    for xl z
    using assms
    unfolding vars_constr_subs
    by (auto simp: Setcompr_eq_image image_iff sum.reindex inj_on_def constr_max_def vars_poly_def vars_constr_def intro: sum.cong)

  have \<open>sat_constr lp_sol (constr_max E l scopes z xl) \<longleftrightarrow> 
    (\<Sum>f\<in>E. lp_sol (restr_f f (z(l \<mapsto> xl)) scopes)) \<le> lp_sol (var_f' (f_e l) z)\<close>
    if \<open>z \<in> vecs_on scope_e\<close> \<open>xl\<in>doms l\<close> for z xl
    using that *[of z xl]
    unfolding constr_max_def sat_constr_def
    by auto
  thus ?thesis
    unfolding sat_lp_def constrs_max_def
    by blast
qed

lemma vars_constrs_init: \<open>vars_lp constrs_init \<subseteq> lp_vars\<close>
  using vars_constr_b vars_constr_c
  unfolding lp_vars_def constrs_init_def constrs_b_def constrs_c_def vars_lp_def
  by (fastforce split: if_splits)+

lemma vars_constr_eq[simp]: 
  \<open>vars_constr (constr.Eq p rhs) = vars_poly p\<close>
  \<open>vars_constr (constr.Le p rhs) = vars_poly p\<close>
  unfolding vars_constr_def 
  by auto

lemma vars_poly_var_name[simp]: \<open>vars_poly (case_var_name fv fw fphi) = 
  (if fphi = 0 then {} else {var_phi}) \<union> {var_w i |i . fw i \<noteq> 0} \<union>
  {var_f p f x | p f x. fv p f x \<noteq> 0}\<close>
  unfolding vars_poly_def
  by (auto split: var_name.splits) (meson var_name.exhaust)+

lemma invar_init: "invar_lp constrs_init \<F>_init scopes_init 0"
  using vars_constrs_init sat_expl_impl_sat_init sat_init_impl_sat_expl 
    scope_c scope_b scope_c_subs scope_b_subs ne_dom_dim
  unfolding invar_lp_def vars_poly_def vars_constr_def constrs_init_def constr_b_def constrs_b_def
    constr_c_def constrs_c_def \<F>_init_def scopes_init_def
  using ne_dom_dim 
  by (auto simp: subset_iff)

lemma update_restrict[simp]: \<open>(x(i \<mapsto> y)) |` D = (if i \<in> D then (x |` D)(i \<mapsto> y) else x |` D)\<close>
  by auto

lemma partial_vecs_upd: \<open>x \<in> partial_vecs \<Longrightarrow> i < dims \<Longrightarrow> xl \<in> doms i \<Longrightarrow> x(i \<mapsto> xl) \<in> partial_vecs\<close>
  unfolding partial_vecs_def
  by (auto simp: case_prod_unfold in_graphI dest!: in_graphD split: if_splits)

definition \<open>\<F>s = {f_b i | i. i < num_b} \<union> {f_c i | i. i < num_c} \<union> {f_e i | i. i < dims} \<close>

lemma vars_constr_max: \<open>l < dims \<Longrightarrow> E \<subseteq> \<F>s \<Longrightarrow> z \<in> partial_vecs \<Longrightarrow> xl \<in> doms l \<Longrightarrow>
  vars_constr (constr_max E l scopes z xl) \<subseteq> insert (var_f' (f_e l) z) {var_f' f (z(l \<mapsto> xl) |` scopes f) | f. f \<in> E}\<close>
  unfolding constr_max_def
  by auto

lemma vars_constr_max': \<open>l < dims \<Longrightarrow> E \<subseteq> \<F>s \<Longrightarrow> z \<in> partial_vecs \<Longrightarrow> xl \<in> doms l \<Longrightarrow>
  vars_constr (constr_max E l scopes z xl) \<subseteq> lp_vars\<close>
  unfolding \<F>s_def lp_vars_def
  using partial_vecs_upd[of z l]
  by (intro order.trans[OF vars_constr_max[unfolded \<F>s_def lp_vars_def]]) blast+

lemma vars_constrs_max: \<open>l < dims \<Longrightarrow> scope_e \<subseteq> {..<dims} \<Longrightarrow> E \<subseteq> \<F>s \<Longrightarrow>
   vars_lp (constrs_max E l scopes scope_e) \<subseteq> lp_vars\<close>
  unfolding constrs_max_def vars_lp_def
  using vars_constr_max'[of l E]
  by blast

lemma order_ltI: \<open>i < dims \<Longrightarrow> order i < dims\<close>
  using bij_betwE lessThan_atLeast0 order
  by blast

lemma \<F>_init_subs: \<open>\<F>_init \<subseteq> \<F>s\<close>
  unfolding \<F>s_def \<F>_init_def by auto

lemma invar_lp_\<F>s: 
  assumes \<open>i < dims\<close> \<open>invar_lp constrs \<F> scopes i\<close>
  shows \<open>\<F> \<subseteq> \<F>s\<close>
proof -
  have \<open>(\<lambda>i. f_e (order i)) ` {0..<i} \<subseteq> \<F>s\<close>
    using assms
    by (auto intro!: order_ltI simp: \<F>s_def)
  hence \<open>\<F>_init \<union> (\<lambda>i. f_e (order i)) ` {0..<i} \<subseteq> \<F>s\<close>
    using assms \<F>_init_subs by auto

  thus ?thesis
    using assms order.trans unfolding invar_lp_def by metis
qed

lemma invar_lp_step:
  assumes "i < dims"
  assumes invar_constrs: "invar_lp constrs \<F> scopes i"
  assumes "(constrs', \<F>', scopes', Suc i) = elim_step constrs \<F> scopes i"
  shows "invar_lp constrs' \<F>' scopes' (Suc i)"
proof -
  define l where "l = order i"
  define E where "E = {e |e. e \<in> \<F> \<and> l \<in> scopes e}"
  define scope_e where "scope_e = \<Union> (scopes ` E) - {l}"

  have l_less_num_vars[simp, intro]: "l < dims"
    unfolding l_def
    using assms bij_betwE lessThan_atLeast0 order
    by blast

  have E_subs: "E \<subseteq> \<F>"
    by (simp add: E_def)

  have

constrs'_def: "constrs' = constrs \<union> constrs_max E l scopes scope_e" and
\<F>'_def: "\<F>' = \<F> - E \<union> {f_e l}" and 
scopes'_def: "scopes' = scopes(f_e l := scope_e)"
    using assms
    by (auto simp: elim_step_def E_def l_def scope_e_def Let_def)


  have f_e_order_notin: "f_e (order j) \<notin> \<F>" if "j \<ge> i" "j < dims" for j
  proof -
    have "f_e (order j) \<notin> (\<lambda>i. f_e (order i)) ` {0..<i}"
      using order assms that
      unfolding bij_betw_def
      by (auto dest!: inj_onD)
    thus ?thesis
      using assms
      unfolding invar_lp_def \<F>_init_def
      by auto
  qed
  hence f_e_l_notin[simp, intro]: "f_e l \<notin> \<F>" \<open>f_e l \<notin> E\<close>
    using l_def assms \<open>E \<subseteq> \<F>\<close>
    by auto


  have fins[simp, intro]: \<open>finite \<F>\<close> \<open>finite E\<close> \<open>finite (\<F> - E)\<close> \<open>finite \<F>'\<close>
    using \<open>E \<subseteq> \<F>\<close> infinite_super invar_constrs invar_lp_def \<F>'_def 
    by auto

  have scopes'[simp]:
    \<open>f \<in> \<F> \<Longrightarrow> scopes' f = scopes f\<close>
    \<open>f \<in> E \<Longrightarrow> scopes' f = scopes f\<close>
    \<open>scopes' (f_e l) = scope_e\<close>
    for f
    using \<open>f_e l \<notin> E\<close> \<open>f_e l \<notin> \<F>\<close>
    by (auto simp: scopes'_def)

  have insert_l_scopes: "f \<in> E \<Longrightarrow> insert l ((\<Union> (scopes ` E)) \<inter> scopes f) = scopes f" for f
    using E_def by blast

  have "sat_lp lp_sol explicit_lp"
    if "sat_lp lp_sol constrs" 
      "sat_lp lp_sol (constrs_max E l scopes scope_e)"
      "sat_lp lp_sol (constrs_\<F> (\<F> - E \<union> {f_e l}) (scopes(f_e l := scope_e)))"
    for lp_sol
  proof -
    have le_f_e_l: "(\<Sum>f\<in>E. lp_sol (var_f' f ((z(l \<mapsto> xl)) |` (scopes f)))) \<le> lp_sol (var_f' (f_e l) z)"
      if \<open>z \<in> vecs_on scope_e\<close> \<open>xl \<in> doms l\<close> for xl z
      using sat_constr_max_iff \<open>finite E\<close> \<open>E \<subseteq> \<F>\<close> \<open>f_e l \<notin> \<F>\<close> \<open>sat_lp lp_sol (constrs_max E l scopes scope_e)\<close> that
      by blast


    have \<open>f \<in> \<F> \<Longrightarrow> scopes f \<subseteq> {0..<dims} - order ` {0..<i}\<close> for f
      using invar_constrs
      unfolding invar_lp_def
      by auto

    hence scopes_in_dims: \<open>f \<in> \<F> \<Longrightarrow> scopes f \<subseteq> {..<dims}\<close> for f
      by fastforce

    have "(\<Sum>f\<in>\<F>. lp_sol (var_f' f (x |` (scopes f)))) \<le> lp_sol var_phi"
      if \<open>x \<in> full_vecs\<close> for x
    proof -
      have "(\<Sum>f\<in>\<F>. lp_sol (var_f' f (x |` (scopes f)))) = (\<Sum>f\<in>\<F>. lp_sol (var_f' f (x |` (scopes' f))))"
        by auto
      also have "\<dots> =
        (\<Sum>f\<in>\<F> - E \<union> {f_e l}. lp_sol (var_f' f (x |` (scopes' f))))
        + (\<Sum>f\<in> E. lp_sol (var_f' f (x |` (scopes' f))))
        - (\<Sum>f\<in>{f_e l}. lp_sol (var_f' f (x |` (scopes' f))))"
        using \<open>E \<subseteq> \<F>\<close> \<open>f_e l \<notin> \<F>\<close> \<open>finite \<F>\<close> sum.subset_diff 
        by fastforce
      also have "\<dots> \<le> (\<Sum>f\<in>\<F> - E \<union> {f_e l}. lp_sol (var_f' f (x |` (scopes' f))))"
      proof -
        have \<open>scope_e \<subseteq> dom x\<close>
          using that scopes_in_dims
          unfolding full_vecs_def scope_e_def E_def
          by auto
        hence "(x |` (scopes' (f_e l))) \<in> vecs_on scope_e"
          using that invar_constrs[unfolded invar_lp_def] \<open>E \<subseteq> \<F>\<close> 
          by auto
        hence *: "(\<Sum>f\<in>E. lp_sol (var_f' f (((x |` (scopes' (f_e l)))(l \<mapsto> xl)) |` (scopes f)))) \<le> lp_sol (var_f' (f_e l) (x |` (scopes' (f_e l))))"        
          if \<open>xl \<in> doms l\<close> for xl
          using le_f_e_l that
          by blast


        have scopes_f_eq: \<open>f \<in> E \<Longrightarrow> (scopes f - {l}) = (scopes' (f_e l)) \<inter> (scopes f)\<close> for f
          by (auto simp: scope_e_def)

        have *: "(\<Sum>f\<in> E. lp_sol (var_f' f ((x(l \<mapsto> xl)) |` (scopes' f)))) \<le> lp_sol (var_f' (f_e l) (x |` (scopes' (f_e l))))"
          if \<open>xl \<in> doms l\<close> for xl
          using E_def that *[of xl]
          by (auto simp: scopes_f_eq)

        moreover have \<open>the (x l) \<in> doms l\<close>
          using \<open>x \<in> full_vecs\<close>
          unfolding full_vecs_def vecs_on_def partial_vecs_def Map.graph_def
          by (simp add: domD)

        moreover have \<open>f \<in> E \<Longrightarrow> l \<in> scopes f\<close> for f
          by (simp add: E_def)

        have \<open>(x(l \<mapsto> the (x l))) = x\<close>
          by (metis domIff full_vecs_def fun_upd_idem l_less_num_vars lessThan_iff option.exhaust_sel that vecs_onE)

        ultimately have "(\<Sum>f\<in> E. lp_sol (var_f' f (x |` (scopes' f)))) \<le> lp_sol (var_f' (f_e l) (x |` (scopes' (f_e l))))"
          by (intro order.trans[OF _ *[of \<open>the (x l)\<close>]]) auto

        thus ?thesis
          by fastforce
      qed
      finally have "(\<Sum>f\<in>\<F>. lp_sol (var_f' f (x |` (scopes f)))) \<le> (\<Sum>f\<in>\<F> - E \<union> {f_e l}. lp_sol (var_f' f (x |` (scopes' f))))".
      moreover have "(\<Sum>f\<in>\<F> - E \<union> {f_e l}. lp_sol (var_f' f (x |` (scopes' f)))) \<le> lp_sol var_phi"
        using \<open>finite \<F>\<close> that \<open>sat_lp lp_sol (constrs_\<F> (\<F> - E \<union> {f_e l}) (scopes(f_e l := scope_e)))\<close>
        unfolding constrs_\<F>_def
        by (auto simp: sat_constr_\<F> scopes'_def)
      ultimately show "(\<Sum>f\<in>\<F>. lp_sol (var_f' f (x |` (scopes f)))) \<le> lp_sol var_phi"
        by auto
    qed
    hence "sat_lp lp_sol (constrs_\<F> \<F> scopes)"
      unfolding constrs_\<F>_def
      by (auto simp: sat_constr_\<F>)
    thus "sat_lp lp_sol explicit_lp"
      using invar_constrs invar_lp_def that by fastforce
  qed
  hence "(\<forall>lp_sol. (sat_lp lp_sol (constrs' \<union> constrs_\<F> \<F>' scopes') \<longrightarrow> sat_lp lp_sol explicit_lp))"
    by (simp add: \<F>'_def constrs'_def scopes'_def)

  have ex_sol: "(\<exists>lp_sol' :: ('x, 'a) var_name \<Rightarrow> real. lp_sol var_phi = lp_sol' var_phi \<and> (\<forall>i. (lp_sol :: ('x, 'a) var_name \<Rightarrow> real) (var_w i) = lp_sol' (var_w i)) \<and> sat_lp lp_sol' (constrs' \<union> constrs_\<F> \<F>' scopes'))"
    if "(sat_lp lp_sol explicit_lp)" for lp_sol
  proof -
    obtain lp_sol' where 
      lp_sol': \<open>lp_sol var_phi = lp_sol' var_phi \<and> (\<forall>i. lp_sol (var_w i) = lp_sol' (var_w i)) \<and> sat_lp lp_sol' (constrs \<union> constrs_\<F> \<F> scopes)\<close>
      using invar_constrs \<open>sat_lp lp_sol explicit_lp\<close> 
      unfolding invar_lp_def
      by presburger
    define lp_sol'' where "lp_sol'' = (\<lambda>v.
        case v of (var_f p (f_e j) z) \<Rightarrow> 
          if p = prefix \<and> j = l \<and> z \<in> vecs_on scope_e then MAX xl \<in> doms l. (\<Sum>f \<in> E. lp_sol' (var_f' f ((z(l \<mapsto> xl)) |` (scopes f)))) 
          else lp_sol' v
        | _ \<Rightarrow> lp_sol' v)"

    have var_w_eq: "\<And>i. lp_sol (var_w i) = lp_sol'' (var_w i)"
      unfolding lp_sol''_def
      by (simp add: lp_sol')

    have lp_sol''_phi[simp]: \<open>lp_sol'' var_phi = lp_sol' var_phi\<close>
      by (simp add: lp_sol''_def)

    have lp_sol''_\<F>[simp]: \<open>f \<in> \<F> \<Longrightarrow> lp_sol'' (restr_f f x X) = lp_sol' (restr_f f x X)\<close> for f X x
      by (auto simp: lp_sol''_def split: f_name.splits)


    have lp_sol''_\<F>'[simp]: \<open>f \<in> \<F> \<Longrightarrow> lp_sol''(var_f' f x)  = lp_sol' (var_f' f x)\<close> for f X x
      by (auto simp: lp_sol''_def split: f_name.splits)

    hence lp_sol''_E[simp]: \<open>f \<in> E \<Longrightarrow> lp_sol'' (restr_f f x X) = lp_sol' (restr_f f x X)\<close> for f X x
      using \<open>E \<subseteq> \<F>\<close>
      by auto

    hence lp_sol''_E'[simp]: \<open>f \<in> E \<Longrightarrow> lp_sol'' (var_f' f x) = lp_sol' (var_f' f x)\<close> for f X x
      using \<open>E \<subseteq> \<F>\<close>
      by auto

    have "lp_sol'' v = lp_sol' v" if "c \<in> constrs" "v \<in> vars_constr c" for v c
      using that l_def assms
      unfolding lp_sol''_def invar_lp_def
      by (auto split: var_name.splits f_name.splits)

    moreover have "sat_lp lp_sol' constrs"
      using lp_sol' by auto

    ultimately have "sat_lp lp_sol'' constrs"
      using \<open>sat_lp lp_sol' constrs\<close>
      unfolding sat_lp_def
      by (auto cong: sat_constr_indep)

    have lp_sol''_f_l: "lp_sol'' (var_f' (f_e l) z) = (MAX xl\<in>doms l. \<Sum>f\<in>E. lp_sol' (restr_f f (z(l \<mapsto> xl)) scopes))"
      if \<open>z \<in> vecs_on scope_e\<close> for z
      by (auto simp: lp_sol''_def that)

    have sat_constrs_max: "sat_lp lp_sol'' (constrs_max E l scopes scope_e)"
      using \<open>finite E\<close> \<open>f_e l \<notin> E\<close> restrict_fun_upd 
      by (subst sat_constr_max_iff) 
        (auto simp: sat_constr_max_iff lp_sol''_f_l image_iff intro!: Max_ge sum.cong)

    have restrict_restrict: "f \<in> E \<Longrightarrow> ((x |` scope_e)(l \<mapsto> xl)) |` (scopes f) = (x (l \<mapsto> xl)) |` (scopes f)" for f x xl
      using scope_e_def E_def restrict_fun_upd  insert_l_scopes
      by (smt (verit, del_insts) Int_insert_right_if1 Map.restrict_restrict UN_I insertCI insert_absorb2 insert_l_scopes restrict_fun_upd)

    have \<open>l < dims\<close>
      by simp

    hence \<open>scope_e \<subseteq> {..<dims}\<close>
      using assms atLeast0LessThan
      by (auto simp: invar_lp_def scope_e_def E_def simp del: \<open>l < dims\<close>)

    hence Dom_restr_scope_e: "x \<in> full_vecs \<Longrightarrow> x |` scope_e \<in> vecs_on scope_e" for x
      by auto

    hence "(\<Sum>f\<in>\<F>'. lp_sol'' (restr_f f x scopes')) \<le> lp_sol'' var_phi"
      if x[simp]: "x \<in> full_vecs" for x
    proof -
      have upd_l_Dom_total: "xl \<in> doms l \<Longrightarrow> x(l \<mapsto> xl) \<in> full_vecs" for xl
        using  x
        unfolding full_vecs_def vecs_on_def partial_vecs_def Map.graph_def
        by auto

      have "sat_lp lp_sol' (constrs_\<F> \<F> scopes)"
        using lp_sol' 
        by auto

      hence "(\<Sum>f\<in>\<F>. lp_sol' (restr_f f (x(l \<mapsto> xl)) scopes)) \<le> lp_sol' var_phi"
        if \<open>xl \<in> doms l\<close> for xl
        using invar_constrs that upd_l_Dom_total
        by (fastforce simp: invar_lp_def sat_lp_def sat_constr_\<F> constrs_\<F>_def)
      hence *: "(\<Sum>f\<in> E. lp_sol' (restr_f f (x(l \<mapsto> xl)) scopes)) \<le> lp_sol' var_phi - (\<Sum>f\<in>\<F> - E. lp_sol' (restr_f f x scopes))"
        if \<open>xl \<in> doms l\<close> for xl
        using E_def that \<open>E \<subseteq> \<F>\<close> \<open>finite \<F>\<close>
        by (auto simp: sum.subset_diff algebra_simps)

      have scope_e_int[simp]: \<open>scope_e \<inter> (scopes f - {l}) = scopes f - {l}\<close> if \<open>f \<in> E\<close> for f
        using that Dom_restr_scope_e 
        by (auto simp: scope_e_def)

      have "lp_sol'' (restr_f (f_e l) x scopes') \<le> lp_sol' var_phi - (\<Sum>f\<in>\<F> - E. lp_sol' (restr_f f x scopes))"
        using \<open>l < dims\<close> ne_dom_dim Dom_restr_scope_e insert_l_scopes
        by (auto simp: lp_sol''_f_l intro!: sum_mono order.trans[OF _ *])+
      thus ?thesis
        using \<F>'_def \<open>f_e l \<notin> \<F>\<close> \<open>finite (\<F> - E)\<close>
        by fastforce
    qed
    hence "sat_lp lp_sol'' (constrs_\<F> \<F>' scopes')"
      unfolding constrs_\<F>_def
      using sat_constr_\<F>
      by blast

    moreover have "sat_lp lp_sol'' constrs'"
      unfolding constrs'_def
      using \<open>sat_lp lp_sol'' constrs\<close> sat_constrs_max
      by auto

    ultimately show ?thesis
      using lp_sol' var_w_eq
      by (auto intro!: exI[of _ lp_sol''])
  qed

  have order_ne: "i \<noteq> j \<Longrightarrow> order i \<noteq> order j" if "i < dims" "j < dims" for i j
    using that order
    unfolding bij_betw_def inj_on_def
    by auto

  have vars_constrs: \<open>vars_lp constrs \<subseteq> lp_vars\<close>
    using invar_constrs invar_lp_def by auto

  have E_subs: \<open>E \<subseteq> \<F>s\<close>
    using assms invar_lp_\<F>s \<open>E \<subseteq> \<F>\<close> by blast

  have scope_e_subs: \<open>scope_e \<subseteq> {..<dims}\<close>
    using assms atLeast0LessThan unfolding invar_lp_def scope_e_def E_def by auto


  have "(\<forall>constr\<in>constrs'. \<forall>z j. Suc i \<le> j \<longrightarrow> j < dims \<longrightarrow> var_f' (f_e (order j)) z \<notin> vars_constr constr)"
    using invar_constrs assms order_ne
    unfolding constrs_max_def constr_max_def vars_constr_def l_def invar_lp_def E_def vars_poly_def constrs'_def
    by (auto simp: f_e_order_notin)

  moreover have \<open>\<F>' \<subseteq> \<F>_init \<union> (\<lambda>i. f_e (order i)) ` {0..<Suc i}\<close>
    using assms(2)
    unfolding invar_lp_def \<F>'_def l_def 
    by auto
  moreover have "constrs_init \<subseteq> constrs'"
    using assms(2)
    unfolding invar_lp_def constrs'_def 
    by auto
  moreover have \<open>(\<forall>f\<in>\<F>'. scopes' f \<subseteq> {0..<dims} - order ` {0..<Suc i})\<close>
  proof -
    have "\<And>f j. j < i \<Longrightarrow> f \<in> \<F> \<Longrightarrow> order j \<notin> scopes f"
      using assms(2)
      unfolding invar_lp_def atLeast0LessThan
      by blast

    thus ?thesis
      using assms(2)
      unfolding invar_lp_def \<F>'_def
      by (auto simp: scope_e_def l_def scopes'_def E_def less_Suc_eq)
  qed
  moreover have \<open>vars_lp constrs' \<subseteq> lp_vars\<close>
    using constrs'_def vars_constrs_max E_subs vars_constrs scope_e_subs
    by (auto simp: vars_lp_def)

  ultimately show "invar_lp constrs' \<F>' scopes' (Suc i)"
    using assms(2)
    unfolding invar_lp_def
    using \<open>\<forall>lp_sol. sat_lp lp_sol (constrs' \<union> constrs_\<F> \<F>' scopes') \<longrightarrow> sat_lp lp_sol explicit_lp\<close>
      ex_sol
    by auto
qed

lemma invar_lp_elim_step_iter:
  assumes 
    "i \<le> dims" 
    "(\<Omega>, \<F>, scopes, n) = ((\<lambda>(\<Omega>, \<F>, scopes, n). elim_step \<Omega> \<F> scopes n) ^^ i) (constrs_init, \<F>_init, scopes_init, 0)"
  shows "invar_lp \<Omega> \<F> scopes n \<and> n = i"
  using invar_init invar_lp_step assms
  by (induction i arbitrary: \<Omega> \<F> scopes n) (auto simp: elim_step_def Let_def split: prod.splits)

lemma invar_lp_elim_vars'_aux:
  assumes "(\<Omega>, \<F>, scopes, n) = elim_vars_aux"
  shows "invar_lp \<Omega> \<F> scopes n \<and> n = dims"
  using assms invar_lp_elim_step_iter 
  unfolding elim_vars_aux_def
  by force

lemma scopes_elim_vars'_aux:
  assumes "(\<Omega>, \<F>, scopes, n) = elim_vars_aux"
  shows "(\<forall>f \<in> \<F>. scopes f = {})"
  using assms invar_lp_elim_vars'_aux[OF assms] order
  unfolding invar_lp_def
  by (auto dest: bij_betw_imp_surj_on)

lemma Dom_total_ne: "full_vecs \<noteq> {}"
proof -
  have \<open>(\<lambda>i. if i < dims then Some (SOME y. y \<in> doms i) else None) \<in> full_vecs\<close>
    unfolding full_vecs_def vecs_on_def partial_vecs_def Map.graph_def
    using ne_dom_dim some_in_eq
    by (auto split: if_splits)
  thus ?thesis 
    by auto
qed

lemma sat_elim_vars'_aux:
  assumes 
    "(\<Omega>, \<F>, scopes, n) = elim_vars_aux" 
  shows "sat_lp lp_sol (constrs_\<F> \<F> scopes) = sat_lp lp_sol {Le (\<lambda>v.
    case v of
      var_f p f z \<Rightarrow> if p = prefix \<and> f \<in> \<F> \<and> z = Map.empty then 1 else 0
    | var_phi \<Rightarrow> -1
    | _ \<Rightarrow> 0) 0}"
  unfolding constrs_\<F>_def constr_\<F>_def restrict_def
  using Dom_total_ne assms
  by (intro arg_cong[where f = \<open>sat_lp lp_sol\<close>]) 
    (auto simp: scopes_elim_vars'_aux intro!: ext split: var_name.splits)

lemma sat_lp_elim_vars'_imp_sat_expl:
  assumes 
    "sat_lp lp_sol elim_vars"
  shows "sat_lp lp_sol explicit_lp"
proof -
  obtain \<Omega> \<F> scopes i where "(\<Omega>, \<F>, scopes, i) = (elim_vars_aux)"
    by (metis surj_pair)
  hence "invar_lp \<Omega> \<F> scopes i"
    using invar_lp_elim_vars'_aux 
    by auto
  hence "(sat_lp lp_sol (\<Omega> \<union> constrs_\<F> \<F> scopes) \<Longrightarrow> sat_lp lp_sol explicit_lp)"
    unfolding invar_lp_def
    by presburger
  thus ?thesis
    using assms sat_elim_vars'_aux \<open>(\<Omega>, \<F>, scopes, i) = elim_vars_aux\<close>[symmetric]
    unfolding gen_constrs_def elim_vars_def
    by (auto simp: sat_lp_def)
qed

lemma sat_lp_expl_imp_elim_vars':
  assumes "sat_lp (lp_sol :: ('x, 'a) var_name \<Rightarrow> _) explicit_lp"
  shows "(\<exists>lp_sol'. lp_sol var_phi = lp_sol' var_phi \<and> (\<forall>i. lp_sol (var_w i) = lp_sol' (var_w i)) \<and> sat_lp lp_sol' elim_vars)"
proof -
  obtain \<Omega> \<F> scopes i where "(\<Omega>, \<F>, scopes, i) = (elim_vars_aux)"
    by (metis surj_pair)
  hence "invar_lp \<Omega> \<F> scopes i"
    using invar_lp_elim_vars'_aux 
    by auto
  hence "\<exists>lp_sol'. lp_sol var_phi = lp_sol' var_phi \<and> (\<forall>i. lp_sol (var_w i) = lp_sol' (var_w i)) \<and> sat_lp lp_sol' (\<Omega> \<union> constrs_\<F> \<F> scopes)" 
    if \<open>sat_lp (lp_sol :: ('x, 'a) var_name \<Rightarrow> _) explicit_lp\<close> for lp_sol
    unfolding invar_lp_def
    using assms that
    by auto
  hence "(\<exists>lp_sol'. lp_sol var_phi = lp_sol' var_phi \<and> (\<forall>i. lp_sol (var_w i) = lp_sol' (var_w i)) \<and> sat_lp lp_sol' (\<Omega> \<union> constrs_\<F> \<F> scopes))"
    using assms by blast
  thus ?thesis
    using assms sat_elim_vars'_aux \<open>(\<Omega>, \<F>, scopes, i) = elim_vars_aux\<close>[symmetric]
    unfolding gen_constrs_def elim_vars_def
    by (fastforce simp: sat_lp_def)
qed

lemma sat_explicit_alt: \<open>sat_lp lp_sol explicit_lp \<longleftrightarrow>
   (\<forall>x \<in> full_vecs. 
    ereal (lp_sol var_phi) \<ge> (\<Sum>i < length C. lp_sol (var_w i) * (fst (C ! i) x)) + (\<Sum>i < length B. fst (B! i) x))\<close>
proof -
  have 1: \<open>x \<in> full_vecs \<Longrightarrow> i < num_c \<Longrightarrow> c_r i x = c i x\<close> for i x
    using scope_c_subs
    unfolding full_vecs_def vecs_on_def
    using atLeast0LessThan 
    by (subst c_r_eq_c) auto

  have 2: \<open>x \<in> full_vecs \<Longrightarrow> i < num_b \<Longrightarrow> b_r i x = b i x\<close> for i x
    using scope_b_subs
    unfolding full_vecs_def vecs_on_def
    using atLeast0LessThan 
    by (subst b_r_eq_b) auto

  have \<open>sat_lp lp_sol explicit_lp \<longleftrightarrow> (\<forall>x\<in>full_vecs. ereal (eval_c (lp_sol \<circ> var_w) x) + eval_b x \<le> ereal (lp_sol var_phi))\<close>
    unfolding sat_explicit_lp_iff
    by auto
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>x\<in>full_vecs. (\<Sum>i<num_c. lp_sol (var_w i) * c i x) + (\<Sum>i<num_b. b i x) \<le> ereal (lp_sol var_phi))\<close>
    unfolding eval_b_def eval_c_def comp_def
    using 1 2
    by (auto simp: eval_c_def eval_b_def num_c_def num_b_def)
  finally show ?thesis
    unfolding num_c_def num_b_def c_def b_def by auto
qed

definition \<open>constr_set lp = {(\<phi>, w). \<exists>lp_sol. sat_lp lp_sol lp \<and> lp_sol var_phi = \<phi> \<and> (\<forall>i. w i = lp_sol (var_w i))}\<close>

lemma constr_set_explicit: \<open>constr_set explicit_lp = {(\<phi>, w).
  (\<forall>x\<in>full_vecs. ereal (\<Sum>i<length C. w i * fst (C ! i) x) + (\<Sum>i<length B. fst (B ! i) x) \<le> ereal \<phi>)}\<close>
  unfolding constr_set_def sat_explicit_alt
  by (auto intro!: exI[of _ \<open>\<lambda>v. case v of var_phi \<Rightarrow> _ | var_w i \<Rightarrow> _ i\<close>])

lemma constr_set_factored_eq: \<open>constr_set (explicit_lp :: (('x, 'a) var_name) constr set) = constr_set elim_vars\<close>
  unfolding constr_set_def
  using sat_lp_elim_vars'_imp_sat_expl
  by (auto dest!:  sat_lp_expl_imp_elim_vars')


lemma constr_set_factored_eq': \<open>{(x var_phi, \<lambda>i. x (var_w i)) |x. x \<in> ({v |v. Ball elim_vars (sat_constr v)})} =
    {(\<phi>, w). \<forall>x\<in>full_vecs. ereal (\<Sum>i<length C. w i * fst (C ! i) x) + (\<Sum>i<length B. fst (B ! i) x) \<le> ereal \<phi>}\<close>
  using constr_set_factored_eq
  unfolding constr_set_explicit
  unfolding constr_set_def
  by auto fastforce

lemma vars_elim_vars_aux: \<open>vars_lp (fst elim_vars_aux) \<subseteq> lp_vars\<close> 
  using invar_lp_elim_vars'_aux
  unfolding invar_lp_def
  by (cases \<open>elim_vars_aux\<close>) auto

lemma elim_vars_aux_\<F>: \<open>fst (snd elim_vars_aux) \<subseteq> \<F>_init \<union> {f_e i | i. i < dims}\<close>
  using invar_lp_elim_vars'_aux
  by (auto simp: invar_lp_def subset_iff image_iff atLeast0LessThan)
    (metis lessThan_iff order_ltI prod.collapse)

lemma empty_in_partial_vecs: \<open>Map.empty \<in> partial_vecs\<close>
  unfolding partial_vecs_def by auto

lemma vars_elim_vars: \<open>vars_lp elim_vars \<subseteq> lp_vars\<close>
proof safe
  fix x
  assume h: \<open>x \<in> vars_lp elim_vars\<close> 
  show \<open>x \<in> lp_vars\<close>
  proof (cases \<open>x \<in> vars_lp (fst elim_vars_aux)\<close>)
    case True
    then show ?thesis 
      using vars_elim_vars_aux 
      by auto
  next
    case False
    hence \<open>x \<in> insert var_phi {var_f' f Map.empty | f. f \<in> fst (snd (elim_vars_aux))}\<close>
      using h 
      by (auto simp: case_prod_unfold elim_vars_def gen_constrs_def vars_lp_def)
    thus \<open>x \<in> lp_vars\<close>
      unfolding lp_vars_def 
      using elim_vars_aux_\<F> empty_in_partial_vecs
      by (auto simp: \<F>_init_def)
  qed
qed
end

locale Factored_LP_Inst =
  fixes 
    prefix_ty :: \<open>'p itself\<close> and
    dom_ty :: \<open>'a itself\<close>
begin

definition \<open>inv_constr = (\<lambda>(cs :: ('p, 'a) var_name constr set, ps :: 'p set). 
  vars_lp cs \<subseteq> {var_name.var_phi} \<union> {var_name.var_w i | i. True} \<union> { var_name.var_f p f x | p f x. p \<in> ps})\<close>

definition \<open>disj_privs c1 c2 \<longleftrightarrow> disj (fst c1) (fst c2)\<close>
definition \<open>union_constr c1 c2 = (fst c1 \<union> fst c2, snd c1 \<union> snd c2)\<close>
lemmas refl[of union_constr, cong]

definition \<open>empty_constr = ({}, {})\<close>
definition \<open>privates = snd\<close>
definition \<open>constr_set cs = {(x var_name.var_phi, (\<lambda>i. x (var_name.var_w i))) | x. x \<in> {v. sat_lp v (fst cs)}}\<close>
lemmas refl[of constr_set, cong]

sublocale Constr_Consts inv_constr union_constr privates empty_constr constr_set .

lemma inv_constr_union[intro!]: \<open>inv_constr cs \<Longrightarrow> inv_constr cs' \<Longrightarrow> inv_constr (union_constr cs cs')\<close>
  unfolding inv_constr_def union_constr_def
  by (auto simp: subset_iff vars_lp_def)+

lemma union_spec: "union_spec"
proof -
  {
    fix cs cs'
    fix sol sol'
    assume \<open>disjnt (privates cs) (privates cs')\<close> \<open>inv_constr cs\<close> \<open>inv_constr cs'\<close>
    assume \<open>sat_lp sol (fst cs)\<close> \<open>sat_lp sol' (fst cs')\<close>
    assume phi: \<open>sol var_name.var_phi = sol' var_name.var_phi\<close>
    assume w: \<open>\<And>i. sol (var_name.var_w i) = sol' (var_name.var_w i)\<close>
    let ?sol = \<open>(\<lambda>x. case x of var_name.var_f p f z \<Rightarrow> if p \<in> snd cs then sol x else sol' x | _ \<Rightarrow> sol x)\<close>

    have 1: \<open>?sol i = sol i\<close> if \<open>i \<in> vars_lp (fst cs)\<close> for i
      using that \<open>inv_constr cs\<close> \<open>disjnt (privates cs) (privates cs')\<close>  \<open>inv_constr cs'\<close>
      by (auto split: var_name.splits simp: privates_def disjnt_def inv_constr_def)
    have 2: \<open>?sol i = sol' i\<close> if \<open>i \<in> vars_lp (fst cs')\<close> for i
      using that \<open>inv_constr cs\<close> \<open>disjnt (privates cs) (privates cs')\<close>  \<open>inv_constr cs'\<close> phi w
      by (auto split: var_name.splits simp: privates_def disjnt_def inv_constr_def subset_iff)+
    have \<open>sat_lp ?sol (fst cs)\<close> \<open>sat_lp ?sol (fst cs')\<close>
      using \<open>sat_lp sol (fst cs)\<close> \<open>sat_lp sol' (fst cs')\<close> sat_lp_indep[OF 1] sat_lp_indep[OF 2]
      by fastforce+
    hence \<open>(sat_lp ?sol (fst (union_constr cs cs')))\<close>
      by (auto simp: union_constr_def)
  }
  thus ?thesis
    using inv_constr_union
    by (auto simp: union_constr_def union_spec_def constr_set_def privates_def case_prod_unfold)
      (metis (no_types, lifting) var_name.case)
qed

lemma empty_constr_spec: \<open>empty_constr_spec\<close>
  unfolding empty_constr_spec_def
  unfolding empty_constr_def privates_def constr_set_def inv_constr_def vars_lp_def vars_constr_def sat_lp_def
  by (auto intro: exI[of _ \<open>\<lambda>v. case v of var_name.var_phi \<Rightarrow> _ | var_name.var_w i \<Rightarrow> _ i \<close>])

end
end