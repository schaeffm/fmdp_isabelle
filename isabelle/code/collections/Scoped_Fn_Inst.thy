theory Scoped_Fn_Inst
  imports 
    Scoped_Fn_Code
    "HOL-Library.IArray"
    "HOL-Analysis.Analysis"
begin

section \<open>Util\<close>
lemma ballE':
  assumes \<open>\<forall>x \<in> X. P x\<close>
  obtains \<open>\<And>x. x \<in> X \<Longrightarrow> P x\<close>
  using assms by auto

lemma restr_eq_imp_eq_on:
  assumes \<open>m |` dom m' = m'\<close>
  obtains \<open>\<And>i. i \<in> dom m' \<Longrightarrow> m i = m' i\<close>
  using assms
  unfolding restrict_map_def
  by (smt (verit))

lemma eq_restr_imp_eq_on:
  assumes \<open>m' = m |` dom m'\<close>
  obtains \<open>\<And>i. i \<in> dom m' \<Longrightarrow> m i = m' i\<close>
  using assms
  unfolding restrict_map_def
  by (smt (verit))

lemma fun_neqE:
  assumes \<open>f \<noteq> g\<close>
  obtains x where \<open>f x \<noteq> g x\<close>
  using assms
  by auto

lemma restric_map_if: \<open>(m |` d) x = (if x \<in> d then m x else None)\<close>
  unfolding Map.restrict_map_def
  by auto

lemma ex_dom_iff: \<open>(\<exists>x \<in> dom m. P x) \<longleftrightarrow> (\<exists>x. m x \<noteq> None \<and> P x)\<close>
  by auto

section \<open>Scoped Fn Instantiation\<close>

text \<open>
Scoped Functions based on nested arrays.
Each level stores the variable index + a nested array.
Scopes are stored explicitly at the outermost level for efficiency.
\<close>

text \<open>Some lemmas to help with termination proofs.\<close>
lemma size_iarray_eq: \<open>size_iarray size xs = 
  sum_list (map size (IArray.list_of xs)) + Suc (IArray.length xs)\<close>
  by (cases xs) (auto simp: size_list_conv_sum_list)

lemma size_x_less[termination_simp]: 
  \<open>x \<in> set (IArray.list_of xs) \<Longrightarrow> size x < size_iarray size xs\<close>
  using member_le_sum_list[of \<open>size x\<close> \<open>map size (IArray.list_of xs)\<close>]
  by (auto simp: size_iarray_eq)


type_synonym ('v, 'y, 's) scoped_fn = \<open>('v \<Rightarrow> 'y) \<times> 's\<close>

definition scoped_apply :: "('v, 'y, 's) scoped_fn \<Rightarrow> 'v \<Rightarrow> 'y" where
  \<open>scoped_apply f v = (fst f) v\<close>

definition scoped_scope :: "('v, 'y, 'natset) scoped_fn \<Rightarrow> 'natset" where
  \<open>scoped_scope f = snd f\<close>

definition scoped_scale :: \<open>('v, 'y :: times, 'natset) scoped_fn \<Rightarrow> 'y \<Rightarrow> ('v, 'y, 'natset) scoped_fn\<close> where
  \<open>scoped_scale f c = (\<lambda>v. (fst f) v * c, snd f)\<close>

definition scoped_from_fn :: "'natset \<Rightarrow> ('v \<Rightarrow> 'y) \<Rightarrow> ('v, 'y, 'natset) scoped_fn" where
 \<open>scoped_from_fn s f = (f, s)\<close>

datatype ('a) Scoped_Tree =
  Scoped_Leaf \<open>'a\<close> |
  Scoped_Node nat \<open>('a Scoped_Tree) iarray\<close>


setup Locale_Code.open_block

locale Scoped_Fn_Impl =
  Vec vec_ops set_ops
  for
  vec_ops :: \<open>('v, nat, 'natset) vec_ops\<close> and
  set_ops :: \<open>(nat, 'natset) oset_ops\<close> and
  doms_fn :: \<open>nat \<Rightarrow> nat\<close> +
  fixes out :: \<open>'y itself\<close>
assumes
  doms_eq: \<open>\<And>i. i < dims \<Longrightarrow> doms = (\<lambda>i. {0..<doms_fn i})\<close> and
  vec_invar_doms: \<open>\<And>v i. invar v \<Longrightarrow> i \<in> Scope.\<alpha> (scope v) \<Longrightarrow> idx v i < doms_fn i\<close> 
begin

lemmas vec_onI[intro!, simp]

definition scoped_inst :: \<open>('v, 'z, 'natset) scoped_fn \<Rightarrow> 'v \<Rightarrow> ('v, 'z, 'natset) scoped_fn\<close> where
  \<open>scoped_inst f v = (
    let s = Scope.inter (scope v) (scoped_scope f) in 
    (\<lambda>v'. (fst f) (vec_inst v v' s)), Scope.diff (scoped_scope f) (scope v))\<close>

definition \<open>scoped_to_ereal f = (ereal o (fst f), scoped_scope f)\<close>

fun scoped_base_apply :: "'y Scoped_Tree \<Rightarrow> 'v \<Rightarrow> 'y"  where
  \<open>scoped_base_apply (Scoped_Leaf x) v = x\<close>
| \<open>scoped_base_apply (Scoped_Node i arr) v =
  (let j = idx v i in
    if j < IArray.length arr then
      scoped_base_apply (IArray.sub arr j) v else undefined)\<close>

fun eval_list where
  \<open>eval_list f x [] = Scoped_Leaf (f x)\<close>
| \<open>eval_list f x (i#is) = 
   Scoped_Node i (IArray (map (\<lambda>z. eval_list f (update x i z) is) [0..<doms_fn i]))\<close>

definition \<open>scoped_eval sf = 
  (let
    (f, s) = sf;
    arr = eval_list f empty (Scope.to_list s);
    f' = scoped_base_apply arr
 in
  (f', s))\<close>

abbreviation \<open>scoped_scope_\<alpha> f \<equiv> Scope.\<alpha> (scoped_scope f)\<close>

definition \<open>scoped_invar f \<longleftrightarrow> (\<forall>v v'.
  invar v \<longrightarrow> invar v' \<longrightarrow>
  scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v) \<longrightarrow>
  scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v') \<longrightarrow>
  (\<alpha> v) |` (scoped_scope_\<alpha> f) = (\<alpha> v') |` (scoped_scope_\<alpha> f) \<longrightarrow> 
  scoped_apply f v = scoped_apply f v') \<and>
 Scope.invar (scoped_scope f)\<close>

definition [icf_rec_def]: \<open>scoped_fn_ops = \<lparr> 
  scoped_fn_op_\<alpha> = scoped_apply,
  scoped_fn_op_scope_\<alpha> = scoped_scope_\<alpha>,
  scoped_fn_op_scope = scoped_scope,
  scoped_fn_op_from_fn = scoped_from_fn,
  scoped_fn_op_invar = scoped_invar,
  scoped_fn_op_inst = scoped_inst,
  scoped_fn_op_eval = scoped_eval
  \<rparr>\<close>

subsection \<open>Properties\<close>

lemma scoped_base_apply_eval_list:
  assumes \<open>\<alpha> v' |` (set xs \<union> dom (\<alpha> x)) = ((\<alpha> x ++ (\<alpha> v |` set xs)) |` (set xs \<union> dom (\<alpha> x)))\<close> \<open>invar v\<close> \<open>invar v'\<close> \<open>invar x\<close> \<open>set xs \<subseteq> {..<dims}\<close>
    \<open>\<And>v v'. invar v \<Longrightarrow> invar v' \<Longrightarrow>
  set xs \<union> dom (\<alpha> x) \<subseteq> dom (\<alpha> v)  \<Longrightarrow>
  set xs \<union> dom (\<alpha> x) \<subseteq> dom (\<alpha> v')  \<Longrightarrow>
  (\<alpha> v) |` (set xs \<union> dom (\<alpha> x)) = (\<alpha> v') |` (set xs \<union> dom (\<alpha> x)) \<Longrightarrow>
  f v = f v'\<close>
  \<open>distinct xs\<close>
  \<open>set xs \<subseteq> dom (\<alpha> v)\<close>
  shows \<open>scoped_base_apply (eval_list f x xs) v = f v'\<close>
  using assms
proof (induction xs arbitrary: f x v v')
  case Nil
  show ?case
    using Nil(1-5)
    by (auto intro!: Nil(6) elim!: restr_eq_imp_eq_on)
next
  case (Cons a xs)
  have idx_a: \<open>idx v a < doms_fn a\<close>
    using vec_invar_doms Cons 
    by fastforce+

  have idx_v_a[simp]: \<open>idx v a = the (\<alpha> v a)\<close>
    using Cons 
    by auto
    
  have \<alpha>_upd[simp]: \<open>\<alpha> (update x a (the (\<alpha> v a))) = (\<alpha> x)(a \<mapsto> (the (\<alpha> v a)))\<close>
        using Cons
        by auto

  have \<open>scoped_base_apply (eval_list f x (a # xs)) v = scoped_base_apply (eval_list f (update x a (idx v a)) xs) v\<close>
    using idx_a
    by auto
  also have \<open>\<dots> = f v'\<close>
    proof (rule "Cons.IH", goal_cases)
      case 1
      have \<open>\<alpha> x i = Some y \<Longrightarrow> \<alpha> v' i = ((\<alpha> x)(a \<mapsto> (the (\<alpha> v a))) ++ \<alpha> v |` set xs) i\<close> for i y
        using Cons(2,9)
        by (cases \<open>i \<in> set xs\<close>) (auto simp: restrict_map_eq_iff  elim!: ballE')
      thus ?case
        unfolding restrict_map_eq_iff
        using Cons(2,8,9)
        by (auto split: option.splits simp: restrict_map_eq_iff elim!: ballE')
    next
      case (6 v v')
      thus ?case
        by (intro Cons.prems(6)) (auto)
    qed (insert Cons, auto)
    finally show ?case .
qed

lemma scoped_base_apply_eval_list':
  assumes \<open>invar v\<close> \<open>set xs \<subseteq> {..<dims}\<close>
    \<open>\<And>v v'. invar v \<Longrightarrow> invar v' \<Longrightarrow>
  set xs \<subseteq> dom (\<alpha> v)  \<Longrightarrow>
  set xs \<subseteq> dom (\<alpha> v')  \<Longrightarrow>
  (\<alpha> v) |` set xs = (\<alpha> v') |` set xs \<Longrightarrow>
  f v = f v'\<close>
  \<open>distinct xs\<close>
  \<open>set xs \<subseteq> dom (\<alpha> v)\<close>
shows \<open>scoped_base_apply (eval_list f empty xs) v = f v\<close>
  by (intro scoped_base_apply_eval_list[of v xs empty v f]) (auto intro!: assms)

lemma scoped_invarI[intro]:
  assumes 
    \<open>\<And>v v'.
  invar v \<Longrightarrow> invar v' \<Longrightarrow>
  scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v) \<Longrightarrow>
  scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v') \<Longrightarrow>
  (\<alpha> v) |` (scoped_scope_\<alpha> f) = (\<alpha> v') |` (scoped_scope_\<alpha> f) \<Longrightarrow>
  scoped_apply f v = scoped_apply f v'\<close>
    \<open>Scope.invar (scoped_scope f)\<close> 
  shows \<open>scoped_invar f\<close>
  using assms 
  unfolding scoped_invar_def
  apply safe
  by blast
  

lemma scoped_scope_snd[simp]: \<open>scoped_scope (a,b) = b\<close>
  unfolding scoped_scope_def by auto

lemma scoped_apply_restr[intro!]:
  assumes 
    \<open>scoped_invar f\<close>  \<open>invar v\<close> \<open>invar v'\<close> 
    \<open>scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v)\<close>
    \<open>scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v')\<close>
    \<open>\<alpha> v |` scoped_scope_\<alpha> f = \<alpha> v' |` scoped_scope_\<alpha> f\<close>
  shows \<open>scoped_apply f v = scoped_apply f v'\<close>
  using assms scoped_invar_def 
  by blast

lemma scope_eval[simp]: \<open>(scoped_scope_\<alpha> (scoped_eval f)) = scoped_scope_\<alpha> f\<close>
  unfolding scoped_scope_def scoped_eval_def Let_def
  by (auto simp: case_prod_beta)

lemma scope_from_dims[simp]: \<open>scoped_scope_\<alpha> (scoped_from_fn s f) = Scope.\<alpha> s\<close>
  unfolding scoped_from_fn_def 
  by (auto simp: Let_def)

lemma vec_to_list_map:
  assumes \<open>invar v\<close>
  shows \<open>vec_to_list v = map (\<lambda>i. if i \<in> Scope.\<alpha> (scope v) then Some (idx v i) else None) [0..<dims]\<close>
  unfolding list_eq_iff_nth_eq 
  using assms 
  by auto

lemma scoped_apply_eq_fst[simp]: \<open>scoped_apply (f,s) = f\<close>
  unfolding scoped_apply_def 
  by auto

lemma scoped_from_dims_correct[simp]:
  \<open>scoped_apply (scoped_from_fn s f) v = f v\<close>
  by (simp add: scoped_from_fn_def)

lemma scoped_scope_invar[intro!, simp]: \<open>scoped_invar f \<Longrightarrow> Scope.invar (scoped_scope f)\<close>
  unfolding scoped_invar_def 
  by auto

lemma scope_inst[simp]: \<open>scoped_invar f \<Longrightarrow>
    invar v \<Longrightarrow> Scope.\<alpha> (scoped_scope (scoped_inst f v)) = Scope.\<alpha> (scoped_scope f) - Scope.\<alpha> (scope v)\<close>
  unfolding scoped_inst_def Let_def 
  by auto

(* lemmas scoped_invar_def[code del] *)

lemma scoped_inst_scope_invar:
  assumes \<open>scoped_invar f\<close> \<open>invar v\<close> 
  shows \<open>Scope.invar (scoped_scope (scoped_inst f v))\<close>
  unfolding scoped_inst_def Let_def 
  using assms 
  by auto

lemma scoped_apply_inst: \<open>scoped_apply (scoped_inst f v) v' = 
  scoped_apply f (vec_inst v v' (Scope.inter (scope v) (scoped_scope f)))\<close>
  unfolding scoped_inst_def Let_def scoped_apply_def 
  by simp

(*
lemma out_invarI[intro!]:
  assumes \<open>scoped_invar f\<close> \<open>invar v\<close> \<open>scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v)\<close>
  shows \<open>out_invar (scoped_apply f v)\<close>
  using assms
  unfolding scoped_invar_def
  by blast
*)

lemma scoped_invar_inst[intro!]: 
  assumes \<open>scoped_invar f\<close> \<open>invar v\<close> 
  shows \<open>scoped_invar (scoped_inst f v)\<close>
  apply (rule scoped_invarI)
  subgoal
    using assms
    unfolding scoped_inst_def Let_def scoped_apply_def[symmetric]
    apply simp
  apply (rule scoped_apply_restr)
    by (auto simp: domIff Map.map_add_def restrict_map_eq_iff split: option.splits)
  using assms 
    unfolding  scoped_inst_def scoped_apply_def[symmetric]
    by auto
(*
  subgoal
    using assms
    unfolding  scoped_inst_def scoped_apply_def[symmetric]
    apply simp
    apply rule
    by auto
  subgoal
    using assms scoped_inst_scope_invar by presburger
  done
*)

lemma scope_invar_eval[intro!]: \<open>scoped_invar f \<Longrightarrow> Scope.invar (scoped_scope (scoped_eval f))\<close>
  unfolding scoped_invar_def scoped_eval_def Let_def case_prod_unfold scoped_scope_def
  by auto

lemma scoped_apply_eval[simp]:
  assumes \<open>scoped_invar f\<close> \<open>invar v\<close> \<open>scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> v)\<close>
  shows \<open>scoped_apply (scoped_eval f) v = scoped_apply f v\<close>  
  unfolding scoped_eval_def Let_def case_prod_unfold scoped_apply_def fst_conv
  using assms
  by (intro scoped_base_apply_eval_list') (auto simp: scoped_apply_def[symmetric] scoped_scope_def[symmetric])

lemma scoped_eval_invar[intro!]: \<open>scoped_invar f \<Longrightarrow> scoped_invar (scoped_eval f)\<close>
  using scoped_apply_eval scope_invar_eval
  using scoped_invar_def
  by (metis scope_eval)



subsection \<open>Interpretation\<close>

sublocale SF: ScopedFnDefs scoped_fn_ops vec_ops set_ops dims doms .

lemma invar_scoped_from_dims[intro!]:
  assumes \<open>SF.valid_input_fn s f\<close> 
  shows \<open>scoped_invar (scoped_from_fn s f)\<close>
  using assms
  unfolding scoped_invar_def scoped_from_fn_def SF.valid_input_fn_def
  by (metis scoped_apply_eq_fst scoped_scope_snd)

sublocale SF: ScopedFn scoped_fn_ops vec_ops set_ops dims doms
  unfolding scoped_fn_ops_def
  using scoped_apply_inst
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (simp add: scoped_apply_inst)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

(*
sublocale noArith: ScopedFn scoped_fn_ops vec_ops set_ops dims doms
  using SF.ScopedFn_axioms .
*)
end

setup Locale_Code.close_block

locale Scoped_Fn_Impl_Arith =
  Scoped_Fn_Impl +
  constrains out :: \<open>'y::{minus,plus,times} itself\<close> and
  vec_ops :: \<open>('v, nat, 'natset) vec_ops\<close> and
  set_ops :: \<open>(nat, 'natset) oset_ops\<close>
begin
lemma scoped_scale_invar[intro!, simp]: \<open>scoped_invar f \<Longrightarrow> scoped_invar (scoped_scale f c)\<close>
  unfolding scoped_scale_def scoped_invar_def scoped_apply_def
  by auto (metis scoped_scope_def)+

definition scoped_diff :: \<open>
  ('v, 'y, 'natset) scoped_fn 
  \<Rightarrow> ('v, 'y, 'natset) scoped_fn 
  \<Rightarrow> ('v, 'y, 'natset) scoped_fn\<close> where
  \<open>scoped_diff f1 f2 = (fst f1 - fst f2, Scope.union (scoped_scope f1) (scoped_scope f2))\<close>

lemma scoped_scale_scope[simp]: 
  \<open>scoped_invar f \<Longrightarrow> scoped_scope_\<alpha> (scoped_scale f c) = scoped_scope_\<alpha> f\<close>
  unfolding scoped_scale_def scoped_invar_def scoped_apply_def scoped_scope_def
  by auto

lemma scoped_scale_apply[simp]:
  \<open>scoped_invar f \<Longrightarrow> scoped_apply (scoped_scale f c) x = scoped_apply f x * c\<close>
  unfolding scoped_scale_def scoped_invar_def scoped_apply_def scoped_scope_def
  by simp

lemma scoped_diff_apply[simp]: \<open>scoped_apply (scoped_diff f f') x = scoped_apply f x - scoped_apply f' x\<close>
  unfolding scoped_apply_def scoped_diff_def
  by simp

lemma scoped_\<alpha>_diff[simp]: 
  \<open>scoped_invar f \<Longrightarrow> scoped_invar f' \<Longrightarrow> 
  scoped_scope_\<alpha> (scoped_diff f f') = scoped_scope_\<alpha> f \<union> scoped_scope_\<alpha> f'\<close>
  unfolding scoped_diff_def
  by simp

lemma scoped_diff_invar[intro!, simp]: \<open>scoped_invar f \<Longrightarrow> scoped_invar f' \<Longrightarrow>
  scoped_invar (scoped_diff f f')\<close>
  by (intro scoped_invarI) (auto simp: scoped_diff_def scoped_apply_def[symmetric] intro!: arg_cong2[where f = \<open>(-)\<close>])
end

locale Scoped_Fn_Impl_Real =
  Scoped_Fn_Impl_Arith +
  constrains out :: \<open>real itself\<close> and
  vec_ops :: \<open>('v, nat, 'natset) vec_ops\<close> and
  set_ops :: \<open>(nat, 'natset) oset_ops\<close>
begin

lemma scoped_to_ereal_invar: \<open>scoped_invar f \<Longrightarrow> scoped_invar (scoped_to_ereal f)\<close>
  unfolding scoped_to_ereal_def scoped_invar_def 
  apply auto
  by (metis scoped_apply_def)


lemma scoped_to_ereal_scope[simp]: \<open>scoped_invar f \<Longrightarrow> scoped_scope_\<alpha> (scoped_to_ereal f) = scoped_scope_\<alpha> f\<close>
  unfolding scoped_to_ereal_def
  by auto

lemma scoped_to_ereal_apply: 
  \<open>scoped_invar f \<Longrightarrow> scoped_scope_\<alpha> f \<subseteq> dom (\<alpha> x) \<Longrightarrow> invar x \<Longrightarrow> scoped_apply (scoped_to_ereal f) x = 
  ereal (scoped_apply f x)\<close>
  unfolding scoped_to_ereal_def scoped_apply_def
  by auto
end

locale Scoped_Fn_Impl_Ereal =
  Scoped_Fn_Impl_Arith +
  constrains out :: \<open>ereal itself\<close> and
  vec_ops :: "('v, nat, 'natset) vec_ops" and
  set_ops :: \<open>(nat, 'natset) oset_ops\<close>
begin

definition scoped_ind :: \<open>'v \<Rightarrow> ('v, ereal, 'natset) scoped_fn\<close> where
  \<open>scoped_ind v = scoped_eval 
  ((\<lambda>v'. if Scope.ball (scope v) (\<lambda>i. idx v i = idx v' i) then -\<infinity> else 0),
  (scope v))\<close>

lemma scoped_invar_if_ind: 
  \<open>invar x \<Longrightarrow>
  scoped_invar (\<lambda>v'. if \<forall>xa\<in>dom (\<alpha> x). the (\<alpha> x xa) = idx v' xa then - \<infinity> else 0, scope x)\<close>
  by (rule scoped_invarI) (auto simp: domIff subset_iff)

lemma scoped_invar_ind[intro!, simp]: \<open>invar v \<Longrightarrow> scoped_invar (scoped_ind v)\<close>
  unfolding scoped_ind_def 
  using scoped_invar_if_ind 
  by auto

lemma scoped_ind_\<alpha>[simp]: \<open>invar x \<Longrightarrow> scoped_scope_\<alpha> (scoped_ind x) = dom (\<alpha> x)\<close>
  by (auto simp: scoped_ind_def)

lemma scoped_ind_cons: \<open>invar x \<Longrightarrow> invar y \<Longrightarrow> dom (\<alpha> x) \<subseteq> dom (\<alpha> y) \<Longrightarrow> \<alpha> x = \<alpha> y |` dom (\<alpha> x) \<Longrightarrow> 
  scoped_apply (scoped_ind x) y = - \<infinity>\<close>
  unfolding scoped_ind_def
  by (auto simp: scoped_invar_if_ind subset_iff elim!: eq_restr_imp_eq_on)

lemma scoped_ind_ncons: \<open>invar x \<Longrightarrow> invar y \<Longrightarrow> dom (\<alpha> x) \<subseteq> dom (\<alpha> y) \<Longrightarrow> \<alpha> x \<noteq> \<alpha> y |` dom (\<alpha> x) \<Longrightarrow> 
  scoped_apply (scoped_ind x) y = 0\<close>
  unfolding scoped_ind_def
  by (fastforce simp: scoped_invar_if_ind subset_iff restric_map_if ex_dom_iff elim!: fun_neqE split: if_splits)

end
end