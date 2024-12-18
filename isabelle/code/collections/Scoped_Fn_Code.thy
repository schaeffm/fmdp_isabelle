theory Scoped_Fn_Code
  imports Vec_Code
begin          

record ('f, 'v, 'y, 'natset) scoped_fn_basic_ops =
    scoped_fn_op_\<alpha> :: \<open>'f \<Rightarrow> 'v \<Rightarrow> 'y\<close>
    scoped_fn_op_scope_\<alpha> :: \<open>'f \<Rightarrow> nat set\<close>
    scoped_fn_op_scope :: \<open>'f \<Rightarrow> 'natset\<close>
    scoped_fn_op_from_fn :: \<open>'natset \<Rightarrow> ('v \<Rightarrow> 'y) \<Rightarrow> 'f\<close>
    scoped_fn_op_invar :: \<open>'f \<Rightarrow> bool\<close>
    scoped_fn_op_inst :: \<open>'f \<Rightarrow> 'v \<Rightarrow> 'f\<close>
    scoped_fn_op_eval :: \<open>'f \<Rightarrow> 'f\<close>

locale ScopedFnDefs =
  fixes 
    ops :: \<open>('f, 'v, 'y, 'natset, 'more) scoped_fn_basic_ops_scheme\<close> and
    scoped_fn_op_vec_ops :: "('v, 'x,'natset) vec_ops" and
    scoped_fn_op_vec_ops_scope_ops :: "(nat,'natset) oset_ops" and
    dims :: nat and
    doms :: \<open>nat \<Rightarrow> 'x set\<close>
begin

  abbreviation scoped_\<alpha> where "scoped_\<alpha> == scoped_fn_op_\<alpha> ops"
  abbreviation scoped_scope_\<alpha> where "scoped_scope_\<alpha> == scoped_fn_op_scope_\<alpha> ops"
  abbreviation scope where "scope == scoped_fn_op_scope ops"
  abbreviation invar where "invar == scoped_fn_op_invar ops"
  abbreviation inst where "inst == scoped_fn_op_inst ops"
  abbreviation from_fn where "from_fn == scoped_fn_op_from_fn ops"
  abbreviation vec_ops where \<open>vec_ops \<equiv> scoped_fn_op_vec_ops\<close>
  abbreviation scope_ops where \<open>scope_ops \<equiv> scoped_fn_op_vec_ops_scope_ops\<close>
  abbreviation scoped_eval where \<open>scoped_eval \<equiv> scoped_fn_op_eval ops\<close> 

sublocale Scope: NatSetDefs scope_ops .
sublocale Vec: VecDefs vec_ops scope_ops dims doms .

abbreviation \<open>scope_\<alpha> x \<equiv> Scope.\<alpha> (scope x)\<close>

definition \<open>valid_input_fn s f \<longleftrightarrow> 
  (\<forall>v v'. 
  Scope.\<alpha> s \<subseteq> dom (Vec.\<alpha> v) \<longrightarrow> Vec.invar v \<longrightarrow>
  Scope.\<alpha> s \<subseteq> dom (Vec.\<alpha> v') \<longrightarrow> Vec.invar v' \<longrightarrow> 
  (Vec.\<alpha> v) |` Scope.\<alpha> s = (Vec.\<alpha> v') |` Scope.\<alpha> s \<longrightarrow> 
  f v = f v') \<and> Scope.invar s\<close>

end

locale ScopedFn =
  ScopedFnDefs scoped_fn_ops scoped_fn_op_vec_ops scoped_fn_op_vec_ops_scope_ops dims doms +
  Vec: Vec scoped_fn_op_vec_ops scoped_fn_op_vec_ops_scope_ops dims doms +
  Scope: Set scoped_fn_op_vec_ops_scope_ops
  for scoped_fn_ops :: \<open>('f, 'v,'y, 'natset, 'more) scoped_fn_basic_ops_scheme\<close> and
    scoped_fn_op_vec_ops :: "('v, 'x,'natset) vec_ops" and
    scoped_fn_op_vec_ops_scope_ops :: "(nat,'natset) oset_ops" and 
    dims :: nat and 
    doms :: \<open>nat \<Rightarrow> 'x set\<close> +
assumes

\<comment> \<open>calling a scoped function f with a scope S should be the same as calling with the restriction to S\<close>
    from_dims_scope[simp]: \<open>\<And>s f. valid_input_fn s f \<Longrightarrow> scoped_scope_\<alpha> (from_fn s f) = Scope.\<alpha> s\<close> and
    scoped_from_dims_invar[intro!]: \<open>\<And>s f. valid_input_fn s f \<Longrightarrow> invar (from_fn s f)\<close> and
    scoped_from_dims_apply[simp]: \<open>\<And>s f v. valid_input_fn s f \<Longrightarrow> Vec.vec_on v (Scope.\<alpha> s) \<Longrightarrow> 
      scoped_\<alpha> (from_fn s f) v = f v\<close> and

\<comment> \<open>scope\<close>
    scoped_invar_scope[intro!, simp]: \<open>\<And>f. invar f \<Longrightarrow> Scope.invar (scope f)\<close> and
    scope_eq[simp]: \<open>\<And>f. invar f \<Longrightarrow> scope_\<alpha> f = scoped_scope_\<alpha> f\<close> and

\<comment> \<open>instantiate\<close>
    scoped_inst_invar[simp, intro!]: 
      \<open>\<And>f v. invar f \<Longrightarrow> Vec.invar v \<Longrightarrow> invar (inst f v)\<close> and
    scoped_inst_scope[simp]:
      \<open>\<And>f v. invar f \<Longrightarrow> Vec.invar v \<Longrightarrow> scoped_scope_\<alpha> (inst f v) = scoped_scope_\<alpha> f - Vec.scope_\<alpha> v\<close> and
    scoped_inst_\<alpha>:
      \<open>\<And>f v x. invar f \<Longrightarrow> Vec.invar v \<Longrightarrow> Vec.vec_on x (scoped_scope_\<alpha> f - Vec.scope_\<alpha> v) \<Longrightarrow>
      scoped_\<alpha> (inst f v) x = scoped_\<alpha> f (Vec.vec_inst v x (Scope.inter (Vec.scope v) (scope f)))\<close> and

  scoped_\<alpha>: \<open>\<And>f v v'. 
    invar f \<Longrightarrow> Vec.invar v \<Longrightarrow> Vec.invar v' \<Longrightarrow>
    Vec.\<alpha> v |` scoped_scope_\<alpha> f = Vec.\<alpha> v' |` scoped_scope_\<alpha> f \<Longrightarrow>
    scope_\<alpha> f \<subseteq> dom (Vec.\<alpha> v) \<Longrightarrow>
    scope_\<alpha> f \<subseteq> dom (Vec.\<alpha> v') \<Longrightarrow>
      scoped_\<alpha> f v = scoped_\<alpha> f v'\<close> and
  scoped_apply_eval[simp]: \<open>\<And>f v. invar f \<Longrightarrow> Vec.invar v \<Longrightarrow> scoped_scope_\<alpha> f \<subseteq> dom (Vec.\<alpha> v) \<Longrightarrow> 
  scoped_\<alpha> (scoped_eval f) v = scoped_\<alpha> f v\<close> and
  scope_eval[simp]: \<open>\<And>f. invar f \<Longrightarrow> scoped_scope_\<alpha> (scoped_eval f) = scoped_scope_\<alpha> f\<close> and 
  invar_eval[intro!, simp]: \<open>\<And>f. invar f \<Longrightarrow> invar (scoped_eval f)\<close>

begin

lemma scoped_\<alpha>_restr[simp]: 
  assumes \<open>invar f\<close> \<open>Vec.vec_on v (scoped_scope_\<alpha> f)\<close>
  \<open>scoped_scope_\<alpha> f \<subseteq> Scope.\<alpha> X\<close> \<open>Scope.invar X\<close>
shows \<open>scoped_\<alpha> f v = scoped_\<alpha> f (Vec.restr v (scope f))\<close>
  using assms
  by (auto intro!: scoped_\<alpha>)


lemma set_rel_scope[simp]: \<open>invar f \<Longrightarrow> Scope.set_rel (scope f) X \<longleftrightarrow> scoped_scope_\<alpha> f = X\<close>
  by auto

sublocale Scope: NatSet scope_ops
  using Vec.Scope .

sublocale Vec: Vec vec_ops scope_ops dims doms
  using Vec.Vec_axioms .

end
end