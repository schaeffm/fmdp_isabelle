theory Scoped_State
  imports 
    Scoped_Fn_Code 
    "HOL-Analysis.Analysis" 
    PMF_Code
begin

record ('f, 'v, 'natset) scoped_fn_real_ops = 
  \<open>('f, 'v, real, 'natset) scoped_fn_basic_ops\<close> +
  scoped_fn_real_op_scale :: \<open>'f \<Rightarrow> real \<Rightarrow> 'f\<close>
  scoped_fn_real_op_diff :: \<open>'f \<Rightarrow> 'f \<Rightarrow> 'f\<close>

locale ScopedStateRealDefs = 
  ScopedFnDefs ops vec_ops set_ops dims doms
  for ops :: \<open>('f, 'v, 'natset) scoped_fn_real_ops\<close>
  and vec_ops :: "('v, nat, 'natset) vec_ops" and set_ops and dims doms
begin
  abbreviation scale where "scale == scoped_fn_real_op_scale ops"
  abbreviation diff where "diff == scoped_fn_real_op_diff ops"
end

locale ScopedStateReal =
  ScopedFn ops vec_ops set_ops dims doms +
  ScopedStateRealDefs ops vec_ops set_ops dims doms
  for
    ops :: \<open>('f, 'v, 'natset) scoped_fn_real_ops\<close>  
    and vec_ops :: "('v, nat, 'natset) vec_ops" 
    and set_ops and dims doms +
  assumes
    \<comment> \<open>scaling functions\<close>
    scale_invar[intro!, simp]: \<open>\<And>f c. invar f \<Longrightarrow> invar (scale f c)\<close> and
    scale_scope[simp]: \<open>\<And>f c. invar f \<Longrightarrow> scoped_scope_\<alpha> (scale f c) = scoped_scope_\<alpha> f\<close> and
    scale_apply[simp]: \<open>\<And>f c x. 
      invar f \<Longrightarrow> 
      Vec.invar x \<Longrightarrow> 
      Scope.\<alpha> (scope f) \<subseteq> Scope.\<alpha> (Vec.scope x) \<Longrightarrow>
      scoped_\<alpha> (scale f c) x = c * scoped_\<alpha> f x\<close> and
    \<comment> \<open>difference\<close>
    diff_invar[intro!, simp]: \<open>\<And>f f'. invar f \<Longrightarrow> invar f' \<Longrightarrow> invar (diff f f')\<close> and
    diff_scope[simp]: \<open>\<And>f f'. 
      invar f \<Longrightarrow> 
      invar f' \<Longrightarrow> 
      scoped_scope_\<alpha> ((diff f f')) = scoped_scope_\<alpha> f \<union> scoped_scope_\<alpha> f'\<close> and
    diff_apply[simp]: \<open>\<And>f f' x. 
      invar f \<Longrightarrow> 
      invar f' \<Longrightarrow>
      Vec.invar x \<Longrightarrow>
      scoped_scope_\<alpha> (diff f f') \<subseteq> Scope.\<alpha> (Vec.scope x) \<Longrightarrow>
      scoped_\<alpha> (diff f f') x = scoped_\<alpha> f x - scoped_\<alpha> f' x\<close>

record ('f, 'v, 'natset) scoped_fn_ereal_ops = 
  \<open>('f, 'v, ereal, 'natset) scoped_fn_basic_ops\<close> +
  scoped_fn_ereal_op_ind :: \<open>'v \<Rightarrow> 'f\<close>

locale ScopedStateERealDefs = 
  ScopedFnDefs ops vec_ops set_ops dims doms
  for ops :: \<open>('f, 'v, 'natset) scoped_fn_ereal_ops\<close>
  and vec_ops :: "('v, nat, 'natset) vec_ops"  and set_ops and dims doms
begin

abbreviation ind where "ind == scoped_fn_ereal_op_ind ops"

end

locale ScopedStateEReal = 
  ScopedFn ops vec_ops set_ops dims doms +
  ScopedStateERealDefs ops vec_ops set_ops dims doms
  for ops :: \<open>('f, 'v, 'natset) scoped_fn_ereal_ops\<close>
  and vec_ops :: "('v, nat, 'natset) vec_ops"  and set_ops and dims doms +
  assumes
    ind_invar[intro!, simp]: \<open>\<And>x. Vec.invar x \<Longrightarrow> invar (ind x)\<close> and
    ind_scope[simp]: \<open>\<And>x. Vec.invar x \<Longrightarrow> scoped_scope_\<alpha> (ind x) = dom (Vec.\<alpha> x)\<close> and
    ind_apply_true:
      \<open>\<And>x y. Vec.invar x \<Longrightarrow> Vec.invar y \<Longrightarrow>
          dom (Vec.\<alpha> x) \<subseteq> dom (Vec.\<alpha> y) \<Longrightarrow>
          Vec.\<alpha> x = Vec.\<alpha> y |` dom (Vec.\<alpha> x) \<Longrightarrow>
          scoped_\<alpha> (ind x) y = -\<infinity>\<close> and
    ind_apply_false: 
      \<open>\<And>x y. Vec.invar x \<Longrightarrow> Vec.invar y \<Longrightarrow>
          dom (Vec.\<alpha> x) \<subseteq> dom (Vec.\<alpha> y) \<Longrightarrow>
          Vec.\<alpha> x \<noteq> Vec.\<alpha> y |` dom (Vec.\<alpha> x) \<Longrightarrow>
          scoped_\<alpha> (ind x) y = 0\<close>

locale ScopedStatePmfDefs = 
  ScopedFnDefs ops vec_ops set_ops dims doms
  for ops :: \<open>('f, 'v, 'pmf, 'set) scoped_fn_basic_ops\<close> 
  and scoped_fn_pmf_ops :: \<open>('pmf, nat, 'pmf_set) pmf_ops\<close>
  and vec_ops :: \<open>('v, nat, 'set) vec_ops\<close>
  and set_ops
  and pmf_set_ops :: \<open>(nat, 'pmf_set) oset_ops\<close>
  and dims doms

begin
abbreviation pmf_ops where "pmf_ops == scoped_fn_pmf_ops"

sublocale Pmf: PmfDefs pmf_ops pmf_set_ops .
end

locale ScopedStatePmf = 
  ScopedFn ops vec_ops set_ops dims doms +
  ScopedStatePmfDefs ops scoped_fn_pmf_ops vec_ops set_ops pmf_set_ops dims doms
  for ops :: \<open>('f, 'v, 'pmf, 'set) scoped_fn_basic_ops\<close> 
  and scoped_fn_pmf_ops :: \<open>('pmf, nat, 'pmf_set) pmf_ops\<close>
  and vec_ops :: "('v, nat, 'set) vec_ops" and set_ops :: \<open>(nat, 'set) oset_ops\<close> and pmf_set_ops and
  dims :: nat and
  doms :: \<open>nat \<Rightarrow> nat set\<close> +
assumes 
  Pmf: \<open>Pmf scoped_fn_pmf_ops pmf_set_ops\<close>
begin

sublocale Pmf: Pmf pmf_ops pmf_set_ops
  using Pmf .

end


record ('rf, 'ef) scoped_fn_to_ereal_ops = 
  scoped_fn_to_ereal_op_to_ereal :: \<open>'rf \<Rightarrow> 'ef\<close>

locale ScopedFnToErealDefs =
  fixes
    ops :: \<open>('rf, 'ef) scoped_fn_to_ereal_ops\<close> and
    real_ops :: \<open>('rf, 'v, 'set) scoped_fn_real_ops\<close> and
    ereal_ops :: \<open>('ef, 'v, 'set) scoped_fn_ereal_ops\<close> and
    vec_ops :: \<open>('v, nat, 'set) vec_ops\<close> and
    set_ops :: \<open>(nat, 'set) oset_ops\<close> and
    dims :: nat and
  doms :: \<open>nat \<Rightarrow> nat set\<close>
begin
  
abbreviation scoped_state_real_ops 
    where "scoped_state_real_ops == real_ops"

abbreviation scoped_state_ereal_ops 
    where "scoped_state_ereal_ops == ereal_ops"

abbreviation to_ereal 
    where "to_ereal == scoped_fn_to_ereal_op_to_ereal ops"


print_locale ScopedStateRealDefs
sublocale SR: ScopedStateRealDefs scoped_state_real_ops vec_ops set_ops dims doms .
sublocale SE: ScopedStateERealDefs scoped_state_ereal_ops vec_ops set_ops dims doms .

end

locale ScopedFnToEreal =
  ScopedFnToErealDefs ops real_ops ereal_ops vec_ops set_ops dims doms +
    SR: ScopedStateReal scoped_state_real_ops vec_ops set_ops dims doms +
    SE: ScopedStateEReal scoped_state_ereal_ops vec_ops set_ops dims doms
  for ops real_ops ereal_ops vec_ops set_ops dims doms +
  assumes
    to_ereal_invar[simp, intro]: \<open>\<And>f. SR.invar f \<Longrightarrow> SE.invar (to_ereal f)\<close> and
    to_ereal_scope[simp]: \<open>\<And>f. SR.invar f \<Longrightarrow> SE.scoped_scope_\<alpha> (to_ereal f) = SR.scoped_scope_\<alpha> f\<close> and
    to_ereal_apply[simp]: \<open>\<And>f x. SR.invar f \<Longrightarrow> 
    SR.scoped_scope_\<alpha> f \<subseteq> dom (SR.Vec.\<alpha> x) \<Longrightarrow> SR.Vec.invar x  \<Longrightarrow>
    SE.scoped_\<alpha> (to_ereal f) x = SR.scoped_\<alpha> f x\<close>


end