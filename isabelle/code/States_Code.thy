theory States_Code
  imports "collections/Scoped_Fn_Rel"
begin

section \<open>Util\<close>

lemmas  domIff[iff del]

lemma restr_same_eq_iff: \<open>m |` X = m |` Y \<longleftrightarrow> X \<inter> dom m = Y \<inter> dom m\<close>
  unfolding restrict_map_def fun_eq_iff
  by (auto simp: domIff elim!: equalityE )

lemma map_add_eqI: \<open>y = z \<Longrightarrow> x ++ y = x ++ z\<close>
  by auto

lemma map_restr_int_self: \<open>m |` (dom m \<inter> C) = (m |` C)\<close>
  unfolding restr_same_eq_iff
  by auto

lemma ballE: 
  assumes \<open>\<forall>x \<in> X. P x\<close>
  obtains \<open>\<And>x. x \<in> X \<Longrightarrow> P x\<close>
  using assms 
  by auto

lemma allE: 
  assumes \<open>\<forall>x. P x\<close>
  obtains \<open>\<And>x. P x\<close>
  using assms 
  by auto

lemma find_SomeE:
  assumes \<open>find P xs = Some x\<close>
  obtains \<open>x \<in> set xs\<close> \<open>P x\<close>
  by (metis assms find_Some_iff nth_mem)

lemma Some_the[simp]:\<open>x = Some y \<Longrightarrow> P (the x) = P y\<close>
  by auto

lemma ball_diffE: 
  assumes \<open>\<forall>x \<in> X - Y. P x\<close>
  obtains \<open>(\<And>x. x \<in> X \<Longrightarrow> x \<notin> Y \<Longrightarrow> P x)\<close>
  using assms
  by auto

context Vec
begin

definition \<open>state_rel v_code v \<longleftrightarrow>
  (dom v \<subseteq> {..<dims}) \<and>
  (\<forall>i \<in> dom v. the (v i) \<in> doms i) \<and>
  vec_rel (=) v_code v\<close>

lemma state_relE:
  assumes \<open>state_rel v_code v\<close>
  obtains \<open>dom v \<subseteq> {..<dims}\<close> \<open>\<And>i. i \<in> dom v \<Longrightarrow> the (v i) \<in> doms i\<close> \<open>vec_rel (=) v_code v\<close>
  using assms 
  unfolding state_rel_def 
  by auto

lemma state_relD: \<open>state_rel v_code v \<Longrightarrow> \<alpha> v_code = v\<close>
  using vec_rel_eqD
  unfolding state_rel_def 
  by auto

lemma state_relE'[elim]:
  assumes \<open>state_rel v_code v\<close>
  obtains \<open>dom v \<subseteq> {..<dims}\<close> \<open>invar v_code\<close> \<open>\<alpha> v_code = v\<close> \<open>dom (\<alpha> v_code) = dom v\<close>
  using assms state_relD unfolding state_rel_def
  by auto

lemma state_rel_dom[dest]: \<open>state_rel v_code v \<Longrightarrow> dom v \<subseteq> {..<dims}\<close>
  by auto

lemma state_rel_in_doms: \<open>state_rel v_code v \<Longrightarrow> i \<in> dom v \<Longrightarrow> the (v i) \<in> doms i\<close>
  by auto

lemma state_rel_vec_rel: \<open>state_rel v_code v \<Longrightarrow> vec_rel (=) v_code v\<close>
  by (meson state_relE)

lemma state_relI: 
  assumes \<open>dom v \<subseteq> {..<dims}\<close> \<open>\<And>i. i \<in> dom v \<Longrightarrow> the (v i) \<in> doms i\<close> \<open>vec_rel (=) v_code v\<close>
  shows \<open>state_rel v_code v\<close>
  using assms 
  unfolding state_rel_def
  by auto

lemma state_relI'[intro]: 
  assumes \<open>\<alpha> v_code = v\<close> \<open>invar v_code\<close>
  shows \<open>state_rel v_code v\<close>
  using assms 
  by (auto intro!: state_relI simp: domI)

lemma state_rel_empty[simp, intro]: \<open>state_rel empty Map.empty\<close>
  by auto

lemma vec_relE1: \<open>vec_rel P x_code x \<Longrightarrow> i \<in> dom x \<Longrightarrow> i < dims\<close>
  by fastforce

lemma vec_rel_dom_eq[simp]: \<open>vec_rel P x_code x \<Longrightarrow> dom (\<alpha> x_code) = dom x\<close>
  
  by fastforce

lemmas vec_rel_eqD[simp]

lemma vec_relE2: 
  assumes \<open>vec_rel (=) x_code x\<close> \<open>i \<in> dom x\<close> 
  shows \<open>the (x i) \<in> doms i\<close>
proof -
  have \<open>i < dims\<close>
    using assms 
    by fastforce
  moreover have \<open>invar x_code\<close>
    using assms
    by auto
  ultimately show \<open>?thesis\<close>
    using assms
    by auto
qed


lemma vec_rel_id_state[simp]: \<open>vec_rel (=) x_code x \<longleftrightarrow> state_rel x_code x\<close>
  unfolding state_rel_def
  by (auto elim: vec_relE1 vec_relE2)

lemma state_rel_invar[simp, intro]: \<open>state_rel x_code x \<Longrightarrow> invar x_code\<close>
  by auto

lemma state_rel_update[intro!]: \<open>state_rel x_code x \<Longrightarrow> i < dims \<Longrightarrow> y \<in> doms i \<Longrightarrow> 
  state_rel (update x_code i y) (x(i \<mapsto> y))\<close>
  by auto

lemma state_idx_eq[simp, intro]:
  assumes \<open>state_rel x_code x\<close> \<open>i \<in> dom x\<close>
  shows \<open>idx x_code i = the (x i)\<close>
  using assms idx_\<alpha> state_relE' by metis

lemma state_rel_dom'[simp]: \<open>state_rel t_code t \<Longrightarrow> dom (\<alpha> t_code) = dom t\<close>
  using state_relE'.

lemma state_rel_idx[simp]: \<open>state_rel x_code x \<Longrightarrow> (\<alpha> x_code) = x\<close>
  using state_relE'.

(*
lemma invar_domD[dest]: \<open>invar v \<Longrightarrow> dom (\<alpha> v) \<subseteq> {0..<dims}\<close>
  using scope_invar_subs .
*)

lemma invar_idx_in_doms[dest, simp]: \<open>i \<in> dom (\<alpha> v) \<Longrightarrow> invar v \<Longrightarrow> the (\<alpha> v i) \<in> doms i\<close>
  using invar_subs_doms 
  by blast

lemma vec_idxI[intro!]: \<open>invar v \<Longrightarrow> i < dims \<Longrightarrow> \<alpha> v i = Some y \<Longrightarrow> idx v i = y\<close>
  by (metis some_idx domI option.inject)

lemma state_rel_self[simp, intro!]: \<open>invar v \<Longrightarrow> state_rel v (\<alpha> v)\<close>
  by blast

lemmas state_relD[simp]
(*
lemma state_rel_\<alpha>[simp]: \<open>state_rel x y \<Longrightarrow> \<alpha> x = y\<close>
  using state_relE'.
*)

lemma state_rel_invarD[dest]: \<open>state_rel x_code x \<Longrightarrow> invar x_code\<close>
  using state_relE'
  by blast

(* TODO: delete from simpset? might cause slowdown *)
lemmas \<alpha>_some_in_dims[simp]
lemmas \<alpha>_some_in_doms[simp]

lemma state_rel_\<alpha>I: \<open>invar x \<Longrightarrow> \<alpha> x = y \<Longrightarrow> state_rel x y\<close>
  by auto
  
lemma state_rel_iff: \<open>state_rel x y \<longleftrightarrow> invar x \<and> \<alpha> x = y\<close>
  using state_rel_\<alpha>I[of x y]  state_relD[of x y]  state_rel_invarD[of x y]
  by blast

lemmas vec_invar_insert_list[simp]

(*
lemma state_rel_upd[intro!]: \<open>i \<in> doms l \<Longrightarrow> l < dims \<Longrightarrow> state_rel x_code x  \<Longrightarrow>
  state_rel (update x_code l i) (x(l \<mapsto> i))\<close>
  by auto
*)

lemma vec_inst_rel:
  assumes \<open>state_rel x_code x\<close> \<open>state_rel y_code y\<close> \<open>Scope.invar X\<close> \<open>(Scope.\<alpha> X) \<subseteq> dom y\<close>
  shows \<open>state_rel (vec_inst y_code x_code X) (x ++ (y |` Scope.\<alpha> X))\<close>
  using assms
  unfolding state_rel_iff
  by auto


lemma vec_inst_rel':
  assumes \<open>state_rel x_code x\<close> \<open>invar y_code\<close> 
    \<open>\<alpha> y_code |` Scope.\<alpha> X = y |` Scope.\<alpha> X\<close> 
    \<open>Scope.invar X\<close> 
    \<open>Scope.\<alpha> X = dom y\<close>
  shows \<open>state_rel (vec_inst y_code x_code X) (x ++ y)\<close>
  using assms vec_inst_rel[of x_code x y_code \<open>\<alpha> y_code\<close> X] dom_restrict[of \<open>\<alpha> y_code\<close> \<open>Scope.\<alpha> X\<close>]
  by auto

lemma state_rel_idxE:
  assumes \<open>state_rel x_code x\<close>
  obtains \<open>\<And>i. i \<in> dom x \<Longrightarrow> idx x_code i = the (x i)\<close>
  using assms
  by auto
end

context ScopedFn
begin

definition
  \<open>scoped_fn_state_rel R_out f_code f =
  scoped_fn_vec_rel (=) R_out f_code f\<close>
lemmas refl[where t = scoped_fn_state_rel, cong]

lemma scoped_fn_rel:
  assumes \<open>R_in x_code x\<close> \<open>scoped_fn_rel R_in R_out f_code f\<close>
  shows \<open>R_out (scoped_\<alpha> f_code x_code) (fst f x)\<close>
  using assms by fastforce

lemma scoped_fn_vec_rel:
  assumes \<open>Vec.vec_rel R_elem x_code x\<close> \<open>scoped_fn_vec_rel R_elem R_out f_code f\<close> \<open>snd f \<subseteq> dom x\<close>
  shows \<open>R_out (scoped_\<alpha> f_code x_code) (fst f x)\<close>
  using assms by blast

lemma scoped_fn_vec_rel_eq[simp]:
  shows \<open>scoped_fn_vec_rel (=) = scoped_fn_state_rel\<close>
  unfolding scoped_fn_state_rel_def by auto

lemma scoped_fn_state_rel:
  assumes \<open>Vec.state_rel x_code x\<close> \<open>scoped_fn_state_rel R_out f_code f\<close> \<open>snd f \<subseteq> dom x\<close>
  shows \<open>R_out (scoped_\<alpha> f_code x_code) (fst f x)\<close>
  by (meson assms(1) assms(2) assms(3) scoped_fn_state_rel_def scoped_fn_vec_rel Vec.state_rel_vec_rel)

lemma scoped_fn_state_rel_eq[dest, simp]:
  assumes \<open>Vec.state_rel x_code x\<close> \<open>scoped_fn_state_rel (=) f_code f\<close> \<open>snd f \<subseteq> dom x\<close>
  shows \<open>(scoped_\<alpha> f_code x_code) = (fst f x)\<close>
  using scoped_fn_state_rel assms 
  by blast

lemma scoped_fn_state_relD[dest]:
  assumes \<open>scoped_fn_state_rel R_out f_code f\<close> \<open>Vec.state_rel x_code x\<close>  \<open>snd f \<subseteq> dom x\<close>
  shows \<open>R_out (scoped_\<alpha> f_code x_code) (fst f x)\<close>
  using assms scoped_fn_state_rel
  by metis

lemma scoped_fn_state_rel_eqI[intro]:
  assumes \<open>scoped_fn_state_rel (=) f_code fs\<close> \<open>Vec.state_rel x_code x\<close> \<open>snd fs \<subseteq> dom x\<close> \<open>fst fs = f\<close>
  shows \<open>scoped_\<alpha> f_code x_code = f x\<close>
  using assms 
  by blast

lemma scoped_fn_state_relE[elim]:
  assumes
    \<open>scoped_fn_state_rel R_out f_code f\<close>
  obtains
    \<open>invar f_code\<close> and
    \<open>Scope.set_rel (scope f_code) (snd f)\<close> and
    \<open>rel_fun (\<lambda>v v'. Vec.state_rel v v' \<and> snd f \<subseteq> dom v') R_out 
  (scoped_\<alpha> f_code) (fst f)\<close>
  using assms
  unfolding scoped_fn_state_rel_def 
  by (auto simp del: scoped_fn_vec_rel_eq)

lemma scoped_fn_state_relI[intro]:
  assumes 
    \<open>invar f_code\<close> and
    \<open>Scope.set_rel (scope f_code) (snd f)\<close> and
    \<open>rel_fun (\<lambda>v v'. Vec.state_rel v v' \<and> snd f \<subseteq> dom v') R_out 
  (scoped_\<alpha> f_code) (fst f)\<close>
  shows \<open>scoped_fn_state_rel R_out f_code f\<close>
  using assms 
  unfolding scoped_fn_state_rel_def scoped_fn_vec_rel_def
  by auto

lemma scoped_fn_state_relE'[elim, simp]:
  assumes \<open>scoped_fn_state_rel (=) f_code f\<close>
  shows 
    \<open>\<And>x_code x. Vec.state_rel x_code x \<Longrightarrow> snd f \<subseteq> dom x \<Longrightarrow> scoped_\<alpha> (f_code) x_code = fst f x\<close>
    \<open>scoped_scope_\<alpha> f_code = snd f\<close>
    \<open>invar f_code\<close>
  using assms
  by auto

lemma scoped_fn_state_rel_inst:
  assumes \<open>scoped_fn_state_rel (=) f_code f\<close> 
    \<open>snd f - dom t' \<subseteq> dom x\<close> \<open>Vec.state_rel x_code x\<close> \<open>Vec.state_rel t'_code t'\<close> 
  shows \<open>scoped_\<alpha> (inst f_code t'_code) x_code = fst f (x ++ (t' |` snd f))\<close>
  using assms
  by (auto intro!: scoped_fn_state_rel_eq simp: scoped_inst_\<alpha> map_restr_int_self iff del: domIff)

lemma scoped_fn_state_rel_inst': 
  assumes \<open>scoped_fn_state_rel (=) f_code (f, s)\<close> 
    \<open>s - dom t' \<subseteq> dom x\<close> \<open>Vec.state_rel x_code x\<close> \<open>Vec.state_rel t'_code t'\<close> 
  shows \<open>scoped_\<alpha> (inst f_code t'_code) x_code = f (x ++ (t' |` s))\<close>
  using scoped_fn_state_rel_inst[OF assms(1)] assms(2-) 
  by auto

lemma scoped_fn_state_rel_invarD[dest]: \<open>scoped_fn_state_rel R f_code f \<Longrightarrow> invar f_code\<close>
  by auto

lemma scoped_fn_state_rel_scope_eq[simp]: \<open>scoped_fn_state_rel R f_code f \<Longrightarrow> scoped_scope_\<alpha> f_code = snd f\<close>
  by auto

end

(* TODO: find a better/simpler way to relate dims and doms *)
locale States_Code_Transfer = 
  fixes 
    dims :: nat and
    doms :: \<open>nat \<Rightarrow> nat set\<close> and
    
    doms_code :: \<open>nat \<Rightarrow> nat\<close> and
    dims_code :: nat
begin

definition \<open>dims_rel \<longleftrightarrow> nat_rel dims_code dims\<close>

definition \<open>doms_rel = rel_fun (and_rel (=) (\<lambda>x y. y < dims)) (\<lambda>dc d. {..<dc} = d) doms_code doms\<close>

lemma dims_relD[dest!]: \<open>dims_rel \<Longrightarrow> dims_code = dims\<close>
  unfolding dims_rel_def by auto

end

end