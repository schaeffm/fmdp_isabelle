theory Scoped_Fn_Rel
  imports Rel_Util Set_Code Scoped_Fn_Code 
begin

context ScopedFn
begin

definition \<open>scoped_fn_rel R_in R_out f_code f \<longleftrightarrow> 
  invar f_code \<and>
  (Scope.set_rel (scope f_code) (snd f)) \<and>
  (rel_fun R_in R_out (scoped_\<alpha> f_code) (fst f))\<close>

lemma scoped_fn_relE[elim]:
  assumes 
    \<open>scoped_fn_rel R_in R_out f_code f\<close>
  obtains 
    \<open>invar f_code\<close> and
    \<open>Scope.set_rel (scope f_code) (snd f)\<close> and
    \<open>rel_fun R_in R_out (scoped_\<alpha> f_code) (fst f)\<close>
  using assms unfolding scoped_fn_rel_def by auto

lemma scoped_fn_relI[intro]:
  assumes 
    \<open>invar f_code\<close> and
    \<open>Scope.set_rel (scope f_code) (snd f)\<close> and
    \<open>rel_fun R_in R_out (scoped_\<alpha> f_code) (fst f)\<close>
  shows
    \<open>scoped_fn_rel R_in R_out f_code f\<close>
  using assms unfolding scoped_fn_rel_def by auto

definition \<open>scoped_fn_vec_rel R_elem R_out f_code f =
  scoped_fn_rel (\<lambda>v v'. Vec.vec_rel R_elem v v' \<and> snd f \<subseteq> dom v') R_out f_code f\<close>

lemma scoped_fn_vec_relE[elim]:
  assumes 
    \<open>scoped_fn_vec_rel R_elem R_out f_code f\<close>
  obtains 
    \<open>invar f_code\<close> and
    \<open>Scope.set_rel (scope f_code) (snd f)\<close> and
    \<open>rel_fun (\<lambda>v v'. Vec.vec_rel R_elem v v' \<and> snd f \<subseteq> dom v') R_out (scoped_\<alpha> f_code) (fst f)\<close>
  using assms unfolding scoped_fn_vec_rel_def
  by auto

end
end