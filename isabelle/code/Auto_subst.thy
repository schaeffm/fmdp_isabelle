theory Auto_subst
  imports Main
begin

section \<open>subst attribute for auto\<close>

named_theorems subst
setup \<open>
  let
    fun subst_looper ctxt =
      let
        val thms = Named_Theorems.get ctxt \<^named_theorems>\<open>subst\<close>
      in
        EqSubst.eqsubst_tac ctxt [0] thms
      end
  in
    map_theory_simpset (fn ctxt0 => ctxt0 addloop ("subst looper", subst_looper))
  end
\<close>

setup \<open>
  let
    fun subst_looper ctxt =
      let
        val thms = Named_Theorems.get ctxt \<^named_theorems>\<open>subst\<close>
      in
        EqSubst.eqsubst_asm_tac ctxt [0] thms
      end
  in
    map_theory_simpset (fn ctxt0 => ctxt0 addloop ("subst (asm) looper", subst_looper))
  end
\<close>

end