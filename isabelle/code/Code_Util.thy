theory Code_Util
  imports Main
begin

section \<open>Tail recursive code equation for @{const upt}\<close>

fun upt_aux :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where \<open>upt_aux i j acc = 
  (if i \<ge> j then acc else (let j' = j - 1 in upt_aux i j' (j' # acc)))\<close>

lemmas upt_aux.simps[simp del]

definition \<open>upt_tr i j = upt_aux i j []\<close>

lemma upt_eq_aux: \<open>upt i j @ acc = upt_aux i j acc\<close>
proof (induction \<open>j - i\<close> arbitrary: i j acc)
  case 0
  then show ?case by (simp add: upt_aux.simps)
next
  case (Suc x)
  show ?case
    using Suc[symmetric]
    by (cases j) (auto simp add: upt_aux.simps)
qed

lemmas upt_rec[code del]

lemma upt_tr_code[code]: \<open>upt = upt_tr\<close>
  unfolding upt_tr_def 
  using upt_eq_aux[of _ _ \<open>[]\<close>]
  by auto

fun power_aux :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where \<open>power_aux i (Suc j) acc = 
  (power_aux i j (acc * i))\<close> |
  \<open>power_aux i 0 acc = acc\<close>

definition \<open>power_tr i j = power_aux i j 1\<close>

lemma power_eq_aux: \<open>power i j * acc = power_aux i j acc\<close>
proof (induction j arbitrary: acc)
  case 0
  then show ?case
    by auto
next
  case (Suc x)
  show ?case
    using Suc.IH[of \<open>acc * i\<close>]
    by (auto simp: algebra_simps)
qed

lemma power_tr_code[code_unfold]: \<open>power = power_tr\<close>
  unfolding power_tr_def 
  using power_eq_aux[of _ _ 1]
  by auto

end