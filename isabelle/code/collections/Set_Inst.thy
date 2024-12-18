theory Set_Inst
  imports Set_Code
begin

section \<open>Util\<close>

lemma sorted_rev_append: \<open>sorted (rev xs @ [y]) \<longleftrightarrow> sorted (rev xs) \<and> (\<forall>x \<in> set xs. y \<ge> x)\<close>  
  by (subst sorted_wrt_append) auto

text \<open>Encode a set of natural numbers as a natural number (i.e. a bit vector)\<close>
type_synonym bs = nat

text \<open>Bit vector to set\<close>
fun bs_to_list_aux where
\<open>bs_to_list_aux acc i (s :: nat) = (
  if s = 0 then 
    acc
  else 
    bs_to_list_aux (if odd s then i # acc else acc) (Suc i) (s div 2))\<close>

lemmas bs_to_list_aux.simps[simp del]

definition \<open>bs_to_list = bs_to_list_aux [] 0\<close>

text \<open>Abstraction function for bit vectors: set of all indices with value 1\<close>
definition bs_\<alpha> :: "nat \<Rightarrow> nat set" where 
  "bs_\<alpha> l \<equiv> {i. Bit_Operations.bit l i}"

declare [[code abort: bs_\<alpha>]]

definition bs_iteratei :: "nat \<Rightarrow> (nat, 'b) set_iterator"
  where "bs_iteratei x = foldli (bs_to_list x)"

definition bs_iteratei_rev :: "nat \<Rightarrow> (nat, 'b) set_iterator"
  where "bs_iteratei_rev x = foldri (bs_to_list x)"

definition bs_basic_ops :: "(nat, bs) oset_basic_ops" where
  [icf_rec_def]: "bs_basic_ops \<equiv> \<lparr>
    bset_op_\<alpha> = bs_\<alpha>,
    bset_op_invar = \<lambda>_. True,
    bset_op_empty = \<lambda>_. 0,
    bset_op_memb = (\<lambda>x s. Bit_Operations.bit s x),
    bset_op_ins = (\<lambda>x s. Bit_Operations.set_bit x s),
    bset_op_ins_dj = (\<lambda>x s. Bit_Operations.set_bit x s),
    bset_op_delete = (\<lambda>x s. Bit_Operations.unset_bit x s),
    bset_op_list_it = bs_iteratei,
    bset_op_ordered_list_it = bs_iteratei_rev,
    bset_op_rev_list_it = bs_iteratei
    \<rparr>"

section \<open>Correctness proofs\<close>
lemma bs_\<alpha>_0[simp]: \<open>bs_\<alpha> 0 = {}\<close>
  unfolding bs_\<alpha>_def
  by auto

lemma \<open>bit (s div 2) xa \<longleftrightarrow> bit s (Suc xa)\<close>
  by (auto simp: bit_Suc)

lemma even_bit_Suc_iff: \<open>even a \<Longrightarrow> bit (Suc a) n = (bit a n \<or> n = 0)\<close>
  using even_bit_succ_iff 
  by force

lemma bs_\<alpha>_Suc:
  \<open>even s \<Longrightarrow> Suc ` bs_\<alpha> (s div 2) = bs_\<alpha> s\<close>
  \<open>odd s \<Longrightarrow> insert 0 (Suc ` bs_\<alpha> (s div 2)) = bs_\<alpha> s\<close>
  by (auto simp: bs_\<alpha>_def bit_Suc image_iff) (metis bit_0 bit_Suc not0_implies_Suc)+

lemma set_bs_to_list_aux: \<open>set (bs_to_list_aux acc i s) = (\<lambda>j. j + i) ` bs_\<alpha> s \<union> set acc\<close>
proof (induction acc i s rule: bs_to_list_aux.induct)
  case (1 acc i s)
  thus ?case
  proof (cases \<open>s = 0\<close>)
    case True
    then show ?thesis
      by (auto simp: bs_to_list_aux.simps)
  next
    case False
    
  have \<open>set (bs_to_list_aux acc i s) = set (bs_to_list_aux (if odd s then i # acc else acc) (Suc i) (s div 2))\<close>
    using False
    by (subst bs_to_list_aux.simps) auto
  also have \<open>\<dots> = (\<lambda>j. j + i) ` Suc ` bs_\<alpha> (s div 2) \<union> set (if odd s then i # acc else acc)\<close>
    by (subst 1[OF False]) auto
  also have \<open>\<dots> = (\<lambda>j. j + i) ` bs_\<alpha> s \<union> set acc\<close>
    using bs_\<alpha>_Suc[of s]
    by (cases \<open>even s\<close>) (auto simp: image_iff insert_iff gr0_conv_Suc)
  finally show ?thesis .
  qed
qed

lemma distinct_bs_to_list_aux: \<open>distinct acc \<Longrightarrow> set acc \<subseteq> {..<i} \<Longrightarrow> distinct (bs_to_list_aux acc i s)\<close>
 apply (induction acc i s rule: bs_to_list_aux.induct)
 by (subst bs_to_list_aux.simps) (fastforce split: if_splits)

lemma sorted_bs_to_list_aux: \<open>sorted (rev acc) \<Longrightarrow> set acc \<subseteq> {..<i} \<Longrightarrow> sorted (rev (bs_to_list_aux acc i s))\<close>
 apply (induction acc i s rule: bs_to_list_aux.induct)
 by (subst bs_to_list_aux.simps) (fastforce simp: sorted_rev_append split: if_splits)

lemma sorted_bs_to_list: \<open>sorted (rev (bs_to_list s))\<close>
  unfolding bs_to_list_def 
  using sorted_bs_to_list_aux 
  by auto

lemma distinct_bs_to_list: \<open>distinct (bs_to_list s)\<close>
  unfolding bs_to_list_def
  apply (rule distinct_bs_to_list_aux) 
  by auto

lemma set_bs_to_list[simp]: \<open>set (bs_to_list s) = bs_\<alpha> s\<close>
  unfolding bs_to_list_def bs_\<alpha>_def set_bs_to_list_aux
  by auto

lemma bit_imp_ge: \<open>bit (s :: nat) i \<Longrightarrow> s \<ge> 2^i\<close>
  by (metis One_nat_def bit_iff_odd div_less even_Suc leI odd_of_bool_self of_bool_eq(2))

lemma Collect_bit_eq_\<alpha>: \<open>Collect (bit xs) = bs_\<alpha> xs\<close>
  using bs_\<alpha>_def by presburger

lemma finite_bits: \<open>finite ({x. bit (s :: nat) x})\<close>
proof -
  have \<open>\<forall>n' \<ge> s. \<not> bit s n'\<close>
    using bit_imp_ge[of s]
    by (meson leD le_trans less_or_eq_imp_le n_less_equal_power_2)
  hence \<open>{x. bit (s :: nat) x} \<subseteq> {..<s}\<close>
    using not_le_imp_less by blast
  thus ?thesis
    using finite_nat_iff_bounded by blast
qed

lemma bs_iterators_correct:
    \<open>set_iterator (bs_iteratei x) (Collect (bit x))\<close>
    \<open>set_iterator_linord (bs_iteratei_rev x) (Collect (bit x))\<close>
    \<open>set_iterator_rev_linord (bs_iteratei x) (Collect (bit x))\<close>
    unfolding bs_iteratei_def bs_iteratei_rev_def
    using  
      set_iterator_linord_foldri_correct[of \<open>(bs_to_list x)\<close>]
      distinct_bs_to_list 
      Collect_bit_eq_\<alpha>
      sorted_bs_to_list
    by force+

section \<open>Interpretation\<close>
setup Locale_Code.open_block

interpretation bs_basic: StdBasicOSet bs_basic_ops
  unfolding bs_basic_ops_def bs_\<alpha>_def[abs_def]
  by unfold_locales (auto simp: 
              bs_iterators_correct finite_bits
              semiring_bit_operations_class.bit_set_bit_iff
              semiring_bit_operations_class.bit_unset_bit_iff)

setup Locale_Code.close_block

definition [icf_rec_def]: "bs_ops \<equiv> bs_basic.dflt_oops"

setup Locale_Code.open_block

interpretation bs: StdOSet bs_ops
  unfolding bs_ops_def
  using bs_basic.dflt_oops_impl by blast

interpretation bs: StdSet_no_invar bs_ops
  by unfold_locales (simp add: icf_rec_unf)

interpretation SetCode: NatSet \<open>bs_ops\<close>
  by standard

setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "bs"\<close>

lemma pi_bs[proper_it]:
  "proper_it' bs_iteratei bs_iteratei"
  unfolding bs_iteratei_def
  by (intro proper_it'I icf_proper_iteratorI )

lemma pi_bs'[proper_it]:
  "proper_it' bs.iteratei bs.iteratei"
  using Set_Inst.bs.proper .

interpretation pi_bs: proper_it_loc bs_iteratei bs_iteratei
  by unfold_locales (rule pi_bs)

interpretation pi_bs': proper_it_loc bs.iteratei bs.iteratei
  by unfold_locales (rule pi_bs')

end