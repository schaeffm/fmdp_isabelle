theory LP_Cert_Code
  imports 
    "../API_Code"
    "Collections.Collections" 
    "Collections.Code_Target_ICF" 
    "LP_File_Certification"
    "Deriving.Hash_Instances"
    "../Code_Setup"
    "../collections/Vec_Inst"
    "../collections/Set_Inst"
    "Collections.RBTSetImpl"
    "Collections.ArrayMapImpl"
    "../collections/Pmf_Inst"
    "HOL-Data_Structures.AList_Upd_Del"
begin

lemma A_List_map_of_eq_map_of[simp]: \<open>AList_Upd_Del.map_of = Map.map_of\<close>
proof
  fix xs  
  show \<open>AList_Upd_Del.map_of xs = Map.map_of xs\<close>
    by (induction xs) auto
qed

class lin_equal = linorder + equal

instantiation RBT.rbt :: (lin_equal , equal) equal
begin

definition \<open>equal_rbt (x :: ('a, 'b) RBT.rbt) y \<longleftrightarrow>  
  equal_class.equal (RBT.impl_of x) (RBT.impl_of y)\<close>

instance 
  apply standard
  unfolding equal_rbt_def
  by (auto simp: rbt.impl_of_inject equal_eq)

end

instance nat :: lin_equal by standard

definition \<open>am_empty = []\<close>
definition \<open>am_update = upd_list\<close>
definition \<open>am_delete = del_list\<close>
definition \<open>am_lookup = Map.map_of\<close>
definition \<open>am_invar = sorted1\<close>

definition \<open>am_empty' = []\<close>
definition \<open>am_update' = upd_list\<close>
definition \<open>am_delete' = del_list\<close>
definition \<open>am_lookup' = Map.map_of\<close>
definition \<open>am_invar' = sorted1\<close>


definition \<open>rbtm_empty = RBT_Set.empty\<close>
definition \<open>rbtm_update = update\<close>
definition \<open>rbtm_delete = delete\<close>
definition \<open>rbtm_lookup = lookup\<close>
definition \<open>rbtm_invar = rbt\<close>
definition \<open>rbtm_inorder = Tree2.inorder\<close>

definition \<open>rbtm_empty' = RBT_Set.empty\<close>
definition \<open>rbtm_update' = update\<close>
definition \<open>rbtm_delete' = delete\<close>
definition \<open>rbtm_lookup' = lookup\<close>
definition \<open>rbtm_invar' = rbt\<close>
definition \<open>rbtm_inorder' = Tree2.inorder\<close>

lemma am_Map_by_Ordered: \<open>Map_by_Ordered am_empty am_update am_delete am_lookup id am_invar\<close>
  unfolding am_empty_def am_update_def am_delete_def am_lookup_def am_invar_def  
  by unfold_locales
    (auto simp: 
      sorted_upd_list[unfolded A_List_map_of_eq_map_of] sorted_del_list[unfolded A_List_map_of_eq_map_of] 
      map_of_ins_list[unfolded A_List_map_of_eq_map_of] map_of_del_list[unfolded A_List_map_of_eq_map_of])

lemma am_Map_by_Ordered': \<open>Map_by_Ordered am_empty' am_update' am_delete' am_lookup' id am_invar'\<close>
  unfolding am_empty'_def am_update'_def am_delete'_def am_lookup'_def am_invar'_def  
  by unfold_locales
    (auto simp: 
      sorted_upd_list[unfolded A_List_map_of_eq_map_of] sorted_del_list[unfolded A_List_map_of_eq_map_of] 
      map_of_ins_list[unfolded A_List_map_of_eq_map_of] map_of_del_list[unfolded A_List_map_of_eq_map_of])


derive "show" RBT_Impl.rbt

locale Var_Map_Defs =
  fixes
    empty_var_map :: \<open>'var_map\<close> and
    num_vars :: \<open>'var_map \<Rightarrow> nat\<close> and
    nat_to_var :: \<open>'var_map \<Rightarrow> nat \<Rightarrow> 'var\<close> and
    var_to_nat_upd :: \<open>'var_map \<Rightarrow> 'var \<Rightarrow> 'var_map \<times> nat\<close> and
    var_map_\<alpha> :: \<open>'var_map \<Rightarrow> ('var \<Rightarrow> nat option)\<close> and
    var_map_inv :: \<open>'var_map \<Rightarrow> bool\<close>

locale Var_Map =
  Var_Map_Defs +
  assumes
    vm_inv_empty[intro, simp]: \<open>var_map_inv empty_var_map\<close> and
    vm_inv_upd: \<open>var_map_inv vm \<Longrightarrow> var_map_inv (fst (var_to_nat_upd vm v))\<close> and
    var_map_empty[simp]: \<open>var_map_\<alpha> empty_var_map = Map.empty\<close> and
    num_vars_correct: \<open>var_map_inv vm \<Longrightarrow> ran (var_map_\<alpha> vm) = {..<num_vars vm}\<close> and
    var_to_nat_inj: \<open>var_map_inv vm \<Longrightarrow> inj_on (\<lambda>v. var_map_\<alpha> vm v) (dom (var_map_\<alpha> vm))\<close> and
    nat_to_var_correct: \<open>\<And>vm i. var_map_inv vm \<Longrightarrow> i \<in> ran (var_map_\<alpha> vm) \<Longrightarrow> 
      nat_to_var vm i = (THE v. var_map_\<alpha> vm v = Some i)\<close> and
    var_to_nat_upd_correct_dom: \<open>\<And>vm v. var_map_inv vm \<Longrightarrow> v \<in> dom (var_map_\<alpha> vm) \<Longrightarrow> 
      snd (var_to_nat_upd vm v) = the (var_map_\<alpha> vm v) \<and> var_map_\<alpha> (fst (var_to_nat_upd vm v)) = var_map_\<alpha> vm\<close> and
    var_to_nat_upd_correct_fresh: \<open>\<And>vm v. var_map_inv vm \<Longrightarrow> v \<notin> dom (var_map_\<alpha> vm) \<Longrightarrow> 
      var_map_\<alpha> (fst (var_to_nat_upd vm v)) = (var_map_\<alpha> vm)(v \<mapsto> snd (var_to_nat_upd vm v))\<close>
begin

lemma num_vars_eq_card_ran: \<open>var_map_inv vm \<Longrightarrow> num_vars vm = card (ran (var_map_\<alpha> vm))\<close>
  by (auto dest: num_vars_correct)

lemma num_vars_eq_card_dom: \<open>var_map_inv vm \<Longrightarrow> num_vars vm = card (dom (var_map_\<alpha> vm))\<close>
  by (metis card_image dom_def inj_on_map_the mem_Collect_eq num_vars_eq_card_ran ran_is_image subset_Collect_conv var_to_nat_inj)

lemma vars_empty[simp]: \<open>num_vars empty_var_map = 0\<close>
  by (auto simp: num_vars_eq_card_dom)

lemma snd_var_to_nat_upd_in_dom[simp]:
  assumes \<open>var_map_inv vm\<close> \<open>v \<in> dom (var_map_\<alpha> vm)\<close>
  shows \<open>snd (var_to_nat_upd vm v) = the (var_map_\<alpha> vm v)\<close>
  using assms var_to_nat_upd_correct_dom by auto

lemma fst_var_to_nat_upd_in_dom:
  assumes \<open>var_map_inv vm\<close> \<open>v \<in> dom (var_map_\<alpha> vm)\<close>
  shows \<open>var_map_\<alpha> (fst (var_to_nat_upd vm v)) = var_map_\<alpha> vm\<close>
  using assms var_to_nat_upd_correct_dom by auto

lemma fst_var_to_nat_upd_notin_dom[simp]:
  assumes \<open>var_map_inv vm\<close>
  shows \<open>var_map_\<alpha> (fst (var_to_nat_upd vm v)) = (var_map_\<alpha> vm)(v \<mapsto> snd (var_to_nat_upd vm v))\<close>
  apply (cases \<open>v \<in> dom (var_map_\<alpha> vm)\<close>)
  using assms var_to_nat_upd_correct_fresh fst_var_to_nat_upd_in_dom
  by (auto simp add: domIff map_upd_triv)
end

setup Locale_Code.open_block
locale Var_Map_Inst =
  Map: StdBasicMap map_ops
  for map_ops :: \<open>(_, nat, 'm) map_basic_ops\<close>
begin

definition \<open>empty_var_map = (Map.empty (), 0, [])\<close>
definition \<open>num_vars m = (case m of (_, n, _) \<Rightarrow> n)\<close>
definition \<open>nat_to_var m = (case m of (_, _, m) \<Rightarrow> let arr = IArray (rev m) in IArray.sub arr)\<close>
definition \<open>var_to_nat_upd m v = (case m of (m', n::nat, to_v) \<Rightarrow>
    (case Map.lookup v m' of None \<Rightarrow> 
      ((Map.update v n m', Suc n, v # to_v), n)
     | Some i \<Rightarrow> ((m',n,to_v), i)))\<close>
definition \<open>var_map_\<alpha> m v = (case m of (m', n::nat, to_v) \<Rightarrow> Map.lookup v m')\<close>
definition \<open>var_map_inv vm \<longleftrightarrow>
  (\<forall>i. i \<in> ran (var_map_\<alpha> vm) \<longrightarrow> nat_to_var vm i = (THE v. var_map_\<alpha> vm v = Some i)) \<and>
  (ran (var_map_\<alpha> vm) = {..<num_vars vm}) \<and>
  (Map.invar (fst vm)) \<and>
  (length (snd (snd vm)) = num_vars vm) \<and>
  (num_vars vm = card (dom (var_map_\<alpha> vm))) \<and>
  (inj_on (var_map_\<alpha> vm) (dom (var_map_\<alpha> vm)))\<close>

sublocale Var_Map_Defs
  where 
    empty_var_map = empty_var_map and
    num_vars = num_vars and
    nat_to_var = nat_to_var and
    var_to_nat_upd = var_to_nat_upd and
    var_map_inv = var_map_inv and
    var_map_\<alpha> = var_map_\<alpha> .

lemma num_vars_empty_vm[simp]: \<open>num_vars empty_var_map = 0\<close>
  unfolding empty_var_map_def num_vars_def
  by auto

lemma var_map_\<alpha>_empty[simp]: \<open>var_map_\<alpha> empty_var_map = (\<lambda>x. None)\<close>
  unfolding empty_var_map_def var_map_\<alpha>_def
  by auto

lemma map_inv_empty_vm: \<open>Map.invar (fst empty_var_map)\<close>
  unfolding empty_var_map_def
  by auto

lemma n_to_v_empty[simp]: \<open>snd (snd empty_var_map) = []\<close>
  unfolding empty_var_map_def
  by auto

lemma vm_inv_empty': \<open>var_map_inv empty_var_map\<close>
  unfolding var_map_inv_def
  using map_inv_empty_vm
  by auto
 
lemma num_vars_eq_vm_sz[simp]: \<open>var_map_inv vm \<Longrightarrow> num_vars vm = card (dom (var_map_\<alpha> vm))\<close>
  unfolding num_vars_def var_map_\<alpha>_def var_map_inv_def
  by auto

lemma var_map_inv_inj: \<open>var_map_inv vm \<Longrightarrow> inj_on (var_map_\<alpha> vm) (dom (var_map_\<alpha> vm))\<close>
  unfolding var_map_inv_def
  by auto

lemma var_to_nat_upd_mem: \<open>var_map_inv vm \<Longrightarrow>
    v \<in> dom (var_map_\<alpha> vm) \<Longrightarrow>
    fst (var_to_nat_upd vm v) = vm\<close>
  unfolding var_to_nat_upd_def var_map_\<alpha>_def
  by (auto simp: case_prod_unfold  split: option.splits)

lemma var_to_nat_upd_mem_lookpup: \<open>var_map_inv vm \<Longrightarrow>
    v \<in> dom (var_map_\<alpha> vm) \<Longrightarrow>
    snd (var_to_nat_upd vm v) = the (var_map_\<alpha> vm v)\<close>
  unfolding var_to_nat_upd_def var_map_\<alpha>_def
  by (auto simp: case_prod_unfold  split: option.splits)

lemma var_to_nat_upd_no_mem_lookpup: \<open>var_map_inv vm \<Longrightarrow>
    v \<notin> dom (var_map_\<alpha> vm) \<Longrightarrow> var_map_\<alpha> (fst (var_to_nat_upd vm v)) = (var_map_\<alpha> vm)(v \<mapsto> snd (var_to_nat_upd vm v))\<close>  
  unfolding var_to_nat_upd_def var_map_\<alpha>_def var_map_inv_def
  by (fastforce simp add: case_prod_unfold split: option.splits)


lemma var_to_nat_upd_no_mem_snd[simp]: \<open>var_map_inv vm \<Longrightarrow>
    v \<notin> dom (var_map_\<alpha> vm) \<Longrightarrow> snd (var_to_nat_upd vm v) = num_vars vm\<close>  
  unfolding var_to_nat_upd_def var_map_\<alpha>_def var_map_inv_def num_vars_def
  by (auto simp add: case_prod_unfold split: option.splits)

lemma var_to_nat_upd_map_inv: \<open>var_map_inv vm \<Longrightarrow> Map.invar (fst (fst (var_to_nat_upd vm v)))\<close>
  unfolding var_map_inv_def var_to_nat_upd_def case_prod_unfold
  by (auto split: option.splits)
  
lemma var_to_nat_upd_num_vars: \<open>var_map_inv vm \<Longrightarrow> 
  (num_vars (fst (var_to_nat_upd vm v))) = card (dom (var_map_\<alpha> (fst (var_to_nat_upd vm v))))\<close>
  unfolding var_to_nat_upd_def case_prod_unfold var_map_inv_def num_vars_def var_map_\<alpha>_def
  by (auto split: option.splits simp: domIff)

lemma var_map_lookup_lt_num_vars: \<open>var_map_inv vm \<Longrightarrow> Map.\<alpha> (fst vm) y = Some z \<Longrightarrow> z < num_vars vm\<close>
  unfolding Map.ran_def var_map_inv_def var_to_nat_upd_def case_prod_unfold var_map_\<alpha>_def inj_on_def num_vars_def
  apply (auto split: option.splits)
  by blast

lemma var_to_nat_upd_inj:
  assumes \<open>var_map_inv vm\<close>
  shows \<open>inj_on (var_map_\<alpha> (fst (var_to_nat_upd vm v))) (dom (var_map_\<alpha> (fst (var_to_nat_upd vm v))))\<close>
  apply (cases \<open>v \<in> dom (var_map_\<alpha> vm)\<close>)
  subgoal
    using assms
    unfolding var_map_inv_def var_to_nat_upd_def case_prod_unfold var_map_\<alpha>_def inj_on_def num_vars_def
    by (auto split: option.splits)

  using assms var_map_lookup_lt_num_vars[of vm]
  unfolding  var_map_inv_def var_to_nat_upd_def case_prod_unfold var_map_\<alpha>_def inj_on_def num_vars_def
  apply (auto split: option.splits dest!: )
   apply blast
  by auto

lemma var_to_nat_upd_ran: \<open>var_map_inv vm \<Longrightarrow> ran (var_map_\<alpha> (fst (var_to_nat_upd vm v))) = {..<num_vars (fst (var_to_nat_upd vm v))}\<close>
    unfolding var_map_inv_def var_to_nat_upd_def case_prod_unfold var_map_\<alpha>_def inj_on_def num_vars_def
    by (auto split: option.splits)

lemmas var_to_nat_upd_mem[simp]
lemmas var_to_nat_upd_ran[simp]

lemma num_vars_upd_notin[simp]: \<open>var_map_inv vm \<Longrightarrow> v \<notin> dom (var_map_\<alpha> vm) \<Longrightarrow> 
  num_vars (fst (var_to_nat_upd vm v)) = num_vars vm + 1\<close>
  unfolding var_map_inv_def var_to_nat_upd_def var_map_\<alpha>_def num_vars_def
  by (auto split: option.splits simp:  case_prod_unfold)

lemma nat_to_var_upd_notin:
  assumes \<open>var_map_inv vm\<close> \<open>i \<in> ran (var_map_\<alpha> (fst (var_to_nat_upd vm v)))\<close> \<open>v \<notin> dom (var_map_\<alpha> vm)\<close>
  shows \<open>nat_to_var (fst (var_to_nat_upd vm v)) i = (THE va. var_map_\<alpha> (fst (var_to_nat_upd vm v)) va = Some i)\<close>
proof -
  have *: \<open>length (snd (snd vm)) = num_vars vm\<close>
    using assms
    unfolding var_map_inv_def
    by auto

  have 2[simp]: \<open>var_map_\<alpha> vm v = None\<close>
    using assms
    by auto

  have \<open>nat_to_var (fst (var_to_nat_upd vm v)) i = IArray (rev ((v # snd (snd vm)))) !! i\<close>
    unfolding nat_to_var_def case_prod_unfold Let_def
    unfolding var_to_nat_upd_def case_prod_unfold
    using assms
    by (auto simp: var_map_\<alpha>_def case_prod_unfold split: option.splits)
  also have \<open>\<dots> = (THE va. var_map_\<alpha> (fst (var_to_nat_upd vm v)) va = Some i)\<close>
    apply (cases \<open>i < num_vars vm\<close>)
    subgoal
      using assms 
      apply (auto simp: var_to_nat_upd_no_mem_lookpup )
      unfolding var_map_inv_def
      apply (auto simp: nat_to_var_def case_prod_unfold)
      using *
      apply simp
      by (metis "2" option.simps(2))
    subgoal
          apply (cases \<open>i = num_vars vm\<close>)

      using * assms
       apply (auto simp:  List.nth_append var_to_nat_upd_no_mem_lookpup)
      by (smt (verit, del_insts) lessThan_iff less_not_refl ranI the1I2 var_map_inv_def)+
    done
  finally show ?thesis.
qed

lemma nat_to_var_upd: \<open>var_map_inv vm \<Longrightarrow> 
  i \<in> ran (var_map_\<alpha> (fst (var_to_nat_upd vm v))) \<Longrightarrow> 
  nat_to_var (fst (var_to_nat_upd vm v)) i = (THE va. var_map_\<alpha> (fst (var_to_nat_upd vm v)) va = Some i)\<close>
  apply (cases \<open>v \<in> dom (var_map_\<alpha> vm)\<close>)
  subgoal
  apply (auto split: option.splits simp:  case_prod_unfold)
    apply (subst (asm) var_map_inv_def)
    by auto
  subgoal
    using nat_to_var_upd_notin
    by blast
  done

lemma len_n_to_v_upd: \<open>var_map_inv vm \<Longrightarrow>length (snd (snd (fst (var_to_nat_upd vm v)))) = num_vars (fst (var_to_nat_upd vm v))\<close>
  unfolding var_map_inv_def
  by (auto simp:  num_vars_def var_to_nat_upd_def case_prod_unfold split: option.splits)

lemma var_to_nat_upd_inv: \<open>var_map_inv vm \<Longrightarrow> var_map_inv (fst (var_to_nat_upd vm v))\<close>
  using nat_to_var_upd var_to_nat_upd_map_inv var_to_nat_upd_num_vars var_to_nat_upd_inj var_to_nat_upd_ran len_n_to_v_upd
  apply (subst var_map_inv_def)
  by auto

lemma n_to_v_eq_the: \<open>var_map_inv vm \<Longrightarrow> i \<in> ran (var_map_\<alpha> vm) \<Longrightarrow> nat_to_var vm i = (THE v. var_map_\<alpha> vm v = Some i)\<close>
  unfolding var_map_inv_def nat_to_var_def case_prod_unfold Let_def
  by auto


sublocale Var_Map
  where 
    empty_var_map = empty_var_map and
    num_vars = num_vars and
    nat_to_var = nat_to_var and
    var_to_nat_upd = var_to_nat_upd and
    var_map_inv = var_map_inv and
    var_map_\<alpha> = var_map_\<alpha>
  apply unfold_locales
  subgoal using vm_inv_empty' .
  subgoal using var_to_nat_upd_inv .
  subgoal using var_map_\<alpha>_empty .
  subgoal using var_map_inv_def by blast
  subgoal using var_map_inv_inj .
  subgoal using n_to_v_eq_the .
  subgoal
    using var_to_nat_upd_mem var_to_nat_upd_mem_lookpup
    by auto
  subgoal using var_to_nat_upd_no_mem_lookpup .
  done

end
setup Locale_Code.close_block

definition \<open>rat_of_real r = (THE x. r = Ratreal x)\<close>

lemma [code]: \<open>rat_of_real (Ratreal x) = x\<close>
  unfolding rat_of_real_def
  by auto


setup Locale_Code.open_block

locale LP_Cert_Code_Defs =
  Coeffs : CoeffsDefs
  where
    constr_op_map_ops = map_ops +
    VM: Var_Map
  where nat_to_var = nat_to_var +
    LPC: LP_Code
  where
    m_update = m_update
  for
    map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> and
    m_update :: "nat \<Rightarrow> 'v \<Rightarrow> 'lp_m \<Rightarrow> 'lp_m" and
    nat_to_var :: "'var_map \<Rightarrow> nat \<Rightarrow> var_code_ty"  +
  fixes
    lp_oracle :: \<open>nat \<Rightarrow> 'v \<Rightarrow> 'lp_m \<Rightarrow> 'v \<Rightarrow> 'v LP_Cert option\<close> and 
    dims :: nat and 
    doms :: \<open>nat \<Rightarrow> nat\<close>
begin

fun conv_kind :: \<open>_ \<Rightarrow> sense\<close> where
  \<open>conv_kind (Constr_Le _ _) = sense.Leq\<close> |
  \<open>conv_kind (Constr_Eq _ _) = sense.Eq\<close>
lemmas refl[of conv_kind, cong]

definition \<open>coeffs_to_nat cs vm = fold (\<lambda>(v, c) (cs, vm).
      let (vm', i) = var_to_nat_upd vm v in
       ((i, c) # cs, vm')) (Coeffs.to_list cs) ([], vm)\<close>
lemmas refl[of coeffs_to_nat, cong]

definition constr_to_nat :: \<open>'m Constr_Code \<Rightarrow> 'var_map \<Rightarrow> nat constraint \<times> _\<close> where
  \<open>constr_to_nat c vm = (case c of 
    Constr_Le cs r \<Rightarrow> (let (coeffs_nat, vm') = coeffs_to_nat cs vm in ((coeffs_nat, sense.Leq, r), vm')) |
    Constr_Eq cs r \<Rightarrow> (let (coeffs_nat, vm') = coeffs_to_nat cs vm in ((coeffs_nat, sense.Eq, r), vm'))
)\<close>
lemmas refl[of constr_to_nat, cong]

definition \<open>constrs_to_nat cs vm = fold (\<lambda>c (cs, vm). let (c_nat, vm') = constr_to_nat c vm in (c_nat#cs, vm')) cs ([], vm)\<close>

definition lp_to_nat :: \<open>('m Constr_Code) list \<Rightarrow> 'm \<Rightarrow> _\<close> where
  \<open>lp_to_nat cs obj = (let
  (obj_nat, vm') = coeffs_to_nat obj empty_var_map;
  (cs_nat, vm'') = constrs_to_nat cs vm'
  in
    ((True, num_vars vm'', obj_nat, cs_nat), vm''))\<close>
lemmas refl[of lp_to_nat, cong]


definition \<open>solve_lp lp_vm = 
  (
  let
    (lp, vm) = lp_vm;
    (m, n, c, cs) = lp;
    (n, c, cs, bs) = LPC.from_file' m n c cs
in 
  (case lp_oracle n c cs bs of 
  Some (Cert_Opt x y) \<Rightarrow> (if 
  LPC.check_cert (Cert_Opt x y) cs bs c  then Some x else None)
  | _ \<Rightarrow> None))\<close>
lemmas refl[of solve_lp, cong]


definition \<open>lp_minimize lp_vm = (
  case solve_lp lp_vm of
    None \<Rightarrow> Infeasible
  | Some sol' \<Rightarrow>
  (let
    (lp, vm) = lp_vm;
    (m, n, c, cs) = lp;
    n_to_v = nat_to_var vm;
    nv = num_vars vm;
    v_var = Coeffs.to_map (List.map_filter (\<lambda>(i,r). if i < nv then Some (n_to_v i, r) else None) (v_inorder sol'))
    in
    Opt v_var ((fold (+) (map (\<lambda>(i, c). (Coeffs.lookup0_code (n_to_v i) v_var) * c) c) 0))))\<close>
lemmas refl[of lp_minimize, cong]


definition \<open>minimize lp = (case lp of Factored_LP_Code.LP_Code obj cs \<Rightarrow> 
  let lp_vm = lp_to_nat cs obj in lp_minimize lp_vm)\<close>
lemmas refl[of minimize, cong]


end


locale LP_Cert_Code = 
LP_Cert_Code_Defs
  where map_ops = map_ops +
  Coeffs : Coeffs
where constr_op_map_ops = map_ops 
for map_ops
begin

lemmas 
  VM.vm_inv_empty[simp, intro]
  VM.vm_inv_upd[intro!]

lemma vm_inv_coeffs_to_nat:
  shows \<open>var_map_inv (snd (coeffs_to_nat obj empty_var_map))\<close>
  unfolding coeffs_to_nat_def Let_def case_prod_unfold
  apply (rule List.fold_invariant)
  by fastforce+

lemma Coeffs_list_empty_iff[simp]: \<open>Coeffs.invar m \<Longrightarrow> [] = Coeffs.to_list m \<longleftrightarrow> Coeffs.\<alpha> m = Map.empty\<close>
  using Coeffs.correct(25) by fastforce

lemma fst_coeffs_list[simp]: \<open>Coeffs.invar m \<Longrightarrow> fst ` set (Coeffs.to_list m) = dom (Coeffs.\<alpha> m)\<close>
  using Coeffs.correct(25)[of m]  weak_map_of_SomeI
  apply (auto simp: image_iff)
   apply (metis weak_map_of_SomeI)
  by (metis fst_conv map_of_SomeD)

lemma dom_coeffs_to_nat:
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar m\<close>
  shows \<open>dom (var_map_\<alpha> (snd (coeffs_to_nat m vm))) = dom (Coeffs.\<alpha> m) \<union> dom (var_map_\<alpha> vm)\<close>
proof -
  have *: \<open>dom (var_map_\<alpha>
          (snd (fold (\<lambda>(v, c) (cs, vm). let (vm', i) = var_to_nat_upd vm v in ((i, c) # cs, vm')) xs (cs, vm)))) =
    fst ` set xs \<union> dom (var_map_\<alpha> vm)\<close> if \<open>var_map_inv vm\<close> for cs xs
    using that
  proof (induction xs arbitrary: vm cs)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case
      apply (simp add: case_prod_unfold)
      apply (cases \<open>fst a \<in> dom (var_map_\<alpha> vm)\<close>)
        using VM.vm_inv_upd VM.var_to_nat_upd_correct_dom[of vm \<open>fst a\<close>]
        VM.var_to_nat_upd_correct_fresh[of vm \<open>fst a\<close>] map_upd_nonempty[symmetric]
        by auto
    qed
    show ?thesis
      using *[of \<open>Coeffs.to_list m\<close> \<open>[]\<close>] assms
      unfolding coeffs_to_nat_def
      by auto
  qed

lemma var_to_nat_upd_const[simp]:
  assumes \<open>var_map_inv vm\<close> \<open>i \<in> dom (var_map_\<alpha> vm)\<close>
  shows \<open>var_map_\<alpha> (fst (var_to_nat_upd vm x)) i = var_map_\<alpha> vm i\<close>
  using assms VM.var_to_nat_upd_correct_dom[of vm i]
  by (metis VM.var_to_nat_upd_correct_dom VM.var_to_nat_upd_correct_fresh fun_upd_apply_ne)

lemma map_upd_empty_iff_false[simp]: \<open>Map.empty = [x \<mapsto> y] \<longleftrightarrow> False\<close>
  using map_upd_nonempty by metis

lemma var_to_nat_upd_if[simp]:
  assumes \<open>var_map_inv vm\<close>
  shows \<open>var_map_\<alpha> (fst (var_to_nat_upd vm x)) = 
  (if x \<in> dom (var_map_\<alpha> vm) then var_map_\<alpha> vm else (var_map_\<alpha> vm) (x \<mapsto> snd (var_to_nat_upd vm x)))\<close>
  apply (cases \<open>x \<in> dom (var_map_\<alpha> vm)\<close>)
  using assms 
  by auto

lemma inv_coeffs_to_nat[intro!]:
  assumes \<open>var_map_inv vm\<close>
  shows \<open>var_map_inv (snd (coeffs_to_nat x vm))\<close>
  unfolding coeffs_to_nat_def
  apply (rule List.fold_invariant[where Q = \<open>\<lambda>_. True\<close>])
  using assms
  by (auto simp: case_prod_unfold)

lemma vm_\<alpha>_dom_coeffs_to_nat[simp]:
  assumes \<open>var_map_inv vm\<close> \<open>i \<in> dom (var_map_\<alpha> vm)\<close>
  shows \<open>var_map_\<alpha> (snd (coeffs_to_nat x vm)) i = var_map_\<alpha> vm i\<close>
proof -
  have \<open>var_map_inv (snd (coeffs_to_nat x vm)) \<and> var_map_\<alpha> (snd (coeffs_to_nat x vm)) i = var_map_\<alpha> vm i\<close>
  unfolding coeffs_to_nat_def
  apply (rule List.fold_invariant[where Q = \<open>\<lambda>_. True\<close>])
  using assms
  by (auto simp: case_prod_unfold domIff)
  thus ?thesis by blast
qed

lemma var_map_inj: \<open>var_map_inv vm \<Longrightarrow> var_map_\<alpha> vm x = var_map_\<alpha> vm y \<Longrightarrow> x \<in> dom (var_map_\<alpha> vm) \<Longrightarrow> x = y\<close>
  using VM.var_to_nat_inj
  unfolding inj_on_def
  apply (cases \<open>y \<in> dom (var_map_\<alpha> vm)\<close>)
  by auto fastforce


lemma coeffs_to_nat_aux: 
  fixes vm init xs
  defines \<open>ys \<equiv> fold (\<lambda>(v, c) (cs, vm).
      let (vm', i) = var_to_nat_upd vm v in
       ((i, c) # cs, vm')) xs ([], vm)\<close>
  assumes \<open>var_map_inv vm\<close> \<open>distinct (map fst xs)\<close>
  shows \<open>var_map_inv (snd ys)\<close> \<open>fst ys = rev (map (\<lambda>(i, v). (the (var_map_\<alpha> (snd ys) i), v)) xs)\<close>
  using assms
  apply (induction xs arbitrary: vm ys rule: rev_induct)
  by (auto simp: Let_def case_prod_unfold)

lemma coeffs_to_nat_aux': 
  fixes vm init xs
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar cs\<close>
  shows \<open>fst (coeffs_to_nat cs vm) = rev (map (\<lambda>(i, v). (the (var_map_\<alpha> (snd (coeffs_to_nat cs vm)) i), v)) (Coeffs.to_list cs))\<close>
  using assms coeffs_to_nat_aux[of vm \<open>Coeffs.to_list cs\<close>] Coeffs.correct(26)
  unfolding coeffs_to_nat_def
  by (auto simp: case_prod_unfold)


lemma fst_coeffs_to_nat_eq: 
  fixes vm init xs
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar cs\<close>
  shows \<open>fst (coeffs_to_nat cs vm) = fst (coeffs_to_nat cs (snd (coeffs_to_nat cs vm)))\<close>
  using assms
  apply (subst coeffs_to_nat_aux')
  using assms
  apply auto
  apply (subst coeffs_to_nat_aux')
  apply auto
  by (metis LPC.in_fstD Un_iff dom_coeffs_to_nat fst_coeffs_list inv_coeffs_to_nat vm_\<alpha>_dom_coeffs_to_nat)
  
lemma coeffs_to_nat_distinct[intro!]: 
  fixes vm init xs
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar cs\<close>
  shows \<open>distinct (map fst (fst (coeffs_to_nat cs vm)))\<close>
  using  Coeffs.correct(26) assms inv_coeffs_to_nat[of vm] 
  apply (auto simp: List.distinct_map inj_on_def coeffs_to_nat_aux')
  apply (metis (no_types, lifting) Un_iff domIff dom_coeffs_to_nat fst_coeffs_list img_fst  option.expand var_map_inj)
  by (metis (no_types, lifting) LPC.in_fstD Un_iff domIff dom_coeffs_to_nat fst_coeffs_list option.expand prod.sel(1) prod.simps(1) var_map_inj)


lemma vm_\<alpha>_dom_constr_to_nat[simp]:
  assumes \<open>var_map_inv vm\<close> \<open>i \<in> dom (var_map_\<alpha> vm)\<close>
  shows \<open>var_map_\<alpha> (snd (constr_to_nat x vm)) i = var_map_\<alpha> vm i\<close>
  unfolding constr_to_nat_def
  by (auto simp: assms case_prod_unfold split: Constr_Code.splits)


lemma vm_inv_constr_to_nat[simp, intro!]:
  assumes \<open>var_map_inv vm\<close>
  shows \<open>var_map_inv (snd (constr_to_nat x vm))\<close>
  unfolding constr_to_nat_def
  by (auto simp: assms case_prod_unfold split: Constr_Code.splits)


lemma vm_\<alpha>_dom_constrs_to_nat[simp]:
  assumes \<open>var_map_inv vm\<close> \<open>i \<in> dom (var_map_\<alpha> vm)\<close>
  shows \<open>var_map_\<alpha> (snd (constrs_to_nat cs vm)) i = var_map_\<alpha> vm i\<close>
proof -
  have \<open>var_map_inv (snd (constrs_to_nat cs vm)) \<and> var_map_\<alpha> (snd (constrs_to_nat cs vm)) i = var_map_\<alpha> vm i\<close>
  unfolding constrs_to_nat_def
  apply (rule List.fold_invariant[where Q = \<open>\<lambda>_. True\<close>])
  using assms
  by (auto simp: case_prod_unfold domIff)
  thus ?thesis by blast
qed

lemma vm_inv_constrs_to_nat[simp, intro!]:
  assumes \<open>var_map_inv vm\<close>
  shows \<open>var_map_inv (snd (constrs_to_nat cs vm))\<close>
  unfolding constrs_to_nat_def
  apply (rule List.fold_invariant[where Q = \<open>\<lambda>_. True\<close>])
  using assms
  by (auto simp: case_prod_unfold)


lemma constr_to_nat_to_aux: 
  fixes vm init xs
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar (constr_code_poly c)\<close>
  shows \<open>fst (constr_to_nat c vm) = fst (constr_to_nat c (snd ((constr_to_nat c vm))))\<close>
  using assms
  unfolding constr_to_nat_def
  by (auto simp: constr_code_poly_def Let_def case_prod_unfold constr_to_nat_def fst_coeffs_to_nat_eq split: Constr_Code.splits)

lemma coeffs_to_nat_twice:
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar x\<close> \<open>Coeffs.invar y\<close>
    \<open>dom (Coeffs.\<alpha> x) \<subseteq> dom (var_map_\<alpha> vm)\<close>
  shows \<open>fst (coeffs_to_nat x (snd (coeffs_to_nat y vm))) = fst (coeffs_to_nat x vm)\<close>
  using assms
  apply (auto simp: coeffs_to_nat_aux')
  apply (subst coeffs_to_nat_aux')
  apply auto
  by (metis (no_types, lifting) domIff fst_coeffs_list fst_image_mp inv_coeffs_to_nat vm_\<alpha>_dom_coeffs_to_nat)

lemma constr_to_nat_twice:
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar (constr_code_poly x)\<close> \<open>Coeffs.invar (constr_code_poly y)\<close>
    \<open>dom (Coeffs.\<alpha> (constr_code_poly x)) \<subseteq> dom (var_map_\<alpha> vm)\<close>
  shows \<open>fst (constr_to_nat x (snd (constr_to_nat y vm))) = fst (constr_to_nat x vm)\<close>
  unfolding constr_to_nat_def
  using assms
  by (auto simp: case_prod_unfold coeffs_to_nat_twice constr_code_poly_def split: Constr_Code.splits)

lemma constr_to_nat_dom:
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar (constr_code_poly x)\<close>
  shows \<open>dom (var_map_\<alpha> (snd (constr_to_nat x vm))) = dom (var_map_\<alpha> vm) \<union> dom (Coeffs.\<alpha> (constr_code_poly x))\<close>
  unfolding constr_to_nat_def
  using assms vm_\<alpha>_dom_coeffs_to_nat dom_coeffs_to_nat
  by (auto simp: case_prod_unfold coeffs_to_nat_twice constr_code_poly_def split: Constr_Code.splits)


lemma constr_to_nat_distinct:
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar (constr_code_poly x)\<close>
  shows \<open>distinct (map fst (fst (fst (constr_to_nat x vm))))\<close>
  unfolding constr_to_nat_def
  using assms vm_\<alpha>_dom_coeffs_to_nat dom_coeffs_to_nat
  by (auto simp: case_prod_unfold coeffs_to_nat_twice constr_code_poly_def split: Constr_Code.splits)



lemma constrs_to_nat_to_nat_aux':
  fixes vm init xs
  assumes \<open>var_map_inv vm\<close> \<open>\<And>i. i \<in> set cs \<Longrightarrow> Coeffs.invar (constr_code_poly i)\<close>
  shows 
    \<open>var_map_inv (snd (constrs_to_nat cs vm))\<close> 
    \<open>fst (constrs_to_nat cs vm) = rev (map (\<lambda>c. fst (constr_to_nat c (snd ((constrs_to_nat cs vm))))) cs)\<close>
    \<open>dom (var_map_\<alpha> (snd (constrs_to_nat cs vm))) = dom (var_map_\<alpha> vm) \<union> (\<Union>c \<in> set cs. dom (Coeffs.\<alpha> (constr_code_poly c)))\<close>
  using assms
   apply (induction cs arbitrary: vm rule: rev_induct )
  subgoal by blast
  subgoal     by (auto simp: constrs_to_nat_def Let_def case_prod_unfold  split: Constr_Code.splits)
  subgoal
    by (auto simp: constrs_to_nat_def Let_def case_prod_unfold  split: Constr_Code.splits)
  subgoal
    by (simp add: constrs_to_nat_def case_prod_unfold)
    subgoal
      apply (simp add: constrs_to_nat_def case_prod_unfold)
  
   apply (auto simp: constrs_to_nat_def Let_def case_prod_unfold  split: Constr_Code.splits)
   apply (subst constr_to_nat_to_aux)
       apply auto
    apply (subst constr_to_nat_twice)
      by (auto simp: constr_to_nat_twice split: Constr_Code.splits simp: case_prod_unfold)
    using constr_to_nat_dom
    by (auto iff del: simp: case_prod_unfold constrs_to_nat_def)

lemma vm_inv_lp_to_nat: \<open>lp_to_nat cs obj = (lp, vm) \<Longrightarrow> var_map_inv vm\<close>
  unfolding lp_to_nat_def
  by (auto simp: Let_def case_prod_unfold)


lemma ignore_constrs_to_nat:
  assumes \<open>var_map_inv vm\<close> \<open>\<And>i. i \<in> set cs \<Longrightarrow> Coeffs.invar (constr_code_poly i)\<close>
    \<open>dom (Coeffs.\<alpha> v) \<subseteq> dom (var_map_\<alpha> vm)\<close> \<open>Coeffs.invar v\<close>
  shows  \<open>fst (coeffs_to_nat v (snd (constrs_to_nat cs vm))) = fst (coeffs_to_nat v vm)\<close>
  using assms
  apply (subst coeffs_to_nat_aux')
  apply auto
  apply (subst coeffs_to_nat_aux')
  apply auto
  by (metis (no_types, lifting) domIff fst_coeffs_list fst_image_mp vm_\<alpha>_dom_coeffs_to_nat vm_\<alpha>_dom_constrs_to_nat vm_inv_constrs_to_nat)

definition \<open>coeffs_vm_upd = (\<lambda>(v, c) (cs, vm). let (vm', i) = var_to_nat_upd vm v in ((i, c) # cs, vm'))\<close>

lemma vm_inv_coeffs_upd[intro!]: \<open>var_map_inv vm \<Longrightarrow> var_map_inv (snd (coeffs_vm_upd a (ys, vm)))\<close>
  by (auto simp: coeffs_vm_upd_def case_prod_unfold)

lemma vm_inv_fold_coeffs[intro!]: \<open>var_map_inv vm \<Longrightarrow> var_map_inv (snd (fold coeffs_vm_upd xs (ys, vm)))\<close>
  apply (rule List.fold_invariant[where Q = \<open>\<lambda>_. True\<close>])
  by (auto simp: vm_inv_coeffs_upd case_prod_unfold)

lemma check_opt''_inv:
  assumes 
    \<open>LPC.check_opt'' A b c x y\<close>
    \<open>LPC.mat_code_invar A\<close> 
    \<open>LPC.Sparse_Vec.invar b\<close> 
    \<open>LPC.Sparse_Vec.invar c\<close>
  shows 
    \<open>LPC.Sparse_Vec.invar x\<close>
    \<open>LPC.Sparse_Vec.invar y\<close>
  using assms LPC.check_opt''_feas
  unfolding LPC.check_cert_def LPC.check_opt''_def
  by auto

lemma check_cert_correct:
  assumes \<open>LPC.check_cert (Cert_Opt x y) A b c\<close>
  and \<open>LPC.mat_code_invar A\<close> \<open>LPC.Sparse_Vec.invar b\<close> \<open>LPC.Sparse_Vec.invar c\<close>
  shows 
      \<open>LPC.Sparse_Vec.invar x\<close>
      \<open>LPC.Sparse_Vec.invar y\<close>
      \<open>LPC.feasible_dual_map A c (v_lookup y)\<close>
      \<open>LPC.feasible_map A b (v_lookup x)\<close>
      \<open>LPC.scalar_prod_map (v_lookup c) (v_lookup x) = LPC.scalar_prod_map (v_lookup b) (v_lookup y)\<close>
      \<open>\<And>x'. LPC.feasible_map A b x' \<Longrightarrow> LPC.scalar_prod_map (v_lookup x) (v_lookup c) \<le> LPC.scalar_prod_map x' (v_lookup c)\<close>
  using assms LPC.check_opt''_feas LPC.check_opt''_duality LPC.check_opt''_opt check_opt''_inv
  unfolding LPC.check_cert_def
  by force+
  
lemma fold_plus[simp]: \<open>fold (+) xs (c :: _ :: ab_semigroup_add) = sum_list xs + c\<close>
  by (induction xs arbitrary: c) (auto simp: algebra_simps)

lemma from_file'_eq: \<open>LPC.from_file' True n c cs = 
  (
  n, 
  LPC.Sparse_Vec.from_list2 c, 
  LPC.Sparse_Mat.from_list2 (List.enumerate 0 (fst (LPC.constraints_to_map cs))), 
  LPC.Sparse_Vec.from_list2 (List.enumerate 0 (snd (LPC.constraints_to_map cs)))
  )\<close>
  unfolding LPC.from_file'_def Let_def case_prod_unfold
  by simp

lemma solve_lp_invar: 
  assumes \<open>solve_lp ((True, n, c, cs), vm) = Some x\<close>
  shows \<open>LPC.Sparse_Vec.invar x\<close>
  using assms LPC.from_file'_mat_code_inv LPC.from_file'_invar
  unfolding solve_lp_def
  by (auto simp: from_file'_eq split: option.splits LP_Cert.splits if_splits dest!: check_cert_correct(1))

lemma solve_lp_opt_aux:
  assumes 
    \<open>solve_lp ((True, n, c, cs), vm) = Some x\<close>  
    \<open>LPC.from_file' True n c cs = (n, c_vec, A_mat, b_vec)\<close> \<open>LPC.feasible_map A_mat b_vec x'\<close>
  shows \<open>LPC.scalar_prod_map (v_lookup x) (v_lookup c_vec) \<le> LPC.scalar_prod_map x' (v_lookup c_vec)\<close>
  using assms
  unfolding solve_lp_def Let_def
  apply (auto split: option.splits LP_Cert.splits if_splits)
  by (meson LPC.from_file'_invar(1) LPC.from_file'_invar(2) LPC.from_file'_mat_code_inv check_cert_correct(6))

lemma solve_lp_opt:
  assumes 
    \<open>solve_lp ((True, n, c, cs), vm) = Some x\<close> \<open>LPC.sat_lp_list cs x'\<close> and
    \<open>distinct (map fst c)\<close> \<open>\<forall>(p, _, _) \<in> set cs. distinct (map fst p)\<close>
  shows \<open>LPC.scalar_prod_map (v_lookup x) (Map.map_of c) \<le> LPC.scalar_prod_map x' (Map.map_of c)\<close>
  using assms
  by (auto 
      split: option.splits LP_Cert.splits if_splits 
      simp: LPC.feasible_map_iff_sat_lp_list from_file'_eq case_prod_unfold 
      dest!: solve_lp_opt_aux)

lemma solve_lp_feas:
  assumes 
    \<open>solve_lp ((True, n, c, cs), vm) = Some x\<close>
    \<open>distinct (map fst c)\<close> \<open>\<forall>(p, _, _) \<in> set cs. distinct (map fst p)\<close>
  shows \<open>LPC.sat_lp_list cs (v_lookup x)\<close>
  apply (subst LPC.feasible_map_iff_sat_lp_list[symmetric])
  using assms check_cert_correct
  apply (auto 
      split: option.splits LP_Cert.splits if_splits 
      simp: solve_lp_def  from_file'_eq case_prod_unfold 
      dest!: )
  by (meson LPC.from_file'_mat_code_inv LPC.v_from_list_invar from_file'_eq)

definition \<open>nat_to_var_vec vm (ns :: (nat \<times> real) list) = Coeffs.to_map (map (\<lambda>(v, r). (nat_to_var vm v, r)) ns)\<close>
definition \<open>var_to_nat_vec vm vs = map (\<lambda>(v, r). (the (var_map_\<alpha> vm v), r)) (Coeffs.to_list vs)\<close>

lemma cross_prod_code_eq: \<open>Coeffs.invar v1 \<Longrightarrow> Coeffs.invar v2 \<Longrightarrow> 
  Coeffs.cross_prod_code v1 v2 = (\<Sum>i \<in> dom (Coeffs.\<alpha> v1) \<inter> dom (Coeffs.\<alpha> v2). 
  the (Coeffs.\<alpha> v1 i) *  the (Coeffs.\<alpha> v2 i))\<close>
  unfolding cross_prod_def lookup0_def
  by (auto split: option.splits intro!: sum.mono_neutral_cong_left)

lemma dom_coeffs_to_nat_subs: 
  assumes \<open>Coeffs.invar v1\<close> \<open>var_map_inv vm\<close> \<open>dom (Coeffs.\<alpha> v1) \<subseteq> dom (var_map_\<alpha> vm)\<close>
  shows \<open>dom (Map.map_of (fst (coeffs_to_nat v1 vm))) =
  (\<lambda>v. the (var_map_\<alpha> vm v)) ` dom (Coeffs.\<alpha> v1)\<close>
  using assms
  apply (auto simp:  case_prod_unfold image_iff coeffs_to_nat_aux' fst_coeffs_to_nat_eq)
   apply (metis LPC.in_fstD fst_coeffs_list fst_image_mp vm_\<alpha>_dom_coeffs_to_nat)
  by (metis (no_types, opaque_lifting) Coeffs.to_list_correct(1) Misc.set_simps(6) domI map_of_SomeD mem_simps(3) prod.sel(1) vm_\<alpha>_dom_coeffs_to_nat)

lemma var_map_\<alpha>_lt_nv[intro!]:
  assumes \<open>v \<in> dom (var_map_\<alpha> vm)\<close> \<open>var_map_inv vm\<close>
  shows "the (var_map_\<alpha> vm v) < num_vars vm"
  using assms
  by (metis VM.num_vars_correct domIff lessThan_iff option.exhaust_sel ranI)

lemma dom_coeffs_to_nat_subs_nv: 
  assumes \<open>Coeffs.invar v1\<close> \<open>var_map_inv vm\<close> \<open>dom (Coeffs.\<alpha> v1) \<subseteq> dom (var_map_\<alpha> vm)\<close>
  shows \<open>dom (Map.map_of (fst (coeffs_to_nat v1 vm))) \<subseteq> {..<num_vars vm}\<close>
  using assms
  apply (subst dom_coeffs_to_nat_subs)
  by (auto simp:  case_prod_unfold  )

lemma inj_on_the_vm_\<alpha>[intro!]:
  assumes \<open>X \<subseteq> dom (var_map_\<alpha> vm) \<close> \<open>var_map_inv vm\<close>
  shows \<open>inj_on (\<lambda>v. the (var_map_\<alpha> vm v)) X\<close>
  using assms VM.var_to_nat_inj[of vm]
  apply (auto simp: inj_on_def)
  by (meson basic_trans_rules(31) domIff option.expand)

lemma lookup'_coeffs_to_nat:
  assumes \<open>x \<in> dom (var_map_\<alpha> vm)\<close> \<open>var_map_inv vm\<close> \<open>Coeffs.invar v1\<close> \<open>x \<in> dom (Coeffs.\<alpha> v1)\<close>
  shows \<open>LPC.lookup' (Map.map_of (fst (coeffs_to_nat v1 vm))) (the (var_map_\<alpha> vm x)) = 
    the (Coeffs.\<alpha> v1 x)\<close>
  unfolding LPC.lookup'_def
  using assms
  apply (auto split: option.splits simp: map_of_eq_Some_iff fst_coeffs_list coeffs_to_nat_aux' Map.map_of_eq_None_iff case_prod_unfold image_iff)
   apply (metis assms(1) assms(4) fst_coeffs_list fst_conv in_fst_imageE option.sel vm_\<alpha>_dom_coeffs_to_nat)
   apply (subst (asm) map_of_eq_Some_iff)
  subgoal
    using coeffs_to_nat_distinct[of vm v1]
    by (auto simp: coeffs_to_nat_aux' case_prod_unfold)
  apply auto
  subgoal for r k v
    apply (cases \<open>(var_map_\<alpha> (snd (coeffs_to_nat v1 vm)) k)\<close>)
    subgoal
      apply auto
      by (metis LPC.in_fstD domIff dom_coeffs_to_nat fst_coeffs_list mem_simps(3))
    subgoal
      apply auto
      by (metis Coeffs.correct(25) Coeffs.map_to_list_axioms domI inv_coeffs_to_nat map_of_is_SomeI map_to_list.to_list_correct(2) option.inject var_map_inj vm_\<alpha>_dom_coeffs_to_nat)
    done
  done

lemma cross_prod_code_eq_scalar_prod_map:
  assumes \<open>var_map_inv vm\<close> \<open>Coeffs.invar v1\<close> \<open>Coeffs.invar v2\<close> \<open>dom (Coeffs.\<alpha> v1) \<subseteq> dom (var_map_\<alpha> vm)\<close> \<open>dom (Coeffs.\<alpha> v2) \<subseteq> dom (var_map_\<alpha> vm)\<close>
  shows \<open>Coeffs.cross_prod_code v1 v2 = 
    LPC.scalar_prod_map (Map.map_of (fst (coeffs_to_nat v1 vm))) (Map.map_of (fst (coeffs_to_nat v2 vm)))\<close>
  unfolding LPC.scalar_prod_map_def
  apply (subst dom_coeffs_to_nat_subs[OF \<open>Coeffs.invar v1\<close> \<open>var_map_inv vm\<close> \<open>dom (Coeffs.\<alpha> v1) \<subseteq> dom (var_map_\<alpha> vm)\<close>])
  apply (subst dom_coeffs_to_nat_subs[OF \<open>Coeffs.invar v2\<close> \<open>var_map_inv vm\<close> \<open>dom (Coeffs.\<alpha> v2) \<subseteq> dom (var_map_\<alpha> vm)\<close>])
  apply (subst Fun.inj_on_image_Int[symmetric, of _ \<open>dom (Coeffs.\<alpha> v1) \<union> dom (Coeffs.\<alpha> v2)\<close>])
  subgoal
    using assms
    by auto
  subgoal by auto
  subgoal by auto
  apply (subst sum.reindex)
  subgoal using assms by auto
  apply (subst cross_prod_code_eq)
  subgoal using assms by auto
  subgoal using assms by auto
  apply (rule sum.cong[OF refl])
  using assms
  apply (auto simp add: lookup'_coeffs_to_nat)
  apply (subst lookup'_coeffs_to_nat)
  apply auto
  apply (subst (asm) lookup'_coeffs_to_nat)
  by auto

lemma scalar_prod_list_eq_prod_map: \<open>distinct (map fst (xs :: (_ \<times> real) list)) \<Longrightarrow> LPC.scalar_prod_list xs m = LPC.scalar_prod_map (Map.map_of xs) m\<close>
  unfolding LPC.scalar_prod_list_def LPC.scalar_prod_map_def
  by (auto simp: case_prod_unfold )

lemma dom_vm_lp_to_nat:
  assumes \<open>\<And>i. i \<in> set cs \<Longrightarrow> Coeffs.invar (constr_code_poly i)\<close> \<open>Coeffs.invar obj\<close>
shows \<open>dom (var_map_\<alpha> (snd (lp_to_nat cs obj))) =
  (dom (Coeffs.\<alpha> obj)) \<union>
  (\<Union>c\<in>set cs. dom (Coeffs.\<alpha> (constr_code_poly c)))\<close>
  unfolding lp_to_nat_def Let_def case_prod_unfold
  using assms dom_coeffs_to_nat
  apply simp
  apply (subst constrs_to_nat_to_nat_aux'(3))
  by auto

lemma var_map_\<alpha>_nat_to_var[simp]:
  assumes \<open>var_map_inv vm\<close> \<open>i < num_vars vm\<close>
  shows \<open>var_map_\<alpha> vm (nat_to_var vm i) = Some i\<close>
proof -
  have *: \<open>i \<in> ran (var_map_\<alpha> vm)\<close>
    using assms   VM.num_vars_correct[of vm]
    by blast
  hence \<open>\<exists>v. var_map_\<alpha> vm v = Some i\<close>
    unfolding ran_def by blast
  hence \<open>\<exists>!v. var_map_\<alpha> vm v = Some i\<close>
    using assms var_map_inj[of vm]
    apply auto
    by (metis domI)
  thus ?thesis
  using assms *
  apply (subst VM.nat_to_var_correct)
  apply auto
  by (metis (mono_tags, lifting) the1_equality)
qed

lemma var_map_imp_ntv_eq: \<open>var_map_inv vm \<Longrightarrow> var_map_\<alpha> vm i = Some y \<Longrightarrow> nat_to_var vm y = i\<close>
  by (metis VM.num_vars_correct domIff lessThan_iff option.distinct(1) ranI var_map_\<alpha>_nat_to_var var_map_inj)

lemma distinct_fst_v_inorderI[intro!]: \<open>LPC.Sparse_Vec.invar v \<Longrightarrow> distinct (map fst (v_inorder v))\<close>
  by (meson LPC.Sparse_Vec.Map_by_Ordered_axioms Map_by_Ordered.invar_def strict_sorted_iff)

lemma distinct_v_inorderI[intro!]: \<open>LPC.Sparse_Vec.invar v \<Longrightarrow> distinct (v_inorder v)\<close>
  using distinct_fst_v_inorderI distinct_mapI
  by fast

lemma set_coeffs_list[simp]: \<open>Coeffs.invar m \<Longrightarrow> set (Coeffs.to_list m) = Map.graph (Coeffs.\<alpha> m)\<close>
  using Coeffs.correct(25)[of m]  weak_map_of_SomeI
  apply (auto simp: image_iff Map.graph_def)
  by (metis Coeffs.correct(26) Some_eq_map_of_iff)+

lemma vm_coeffs_to_nat_unchanged: \<open>var_map_inv vm \<Longrightarrow> Coeffs.invar v \<Longrightarrow> dom (Coeffs.\<alpha> v) \<subseteq> dom (var_map_\<alpha> vm) \<Longrightarrow> var_map_\<alpha> (snd (coeffs_to_nat v vm)) = var_map_\<alpha> vm\<close>
  apply (auto intro!: ext)
  subgoal for x
    apply (cases \<open>x \<in> dom (var_map_\<alpha> vm)\<close>)
    using vm_\<alpha>_dom_coeffs_to_nat apply auto
    by (metis Misc.set_simps(5) domIff dom_coeffs_to_nat vm_\<alpha>_dom_coeffs_to_nat)
  done

definition \<open>vm_rel vm n v \<longleftrightarrow>
  var_map_inv vm \<and>
  dom n \<subseteq> {..<num_vars vm} \<and>
  dom v \<subseteq> dom (var_map_\<alpha> vm) \<and>
  finite (dom n) \<and>
  finite (dom v) \<and>
  (\<forall>i \<in> dom n. v (nat_to_var vm i) = n i) \<and>
  (\<forall>i \<in> dom v. v i = n (the (var_map_\<alpha> vm i)))
\<close>

lemma scalar_prod_map_eqI:
  assumes \<open>vm_rel vm n1 v1\<close> \<open>vm_rel vm n2 v2\<close>
  shows \<open>LPC.scalar_prod_map n1 n2 = cross_prod (lookup0 v1 :: _ \<Rightarrow> real) (lookup0 v2)\<close>
  unfolding LPC.scalar_prod_map_def LPC.lookup'_def cross_prod_def lookup0_def
  using assms
  unfolding vm_rel_def
  apply auto
  apply (subst sum.mono_neutral_left[where T = \<open>dom v1 \<inter> dom v2\<close>])
  subgoal
    apply (rule finite_subset[of _ \<open>dom v1\<close>])
    by (auto simp: )
  subgoal
    by auto
  subgoal 
    apply auto
    apply (auto split: option.splits)
    by (metis domI option.inject)+
  apply (auto intro!: sum.cong)
  apply (subst sum.reindex[of \<open>\<lambda>i. the (var_map_\<alpha> vm i)\<close>, symmetric, unfolded comp_def])
   apply (auto intro!: sum.mono_neutral_cong_right simp: image_iff)
  apply (metis domI)
  apply (metis domI)
  by (metis (no_types, opaque_lifting) IntI domI lessThan_iff option.sel subset_eq var_map_\<alpha>_nat_to_var)

lemma lp_minimize_sound:
  assumes \<open>lp_minimize (lp_to_nat cs obj) = Opt sol' val'\<close> \<open>Coeffs.invar obj\<close> \<open>\<And>i. i \<in> set cs \<Longrightarrow> Coeffs.invar (constr_code_poly i)\<close>
  shows 
    \<open>sol' \<in> Coeffs.sol_space_code cs\<close> 
    \<open>Coeffs.cross_prod_code sol' obj = val'\<close>
    \<open>\<And>sol. sol \<in> Coeffs.sol_space_code cs \<Longrightarrow> Coeffs.cross_prod_code sol' obj \<le> Coeffs.cross_prod_code sol obj\<close>
proof -
  let ?vm = \<open>snd (lp_to_nat cs obj)\<close>
  let ?lp = \<open>fst (lp_to_nat cs obj)\<close>

  obtain sol_nat where solve_lp: \<open>solve_lp (lp_to_nat cs obj) = Some sol_nat\<close>
    using assms
    unfolding lp_minimize_def 
    by (auto split: option.splits)

  let ?c_nat = \<open>fst (coeffs_to_nat obj empty_var_map)\<close>
  let ?vm' = \<open>snd (coeffs_to_nat obj empty_var_map)\<close>
  let ?cs_nat = \<open>fst (constrs_to_nat cs ?vm')\<close>
  let ?vm'' = \<open>snd (constrs_to_nat cs ?vm')\<close>  
  let ?n = \<open>num_vars ?vm''\<close>

  have lp_eq: \<open>?lp = (True, ?n, ?c_nat, ?cs_nat)\<close>
    unfolding lp_to_nat_def
    by (simp add: lp_to_nat_def split_def)

  have lp_eq': \<open>(lp_to_nat cs obj) = ((True, ?n, ?c_nat, ?cs_nat), ?vm'')\<close>
    using lp_eq
    unfolding lp_to_nat_def
    by (auto simp: case_prod_unfold)

  have d_c: \<open>distinct (map fst ?c_nat)\<close>
    using assms
    by (auto simp: case_prod_unfold)

  have d_cs: \<open>\<forall>(p, _, _)\<in>set ?cs_nat. distinct (map fst p)\<close>
    using assms constr_to_nat_distinct
    apply (auto simp:  case_prod_unfold)
    apply (subst (asm) constrs_to_nat_to_nat_aux'(2))
      apply auto
    by (metis lp_eq' prod.sel(1) vm_inv_lp_to_nat)

  have \<open>LPC.sat_lp_list ?cs_nat x' \<Longrightarrow>
  LPC.scalar_prod_map (v_lookup sol_nat) (Map.map_of ?c_nat) \<le> LPC.scalar_prod_map x' (Map.map_of ?c_nat)\<close>
    for x'
    apply (rule solve_lp_opt)
    using solve_lp assms d_c d_cs
    unfolding lp_to_nat_def
    by (auto simp: case_prod_unfold)

  have dom_vm'': \<open>dom (var_map_\<alpha> ?vm'') = (dom (Coeffs.\<alpha> obj)) \<union>
    (\<Union>c\<in>set cs. dom (Coeffs.\<alpha> (constr_code_poly c)))\<close>
    by (metis assms(2) assms(3) dom_vm_lp_to_nat lp_eq' snd_conv)

  have sol_nat_inv[intro, simp]: \<open>LPC.Sparse_Vec.invar sol_nat\<close>
    by (metis lp_eq' solve_lp solve_lp_invar)

  have sol'_eq: \<open>sol' = 
    Coeffs.to_map (List.map_filter (\<lambda>(i, r). if i < num_vars ?vm'' then Some (nat_to_var ?vm'' i, r) else None) (v_inorder sol_nat))\<close>
    using assms
    unfolding lp_minimize_def
    unfolding solve_lp
    apply (auto simp:  case_prod_unfold Let_def lp_to_nat_def)
    by (metis snd_eqD)

  have vm_inv[simp, intro]: \<open>var_map_inv ?vm''\<close>
    by blast
  
  have sol'_\<alpha>_eq: \<open>Coeffs.\<alpha> sol' i = (case var_map_\<alpha> ?vm'' i of None \<Rightarrow> None | 
      Some v \<Rightarrow> v_lookup sol_nat v)\<close> for i
    apply (auto split: option.splits simp: set_map_filter sol'_eq Coeffs.to_map_correct map_of_eq_None_iff )
    subgoal for y
      apply (cases \<open>v_lookup sol_nat y\<close>)
      subgoal
        by (auto split: option.splits simp: set_map_filter sol'_eq Coeffs.to_map_correct map_of_eq_None_iff )
      
      apply (auto split: option.splits simp: set_map_filter sol'_eq Coeffs.to_map_correct  )
      apply (subst map_of_eq_Some_iff)
      subgoal
        apply (auto simp:  List.map_filter_def comp_def case_prod_unfold List.distinct_map)
        subgoal by (auto intro!: List.distinct_filter)
        subgoal
          unfolding  Map.graph_def
          apply (auto intro!: inj_onI)
          by (metis option.sel var_map_\<alpha>_nat_to_var vm_inv)+
        done
      subgoal for z
        apply (subst set_map_filter)
        apply (auto simp: )
        unfolding Map.graph_def
        using vm_inv_lp_to_nat
        apply (auto intro!: exI[of _ y] dest: var_map_imp_ntv_eq)
         apply (metis VM.num_vars_correct lessThan_iff lp_eq' ranI vm_inv_lp_to_nat)
        using var_map_imp_ntv_eq by auto
      done
    done

  have dom_sol': \<open>dom (Coeffs.\<alpha> sol') = nat_to_var ?vm'' ` (dom (v_lookup sol_nat) \<inter> {..<num_vars ?vm''})\<close>
    using sol_nat_inv
    apply (auto simp: case_prod_unfold  image_iff sol'_\<alpha>_eq Coeffs.correct(27)  split: option.splits)
    unfolding Map.graph_def
    by (metis (mono_tags, lifting) IntI VM.num_vars_correct domI ranI var_map_imp_ntv_eq vm_inv)

  have sol_nat_feas: \<open>LPC.sat_lp_list ?cs_nat (v_lookup sol_nat)\<close>
    apply (rule solve_lp_feas)
    using solve_lp assms assms
      apply (auto simp: lp_eq' )
    apply (subst (asm) (3) constrs_to_nat_to_nat_aux'(2))
    using constr_to_nat_distinct
      apply (auto simp: )
    by (metis fst_conv lp_eq' vm_inv_lp_to_nat)

  have sol'_inv: \<open>Coeffs.invar sol'\<close>
    unfolding sol'_eq
    using Coeffs.to_map_correct
    by auto

    have sol_sol'_subs: \<open>dom (Coeffs.\<alpha> sol') \<subseteq> dom (var_map_\<alpha> ?vm'')\<close>
      unfolding dom_sol'
      by auto

    have map_of_sol'_eq_sol_nat: \<open>Map.map_of (fst (coeffs_to_nat sol' ?vm'')) i = v_lookup sol_nat i\<close> if \<open>i < num_vars ?vm''\<close> for i
    proof (cases \<open>v_lookup sol_nat i\<close>)
      case None
      then show ?thesis
        apply (simp only: map_of_eq_None_iff image_iff)
        apply (subst coeffs_to_nat_aux')
        subgoal by auto
        subgoal using sol'_inv .
        subgoal
          using sol_sol'_subs that
          apply auto
          apply (subst (asm) vm_\<alpha>_dom_coeffs_to_nat)
            apply (auto simp: sol'_inv Coeffs.to_list_correct )
          unfolding Map.graph_def
          apply auto
          by (metis option.case(1) option.case(2) option.distinct(1) option.exhaust_sel sol'_\<alpha>_eq)
        done
    next
      case (Some a)
      then show ?thesis
        apply (simp only: map_of_eq_None_iff image_iff)
        apply (subst coeffs_to_nat_aux')
        subgoal by auto
        subgoal using sol'_inv .
        subgoal
          apply (subst map_of_eq_Some_iff)
           apply auto
          using coeffs_to_nat_aux' coeffs_to_nat_distinct sol'_inv vm_inv apply presburger
          apply (auto simp: case_prod_unfold sol'_inv)
          unfolding Map.graph_def
          apply (auto simp: image_iff)
          apply (rule exI[of _ \<open>nat_to_var ?vm'' i\<close>])
          using sol_sol'_subs that
          apply (auto simp: image_iff sol'_\<alpha>_eq split: option.splits)
          apply (subst vm_\<alpha>_dom_coeffs_to_nat)
          by (auto simp: sol'_inv Coeffs.to_list_correct )
        done
    qed
    hence map_of_sol'_eq_sol_nat': \<open>Map.map_of (fst (coeffs_to_nat sol' ?vm'')) = (v_lookup sol_nat |` {..<num_vars ?vm''})\<close>
      using dom_sol' sol'_inv
      apply (auto intro!: ext simp: Map.restrict_map_def map_of_eq_None_iff)
      apply (subst (asm) coeffs_to_nat_aux')
        apply auto
      apply (subst (asm) coeffs_to_nat_aux')
      apply auto
      unfolding Map.graph_def Coeffs.correct(27)
      apply (auto simp add: image_iff)
      subgoal for z y
        apply (subst (asm) vm_coeffs_to_nat_unchanged)
           apply auto
        apply (subst (asm) vm_coeffs_to_nat_unchanged)
           apply auto
        apply (cases \<open>z \<in> dom (var_map_\<alpha> ?vm'')\<close>)
        using VM.num_vars_correct[OF vm_inv]
        unfolding ran_def
         apply auto
        by (metis (no_types, lifting) domI domIff dom_coeffs_to_nat mem_simps(3) option.collapse sol_sol'_subs vm_coeffs_to_nat_unchanged vm_inv)
      done

    have sat_constr_cong: \<open>LPC.sat_constr (c :: ((nat \<times> real) list) \<times> _ \<times> _) v'\<close> if \<open>LPC.sat_constr c v\<close> \<open>\<And>i. i \<in> set (map fst (fst c)) \<Longrightarrow> v i = v' i\<close> for v v' c
      using that
      unfolding LPC.sat_constr_def
      apply (auto split: sense.splits option.splits intro!: sum_list_map_cong simp: LPC.lookup'_def LPC.scalar_prod_list_def case_prod_unfold image_iff)
      by (metis (mono_tags, lifting)  sum_list_map_cong)+
      
  {
    fix c
    let ?sol_nat'' = \<open>(v_lookup sol_nat |` {..<num_vars ?vm''})\<close>
    assume \<open>c \<in> set cs\<close>


    have dom_c_subs: \<open>dom (Coeffs.\<alpha> (constr_code_poly c)) \<subseteq> dom (var_map_\<alpha> ?vm'')\<close>
      unfolding constr_code_poly_def
      using  \<open>c \<in> set cs\<close>      using dom_vm''
      by (auto simp: constr_code_poly_def split: Constr_Code.splits)

    have the_vm_lt_nv: \<open>the (var_map_\<alpha> ?vm'' x) < num_vars ?vm''\<close> if \<open>x \<in> dom (var_map_\<alpha> ?vm'')\<close> for x
      using that VM.num_vars_correct[of \<open>?vm''\<close>]
      apply (cases \<open>var_map_\<alpha> ?vm'' x\<close>)
      by (auto simp: ran_def vm_inv)

    hence \<open>LPC.sat_constr (fst (constr_to_nat c ?vm'')) (v_lookup sol_nat)\<close>
      using sol_nat_feas assms\<open>c \<in> set cs\<close>
      unfolding  LPC.sat_lp_list_def
      apply (subst (asm) constrs_to_nat_to_nat_aux'(2))
      by auto
    hence \<open>LPC.sat_constr (fst (constr_to_nat c ?vm'')) ?sol_nat''\<close>
      apply (rule sat_constr_cong)
      apply (auto split: sense.splits simp add: restrict_map_def constr_to_nat_def case_prod_unfold  split: Constr_Code.splits)
       apply (subst (asm)coeffs_to_nat_aux')
      using \<open>c \<in> set cs\<close> assms(3)[of c]
         apply (auto simp: constr_code_poly_def split: Constr_Code.splits)
       apply (subst (asm) vm_coeffs_to_nat_unchanged)
      using dom_vm'' dom_c_subs the_vm_lt_nv
         apply (auto simp:  split: Constr_Code.splits)
      unfolding Map.graph_def
         apply (auto simp: constr_code_poly_def subset_iff intro!: the_vm_lt_nv split: Constr_Code.splits)
       apply (metis (no_types, lifting) Constr_Code.case(1) constr_code_poly_def domI domIff dom_c_subs dom_coeffs_to_nat mem_simps(3) option.exhaust_sel vm_coeffs_to_nat_unchanged vm_inv)
      subgoal apply (subst (asm)coeffs_to_nat_aux')
      using \<open>c \<in> set cs\<close> assms(3)[of c]
         apply (auto simp: constr_code_poly_def split: Constr_Code.splits)
       apply (subst (asm) vm_coeffs_to_nat_unchanged)
      using dom_vm'' dom_c_subs the_vm_lt_nv
         apply (auto simp:  split: Constr_Code.splits)
      unfolding Map.graph_def
      apply (auto simp: constr_code_poly_def subset_iff intro!: the_vm_lt_nv split: Constr_Code.splits)
      by (metis (no_types, lifting) Constr_Code.case(2) constr_code_poly_def domI domIff dom_c_subs dom_coeffs_to_nat mem_simps(3) option.exhaust_sel vm_coeffs_to_nat_unchanged vm_inv)
    done

    hence \<open>Coeffs.eval_constr_code c sol'\<close>
      apply (cases c)
       apply (auto simp: constr_to_nat_def case_prod_unfold LPC.sat_constr_def)
      subgoal
        apply (subst (asm) scalar_prod_list_eq_prod_map)
        subgoal using assms \<open>c \<in> set cs\<close> unfolding constr_code_poly_def by fastforce
        subgoal 
          apply (subst cross_prod_code_eq_scalar_prod_map[of \<open>?vm''\<close>])
          subgoal by auto
          subgoal using assms \<open>c \<in> set cs\<close> unfolding constr_code_poly_def by fastforce
          subgoal using \<open>Coeffs.invar sol'\<close> .
          subgoal
            using \<open>c \<in> set cs\<close>
            unfolding dom_vm'' constr_code_poly_def
            by (auto split: Constr_Code.splits)
          subgoal using sol_sol'_subs by blast
          subgoal
            apply (subst map_of_sol'_eq_sol_nat')
            unfolding  LPC.scalar_prod_map_def
            by auto
          done
        done

      subgoal
        apply (subst scalar_prod_list_eq_prod_map)
        subgoal using assms(3)[of c] \<open>c \<in> set cs\<close> unfolding constr_code_poly_def
          by (auto split: Constr_Code.splits)
        subgoal 
          apply (subst cross_prod_code_eq_scalar_prod_map[of \<open>?vm''\<close>])
          subgoal by auto
          subgoal using assms \<open>c \<in> set cs\<close> unfolding constr_code_poly_def by fastforce
          subgoal using \<open>Coeffs.invar sol'\<close> .
          subgoal
            using \<open>c \<in> set cs\<close>
            unfolding dom_vm'' constr_code_poly_def
            by (auto split: Constr_Code.splits)
          subgoal using sol_sol'_subs by blast
          subgoal
            apply (subst map_of_sol'_eq_sol_nat')
            unfolding  LPC.scalar_prod_map_def
            by auto
          done
        done
      done
  }
  thus \<open>sol' \<in> Coeffs.sol_space_code cs\<close>
    unfolding sol'_eq Coeffs.sol_space_code_def Coeffs.sol_space_code_constr_def
    apply safe
    subgoal using Coeffs.correct(28) by auto
     apply auto
    using sol'_eq sol'_inv by blast

  have var_map_obj_eq: \<open>i \<in> dom (Coeffs.\<alpha> obj) \<Longrightarrow> var_map_\<alpha> (snd (coeffs_to_nat obj empty_var_map)) i = var_map_\<alpha> (?vm'') i\<close> for i
    by (simp add: assms(2) dom_coeffs_to_nat dom_vm'' inv_coeffs_to_nat)

  have nat_to_var_inj: \<open>inj_on (nat_to_var vm) {..<num_vars vm}\<close> if \<open>var_map_inv vm\<close> for vm
    using that var_map_\<alpha>_nat_to_var[of vm]
    apply (auto intro!: inj_onI)
    by (metis option.simps(1) var_map_\<alpha>_nat_to_var)

  have dom_obj_subs: \<open>dom (Coeffs.\<alpha> obj) \<subseteq> dom (var_map_\<alpha> ?vm'')\<close>
    by (simp add: dom_vm'')

  have \<open>fst ` set (fst (coeffs_to_nat obj empty_var_map)) \<subseteq> {..<num_vars (snd (coeffs_to_nat obj empty_var_map))}\<close>
    apply (auto simp: VM.num_vars_eq_card_dom )
    apply (subst (asm) coeffs_to_nat_aux')
    using assms(2)
      apply auto
    by (metis VM.num_vars_correct domIff dom_obj_subs fst_conv fst_graph_eq_dom fst_image_mp graph_domD lessThan_iff option.exhaust_sel ranI var_map_obj_eq vm_inv_coeffs_to_nat)
  moreover have \<open> {..<num_vars (snd (coeffs_to_nat obj empty_var_map))} \<subseteq> {..<num_vars ?vm''}\<close>
    using assms
    apply (auto simp:  VM.num_vars_eq_card_dom dom_vm'')
    apply (subst VM.num_vars_eq_card_dom)
    by (auto simp: dom_coeffs_to_nat intro!: card_mono)
  ultimately have *: \<open>fst ` set (fst (coeffs_to_nat obj empty_var_map)) \<subseteq> {..<num_vars ?vm''}\<close>
    by auto

    show \<open>Coeffs.cross_prod_code sol' obj = val'\<close>
    proof -
    have \<open>val' = (fold (+) (map (\<lambda>(i, c). Coeffs.lookup0_code (nat_to_var ?vm'' i) sol' * c) ?c_nat) 0)\<close>
      using assms
      unfolding lp_minimize_def 
      by (auto split: option.splits simp: lp_eq')
    also have \<open>\<dots> = (\<Sum>p\<in>set (fst (coeffs_to_nat obj empty_var_map)). 
      Coeffs.lookup0_code (nat_to_var ?vm'' (fst p)) sol' * Coeffs.lookup0_code (nat_to_var ?vm'' (fst p)) obj)\<close>
      unfolding fold_plus case_prod_unfold
      apply (subst sum_list_distinct_conv_sum_set)
      using LPC.distinct_mapD d_c assms(2) sol'_inv
       apply (auto intro!: sum.cong simp: coeffs_to_nat_aux' Coeffs.lookup0_code_def Coeffs.lookup_correct split: option.splits)
      unfolding Map.graph_def
      subgoal using distinct_rev folding_Map_graph.distinct_if_distinct_map by blast
      subgoal for k v apply auto
        apply (subst (asm) (2) var_map_obj_eq)
        apply auto
        apply (subst (asm) (2) var_map_obj_eq)
        using var_map_imp_ntv_eq dom_obj_subs by auto
      subgoal for k v apply auto
        apply (subst (asm) (2) var_map_obj_eq)
        apply auto
        apply (subst (asm) (2) var_map_obj_eq)
        using var_map_imp_ntv_eq dom_obj_subs by auto
      done
    also have \<open>\<dots> = (\<Sum>p\<in>nat_to_var ?vm'' ` fst ` set (fst (coeffs_to_nat obj empty_var_map)).
       Coeffs.lookup0_code p sol' * Coeffs.lookup0_code p obj)\<close>
      apply (subst sum.reindex[of \<open>nat_to_var ?vm''\<close>])
      using nat_to_var_inj[of ?vm''] *
       apply (auto simp: inj_on_def)
      by (metis (mono_tags, lifting) d_c distinct_map sum.reindex_cong)

    also have \<open>\<dots> = (\<Sum>i\<in>dom (Coeffs.\<alpha> sol') \<inter> dom (Coeffs.\<alpha> obj) \<inter> nat_to_var ?vm'' ` fst ` set (fst (coeffs_to_nat obj empty_var_map)). 
      the (Coeffs.\<alpha> sol' i) * the (Coeffs.\<alpha> obj i))\<close>
      using sol'_inv assms(2)
      by (auto intro!: sum.mono_neutral_cong_right simp:  Coeffs.lookup0_code_def  Coeffs.lookup_correct split: option.splits)
    
    also have \<open>\<dots> = (\<Sum>i\<in>dom (Coeffs.\<alpha> sol') \<inter> dom (Coeffs.\<alpha> obj). the (Coeffs.\<alpha> sol' i) * the (Coeffs.\<alpha> obj i))\<close>
      apply (rule sum.cong)
      using assms(2)
       apply (auto simp: image_iff coeffs_to_nat_aux' case_prod_unfold)
      unfolding Map.graph_def
      apply auto
      subgoal for x
        apply (rule exI[of _ x])
        apply (auto simp: )
        apply (subst var_map_obj_eq)
        using dom_obj_subs var_map_imp_ntv_eq by auto
      done
    also have \<open>\<dots> = Coeffs.cross_prod_code sol' obj\<close>
      using sol'_inv assms
      apply (subst cross_prod_code_eq)
      by auto

    finally show ?thesis ..
  qed

  show \<open>Coeffs.cross_prod_code sol' obj \<le> Coeffs.cross_prod_code sol obj\<close> if sol: \<open>sol \<in> Coeffs.sol_space_code cs\<close> for sol
  proof -

    define sol_nat' where \<open>sol_nat' = Map.map_of (fst (coeffs_to_nat sol ?vm'')) |` {..<num_vars ?vm''}\<close>

    have sol_inv[simp, intro]: \<open>Coeffs.invar sol\<close>
      using sol
      unfolding Coeffs.sol_space_code_def
      by auto

    have opt_nat: \<open>LPC.sat_lp_list ?cs_nat x' \<Longrightarrow> 
      LPC.scalar_prod_map (v_lookup sol_nat) (Map.map_of ?c_nat) \<le> LPC.scalar_prod_map x' (Map.map_of ?c_nat)\<close> for x'
      apply (rule solve_lp_opt[OF solve_lp[unfolded lp_eq']])
      using assms  d_cs
        unfolding constr_code_poly_def
        by auto

      have dom_vm_obj[simp]: \<open>dom (var_map_\<alpha> (snd (coeffs_to_nat obj empty_var_map))) = dom (Coeffs.\<alpha> obj)\<close>
        using assms(2) dom_coeffs_to_nat by force

      have obj_nat_vm'': \<open>(fst (coeffs_to_nat obj empty_var_map)) = (fst (coeffs_to_nat obj ?vm''))\<close>
        using assms
        apply (subst ignore_constrs_to_nat)
        using fst_coeffs_to_nat_eq by auto

      have vm_\<alpha>_lt[intro!]: \<open>the (var_map_\<alpha> vm i) < num_vars vm\<close> if \<open>var_map_inv vm\<close> and \<open>i \<in> dom (var_map_\<alpha> vm)\<close>
        for vm i
        using that
        by (metis VM.num_vars_correct domD lessThan_iff option.sel ranI)


      let ?obj = \<open>(Map.map_of (fst (coeffs_to_nat obj empty_var_map)))\<close>
    
      have \<open>vm_rel ?vm'' (v_lookup sol_nat |` {..<num_vars ?vm''}) (Coeffs.\<alpha> sol')\<close>
        unfolding vm_rel_def 
        using sol'_inv dom_sol'
        by (auto simp add: sol'_\<alpha>_eq)

      have map_of_coeffs_to_nat: \<open>Map.map_of (fst (coeffs_to_nat v vm)) i = Coeffs.\<alpha> v (nat_to_var vm i)\<close> 
          if \<open>dom (Coeffs.\<alpha> v) \<subseteq> dom (var_map_\<alpha> vm)\<close> \<open>i < num_vars vm\<close> \<open>var_map_inv vm\<close> \<open>Coeffs.invar v\<close> for v vm i
        using that 
        apply (auto simp: coeffs_to_nat_aux')
        apply (cases \<open> Coeffs.\<alpha> v (nat_to_var vm i)\<close>)
        subgoal
        using var_map_imp_ntv_eq vm_coeffs_to_nat_unchanged
        by (auto simp: map_of_eq_None_iff Map.graph_def) 
      apply auto
      apply (subst map_of_eq_Some_iff)
      subgoal
        using coeffs_to_nat_distinct[of vm]
        by (auto simp: coeffs_to_nat_aux')
      subgoal
        apply (auto simp: case_prod_unfold image_iff Map.graph_def)
        using vm_coeffs_to_nat_unchanged by auto
      done

      have map_of_coeffs_to_nat': \<open>Map.map_of (fst (coeffs_to_nat v vm)) i = Coeffs.\<alpha> v (nat_to_var (snd (coeffs_to_nat v vm)) i)\<close> 
          if \<open>i < num_vars (snd (coeffs_to_nat v vm))\<close> \<open>var_map_inv vm\<close> \<open>Coeffs.invar v\<close> for v vm i
        using that 
        apply (auto simp: coeffs_to_nat_aux')
        apply (cases \<open>Coeffs.\<alpha> v (nat_to_var (snd (coeffs_to_nat v vm)) i)\<close>)
        subgoal
        using var_map_imp_ntv_eq vm_coeffs_to_nat_unchanged
        apply (auto simp: map_of_eq_None_iff Map.graph_def) 
        by (simp add: domD domIff dom_coeffs_to_nat inv_coeffs_to_nat)
      apply auto
      apply (subst map_of_eq_Some_iff)
      subgoal
        using coeffs_to_nat_distinct[of vm]
        by (auto simp: coeffs_to_nat_aux')
      subgoal
        apply (auto simp: case_prod_unfold image_iff Map.graph_def)
        using vm_coeffs_to_nat_unchanged 
        apply (auto intro!: exI[of _ \<open>(nat_to_var (snd (coeffs_to_nat v vm)) i)\<close>])
        by (simp add: inv_coeffs_to_nat)
      done

    have nat_to_var_inverse[simp]: \<open>(nat_to_var vm (the (var_map_\<alpha> vm i))) = i\<close> if \<open>var_map_inv vm\<close> \<open>i \<in> dom (var_map_\<alpha> vm)\<close> for vm i
      using that
      apply auto
      using var_map_imp_ntv_eq by blast

      have dom_map_of_coeffs_to_num_vars: \<open>i < num_vars vm\<close>
        if \<open>i \<in> dom (Map.map_of (fst (coeffs_to_nat v vm)))\<close> \<open>dom (Coeffs.\<alpha> v) \<subseteq> dom (var_map_\<alpha> vm)\<close> \<open>var_map_inv vm\<close> \<open>Coeffs.invar v\<close> for v vm i
        using that
        apply (auto simp: coeffs_to_nat_aux')
        apply (cases \<open>Coeffs.\<alpha> v (nat_to_var (snd (coeffs_to_nat v vm)) i)\<close>)
        subgoal
        using var_map_imp_ntv_eq vm_coeffs_to_nat_unchanged
        by (auto simp: map_of_eq_None_iff Map.graph_def) 
      apply auto
      apply (subst (asm) nat_to_var_inverse)
      apply auto
       apply (auto simp: map_of_eq_None_iff Map.graph_def) 
      using vm_coeffs_to_nat_unchanged by auto


    have fin_dom_vm[intro!]: \<open>finite (dom (var_map_\<alpha> vm))\<close> if \<open>var_map_inv vm\<close> for vm
      using that VM.num_vars_eq_card_dom[of vm]
      by (metis bot_nat_0.extremum_strict card.infinite infinite_imp_elem vm_\<alpha>_lt)

    have num_vars_coeffs_ge: \<open> num_vars (snd (coeffs_to_nat v vm)) \<ge> num_vars vm\<close> if \<open>var_map_inv vm\<close> \<open>Coeffs.invar v\<close>  for v vm
      using that
      apply (auto simp: VM.num_vars_eq_card_dom)
      apply (subst VM.num_vars_eq_card_dom)
       apply (auto intro!: card_mono)
      by (simp add: domI)

        have obj_rel: \<open>vm_rel ?vm'' ?obj (Coeffs.\<alpha> obj)\<close>
        unfolding vm_rel_def
        apply safe
        subgoal by auto
        subgoal by (metis assms(2) domI dom_map_of_coeffs_to_num_vars dom_obj_subs obj_nat_vm'' vm_inv)
        subgoal by (metis (no_types, lifting) domD domI dom_vm_obj var_map_obj_eq)
        subgoal by (simp add: assms(2))
        subgoal apply auto 
          by (metis \<open>\<And>y x. Map.map_of (fst (coeffs_to_nat obj empty_var_map)) x = Some y \<Longrightarrow> x < num_vars (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map))))\<close> assms(2) dom_obj_subs map_of_coeffs_to_nat obj_nat_vm'' vm_inv) 
        by (simp add: \<open>\<And>y x. Coeffs.\<alpha> obj x = Some y \<Longrightarrow> \<exists>y. var_map_\<alpha> (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map)))) x = Some y\<close> assms(2) domIff dom_obj_subs map_of_coeffs_to_nat obj_nat_vm'' vm_\<alpha>_lt)

      have sol_rel: \<open>vm_rel ?vm'' (v_lookup sol_nat |` {..<num_vars ?vm''}) (Coeffs.\<alpha> sol')\<close>
        unfolding vm_rel_def 
        using sol'_inv dom_sol' assms dom_obj_subs
        apply (auto simp add: obj_nat_vm'')
        by (metis map_of_coeffs_to_nat map_of_sol'_eq_sol_nat sol_sol'_subs vm_inv)
        

      moreover have \<open>LPC.scalar_prod_map (v_lookup sol_nat |` {..<num_vars ?vm''}) ?obj =
        Coeffs.cross_prod_code sol' obj\<close>
        apply (rule scalar_prod_map_eqI[of \<open>?vm''\<close>])
        using obj_rel sol_rel
        by auto

      moreover have \<open>LPC.scalar_prod_map (v_lookup sol_nat |` {..<num_vars ?vm''}) ?obj = LPC.scalar_prod_map (v_lookup sol_nat) ?obj\<close>
        using *
        by (auto simp:  LPC.lookup'_def LPC.scalar_prod_map_def intro!: sum.cong)
      ultimately have 1: \<open>LPC.scalar_prod_map (v_lookup sol_nat) ?obj = Coeffs.cross_prod_code sol' obj\<close>
        by auto

      have sol_rel: \<open>vm_rel ?vm'' (sol_nat') (Coeffs.\<alpha> sol |` dom (var_map_\<alpha> ?vm''))\<close>
        unfolding vm_rel_def
        apply safe
        subgoal by auto
        subgoal unfolding sol_nat'_def by (simp add: Misc.restrict_map_eq(2))
        subgoal unfolding sol_nat'_def by (simp)
        subgoal unfolding sol_nat'_def by (simp)
        subgoal unfolding sol_nat'_def
          apply (auto simp add: Misc.restrict_map_eq)
          by (smt (z3) LP_Cert_Code.fst_coeffs_to_nat_eq LP_Cert_Code.var_map_imp_ntv_eq LP_Cert_Code.vm_\<alpha>_dom_coeffs_to_nat LP_Cert_Code_axioms domI dom_coeffs_to_nat dom_map_of_coeffs_to_num_vars inv_coeffs_to_nat map_of_coeffs_to_nat' sol_inv sup_ge1 var_map_\<alpha>_nat_to_var vm_inv)
        subgoal
          apply (auto split: if_splits simp add:assms Misc.restrict_map_eq restrict_map_def map_of_coeffs_to_nat obj_nat_vm'' sol_nat'_def)
           apply (metis LPC.the_default_dom LPC.the_default_simps(2) domI inv_coeffs_to_nat vm_\<alpha>_dom_coeffs_to_nat vm_\<alpha>_lt vm_inv)
          apply (subst map_of_coeffs_to_nat')
              apply auto
           apply (metis LPC.the_default_dom LPC.the_default_simps(2) domI inv_coeffs_to_nat vm_\<alpha>_dom_coeffs_to_nat vm_\<alpha>_lt vm_inv)
          by (metis (mono_tags, lifting) domI inv_coeffs_to_nat var_map_imp_ntv_eq vm_\<alpha>_dom_coeffs_to_nat vm_inv)
        done
  
      moreover have \<open>LPC.scalar_prod_map sol_nat' ?obj = cross_prod (lookup0 (Coeffs.\<alpha> sol |` dom (var_map_\<alpha>  ?vm''))) (lookup0 (Coeffs.\<alpha> obj))\<close>
        apply (rule scalar_prod_map_eqI[of \<open>?vm''\<close>])
        using obj_rel sol_rel
        by auto
        
      moreover have \<open>cross_prod (lookup0 (Coeffs.\<alpha> sol |` dom (var_map_\<alpha>  ?vm''))) (lookup0 (Coeffs.\<alpha> obj)) = Coeffs.cross_prod_code (sol) obj\<close>
        using *
        apply (auto simp:  LPC.lookup'_def LPC.scalar_prod_map_def cross_prod_def lookup0_def restrict_map_def split: if_splits option.splits intro!: sum.cong)
        using dom_obj_subs by auto

      ultimately have 2: \<open>LPC.scalar_prod_map sol_nat' ?obj = Coeffs.cross_prod_code sol obj\<close>
        by auto

      have \<open>LPC.sat_constr (fst (constr_to_nat (cs ! i) ?vm'')) sol_nat'\<close> if \<open>i < length cs\<close> for i
      proof (cases \<open> (cs ! i)\<close>)
        case (Constr_Le a b)
        have a: \<open>Coeffs.invar a\<close> \<open>dom (Coeffs.\<alpha> a) \<subseteq> dom (var_map_\<alpha> ?vm'')\<close>
          using assms(3)[of \<open>cs ! i\<close>] Constr_Le that
          unfolding constr_code_poly_def 
          apply (auto simp: dom_vm'' constr_code_poly_def split: Constr_Code.splits) 
           apply (metis nth_mem)
          by (meson domI nth_mem)
        have vm_rel: \<open>vm_rel ?vm'' (Map.map_of (fst (coeffs_to_nat a (?vm'')))) (Coeffs.\<alpha> a)\<close>
          unfolding vm_rel_def
          apply safe
          subgoal by auto
          subgoal
            using dom_coeffs_to_nat_subs_nv[of a ?vm''] a
            by (auto simp del: dom_map_of_conv_image_fst)
          subgoal using a by auto
          subgoal using a by auto
          subgoal
            apply auto
            by (metis \<open>\<And>y x. Map.map_of (fst (coeffs_to_nat a (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map)))))) x = Some y \<Longrightarrow> x < num_vars (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map))))\<close> a(1) a(2) map_of_coeffs_to_nat vm_inv)
          subgoal
            apply auto
            by (metis \<open>\<And>y x. Coeffs.\<alpha> a x = Some y \<Longrightarrow> \<exists>y. var_map_\<alpha> (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map)))) x = Some y\<close> a(1) a(2) domI map_of_coeffs_to_nat nat_to_var_inverse vm_\<alpha>_lt vm_inv)
          done
        have \<open>sol \<in> Coeffs.sol_space_code_constr (cs ! i)\<close>
          using that sol
          unfolding Coeffs.sol_space_code_def
          by auto
        hence \<open>Coeffs.cross_prod_code a sol \<le> b\<close>
          unfolding Coeffs.sol_space_code_constr_def
          using Constr_Le
          by auto

        moreover have \<open>cross_prod (lookup0 (Coeffs.\<alpha> a)) (lookup0 (Coeffs.\<alpha> sol |` dom (var_map_\<alpha> ?vm''))) = LPC.scalar_prod_list (fst (coeffs_to_nat a (?vm''))) sol_nat'\<close>
          apply (subst scalar_prod_list_eq_prod_map)
          subgoal using a by auto
          using scalar_prod_map_eqI[OF vm_rel] sol_rel
          by auto
        moreover have **: \<open>Coeffs.\<alpha> a = Coeffs.\<alpha> a |` dom (var_map_\<alpha> ?vm'')\<close>
          using a
          apply (auto intro!: ext simp: restrict_map_def)
          by auto
        moreover have  \<open>cross_prod (lookup0 (Coeffs.\<alpha> a)) (lookup0 (Coeffs.\<alpha> sol |` dom (var_map_\<alpha> ?vm''))) = Coeffs.cross_prod_code a sol\<close>
          apply (subst **)
          apply (subst (2) **)
          unfolding cross_prod_def lookup0_def
          by (auto split: option.splits simp: restrict_map_def)

        ultimately have \<open>LPC.scalar_prod_list (fst (coeffs_to_nat a (?vm''))) sol_nat' \<le> b\<close>
          by auto
        then show ?thesis
          using Constr_Le
          by (auto simp: LPC.sat_constr_def constr_to_nat_def case_prod_unfold)
      next
        case (Constr_Eq a b)
        have a: \<open>Coeffs.invar a\<close> \<open>dom (Coeffs.\<alpha> a) \<subseteq> dom (var_map_\<alpha> ?vm'')\<close>
          using assms(3)[of \<open>cs ! i\<close>] Constr_Eq that
          unfolding constr_code_poly_def 
          apply (auto simp: dom_vm'' constr_code_poly_def split: Constr_Code.splits) 
           apply (metis nth_mem)
          by (meson domI nth_mem)
        have vm_rel: \<open>vm_rel ?vm'' (Map.map_of (fst (coeffs_to_nat a (?vm'')))) (Coeffs.\<alpha> a)\<close>
          unfolding vm_rel_def
          apply safe
          subgoal by auto
          subgoal
            using dom_coeffs_to_nat_subs_nv[of a ?vm''] a
            by (auto simp del: dom_map_of_conv_image_fst)
          subgoal using a by auto
          subgoal using a by auto
          subgoal
            apply auto
            by (metis \<open>\<And>y x. Map.map_of (fst (coeffs_to_nat a (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map)))))) x = Some y \<Longrightarrow> x < num_vars (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map))))\<close> a(1) a(2) map_of_coeffs_to_nat vm_inv)
          subgoal
            apply auto
            by (metis \<open>\<And>y x. Coeffs.\<alpha> a x = Some y \<Longrightarrow> \<exists>y. var_map_\<alpha> (snd (constrs_to_nat cs (snd (coeffs_to_nat obj empty_var_map)))) x = Some y\<close> a(1) a(2) domI map_of_coeffs_to_nat nat_to_var_inverse vm_\<alpha>_lt vm_inv)
          done
        have \<open>sol \<in> Coeffs.sol_space_code_constr (cs ! i)\<close>
          using that sol
          unfolding Coeffs.sol_space_code_def
          by auto
        hence \<open>Coeffs.cross_prod_code a sol = b\<close>
          unfolding Coeffs.sol_space_code_constr_def
          using Constr_Eq
          by auto

        moreover have \<open>cross_prod (lookup0 (Coeffs.\<alpha> a)) (lookup0 (Coeffs.\<alpha> sol |` dom (var_map_\<alpha> ?vm''))) = LPC.scalar_prod_list (fst (coeffs_to_nat a (?vm''))) sol_nat'\<close>
          apply (subst scalar_prod_list_eq_prod_map)
          subgoal using a by auto
          using scalar_prod_map_eqI[OF vm_rel] sol_rel
          by auto
        moreover have **: \<open>Coeffs.\<alpha> a = Coeffs.\<alpha> a |` dom (var_map_\<alpha> ?vm'')\<close>
          using a
          apply (auto intro!: ext simp: restrict_map_def)
          by auto
        moreover have  \<open>cross_prod (lookup0 (Coeffs.\<alpha> a)) (lookup0 (Coeffs.\<alpha> sol |` dom (var_map_\<alpha> ?vm''))) = Coeffs.cross_prod_code a sol\<close>
          apply (subst **)
          apply (subst (2) **)
          unfolding cross_prod_def lookup0_def
          by (auto split: option.splits simp: restrict_map_def)

        ultimately have \<open>LPC.scalar_prod_list (fst (coeffs_to_nat a (?vm''))) sol_nat' = b\<close>
          by auto
        then show ?thesis
          using Constr_Eq
          by (auto simp: LPC.sat_constr_def constr_to_nat_def case_prod_unfold)
      qed

      hence 3: \<open>LPC.sat_lp_list ?cs_nat sol_nat'\<close>
        unfolding  LPC.sat_lp_list_def
        using assms
        apply (subst constrs_to_nat_to_nat_aux'(2))
          apply (auto simp:)
        by (auto simp:  List.set_conv_nth)
        
      show ?thesis
        using 1 2 3
        using opt_nat[of sol_nat']
        by auto
    qed
  qed

definition eval_constr :: \<open>_ Constr_Code \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>eval_constr c m = (
    case c of 
    Constr_Le cs r \<Rightarrow> (sum_list (map (\<lambda>(k, v). Coeffs.lookup0_code k m * v) (Coeffs.to_list (cs))) \<le> r) |
    Constr_Eq cs r \<Rightarrow> (sum_list (map (\<lambda>(k, v). Coeffs.lookup0_code k m * v) (Coeffs.to_list (cs))) = r)
)\<close>

definition \<open>constr_kind c = fst c\<close>
definition \<open>constr_rhs c = snd (snd c)\<close>
definition \<open>constr_poly c k = Coeffs.lookup0_code k (fst (snd c))\<close>

type_synonym 'vm_ty lp_ty = \<open>(bool \<times> nat \<times> (nat \<times> real) list \<times> ((nat \<times> real) list \<times> sense \<times> real) list \<times> nat bound list) \<times> 'vm_ty\<close>

fun show_min where
  \<open>show_min True = ''Min''\<close>
| \<open>show_min False = ''Max''\<close>

definition \<open>show_n_vars n = show n\<close>

definition \<open>endl = [CHR 10]\<close>

sublocale Vec: Vec_Inst
  where set_ops = bs_ops
    and dims = dims 
    and doms = doms
  by unfold_locales

end
setup Locale_Code.close_block

type_synonym sparse_vec_ty = \<open>((nat \<times> real)) list\<close>
type_synonym sparse_mat_ty = \<open>(nat \<times> ((nat \<times> real) list)) list\<close>

derive hashable f_name_code
derive hashable var_code

locale LP_Cert_Inst_Defs =
  Coeffs : CoeffsDefs where
    constr_op_map_ops = map_ops
  for
    map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> +
  fixes
    lp_oracle :: \<open>nat \<Rightarrow> sparse_vec_ty \<Rightarrow> sparse_mat_ty \<Rightarrow> sparse_vec_ty \<Rightarrow> sparse_vec_ty LP_Cert option\<close> and 
    dims :: nat and 
    doms :: \<open>nat \<Rightarrow> nat\<close>
begin

print_locale Var_Map_Inst
sublocale Var_Map_Inst where
  map_ops = \<open>ahm_basic_ops\<close>
  by unfold_locales

sublocale Map_rbtm: Map_by_Ordered
  rbtm_empty
  rbtm_update
  rbtm_delete
  rbtm_lookup
  rbtm_inorder
  rbtm_invar
  unfolding rbtm_empty_def rbtm_update_def rbtm_delete_def rbtm_lookup_def rbtm_inorder_def rbtm_invar_def
  by (simp add: M.Map_by_Ordered_axioms)

sublocale Map_rbtm': Map_by_Ordered
  rbtm_empty'
  rbtm_update'
  rbtm_delete'
  rbtm_lookup'
  rbtm_inorder'
  rbtm_invar'
  unfolding rbtm_empty'_def rbtm_update'_def rbtm_delete'_def rbtm_lookup'_def rbtm_inorder'_def rbtm_invar'_def
  by (simp add: M.Map_by_Ordered_axioms)

sublocale Map_am: Map_by_Ordered
  am_empty
  am_update
  am_delete
  am_lookup
  id
  am_invar
  using am_Map_by_Ordered
  by auto

sublocale Map_am': Map_by_Ordered
  am_empty'
  am_update'
  am_delete'
  am_lookup'
  id
  am_invar'
  using am_Map_by_Ordered'
  by auto

print_locale LP_Cert_Code_Defs
sublocale LP_Cert_Code_Defs
  where 
    empty_var_map = empty_var_map and
    num_vars = num_vars and
    nat_to_var = nat_to_var and
    var_to_nat_upd = var_to_nat_upd and
    var_map_\<alpha> = var_map_\<alpha> and
    var_map_inv = var_map_inv and
     
    v_empty = am_empty and
    v_update = am_update and
    v_delete = am_delete and
    v_inv = am_invar and
    v_lookup = am_lookup and
    v_inorder = id and

    m_empty = am_empty' and
    m_update = am_update' and
    m_delete = am_delete' and
    m_inv = am_invar' and
    m_lookup = am_lookup' and
    m_inorder = id and
    map_ops = map_ops
  by unfold_locales

end


locale LP_Cert_Inst =
  LP_Cert_Inst_Defs where map_ops = map_ops +
  Coeffs : Coeffs where
    constr_op_map_ops = map_ops
  for
    map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close>
begin

sublocale LP_Cert_Code
  where 
    empty_var_map = empty_var_map and
    num_vars = num_vars and
    nat_to_var = nat_to_var and
    var_to_nat_upd = var_to_nat_upd and
    var_map_\<alpha> = var_map_\<alpha> and
    var_map_inv = var_map_inv and
     
    v_empty = am_empty and
    v_update = am_update and
    v_delete = am_delete and
    v_inv = am_invar and
    v_lookup = am_lookup and
    v_inorder = id and

    m_empty = am_empty' and
    m_update = am_update' and
    m_delete = am_delete' and
    m_inv = am_invar' and
    m_lookup = am_lookup' and
    m_inorder = id and
    map_ops = map_ops
  by unfold_locales

end

end