theory LP_Code
  imports Main
    "HOL-Library.IArray"
    "HOL-Data_Structures.Array_Braun"
    "rbt/RBT_Map"

    "HOL-Eisbach.Eisbach"
    "HOL.String"
    "Show.Show_Instances"
    "Show.Show_Real_Impl"
    "HOL-Library.Extended_Nat"
    
    LP_Duality.LP_Duality
    Linear_Programming.Linear_Programming

    "Certify_Standard_Form"
begin

typedef real_code = \<open>UNIV :: real set\<close>
  by auto                      

lemma rep_abs_real_code[simp]: \<open>Rep_real_code (Abs_real_code x) = x\<close>
  by (simp add: Abs_real_code_inverse)

setup_lifting type_definition_real_code

typedef rat_pair = \<open>{(x :: int, y :: int) | x y. y \<noteq> 0}\<close>
  by (auto intro!: exI[of _ 1])

setup_lifting type_definition_rat_pair


lift_definition Frct' :: \<open>rat_pair \<Rightarrow> real_code\<close> is \<open>\<lambda>r. real_of_rat (Frct r)\<close> .

lift_definition fst' :: \<open>rat_pair \<Rightarrow> int\<close> is \<open>fst\<close> .
lift_definition snd' :: \<open>rat_pair \<Rightarrow> int\<close> is \<open>snd\<close> .

code_datatype Frct'

lift_definition mul_real_code :: \<open>real_code \<Rightarrow> real_code \<Rightarrow> real_code\<close> is \<open>\<lambda>x y. x * y\<close>.
lift_definition add_real_code :: \<open>real_code \<Rightarrow> real_code \<Rightarrow> real_code\<close> is \<open>\<lambda>x y. x + y\<close>.


lift_definition mul_rat_pair :: \<open>rat_pair \<Rightarrow> rat_pair \<Rightarrow> rat_pair\<close> is \<open>\<lambda>(n1, d1) (n2, d2). (n1 * n2, d1 * d2)\<close>
  by auto

lift_definition add_rat_pair :: \<open>rat_pair \<Rightarrow> rat_pair \<Rightarrow> rat_pair\<close> is \<open>\<lambda>(n1, d1) (n2, d2). 
  (n1 * d2 + n2 * d1, d1 * d2)\<close>
  by auto

lemma real_code_eq_iff[simp]: \<open>(x :: real_code) = (y :: real_code) \<longleftrightarrow> Rep_real_code x = Rep_real_code y\<close>
  using Rep_real_code_inject by force

lemma real_of_rat_mult: \<open>real_of_rat x * real_of_rat y = real_of_rat (x * y)\<close>
  using of_rat_mult
  by metis

lemma mul_real_code[code]: \<open>mul_real_code (Frct' r1) (Frct' r2) = Frct' (mul_rat_pair r1 r2)\<close>
  by (auto simp: mul_real_code.rep_eq Frct'.rep_eq mul_rat_pair.rep_eq case_prod_unfold real_of_rat_mult)
  
lift_definition real_to_code :: \<open>real \<Rightarrow> real_code\<close> is id.

lift_definition code_to_real :: \<open>real_code \<Rightarrow> real\<close> is id.

lemmas Rep_real_code_inverse[code]

lemma snd_rat_pair_nz: \<open>snd (Rep_rat_pair x) \<noteq> 0\<close>
  using Rep_rat_pair[of x] by auto

lemma code_to_real_code[code]: \<open>code_to_real (Frct' x) = fst' x / snd' x\<close>
  by (auto simp: snd_rat_pair_nz Rat.of_rat_rat Frct'.rep_eq code_to_real.rep_eq fst'.rep_eq snd'.rep_eq)

lemmas quotient_of_nonzero(2)[simp]

lift_definition quotient_of' :: \<open>rat \<Rightarrow> rat_pair\<close> is \<open>quotient_of\<close>
  by (meson prod.exhaust_sel quotient_of_nonzero(2))

lemmas real_to_code.rep_eq[simp]

lemma Frct'_quot'_rep[simp]: \<open>Rep_real_code (Frct' (quotient_of' x)) = (Ratreal x)\<close>
  using Fract_of_int_quotient Frct'.rep_eq quotient_of'.rep_eq quotient_of_div by force

lemma real_to_code[code]: \<open>real_to_code (Ratreal x) = Frct' (quotient_of' x)\<close>
  by auto

lift_definition to_rat_pair :: \<open>int \<Rightarrow> int \<Rightarrow> rat_pair\<close> is \<open>\<lambda>i j. if j = 0 then (0,1) else (i, j)\<close> by auto

lemmas add_real_code.rep_eq[simp]
lemmas mul_real_code.rep_eq[simp]

lemma add_real_code[code]: \<open>add_real_code (Frct' r1) (Frct' r2) = Frct' (add_rat_pair r1 r2)\<close>
  by (auto simp: snd_rat_pair_nz Frct'.rep_eq case_prod_unfold add_rat_pair.rep_eq Rat.of_rat_add[symmetric])

datatype 'v LP_Cert = 
    Cert_Opt (prim: 'v) (dual: 'v)
  | Cert_Infeas (farkas: 'v)
  | Cert_Unbounded (sol: 'v) (dir : 'v)

derive "show" LP_Cert

lift_definition show_rat_pair_impl :: \<open>rat_pair \<Rightarrow> string\<close> is \<open>show\<close> .

instantiation rat_pair :: "show"
begin

definition shows_prec_rat_pair :: \<open>nat \<Rightarrow> rat_pair \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_prec_rat_pair n r xs = show_rat_pair_impl r @ xs\<close>

definition shows_list_rat_pair :: \<open>rat_pair list \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_list_rat_pair rs xs = concat (map show_rat_pair_impl rs) @ xs\<close>

instance
  by standard (auto simp: shows_list_rat_pair_def shows_prec_rat_pair_def)
end

definition \<open>show_real_code_impl r = (if (\<exists>r'. r =  Frct' r') then show (THE r'. r = Frct' r') else ''Irrational'')\<close>

instantiation real_code :: "show"
begin
definition shows_prec_real_code :: \<open>nat \<Rightarrow> real_code \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_prec_real_code n r xs = show_real_code_impl r @ xs\<close>

definition shows_list_real_code :: \<open>real_code list \<Rightarrow> char list \<Rightarrow> char list\<close> where
  \<open>shows_list_real_code rs xs = concat (map show_real_code_impl rs) @ xs\<close>

instance
  by standard (auto simp: shows_list_real_code_def shows_prec_real_code_def)
end


instantiation rat_pair :: "zero"
begin

lift_definition zero_rat_pair :: rat_pair is \<open>(0, 1)\<close> by auto

instance by standard
end


instantiation real_code :: "ord"
begin

lift_definition less_eq_real_code :: \<open>real_code \<Rightarrow> real_code \<Rightarrow> bool\<close> is \<open>\<lambda>x y. x \<le> y\<close>.

instance by standard
end



instantiation real_code :: "zero"
begin

lift_definition zero_real_code :: real_code is 0.

instance by standard
end

declare [[ coercion Rep_real_code ]]

lemmas zero_real_code.rep_eq[simp]

lemma Rep_real_code_Frct': \<open>Frct' x = fst' x / snd' x\<close>
  using code_to_real.rep_eq code_to_real_code fst'.rep_eq snd'.rep_eq 
  by auto

lemma Frct'_z[simp]: \<open>Frct' 0 = 0\<close>
  by (auto simp: Rep_real_code_Frct' zero_rat_pair.rep_eq  fst'.rep_eq)

lemmas Frct'_z[symmetric, code]

lift_definition rat_pair_eq :: \<open>rat_pair \<Rightarrow> rat_pair \<Rightarrow> bool\<close> is \<open>\<lambda>(n1, d1) (n2, d2). n1 * d2 = n2 * d1\<close>.

lemma Frct'_eq_iff[code]: \<open>Frct' x = Frct' y \<longleftrightarrow> rat_pair_eq x y\<close>
  by (auto simp flip: of_int_mult 
      simp: Rep_real_code_Frct' frac_eq_eq fst'.rep_eq rat_pair_eq.rep_eq snd'.rep_eq snd_rat_pair_nz split_def)

instantiation real_code :: equal
begin

definition \<open>equal_real_code (r1 :: real_code) r2 \<longleftrightarrow> r1 = r2\<close>

instance
  by standard (auto simp: equal_real_code_def)
end


lemma Frct'_equal_iff[code]: \<open>equal_class.equal (Frct' x) (Frct' y) \<longleftrightarrow> rat_pair_eq x y\<close>
  using Frct'_eq_iff
  by (auto simp: equal_eq)

lift_definition rat_pair_le :: \<open>rat_pair \<Rightarrow> rat_pair \<Rightarrow> bool\<close> is \<open>\<lambda>(a, b) (c, d). let d' = b * d in a * d * d' \<le> c * b * d'\<close>.

lemma pair_commute_eq: \<open>(a, b) = p \<longleftrightarrow> p = (a, b)\<close>
  by auto

lemma Frct'_le_iff[code]: \<open>Frct' x \<le> Frct' y \<longleftrightarrow> rat_pair_le x y\<close>
  using snd_rat_pair_nz[of x]   using snd_rat_pair_nz[of y]
  by (auto simp flip: of_int_mult simp: pair_commute_eq rat_pair_le.rep_eq Rep_real_code_Frct' 
      less_eq_real_code.rep_eq algebra_simps divide_le_eq le_divide_eq fst'.rep_eq snd'.rep_eq)

context Map_by_Ordered
begin

definition "from_list2 xs = foldl (\<lambda>acc (k,v). update k v acc) empty xs"

end

fun unzip where
  "unzip [] = ([], [])"
| "unzip ((x,y)#xs) = (
   let (as, bs) = unzip xs in (x#as, y#bs))"

fun combine_lists' where
"combine_lists' f dx dy ((i::nat,x)#xs) ((j,y)#ys) acc = (
    if i < j then combine_lists' f dx dy xs ((j,y)#ys) (f i x dy acc)
    else if j < i then combine_lists' f dx dy ((i,x)#xs) ys (f j dx y acc)
    else combine_lists' f dx dy xs ys (f i x y acc))"
| "combine_lists' f dx dy ((i,x)#xs) [] acc = combine_lists' f dx dy xs [] (f i x dy acc)"
| "combine_lists' f dx dy [] ((j,y)#ys) acc = combine_lists' f dx dy [] ys (f j dx y acc)"
| "combine_lists' f dx dy [] [] acc = acc"

fun merge_lists where
"merge_lists f ((i::nat,x)#xs) ((j,y)#ys) acc = (
    if i < j then merge_lists f xs ((j,y)#ys) ((i,x)#acc)
    else if j < i then merge_lists f ((i,x)#xs) ys ((j,y)#acc)
    else merge_lists f xs ys ((i, f x y)#acc))"
| "merge_lists f ((i, x)#xs) [] acc = merge_lists f xs [] ((i,x)#acc)"
| "merge_lists f [] ((j, y)#ys) acc = merge_lists f [] ys ((j,y)#acc)"
| "merge_lists f [] [] acc = rev acc"

fun combine_lists where
"combine_lists f ((i :: nat,x)#xs) ((j,y)#ys) acc = (
    if i < j then combine_lists f xs ((j,y)#ys) acc
    else if j < i then combine_lists f ((i,x)#xs) ys acc
    else combine_lists f xs ys (f x y acc))"
| "combine_lists _ _ _ acc = acc"

definition "mult_add x y acc = add_real_code (mul_real_code (real_to_code y) (real_to_code x)) acc"

fun combine_lists'_alt where
"combine_lists'_alt f dx dy ((i :: nat,x)#xs) ((j,y)#ys) = (
    if i < j then f i x dy \<and> combine_lists'_alt f dx dy xs ((j,y)#ys)
    else if j < i then f j dx y \<and> combine_lists'_alt f dx dy ((i,x)#xs) ys
    else (f i x y) \<and> combine_lists'_alt f dx dy xs ys)"
| "combine_lists'_alt f dx dy ((i,x)#xs) [] \<longleftrightarrow> (f i x dy) \<and> combine_lists'_alt f dx dy xs []"
| "combine_lists'_alt f dx dy [] ((j,y)#ys) \<longleftrightarrow> (f j dx y) \<and> combine_lists'_alt f dx dy [] ys"
| "combine_lists'_alt f dx dy [] [] = True"

locale LP_Code =
  Sparse_Vec : Map_by_Ordered v_empty "v_update :: nat \<Rightarrow> real \<Rightarrow> 'v \<Rightarrow> 'v" v_delete v_lookup v_inorder v_inv +
  Sparse_Mat : Map_by_Ordered m_empty "m_update :: nat \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm" m_delete m_lookup m_inorder m_inv
  for v_empty v_update v_delete v_lookup v_inorder v_inv
  and m_empty m_update m_delete m_lookup m_inorder m_inv
begin

definition "v_lookup' v i = (case v_lookup v i of None \<Rightarrow> 0 | Some x \<Rightarrow> x)" 
definition "m_lookup' v i = (case m_lookup v i of None \<Rightarrow> v_empty | Some x \<Rightarrow> x)" 

definition \<open>mat_\<alpha> n m mat_code = mat n m (\<lambda>(i, j). v_lookup' (m_lookup' mat_code i) j)\<close>
definition \<open>vec_\<alpha> n v_code = vec n (\<lambda>i. v_lookup' v_code i)\<close>

fun show_LP :: "nat \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'v \<Rightarrow> String.literal" where 
  "show_LP n c A b =
 String.implode (
  ''vars: '' @ show n @ [CHR 10]
  @ ''obj: '' @ show (v_inorder c) @ [CHR 10]
  @ ''constrs: '' @ concat (map (\<lambda>((_, v), (_, b)). show (v_inorder v) @ '' <= '' @ show b @ [CHR 10]) 
    (zip (m_inorder A) (v_inorder b))) 
  @ ''bounds: '' @ show (v_inorder b))"

definition "show_cert c = String.implode (case c of
  Cert_Opt x y \<Rightarrow> ''Optimal:'' @ CHR 0xA # 
    ''  primal sol: '' @ show (v_inorder x) @ CHR 0xA #
    ''  dual sol: '' @ show (v_inorder y)
| Cert_Infeas f \<Rightarrow> undefined
| Cert_Unbounded x d \<Rightarrow> undefined)
" 

lemma combine_lists_fold:
  assumes \<open>sorted1 xs\<close> \<open>sorted1 ys\<close> 
    \<open>\<And>xs ys X. Finite_Set.comp_fun_commute_on X (\<lambda>(i :: nat) acc. f (xs i :: 'b) (ys i :: 'c) acc) \<close>
  shows \<open>combine_lists f xs ys acc =
  Finite_Set.fold (\<lambda>i acc. f (the (Map.map_of xs (i :: nat))) (the (Map.map_of ys i)) acc) acc (fst ` set xs \<inter> fst ` set ys)\<close>
  using assms
proof (induction f xs ys acc rule: combine_lists.induct)

  case (1 f i x xs j y ys acc)
  show ?case 
    apply (cases \<open>i = j\<close>)
    subgoal using 1 apply auto
    apply (cases \<open>i \<in> fst ` set ys\<close>; cases \<open>j \<in> fst ` set xs\<close>)
    apply auto
    apply (subst Finite_Set.comp_fun_commute_on.fold_insert2[of UNIV])
          apply (auto simp: comp_def)
      subgoal
        using "1.prems"(3)[of UNIV, of \<open>\<lambda>i. (the (if i = j then Some x else Map.map_of xs i))\<close>]
        apply (auto simp: Finite_Set.comp_fun_commute_on_def comp_def strict_sorted_iff intro!: ext )
      apply (rule Finite_Set.fold_cong[of UNIV])
        using "1"(6)      by auto
      done
    apply (cases \<open>i < j\<close>)
    subgoal
      using 1
      by (auto intro!: Finite_Set.fold_cong[of UNIV])
    subgoal
      using "1.IH"(2) "1.prems"
      by (auto intro!: Finite_Set.fold_cong[of UNIV])
    done
next
  case ("2_1" uu uw acc)
  then show ?case by auto
next
  case ("2_2" uu uv acc)
  then show ?case by auto
qed

definition \<open>scalar_prod_code x y = combine_lists mult_add (v_inorder x) (v_inorder y) 0\<close>
definition \<open>scalar_prod_code' x y = (if (v_inorder x) = (v_inorder y) then True else False)\<close>

lemma combine_lists_eq_alt: \<open>combine_lists' (\<lambda>i x y acc. acc \<and> f i x y) xd yd xs ys init \<longleftrightarrow>
  init \<and> combine_lists'_alt f xd yd xs ys\<close>
  by (induction \<open>\<lambda>i x y acc. acc \<and> f i x y\<close> xd yd xs ys init rule: combine_lists'.induct)
    auto

definition "the_default d m = (case m of None \<Rightarrow> d | Some v \<Rightarrow> v)"

lemma the_default_simps[simp]:
  \<open>the_default d None = d\<close>
  \<open>the_default d (Some y) = y\<close>
  unfolding the_default_def 
  by auto

lemma the_default_dom: \<open>i \<in> dom m \<Longrightarrow> the_default d (m i) = the (m i)\<close>
  by auto

lemma the_default_not_dom: \<open>i \<notin> dom m \<Longrightarrow> the_default d (m i) = d\<close>
  unfolding the_default_def by (auto split: option.splits)

lemma the_default_not_dom': \<open>distinct (map fst xs) \<Longrightarrow> i \<notin> fst ` set xs \<Longrightarrow> the_default d (Map.map_of xs i) = d\<close>
  unfolding the_default_def by (force split: option.splits)
  
lemma the_default_dom': \<open>distinct (map fst xs) \<Longrightarrow> i \<in> fst ` set xs \<Longrightarrow> 
  the_default d (Map.map_of xs i) = the (Map.map_of xs i)\<close>
  unfolding the_default_def by (force split: option.splits)

lemma combine_lists'_alt_eq:
  assumes \<open>sorted1 xs\<close> \<open>sorted1 ys\<close> \<open>distinct (map fst xs)\<close> \<open>distinct (map fst ys)\<close>
  shows \<open>combine_lists'_alt f dx dy xs ys = 
  (\<forall>i \<in> dom (Map.map_of xs) \<union> dom (Map.map_of ys).
    f i (the_default dx (Map.map_of xs i)) (the_default dy (Map.map_of ys i)))\<close>
  using assms
  apply (induction f dx dy xs ys arbitrary: rule: combine_lists'_alt.induct)
  subgoal for f dx dy i x xs j y ys
    apply (cases \<open>i = j\<close>)
    subgoal by (auto simp: dom_map_of_conv_image_fst)
    subgoal
      apply (cases \<open>i < j\<close>)
      subgoal 
         apply (cases \<open>i \<in> fst ` set ys\<close>)
        subgoal by auto
        subgoal
          apply (simp add: the_default_dom' the_default_not_dom' dom_map_of_conv_image_fst split: if_splits)
          by blast
        done
      apply simp
         apply (cases \<open>j \<in> fst ` set xs\<close>)
      subgoal by auto
      subgoal
        apply (simp add: the_default_dom' the_default_not_dom' dom_map_of_conv_image_fst split: if_splits)
        by blast
      done
    done
  by (auto simp: dom_map_of_conv_image_fst)

lemmas Frct_def[simp del]

lemmas Frct_code_post[simp]

lemma Frct_quot[simp]: \<open>Frct (quotient_of r) = r\<close>
  using Fract_of_int_quotient Frct_def quotient_of_div by auto

lemma sorted1_inorder[intro!]: \<open>Sparse_Vec.invar x \<Longrightarrow> sorted1 (v_inorder x)\<close>
  by (simp add: Sparse_Vec.invar_def)

lemmas VS_Connect.class_semiring.add.finprod_all1[simp del]
lemmas 
Factorial_Ring.normalization_semidom_class.prime_imp_nonzero[simp del] 
Determinant_Impl.sub2_divisor [simp del]
Determinant_Impl.sub1_divisor [simp del]
VS_Connect.class_semiring.add.finprod_infinite[simp del] 
Determinant_Impl.sub3_divisor [simp del]
Factorial_Ring.comm_semiring_1_class.prime_elem_imp_nonzero[simp del]
lemmas bounds_compare_contradictory[simp del]
lemmas Simplex.bounds_lg[simp del]

lemma Rep_mult_add[simp]: \<open>Rep_real_code (mult_add x y acc) = x * y + Rep_real_code acc\<close>
  unfolding mult_add_def by auto

lemmas code_to_real.rep_eq[simp]

lemma Frct_combine_lists_mult_add: \<open>sorted1 xs \<Longrightarrow> sorted1 ys \<Longrightarrow> 
  (combine_lists mult_add xs ys ab) = ab + (\<Sum>i \<in> fst ` set xs \<inter> fst ` set ys. the (Map.map_of xs i) * the (Map.map_of ys i))\<close>
proof (induction mult_add xs ys ab rule: combine_lists.induct)
  case (1 i x xs j y ys acc)
  have \<open>i \<notin> (fst ` set xs)\<close> \<open>j \<notin> (fst ` set ys)\<close>
    using 1 by auto
  thus ?case
    using 1 by (auto intro!: sum.cong)
qed auto

lemma A_List_map_of_eq_map_of[simp]: \<open>AList_Upd_Del.map_of = Map.map_of\<close>
proof
  fix xs  
  show \<open>AList_Upd_Del.map_of xs = Map.map_of xs\<close>
    by (induction xs) auto
qed

lemma vec_\<alpha>_idx[simp]: \<open>i < d \<Longrightarrow> Sparse_Vec.invar v \<Longrightarrow> vec_\<alpha> d v $ i = v_lookup' v i\<close>
  unfolding vec_\<alpha>_def by simp

lemma in_fstD: \<open>(x, y) \<in> X \<Longrightarrow> x \<in> fst ` X\<close>
  by force

lemmas in_graphD[dest] in_graphI[intro]

lemma set_inorder[simp]: \<open>Sparse_Vec.invar v \<Longrightarrow> set (v_inorder v) = Map.graph (v_lookup v)\<close>
  using Sparse_Vec.inorder_lookup[of v]
  by (auto simp: Sparse_Vec.invar_def strict_sorted_iff)

lemma fst_set_inorder[simp]: \<open>Sparse_Vec.invar x \<Longrightarrow> fst ` set (v_inorder x) = dom (v_lookup x)\<close>
  by (auto simp: image_iff Map.graph_def)

lemma inorder_lookup[simp]: \<open>Sparse_Vec.invar v \<Longrightarrow> Map.map_of (v_inorder v) j = v_lookup v j\<close>
  by (simp add: Sparse_Vec.inorder_lookup Sparse_Vec.invar_def)

lemmas Map.fst_graph_eq_dom[simp]

lemma Frct_scalar_prod_code_eq[simp]:
  assumes \<open>Sparse_Vec.invar x\<close> \<open>Sparse_Vec.invar y\<close>
  shows \<open>(scalar_prod_code x y) = (\<Sum>i \<in> dom (v_lookup x) \<inter> dom (v_lookup y). the (v_lookup x i) * the (v_lookup y i))\<close>
  using assms Frct_combine_lists_mult_add
  unfolding scalar_prod_code_def 
  by fastforce

lemma dim_vec_\<alpha>[simp]: \<open>dim_vec (vec_\<alpha> d v) = d\<close>
  unfolding vec_\<alpha>_def by auto

lemma finite_dom_v_lookup[simp, intro!]: \<open>Sparse_Vec.invar v1 \<Longrightarrow> finite (dom (v_lookup v1))\<close>
  using inorder_lookup by (metis List.finite_set finite_graph_iff_finite_dom local.set_inorder)

lemma Frct0: \<open>Frct (the_default (0, 1) p) = (case p of None \<Rightarrow> 0 | Some r \<Rightarrow> Frct r)\<close>
  apply (cases p)
  by auto

lemma v_lookup_empty[simp]: \<open>v_lookup v_empty i = None\<close>
  by (simp add: Sparse_Vec.map_specs(1))

lemma map_of_map: \<open>Map.map_of (map (\<lambda>(p1, p2). (p1, f (p2))) xs) i = (case Map.map_of xs i of None \<Rightarrow> None | Some r \<Rightarrow> Some (f r))\<close>
  apply (induction xs arbitrary: i)
  by auto

lemma map_of_map': \<open>Map.map_of (map (\<lambda>p. (fst p, f (snd p))) xs) i = (case Map.map_of xs i of None \<Rightarrow> None | Some r \<Rightarrow> Some (f r))\<close>
  apply (induction xs arbitrary: i)
  by auto

lemma combine_lists'_and:
  assumes \<open>sorted1 (xs :: (nat \<times> 'a) list)\<close> \<open>sorted1 (ys :: (nat \<times> 'b) list)\<close>
  shows \<open>combine_lists' (\<lambda>(i :: nat) x y acc. acc \<and> f i x y) dx dy xs ys init \<longleftrightarrow> init \<and>
  (\<forall>i \<in> dom (Map.map_of xs) \<union> dom (Map.map_of ys). f i (the_default dx (Map.map_of xs i)) (the_default dy (Map.map_of ys i)))\<close>
  using assms
proof (induction \<open>(\<lambda>i x y acc. acc \<and> f i x y)\<close> dx dy xs ys init rule:  combine_lists'.induct)
  case (1 dx dy i x xs j y ys acc)
  hence \<open>i \<notin> fst ` set xs\<close> \<open>j \<notin> fst ` set ys\<close> \<open>distinct (map fst xs)\<close> \<open>distinct (map fst ys)\<close>
    by (auto simp: strict_sorted_iff)
  then show ?case
        using \<open>i \<notin> fst ` set xs\<close> 1 
        apply (simp add: the_default_not_dom dom_map_of_conv_image_fst image_iff)
        by (smt (verit, best) UnE dom_map_of_conv_image_fst image_iff order_less_asym the_default_not_dom)
next
  case 2
  thus ?case
    apply simp
    by (metis domD fst_conv map_of_SomeD order_less_irrefl)
next
  case 3
  thus ?case
    apply simp
    by (metis domD fst_conv map_of_SomeD order_less_irrefl)
qed auto

lemma sorted1_merge_lists[intro!]: \<open>sorted1 xs \<Longrightarrow> sorted1 ys \<Longrightarrow> sorted1 (rev zs) \<Longrightarrow> 
  (\<And>i j. i \<in> fst ` set zs \<Longrightarrow> j \<in> fst ` set xs \<Longrightarrow> i < j) \<Longrightarrow>
  (\<And>i j. i \<in> fst ` set zs \<Longrightarrow> j \<in> fst ` set ys \<Longrightarrow> i < j)  \<Longrightarrow> 
  sorted1 (merge_lists f xs ys zs)\<close>
proof (induction f xs ys zs rule: merge_lists.induct)
  case (1 f i x xs j y ys acc)
    consider (lt) \<open>i < j\<close> | (gt) \<open>j < i\<close> | (eq) \<open>i = j\<close> by fastforce
    thus ?case
    proof cases
      case lt
      then show ?thesis
        using 1
        apply (auto intro!: 1(1) simp: sorted_snoc_iff )
        apply (auto)
        by (metis in_fstD)+
    next
      case gt
      then show ?thesis 
        using 1
        apply (auto intro!: 1(2) simp: sorted_snoc_iff )
        apply (auto)
        by (metis in_fstD)+
    next
      case eq
      then show ?thesis 
        using 1
        apply (auto intro!: 1(3) simp: sorted_snoc_iff )
        by fastforce
    qed
  qed (auto simp: sorted_snoc_iff)


lemma sorted1_combine_merge: \<open>sorted1 acc \<Longrightarrow>  (\<And>y. y \<in> snd ` set ys \<Longrightarrow> Sparse_Vec.invar y) \<Longrightarrow> 
   sorted1 xs \<Longrightarrow> sorted1 ys \<Longrightarrow> sorted1
     (combine_lists (\<lambda>y ar acc. merge_lists add_real_code (map (\<lambda>(j, a). (j, mul_real_code (real_to_code y) (real_to_code a))) (v_inorder ar)) acc [])
       xs ys acc)\<close>
proof (induction \<open>(\<lambda>y ar acc. merge_lists add_real_code (map (\<lambda>(j, a). (j, mul_real_code (real_to_code y) (real_to_code a))) (v_inorder ar)) acc [])\<close> xs ys acc rule: combine_lists.induct)
  case (1 i x xs j y ys acc)
  show ?case
    apply (cases \<open>i = j\<close>)
    subgoal
      apply simp
      apply (rule 1(3))
      subgoal using 1 by blast
      subgoal using 1 by blast
      subgoal apply (rule sorted1_merge_lists)
        using "1.prems" by (auto simp: comp_def case_prod_unfold)
      subgoal using  "1.prems" by auto
      using 1 by auto
    using 1
    by auto
qed auto

definition \<open>merge_mul_add = (\<lambda>y ar acc. merge_lists add_real_code (map (\<lambda>(j, a). (j, mul_real_code (real_to_code y) (real_to_code a))) (v_inorder ar)) acc [])\<close>

definition \<open>mat_list_idx M i j = (case Map.map_of M i of None \<Rightarrow> 0 :: real | Some r \<Rightarrow> the_default 0 (v_lookup r j))\<close>
definition \<open>list_idx d xs i = the_default d (Map.map_of xs i)\<close>

lemma map_of_merge_lists: \<open>sorted1 xs \<Longrightarrow> sorted1 ys \<Longrightarrow> distinct (map fst zs) \<Longrightarrow> 
  (\<And>i j. fst ` set zs \<inter> fst ` set xs = {}) \<Longrightarrow>
  (\<And>i j. fst ` set zs \<inter> fst ` set ys = {})  \<Longrightarrow> Map.map_of (merge_lists f xs ys zs) i = 
  (if i \<in> dom (Map.map_of xs) \<and> i \<in> dom (Map.map_of ys) then Some (f (the (Map.map_of xs i)) (the (Map.map_of ys i)))
  else if i \<in> dom (Map.map_of xs) then Map.map_of xs i
  else if i \<in> dom (Map.map_of ys) then Map.map_of ys i
  else Map.map_of zs i)\<close>
proof (induction f xs ys zs arbitrary: i rule: merge_lists.induct)
  case (1 f i x xs j y ys acc idx)
  have \<open>i \<notin> fst ` set xs\<close> \<open>j \<notin> fst ` set ys\<close>
    using 1 by (auto simp: strict_sorted_iff)
  
  then show ?case
    apply (cases \<open>idx = i\<close>; cases \<open>idx = j\<close>)
    subgoal
      using 1
      by (auto split: if_splits simp: dom_map_of_conv_image_fst)
    subgoal 
      apply (cases \<open>j \<notin> fst ` set xs\<close>)
      using 1
      by (auto simp: domIff map_of_eq_None_iff dest!: map_of_SomeD)
    subgoal
      apply (cases \<open>i \<notin> fst ` set ys\<close>)
      using 1
      by (auto simp: domIff map_of_eq_None_iff dest!: map_of_SomeD)
    subgoal
      apply (cases \<open>i < j\<close>)
      subgoal
      apply (cases \<open>i \<notin> fst ` set ys\<close>)
        using 1
        by (auto simp add: domIff map_of_eq_None_iff image_iff dest!: map_of_SomeD)
      apply (cases \<open>i > j\<close>)
      subgoal
        using 1
        apply (cases \<open>j \<notin> fst ` set xs\<close>)
        by (auto simp add: domIff map_of_eq_None_iff image_iff dest!: map_of_SomeD)
      subgoal
        using 1
        by (auto simp add: domIff map_of_eq_None_iff image_iff dest!: map_of_SomeD)
      done
    done
next
  case (2 f i x xs acc idx)
  then show ?case
    apply (cases \<open>i \<notin> fst ` set xs\<close>)
    by (auto simp add: domIff map_of_eq_None_iff image_iff dest!: map_of_SomeD)
next
  case (3 f j y ys acc)
  then show ?case
    apply (cases \<open>j \<notin> fst ` set ys\<close>)
    by (auto simp add: domIff map_of_eq_None_iff image_iff dest!: map_of_SomeD)
next
  case (4 f acc)
  then show ?case
    by (simp add: distinct_map_of_rev)
qed


lemma merge_lists_add:
  assumes \<open>sorted1 xs\<close> \<open>sorted1 ys\<close>
  shows
  \<open>(the_default 0 (Map.map_of (merge_lists add_real_code (xs) ys []) idx)) =
  (the_default 0 (Map.map_of xs idx)) + (the_default 0 (Map.map_of ys idx))\<close>
  apply (subst map_of_merge_lists)
  using assms 
  by (fastforce dest!: map_of_SomeD simp: weak_map_of_SomeI image_iff map_of_map map_of_eq_None_iff split: option.splits)+
 
lemma set_inorder_lookup[simp]: \<open>(i,r) \<in> set (v_inorder v) \<Longrightarrow> Sparse_Vec.invar v \<Longrightarrow> v_lookup v i = Some r\<close>
  by auto
lemmas dom_map_of_conv_image_fst[simp]

lemma Fract_quotient_of[simp]: \<open>Rat.Fract (fst (quotient_of r)) (snd (quotient_of r)) = r\<close>
  using Frct_def Frct_quot by presburger

abbreviation \<open>merge_mul \<equiv> (\<lambda>(y :: real) (ar) (acc :: ((nat \<times> real_code) list)). merge_lists add_real_code (map (\<lambda>(j, a). (j, mul_real_code (real_to_code y) (real_to_code a))) (v_inorder ar)) acc [])\<close>

lemma the_default_not_dom_map_of[simp]: \<open>i \<notin>  fst ` set xs \<Longrightarrow> (the_default d (Map.map_of xs i)) = d\<close>
  by (simp add: the_default_not_dom)

lemma frct_combine_lists:
  \<comment> \<open>f combines (y * ar) + acc\<close>
  fixes xs :: \<open>(nat \<times> real) list\<close> and acc :: \<open>(nat \<times> real_code) list\<close>
assumes \<open>sorted1 xs\<close> \<open>sorted1 ys\<close> \<open>sorted1 acc\<close> \<open>\<And>y. y \<in> snd ` set ys \<Longrightarrow> Sparse_Vec.invar y\<close>
  shows
  \<open>Rep_real_code (list_idx 0 (combine_lists merge_mul xs ys acc) i) = Rep_real_code (list_idx 0 acc i) + (\<Sum>j \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys). list_idx 0 xs j * mat_list_idx ys j i)\<close>
  using assms
proof (induction merge_mul xs ys acc arbitrary: i rule: combine_lists.induct)
  case (1 i x xs j y ys acc idx)
    consider (lt) \<open>i < j\<close> | (gt) \<open>j < i\<close> | (eq) \<open>i = j\<close> by fastforce
    thus ?case
    proof cases
      case lt
      have i_notin: \<open>i \<notin> dom (Map.map_of xs)\<close> using 1 by (auto simp: strict_sorted_iff dom_map_of_conv_image_fst)+
      moreover have j_notin: \<open>j \<notin> dom (Map.map_of ys)\<close> using 1 by (auto simp: strict_sorted_iff dom_map_of_conv_image_fst)+
      ultimately have ij_notin_int: \<open>\<And>i. i \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys) \<Longrightarrow> i \<noteq> j\<close>  \<open>\<And>j. j \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys) \<Longrightarrow> j \<noteq> i\<close>
        by auto
      have i_notin_ys: \<open>i\<notin>  dom (Map.map_of ys)\<close>
        by (metis "1"(5) dom_map_of_conv_image_fst list.map(2) lt not_less_iff_gr_or_eq prod.sel(1) set_map sorted_wrt.simps(2))
      have \<open>(list_idx 0 (combine_lists merge_mul ((i, x) # xs) ((j, y) # ys) acc) idx) = 
            (list_idx 0 (combine_lists merge_mul xs ((j, y) # ys) acc) idx)\<close>
        using lt by simp
      also have \<open>\<dots> = (list_idx 0 acc idx) + (\<Sum>ja\<in>dom (Map.map_of xs) \<inter> dom (Map.map_of ((j, y) # ys)). list_idx 0 xs ja * mat_list_idx ((j, y) # ys) ja idx)\<close>
        using lt
        apply (subst 1(1))
        using "1"(4, 5) by (auto simp: image_iff comp_def case_prod_unfold 1)
      also have \<open>\<dots> = (list_idx 0 acc idx) + (\<Sum>ja\<in>dom (Map.map_of ((i,x)#xs)) \<inter> dom (Map.map_of ((j, y) # ys)). list_idx 0 ((i,x)#xs) ja * mat_list_idx ((j, y) # ys) ja idx)\<close>
        using i_notin j_notin lt ij_notin_int i_notin_ys
        by (auto split: option.splits simp:  list_idx_def Set.Int_insert_right finite_dom_map_of mat_list_idx_def the_default_def sum.insert_if)
      finally show ?thesis .
    next
      case gt
      have i_notin: \<open>i \<notin> dom (Map.map_of xs)\<close> using 1 by (auto simp: strict_sorted_iff dom_map_of_conv_image_fst)+
      moreover have j_notin: \<open>j \<notin> dom (Map.map_of ys)\<close> using 1 by (auto simp: strict_sorted_iff dom_map_of_conv_image_fst)+
      ultimately have ij_notin_int: \<open>\<And>i. i \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys) \<Longrightarrow> i \<noteq> j\<close>  \<open>\<And>j. j \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys) \<Longrightarrow> j \<noteq> i\<close>
        by auto
      have j_notin_xs: \<open>j\<notin>  dom (Map.map_of xs)\<close>
        by (metis "1" dom_map_of_conv_image_fst list.map(2) gt not_less_iff_gr_or_eq prod.sel(1) set_map sorted_wrt.simps(2))
      have \<open>(list_idx 0 (combine_lists merge_mul ((i, x) # xs) ((j, y) # ys) acc) idx) = 
            (list_idx 0 (combine_lists merge_mul ((i, x) # xs) ys acc) idx)\<close>
        using gt by simp
      also have \<open>\<dots> = (list_idx 0 acc idx) + (\<Sum>j\<in>dom (Map.map_of ((i, x) # xs)) \<inter> dom (Map.map_of ys). list_idx 0 ((i, x) # xs) j * mat_list_idx ys j idx)\<close>
        using gt
        apply (subst 1(2))
        using "1"(4, 5) by (auto simp: image_iff comp_def case_prod_unfold 1)
      also have \<open>\<dots> = (list_idx 0 acc idx) + (\<Sum>ja\<in>dom (Map.map_of ((i,x)#xs)) \<inter> dom (Map.map_of ((j, y) # ys)). list_idx 0 ((i,x)#xs) ja * mat_list_idx ((j, y) # ys) ja idx)\<close>
        using i_notin j_notin gt ij_notin_int j_notin_xs
        apply (auto split: option.splits simp:  list_idx_def Set.Int_insert_right finite_dom_map_of mat_list_idx_def the_default_def sum.insert_if)
        by (smt (verit, del_insts) IntE j_notin sum.cong)
      finally show ?thesis.
    next
      case eq
      have i_notin: \<open>i \<notin> dom (Map.map_of xs)\<close> using 1 by (auto simp: strict_sorted_iff dom_map_of_conv_image_fst)+
      moreover have j_notin: \<open>j \<notin> dom (Map.map_of ys)\<close> using 1 by (auto simp: strict_sorted_iff dom_map_of_conv_image_fst)+
      ultimately have ij_notin_int: \<open>\<And>i. i \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys) \<Longrightarrow> \<not> i = j\<close>  \<open>\<And>j. i \<in> dom (Map.map_of xs) \<inter> dom (Map.map_of ys) \<Longrightarrow> \<not> j = i\<close>
        by auto
      have \<open>(list_idx 0 (combine_lists merge_mul ((i, x) # xs) ((j, y) # ys) acc) idx) = 
            (list_idx 0 (combine_lists merge_mul xs ys (merge_mul x y acc)) idx)\<close>
        using eq by simp
      also have \<open>\<dots> = (list_idx 0 (merge_lists add_real_code (map (\<lambda>(j, a). (j, mul_real_code (real_to_code x) (real_to_code a))) (v_inorder y)) acc []) idx) +
    (\<Sum>j\<in>dom (Map.map_of xs) \<inter> dom (Map.map_of ys). list_idx 0 xs j * mat_list_idx ys j idx)\<close>
        using eq 
        apply (subst 1(3))
        using "1"(4, 5) by (auto simp: image_iff comp_def case_prod_unfold 1)

      also have \<open>\<dots> = (list_idx 0 acc idx) + (list_idx 0 (map (\<lambda>(j, a). (j, mul_real_code (real_to_code x) (real_to_code a))) (v_inorder y)) idx) +
    (\<Sum>j\<in>dom (Map.map_of xs) \<inter> dom (Map.map_of ys). list_idx 0 xs j * mat_list_idx ys j idx)\<close>
        unfolding list_idx_def using 1 
        apply (subst merge_lists_add)
          apply (auto simp: comp_def map_of_map' case_prod_unfold map_of_eq_None_iff image_iff split: option.splits)
             apply (subst map_of_map')
           apply (auto simp: image_iff the_default_def map_of_eq_None_iff map_of_map' map_of_eq_Some_iff split: option.splits)
             apply (subst (asm) map_of_map')
             apply auto
           apply (metis in_graphI prod.sel(1))
          apply (subst (asm) map_of_map')
        apply auto           apply (metis in_graphI prod.sel(1))
         apply (subst (asm) map_of_map')
        by auto

      also have \<open>\<dots> = (list_idx 0 acc idx) + (\<Sum>ja\<in>dom (Map.map_of ((i, x) # xs)) \<inter> dom (Map.map_of ((j, y) # ys)). list_idx 0 ((i, x) # xs) ja * mat_list_idx ((j, y) # ys) ja idx)\<close>
        using i_notin j_notin eq
        apply (auto simp: list_idx_def Set.Int_insert_right Set.Int_insert_left)
        using finite_dom_map_of ij_notin_int
         apply (auto split: if_splits option.splits simp: map_of_map the_default_def mat_list_idx_def  cong: sum.cong if_cong)
        using ij_notin_int by (auto simp:  1 mul_rat_pair_def case_prod_unfold Frct_def simp flip: mult_rat)
      finally show ?thesis.
    qed
  qed auto

(* computes A * y *)
definition "y_times_A A y = combine_lists (\<lambda>y ar acc. (
    merge_lists add_real_code (map (\<lambda>(j, a). (j, mul_real_code (real_to_code y) (real_to_code a))) (v_inorder ar)) acc []))
      (v_inorder y) (m_inorder A) []"
lemmas refl[of y_times_A, cong]

definition "check_slackness_x A c x y =
    combine_lists' (\<lambda>i x y acc.
        let ci = real_to_code (v_lookup' c i) in
        acc \<and> (x = 0 \<or> ci = y)) 0 0 (v_inorder x) (y_times_A A y) True"
lemmas refl[of check_slackness_x, cong]

definition "check_slackness_yi A b j x =
  (let 
    bj = real_to_code (v_lookup' b j);
    aj = (m_lookup' A j);
    ax = combine_lists mult_add (v_inorder aj) (v_inorder x) 0
  in
    ax = bj)"
lemmas refl[of check_slackness_yi, cong]


definition "check_slackness_y A b x y = (\<forall>(i, yi) \<in> set (v_inorder y). yi = 0 \<or> check_slackness_yi A b i x)"
lemmas refl[of check_slackness_y, cong]

definition "check_opt A b c x y \<longleftrightarrow> check_slackness_x A c x y \<and> check_slackness_y A b x y"
lemmas refl[of check_opt, cong]

definition \<open>A_times_x A x = map (\<lambda>(j, v). (j, scalar_prod_code v x)) (m_inorder A)\<close>
lemmas refl[of A_times_x, cong]

(* Ax \<le> b \<and> inv x *)
definition \<open>check_feas_primal A b x \<longleftrightarrow> 
  combine_lists' (\<lambda>_ l r acc. acc \<and> l \<le> real_to_code r) 0 0 (A_times_x A x) (v_inorder b) True\<close>
lemmas refl[of check_feas_primal, cong]

(* yA = c \<and> y \<le> 0 \<and> inv y *)
definition \<open>check_feas_dual A c y \<longleftrightarrow>
  combine_lists' (\<lambda>_ l r acc. acc \<and> l = (real_to_code r)) 0 0 (y_times_A A y) (v_inorder c) True \<and>
  list_all (\<lambda>(i, r). r \<le> 0) (v_inorder y)\<close>
lemmas refl[of check_feas_dual, cong]

definition \<open>check_feas A b c x y \<longleftrightarrow> check_feas_primal A b x \<and> check_feas_dual A c y\<close>
lemmas refl[of check_feas, cong]

definition \<open>check_duality b c x y \<longleftrightarrow> (scalar_prod_code c x) = (scalar_prod_code b y)\<close>
lemmas refl[of check_duality, cong]

definition \<open>check_opt' A b c x_code y_code \<longleftrightarrow> check_feas A b c x_code y_code \<and> check_duality b c x_code y_code\<close>
lemmas refl[of check_opt', cong]

definition \<open>check_opt'' A b c x_code y_code \<longleftrightarrow> 
  (Sparse_Vec.invar x_code \<and> Sparse_Vec.invar y_code) \<and> (check_opt' A b c x_code y_code)\<close>
lemmas refl[of check_opt'', cong]

definition \<open>lookup' m i = (case m i of None \<Rightarrow> 0 | Some r \<Rightarrow> r)\<close>

definition \<open>scalar_prod_map m1 m2 = (\<Sum>i \<in> dom m1 \<inter> dom m2. lookup' m1 i * lookup' m2 i)\<close>

definition \<open>feasible_map A b v \<longleftrightarrow> (\<forall>i. scalar_prod_map (v_lookup (m_lookup' A i)) v  \<le> v_lookup' b i)\<close>

definition \<open>feasible_dual_map A c v \<longleftrightarrow> (\<forall>i. (\<Sum>j\<in>dom (m_lookup A). v_lookup' (m_lookup' A j) i * lookup' v j) = v_lookup' c i) 
  \<and> (\<forall>i. lookup' v i \<le> 0)\<close>

definition \<open>mat_code_invar A \<longleftrightarrow> (Sparse_Mat.invar A \<and> (\<forall>i \<in> dom (m_lookup A). Sparse_Vec.invar (the (m_lookup A i))))\<close>

definition \<open>m_code A b = (SOME i. (\<forall>j \<in> dom (m_lookup A) \<union> dom (v_lookup b). j < i))\<close>
definition \<open>n_code A c = (SOME i. (\<forall>j \<in> (\<Union>v \<in> ran (m_lookup A). dom (v_lookup v)) \<union> dom (v_lookup c). j < i))\<close>

lemma fst_m_inorder[simp]: \<open>Sparse_Mat.invar m \<Longrightarrow> fst ` set (m_inorder m) = dom (m_lookup m)\<close>
  using Sparse_Mat.inorder_lookup[of m]
  unfolding Sparse_Mat.invar_def
  by (force simp add: weak_map_of_SomeI image_iff dest!: map_of_SomeD)

lemma map_of_m_inorder[simp]: \<open>Sparse_Mat.invar m \<Longrightarrow> Map.map_of (m_inorder m) = m_lookup m\<close>
  using Sparse_Mat.inorder_lookup[of m]
  unfolding Sparse_Mat.invar_def
  by auto

definition \<open>is_opt_map A b c x \<longleftrightarrow> 
  feasible_map A b x \<and> (\<forall>x'. feasible_map A b x' \<longrightarrow> scalar_prod_map x (v_lookup c) \<le> scalar_prod_map x' (v_lookup c) )\<close>

context
  fixes A b c x_code y_code
  assumes 
    x_inv: \<open>Sparse_Vec.invar x_code\<close> and
    y_inv: \<open>Sparse_Vec.invar y_code\<close> and
    A_inv: \<open>mat_code_invar A\<close> and
    b_inv: \<open>Sparse_Vec.invar b\<close> and
    c_inv: \<open>Sparse_Vec.invar c\<close>
begin

lemma A_invar:
  \<open>\<And>i. i \<in> dom (m_lookup A) \<Longrightarrow> Sparse_Vec.invar (the (m_lookup A i))\<close>
  \<open>\<And>i. Sparse_Vec.invar (m_lookup' A i)\<close>
  \<open>Sparse_Mat.invar A\<close>
  using A_inv 
  unfolding mat_code_invar_def
  by (auto simp add: Sparse_Vec.map_specs(4) domIff m_lookup'_def option.case_eq_if)

lemma sorted1_A: \<open>sorted1 (m_inorder A)\<close>
  using A_invar Sparse_Mat.invar_def by auto

lemma sorted1_A_times_x': \<open>sorted1 (A_times_x A x_code)\<close>
  unfolding A_times_x_def 
  using Sparse_Mat.invar_def A_invar
  by (auto simp: comp_def case_prod_unfold)

lemma set_m_inorder: \<open>Sparse_Mat.invar m \<Longrightarrow> set (m_inorder m) = Map.graph (m_lookup m)\<close>
  by (metis map_of_m_inorder Sparse_Mat.invar_def graph_map_of_if_distinct_dom strict_sorted_iff)

lemma sorted1_y_times_A': \<open>sorted1 (y_times_A A y_code)\<close>
  unfolding y_times_A_def
  using sorted1_A y_inv sorted1_combine_merge A_invar
  apply (intro sorted1_combine_merge)
  by (force simp: set_m_inorder domIff dest!: in_graphD)+

lemma the_default0[simp]: \<open>the_default 0 (v_lookup v i) = v_lookup' v i\<close>
  unfolding v_lookup'_def by (auto split: option.splits)

lemma v_lookup'[simp]: \<open>v_lookup' v i = lookup' (v_lookup v) i\<close>
  by (simp add: lookup'_def v_lookup'_def)

lemma lookup'_dom: \<open>i \<in> dom v \<Longrightarrow> lookup' v i = the (v i)\<close>
  by (metis lookup'_def the_default_def the_default_dom)

lemma lookup'_nz: \<open>lookup' v i \<noteq> 0 \<Longrightarrow> i \<in> dom v\<close>
  by (metis domIff lookup'_def the_default_def the_default_simps(1))

lemma lookup'_zero[simp]: \<open>i \<notin> dom v \<Longrightarrow> lookup' v i = 0\<close>
  by (metis domIff lookup'_def the_default_def the_default_simps(1))

lemma Frct_A_times_x[simp]: \<open>(the_default 0 (Map.map_of (A_times_x A x_code) i)) = scalar_prod_map (v_lookup (m_lookup' A i)) (v_lookup x_code)\<close>
  unfolding A_times_x_def
  apply (auto simp: lookup'_dom x_inv A_invar map_of_map map_of_eq_None_iff scalar_prod_def scalar_prod_map_def split: option.splits)
  using Sparse_Vec.map_specs(1) domIff m_lookup'_def apply fastforce
  apply (subst Frct_scalar_prod_code_eq) 
  using A_invar(1) x_inv
  by (fastforce intro!: sum.cong simp add: m_lookup'_def v_lookup'_def)+

lemma map_of_y_times_A': 
  shows \<open>(the_default 0 (Map.map_of (y_times_A A y_code) i)) = (\<Sum>j\<in> dom (m_lookup A). v_lookup' (m_lookup' A j) i * v_lookup' y_code j)\<close>
  unfolding y_times_A_def
  apply (subst frct_combine_lists[unfolded list_idx_def mat_list_idx_def, of \<open>v_inorder y_code\<close> \<open>m_inorder A\<close> \<open>[]\<close> i])
  using y_inv A_invar sorted1_A apply (auto simp:  lookup'_dom algebra_simps v_lookup'_def m_lookup'_def split: option.splits dest: lookup'_nz intro!: sum.mono_neutral_cong_left)
     apply (metis dom_map_of_conv_image_fst in_fstD map_of_is_SomeI map_of_m_inorder option.sel strict_sorted_iff)
  apply (metis finite_dom_map_of map_of_m_inorder)
  by (metis domI lookup'_dom option.sel)

lemma feasible_dual_correct:
  assumes \<open>check_feas_dual A c y_code\<close>
  shows \<open>feasible_dual_map A c (v_lookup y_code)\<close>
  using assms
  unfolding check_feas_dual_def feasible_dual_map_def
  apply safe
  subgoal for i
  apply (subst (asm) combine_lists'_and)
  subgoal using sorted1_y_times_A' by auto
  subgoal using c_inv by auto
  apply (auto simp: c_inv map_of_y_times_A' lookup'_dom )
  apply (cases \<open>i \<in> fst ` set (y_times_A A y_code) \<union> dom (v_lookup c)\<close>)
   apply auto
  by (smt (verit, ccfv_SIG) map_of_eq_None_iff map_of_y_times_A' sum_mono the_default_simps(1) v_lookup' zero_real_code.rep_eq)
  subgoal
    apply (auto simp: list_all_iff case_prod_unfold v_lookup'_def y_inv  split: option.splits)
    by (metis domD in_graphI le_numeral_extra(3) lookup'_dom lookup'_nz option.sel prod.sel(2))
  done

lemma feasible_primal_correct:
  assumes \<open>check_feas_primal A b x_code\<close>
  shows \<open>feasible_map A b (v_lookup x_code)\<close>
  using assms
  unfolding check_feas_primal_def
  apply (subst (asm) combine_lists'_and)
  subgoal using sorted1_A_times_x' by auto
  subgoal using b_inv by auto
  apply (auto simp: b_inv feasible_map_def )
  by (metis Frct_A_times_x UnCI dom_map_of_conv_image_fst less_eq_real_code.rep_eq lookup'_nz mult_zero_right real_to_code.rep_eq the_default_not_dom zero_le_square zero_real_code.rep_eq)

lemma check_opt''_feas:
  assumes \<open>check_opt'' A b c x_code y_code\<close>
  shows \<open>feasible_map A b (v_lookup x_code)\<close> \<open>feasible_dual_map A c (v_lookup y_code)\<close>
  using assms feasible_primal_correct check_opt''_def check_opt'_def check_feas_def feasible_dual_correct
  by auto 

lemma v_lookup'_in_dom: \<open>i \<in> dom (v_lookup v) \<Longrightarrow> Sparse_Vec.invar v \<Longrightarrow> v_lookup' v i = the (v_lookup v i)\<close>
  unfolding v_lookup'_def by auto

lemma check_opt''_duality:
  assumes \<open>check_opt'' A b c x_code y_code\<close>
  shows \<open>scalar_prod_map (v_lookup c) (v_lookup x_code) = scalar_prod_map (v_lookup b) (v_lookup y_code)\<close>
  using assms   check_feas_def feasible_dual_correct
  unfolding check_opt''_def check_opt'_def check_duality_def scalar_prod_map_def
  by (auto simp: x_inv y_inv c_inv b_inv v_lookup'_in_dom lookup'_dom)

lemmas lookup'_nz[dest]

lemma check_opt''_opt:
  assumes \<open>check_opt'' A b c x_code y_code\<close> \<open>feasible_map A b x'\<close>
  shows \<open>scalar_prod_map (v_lookup x_code) (v_lookup c) \<le> scalar_prod_map x' (v_lookup c)\<close>
proof -

  define n :: nat where \<open>n = (SOME i. \<forall>j \<in> dom (v_lookup c) \<union> (\<Union>v \<in> ran (m_lookup A). dom (v_lookup v)). j < i)\<close>
  define m :: nat where \<open>m = (SOME i. \<forall>j \<in> dom (v_lookup b) \<union> dom (m_lookup A). j < i)\<close>

  have fin_m: \<open>finite (dom (v_lookup b) \<union> dom (m_lookup A))\<close>
    using finite_dom_map_of[of \<open>(m_inorder A)\<close>] A_invar 
    by (auto simp: b_inv)

  have fin_n: \<open>finite (dom (v_lookup c) \<union> (\<Union>v \<in> ran (m_lookup A). dom (v_lookup v)))\<close>
    using fin_m finite_ran A_invar
    by (fastforce intro!: finite_Union simp: c_inv ran_def)
    
  hence n_gt: \<open>\<forall>j \<in> dom (v_lookup c) \<union> (\<Union>v \<in> ran (m_lookup A). dom (v_lookup v)). j < n\<close>
    unfolding n_def finite_nat_set_iff_bounded 
    by (rule someI_ex) 

  hence n_gt': \<open>i \<in> dom (v_lookup c) \<Longrightarrow> i < n\<close> \<open>i \<in> (\<Union>v \<in> ran (m_lookup A). dom (v_lookup v)) \<Longrightarrow> i < n\<close> for i
    by auto

  have m_gt: \<open>\<forall>j \<in> dom (v_lookup b) \<union> dom (m_lookup A). j < m\<close>
    using fin_m unfolding m_def finite_nat_set_iff_bounded by (rule someI_ex) 

  hence m_gt': \<open>i \<in> dom (v_lookup b) \<Longrightarrow> i < m\<close> \<open>i \<in> dom (m_lookup A) \<Longrightarrow> i < m\<close> for i
    by auto

  define x where \<open>x = vec_\<alpha> n x_code\<close>
  define x'' where \<open>x'' = vec n (lookup' x')\<close>

define y where  \<open>y = vec_\<alpha> m y_code\<close>
define A' where  \<open>A' = mat_\<alpha> m n A\<close>
define b' where  \<open>b' = vec_\<alpha> m b\<close>
define c' where  \<open>c' = vec_\<alpha> n c\<close>

  have \<open>scalar_prod_map (v_lookup (m_lookup' A i)) (v_lookup x_code) \<le> v_lookup' b i\<close> for i
    using assms by (auto dest!: check_opt''_feas(1) simp: feasible_map_def)

  hence \<open>A' *\<^sub>v x \<le> b'\<close>
    unfolding less_eq_vec_def
    unfolding b'_def A'_def x_def mat_\<alpha>_def vec_\<alpha>_def 
    apply (auto simp: scalar_prod_def scalar_prod_map_def)
    subgoal for i
      apply (subst sum.mono_neutral_cong_right[of _ \<open>dom (v_lookup (m_lookup' A i)) \<inter> dom (v_lookup x_code)\<close>, OF _ _ _ refl])
      using n_gt' 
      by (auto dest: lookup'_nz simp: domIff m_lookup'_def v_lookup'_def ran_def  split: option.splits) blast+
    done

  have \<open>\<And>i. (\<Sum>j\<in>dom (m_lookup A). v_lookup' (m_lookup' A j) i * v_lookup' y_code j) = v_lookup' c i\<close> \<open>\<And>i. 0 \<ge> v_lookup' y_code i\<close>
    using assms check_opt''_feas unfolding feasible_dual_map_def by auto

  hence \<open>A'\<^sup>T *\<^sub>v y = c'\<close> \<open>y \<le> 0\<^sub>v m\<close>
    unfolding b'_def A'_def x_def y_def mat_\<alpha>_def vec_\<alpha>_def vec_eq_iff c'_def less_eq_vec_def
    apply (auto simp: scalar_prod_def scalar_prod_map_def)
    subgoal for i
      apply (subst sum.mono_neutral_cong_right[of _ \<open>dom (m_lookup A)\<close>, OF _ _ _ refl])
      using m_gt'
      by (auto simp: domIff m_lookup'_def v_lookup'_def split: option.splits)
    done

  have \<open>scalar_prod_map (v_lookup (m_lookup' A i)) x' \<le> v_lookup' b i\<close> for i
    using assms by (auto dest!: check_opt''_feas(1) simp: feasible_map_def)
  hence \<open>A' *\<^sub>v x'' \<le> b'\<close>
    unfolding less_eq_vec_def
    unfolding b'_def A'_def x''_def mat_\<alpha>_def vec_\<alpha>_def 
    apply (auto simp: scalar_prod_def scalar_prod_map_def)
    subgoal for i
      apply (subst sum.mono_neutral_cong_right[of _ \<open>dom (v_lookup (m_lookup' A i)) \<inter> dom (x')\<close>, OF _ _ _ refl])
      using n_gt'
         apply (auto dest: lookup'_nz simp: domIff m_lookup'_def v_lookup'_def split: option.splits)
      by (meson ranI) 
    done

  have LP_Abc: \<open>LP A' b' c'\<close>
    apply unfold_locales
    unfolding A'_def b'_def c'_def vec_\<alpha>_def mat_\<alpha>_def by auto

  have dims: \<open>dim_vec x = n\<close> \<open>dim_vec y = m\<close> \<open>dim_col A' = n\<close>  \<open>dim_row A' = m\<close> \<open>dim_vec x'' = n\<close>
    unfolding x_def y_def A'_def x''_def mat_\<alpha>_def by auto

  have \<open>scalar_prod_map (v_lookup c) (v_lookup x_code) = scalar_prod_map (v_lookup b) (v_lookup y_code)\<close>
    using assms check_opt''_duality by auto

  hence \<open>c' \<bullet> x = b' \<bullet> y\<close>
    unfolding scalar_prod_map_def c'_def b'_def x_def y_def vec_\<alpha>_def scalar_prod_def
    apply auto
    apply (subst sum.mono_neutral_cong_right[of _ \<open>dom (v_lookup c) \<inter> dom (v_lookup x_code)\<close>, OF _ _ _ refl])
    subgoal by auto
    subgoal using n_gt' by fastforce  
    subgoal by (auto dest: lookup'_nz simp: v_lookup'_def split: option.splits)
    apply (subst (2) sum.mono_neutral_cong_right[of _ \<open>dom (v_lookup b) \<inter> dom (v_lookup y_code)\<close>, OF _ _ _ refl])
    subgoal using c_inv b_inv by auto
    subgoal using m_gt' by auto blast
    subgoal by (auto  dest:  simp: v_lookup'_def split: option.splits)
    by auto

  have \<open>c' \<bullet> x \<le> c' \<bullet> x''\<close>
    apply (rule LP.strong_duality_theorem_check''[OF LP_Abc, of _ y])
    using dims \<open>A' *\<^sub>v x \<le> b'\<close> \<open>0\<^sub>v m \<ge> y\<close> \<open>A'\<^sup>T *\<^sub>v y = c'\<close> \<open>c' \<bullet> x = b' \<bullet> y\<close>  \<open>A' *\<^sub>v x'' \<le> b'\<close>
    using carrier_dim_vec by fastforce+

  thus ?thesis
    unfolding c'_def x''_def x_def scalar_prod_def scalar_prod_map_def vec_\<alpha>_def
    apply (auto simp: algebra_simps)
    apply (subst (asm) (2) sum.mono_neutral_cong_right[of _ \<open>dom (v_lookup c) \<inter> dom x'\<close>, OF _ _ _ refl])
    subgoal using c_inv b_inv by auto
    subgoal using n_gt' by fastforce  
    subgoal by (auto simp: v_lookup'_def split: option.splits)
    apply (subst (asm) sum.mono_neutral_cong_right[of _ \<open>dom (v_lookup c) \<inter> dom (v_lookup x_code)\<close>, OF _ _ _ refl])
    subgoal using c_inv b_inv by auto
    subgoal using n_gt' by fastforce  
    subgoal by (auto simp: v_lookup'_def split: option.splits)
    by (simp add: inf.commute)
qed

end

section \<open>Certificate Checking\<close>
definition "check_cert cert A b c = (
  case cert of
    Cert_Opt v1 v2 \<Rightarrow> check_opt'' A b c v1 v2
  | Cert_Infeas f_cert \<Rightarrow> False
  | Cert_Unbounded v1 d \<Rightarrow> False)"

definition "solve oracle A b c n = (
  case oracle n A b c of
    None \<Rightarrow> None
  | Some cert \<Rightarrow> (if check_cert cert A b c then Some cert else None))"

lemma solve_correct:
  assumes \<open>solve oracle A b c n = Some (Cert_Opt x_code y_code)\<close> \<open>mat_code_invar A\<close> \<open>Sparse_Vec.invar b\<close> \<open>Sparse_Vec.invar c\<close>
  shows \<open>is_opt_map A b c (v_lookup x_code)\<close> \<open>Sparse_Vec.invar x_code\<close>
proof -        
  have \<open>check_opt'' A b c x_code y_code\<close>
    using assms unfolding solve_def check_cert_def by (auto split: option.splits if_splits)

  hence \<open>Sparse_Vec.invar x_code\<close> \<open>Sparse_Vec.invar y_code\<close>
    unfolding check_opt''_def by auto

  hence \<open>feasible_map A b (v_lookup x_code)\<close> \<open>feasible_dual_map A c (v_lookup y_code)\<close>
    using check_opt''_feas \<open>check_opt'' A b c x_code y_code\<close>
    using assms
    
    by auto

  thus \<open>is_opt_map A b c (v_lookup x_code)\<close> \<open>Sparse_Vec.invar x_code\<close> 
    using \<open>check_opt'' A b c x_code y_code\<close> assms check_opt''_opt \<open>Sparse_Vec.invar x_code\<close> \<open>Sparse_Vec.invar y_code\<close>
    unfolding is_opt_map_def
    by auto
qed

definition "show_rat (r :: rat) = 
  String.implode (show r)"
definition "show_nat (r :: nat) = 
  String.implode (show r)"

definition "vec_lookup = 
  (Lookup2.lookup :: ((((nat \<times> real) \<times> color) tree) \<Rightarrow> nat \<Rightarrow> real option))"

end
derive "show" tree
derive "show" color
end