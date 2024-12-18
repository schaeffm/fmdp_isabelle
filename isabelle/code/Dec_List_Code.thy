theory Dec_List_Code
  imports 
    "../algorithm/Decision_List_Policy"
    Code_Setup
begin     

section \<open>Util\<close>
lemma sorted_wrt_sort_key: \<open>sorted_wrt (\<lambda>a b. f a \<le> f b) (sort_key f xs)\<close>
  using sorted_map sorted_insort_key
  by (induction xs) fastforce+ 

lemma Un_cong: 
  assumes \<open>\<And>i. i \<in> X \<Longrightarrow> f i = g i\<close>
  shows \<open>(\<Union>i \<in> X. f i) = (\<Union>i \<in> X. g i)\<close>
  using assms
  by auto

lemma Un_cong':
  assumes \<open>X = Y\<close>
  assumes \<open>\<And>i. i \<in> X \<Longrightarrow> f i = g i\<close>
  shows \<open>(\<Union>i \<in> X. f i) = (\<Union>i \<in> Y. g i)\<close>
  using assms
  by auto

lemma restrict_SomeD: \<open>(f |` X) i = Some y \<Longrightarrow> i \<in> X \<inter> dom f\<close>
  by auto

lemma sorted_list_of_set_remove[simp]: 
  assumes \<open>finite X\<close>
  shows \<open>sorted_list_of_set (Set.remove y X) = remove1 y (sorted_list_of_set X)\<close>
  using assms
  unfolding Set.remove_def 
  by (auto simp: sorted_list_of_set_remove)

lemma sorted_list_of_set_upt[simp]: \<open>sorted_list_of_set {..<n} = [0..<n]\<close>
  by (induction n) auto

lemma set_map_filter: \<open>set (List.map_filter f xs) = {the (f x) | x. x \<in> set xs \<and> f x \<noteq> None}\<close>
  unfolding List.map_filter_def
  by auto

lemma image_compr: \<open>f ` {q x | x. P x} = {f (q x) | x. P x}\<close>
  by auto

section \<open>Code equations for computation of a Decision List Policy\<close>
locale DecListPolCodeDefs =
  MDPCodeDefs +
  fixes
    g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a\<close> and
    w_code :: \<open>nat \<Rightarrow> real\<close>
begin

definition actions_nondef_code :: \<open>nat list\<close> where
  \<open>actions_nondef_code = remove1 d_code [0..<actions_code]\<close>
lemmas refl[of \<open>actions_nondef_code\<close>, cong]

definition \<open>U\<^sub>a_code a =
  (let r_range = [reward_dim_code d_code..<reward_dim_code a];
       add_scope = (\<lambda>i. Scope.union (SR.scope (rewards_code a i))) in
   fold add_scope r_range (Scope.empty ()))\<close>
lemmas refl[of \<open>U\<^sub>a_code\<close>, cong]

definition \<open>\<Gamma>\<^sub>a'_code a X = Scope.union (\<Gamma>\<^sub>a_code a X) (\<Gamma>\<^sub>a_code d_code X)\<close>
lemmas refl[of \<open>\<Gamma>\<^sub>a'_code\<close>, cong]

(* TODO: could be precomputed *)
definition \<open>T\<^sub>a_code a = (
  let
    ia_list = Scope.to_list (I\<^sub>a_code a);
    i_sets = Scope.Union_sets (map (\<lambda>i. \<Gamma>\<^sub>a'_code a (SR.scope (h_code i))) ia_list)
  in
    Scope.union (U\<^sub>a_code a) i_sets
)\<close>
lemmas refl[of \<open>T\<^sub>a_code\<close>, cong]

definition \<open>bonus_code a x =
  R\<^sub>a_code a x + l_code * 
  (Scope.set_sum (I\<^sub>a_code a) (\<lambda>i. w_code i * (SR.scoped_\<alpha> (g_cache i a) x - SR.scoped_\<alpha> (g_cache i d_code) x)))\<close>
lemmas refl[of \<open>bonus_code\<close>, cong]

definition dec_list_act_code :: \<open>nat \<Rightarrow> ('b \<times> nat \<times> real) list\<close> where
\<open>dec_list_act_code a = (
  let
    ta = T\<^sub>a_code a;
    ts = assignments_impl ta;
    ts' = List.map_filter (\<lambda>t. let b = bonus_code a t in if b > 0 then Some (t, a, b) else None) ts
  in
    ts'
)\<close>
lemmas refl[of \<open>dec_list_act_code\<close>, cong]


fun dec_list_pol_filter_aux_code where
\<open>dec_list_pol_filter_aux_code X ((t, a) # xs) = 
  (if (\<forall>x \<in> X. \<not>Scope.subset (Vec.scope x) (Vec.scope t) \<or>  \<not>consistent_code t x) 
    then 
      (t, a)#dec_list_pol_filter_aux_code (insert t X) xs 
    else 
      dec_list_pol_filter_aux_code X xs)\<close> |
\<open>dec_list_pol_filter_aux_code X [] = []\<close>


definition \<open>sort_dec_list_code = sort_key (\<lambda>(a, b, c). -c)\<close>
lemmas refl[of \<open>sort_dec_list_code\<close>, cong]

definition dec_list_pol_code :: \<open>('b \<times> nat) list\<close> where 
\<open>dec_list_pol_code = (
  let
    \<pi>_unsorted = (Vec.empty, d_code, 0) # concat (map (dec_list_act_code) actions_nondef_code);
    \<pi>_sorted = sort_dec_list_code \<pi>_unsorted;
    \<pi> = map (\<lambda>(t, a, _). (t, a)) \<pi>_sorted;
    \<pi> = dec_list_pol_filter_aux_code {} \<pi>
  in
    \<pi>
)\<close>
lemmas refl[of \<open>dec_list_pol_code\<close>, cong]

end


context Factored_MDP_Default_Consts
begin

sublocale DecListPol_Consts
  where 
    assignment_list = assignments_abs and 
    actions_nondef = \<open>sorted_list_of_set (Set.remove d actions)\<close> and
    sort_dec_list = \<open>sort_key (\<lambda>(_, _, b). -b)\<close>
  by unfold_locales

end

context Factored_MDP_Default
begin

lemma sorted_wrt_le_bonus: \<open>sorted_wrt le_bonus (sort_key (\<lambda>(_, _, b). - b) xs)\<close>
  unfolding le_bonus_def case_prod_unfold
  by (rule sorted_wrt_mono_rel[OF _ sorted_wrt_sort_key]) auto

lemma distinct_assignments_abs: \<open>xs \<subseteq> vars \<Longrightarrow> distinct (assignments_abs xs)\<close>
  by (auto simp add: assignments_abs_def distinct_assignments_abs_aux)

sublocale DecListPol
  where 
    assignment_list = assignments_abs and 
    actions_nondef = \<open>sorted_list_of_set (Set.remove d actions)\<close> and
    sort_dec_list = \<open>sort_key (\<lambda>(_, _, b). -b)\<close>
  using sorted_wrt_le_bonus distinct_assignments_abs actions_fin
  by unfold_locales auto

end

locale DecListPolCode =
  DecListPolCodeDefs + 
  MDPCode
begin

end

print_locale DecListPolCode
locale Dec_List_Pol_Code_Transfer =
  MDP_Code_Transfer
  where 
    actions = actions +
  DecListPolCodeDefs
for
  actions :: \<open>nat set\<close> +
fixes w
begin

end

locale Dec_List_Pol_Code_Transfer_Rel =
  Dec_List_Pol_Code_Transfer +
  MDP_Code_Transfer_Rel + 
  DecListPolCode + 
assumes 
  w_rel: \<open>w_rel w_code w\<close>  and 
  g_cache[simp]: \<open>g_cache = g_code\<close>
begin

lemma w_code_correct[simp]: \<open>i < h_dim \<Longrightarrow> w_code i = w i\<close>
  using w_rel
  unfolding w_rel_def
  by auto

lemma upt_actions_code[simp]: \<open>[0..<actions_code] = sorted_list_of_set actions\<close>
  by (auto simp flip: actions_rel)

lemma actions_nondef_code_correct_eq[simp]: 
  \<open>actions_nondef_code = actions_nondef\<close>
  unfolding actions_nondef_code_def actions_nondef_def using actions_fin by auto

section \<open>@{const U\<^sub>a}\<close>

lemma U\<^sub>a_code_rel:
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.set_rel (U\<^sub>a_code a) (U\<^sub>a a)\<close>
  unfolding U\<^sub>a_code_def U\<^sub>a_def Let_def
  using assms default_act
  supply Scope.fold_union[subst]
  by fastforce  

lemma U\<^sub>a_code_set[simp]:
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.\<alpha> (U\<^sub>a_code a) = U\<^sub>a a\<close>
  using assms U\<^sub>a_code_rel by auto

lemma U\<^sub>a_code_invar[intro, simp]:
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.invar (U\<^sub>a_code a)\<close>
  using assms U\<^sub>a_code_rel by auto

section \<open>@{const "\<Gamma>\<^sub>a'"}\<close>

lemma \<Gamma>\<^sub>a'_code_rel: 
  assumes \<open>a \<in> actions\<close> \<open>Scope.set_rel X_code X\<close> \<open>X \<subseteq> vars\<close>
  shows \<open>Scope.set_rel (\<Gamma>\<^sub>a'_code a X_code) (\<Gamma>\<^sub>a' a X)\<close>
  using assms default_act unfolding \<Gamma>\<^sub>a'_code_def \<Gamma>\<^sub>a'_def 
  by auto

lemma \<Gamma>\<^sub>a'_code_correct[simp]: 
  assumes \<open>a \<in> actions\<close> \<open>Scope.set_rel X_code X\<close> \<open>X \<subseteq> vars\<close>
  shows \<open>Scope.\<alpha> (\<Gamma>\<^sub>a'_code a X_code) = \<Gamma>\<^sub>a' a X\<close>
  using assms \<Gamma>\<^sub>a'_code_rel by blast

lemma \<Gamma>\<^sub>a'_code_correct'[simp]: 
  assumes \<open>a \<in> actions\<close> \<open>Scope.invar X_code\<close> \<open>Scope.\<alpha> X_code \<subseteq> vars\<close>
  shows \<open>Scope.\<alpha> (\<Gamma>\<^sub>a'_code a X_code) = \<Gamma>\<^sub>a' a (Scope.\<alpha> X_code)\<close>
  using assms \<Gamma>\<^sub>a'_code_rel by blast


lemma \<Gamma>\<^sub>a'_code_invar[intro]: 
  assumes \<open>a \<in> actions\<close> \<open>Scope.set_rel X_code X\<close> \<open>X \<subseteq> vars\<close>
  shows \<open>Scope.invar (\<Gamma>\<^sub>a'_code a X_code)\<close>
  using assms \<Gamma>\<^sub>a'_code_rel by blast

lemma \<Gamma>\<^sub>a'_code_invar'[intro, simp]: 
  assumes \<open>a \<in> actions\<close> \<open>Scope.invar X_code\<close> \<open>Scope.\<alpha> X_code \<subseteq> vars\<close>
  shows \<open>Scope.invar (\<Gamma>\<^sub>a'_code a X_code)\<close>
  using assms \<Gamma>\<^sub>a'_code_rel by blast

section \<open>@{const T\<^sub>a}\<close>

lemma T\<^sub>a_code_rel:
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.set_rel (T\<^sub>a_code a) (T\<^sub>a a)\<close>
proof -
  let ?X_code = \<open>Scope.Union_sets (map (\<lambda>i. (\<Gamma>\<^sub>a'_code a (SR.scope (h_code i)))) (Scope.to_list (I\<^sub>a_code a)))\<close>


  have \<open>Scope.\<alpha> ?X_code = (\<Union>i\<in>I\<^sub>a a. \<Gamma>\<^sub>a' a (h_scope i))\<close>
    by (subst Scope.Union_sets_correct) (auto intro!: Un_cong simp: assms)

  hence \<open>Scope.set_rel ?X_code (\<Union>i\<in>I\<^sub>a a. \<Gamma>\<^sub>a' a (h_scope i))\<close>
    using assms
    by fastforce

  thus ?thesis
    using assms default_act unfolding T\<^sub>a_code_def T\<^sub>a_def
    by force
qed

lemma T\<^sub>a_code_correct[simp]: 
  assumes \<open>a \<in> actions\<close>
  shows \<open>Scope.\<alpha> (T\<^sub>a_code a) = T\<^sub>a a\<close>
  using assms T\<^sub>a_code_rel
  by auto

lemma T\<^sub>a_impl_invar[intro!, simp]: \<open>a \<in> actions \<Longrightarrow> Scope.invar (T\<^sub>a_code a)\<close>
  using T\<^sub>a_code_rel 
  by auto

section \<open>@{const bonus}\<close>

lemma bonus_code_correct[simp, intro]:
  assumes \<open>a \<in> actions\<close> \<open>state_rel x_code x\<close> \<open>T\<^sub>a a \<subseteq> dom x\<close>
  shows \<open>bonus_code a x_code = bonus' w a x\<close>
  unfolding bonus_code_def
  using assms
  supply bonus_eq_effects[subst] R\<^sub>a_impl_correct[subst]
  by (auto intro!: sum.cong arg_cong2[where f = \<open>(*)\<close>] arg_cong2[where f = \<open>(-)\<close>] g_impl_correct simp: bonus'_def)+

section \<open>dec list act\<close>

lemma set_dec_list_act_impl: \<open>set (dec_list_act_code a) = 
  {(t, a, bonus_code a t) | t. 
    t \<in> set (assignments_impl (T\<^sub>a_code a)) \<and> bonus_code a t > 0}\<close>
  unfolding dec_list_act_code_def
  by (auto simp: set_map_filter Let_def)

lemma dec_list_act_code_correct: 
  assumes \<open>a \<in> actions\<close>
  shows \<open>rel_set (rel_prod state_rel (rel_prod (=) (=))) (set (dec_list_act_code a))
  {(t, a, (bonus' w a) t) | t. t \<in> partial_states_on_eq (T\<^sub>a a) \<and> (bonus' w a) t > 0}\<close>
  unfolding set_dec_list_act_impl
proof (intro rel_setI, goal_cases)
  case (1 x)
  then show ?case 
    using assignments_impl_set[of \<open>(T\<^sub>a_code a)\<close> \<open>T\<^sub>a a\<close>] assms
    by (auto simp: T\<^sub>a_dims dest!: rel_setD1) (auto intro!: exI)
next
  case (2 y)
  then show ?case
    using assignments_impl_set[of \<open>(T\<^sub>a_code a)\<close> \<open>T\<^sub>a a\<close>] assms
    by (auto simp: T\<^sub>a_dims dest!: rel_setD2) (auto intro!: exI)
qed

lemma dec_list_act_code_rel: 
  assumes \<open>a \<in> actions\<close>
  shows \<open>list_all2 (rel_prod state_rel (rel_prod (=) (=))) ((dec_list_act_code a)) (dec_list_act w a)\<close>
proof -
  have \<open>list_all2 state_rel 
    (filter (\<lambda>x. 0 < bonus_code a x) (assignments_impl (T\<^sub>a_code a)))
    (filter (\<lambda>t. 0 < bonus' w a t) (assignments_abs (T\<^sub>a a)))\<close>
    using assms T\<^sub>a_dims 
    by (force intro!: list_rel_filterI assignments_rel rel_funI)

  thus ?thesis
    unfolding dec_list_act_code_def dec_list_act_def List.map_filter_def Let_def comp_def
    using assms
    by (fastforce intro!: list_rel_mapI rel_funI simp: set_assignments_abs[OF T\<^sub>a_dims] dest!: partial_states_on_eq_domD)
qed

section \<open>sort dec list\<close>

lemma sort_dec_list_impl_sort_fn: 
  \<open>mset (sort_dec_list_code xs) = mset xs\<close>
  \<open>sorted_wrt (\<lambda>(_, _, b) (_, _, b'::real). b \<ge> b') (sort_dec_list_code xs)\<close>
  using sorted_wrt_sort_key[of \<open>(\<lambda>(_, _, c). - c)\<close> xs]
  by (auto simp: case_prod_beta split_beta' sort_dec_list_code_def)

section \<open>@{term dec_list_pol}\<close>

lemma actions_nondef_eq[simp]: \<open>actions_nondef = sorted_list_of_set (Set.remove d actions)\<close>
  using actions_nondef_def .

lemma \<pi>_unsorted_rel: 
  \<open>list_all2 
  (rel_prod state_rel (rel_prod (=) (=))) 
  ((Vec.empty, d, 0) # concat (map (dec_list_act_code) actions_nondef_code)) 
  (\<pi>_unsorted w)\<close>
  using dec_list_act_code_rel
  by (fastforce simp: zip_map_map zip_same intro!: list_all2I List.concat_transfer[THEN rel_funD])

lemma insort_key_map:
  assumes \<open>\<And>x. x \<in> Set.insert a (set xs) \<Longrightarrow> k x = k' (f x)\<close>
  shows \<open>map f (insort_key k a xs) = insort_key k' (f a) ((map f xs))\<close>
  using assms
  by (induction xs arbitrary: a) auto

lemma map_sort_key:
  assumes \<open>\<And>x. x \<in> set xs \<Longrightarrow> k x = k' (f x)\<close>
  shows \<open>map f (sort_key k xs) = sort_key k' (map f xs)\<close>
  using assms insort_key_map[of _ \<open>sort_key k _\<close> k k']
  by (induction xs) auto

lemma sort_dec_list_impl_map: \<open>sort_dec_list_code (map (\<lambda>(x, a). (f x, a)) xs) =
  map (\<lambda>(x, a). (f x, a)) (sort_dec_list_code xs)\<close>
  unfolding sort_dec_list_code_def
  by (subst map_sort_key) auto

lemma sort_dec_list_impl_map': \<open>sort_dec_list_code (map (\<lambda>(x, a, b). (f x, a, b)) xs) = 
  map (\<lambda>(x, a, b). (f x, a, b)) (sort_dec_list_code xs)\<close>
  using sort_dec_list_impl_map by auto

lemma insort_rel:
  assumes 
  \<open>list_all2 R_elem xs ys\<close>
  and \<open>fx x = fy y\<close> and \<open>R_elem x y\<close>
  and \<open>list_all2 (\<lambda>x y. fx x = fy y) xs ys\<close>
shows \<open>list_all2 R_elem (insort_key fx x xs) (insort_key fy y ys)\<close>
  using assms
  by (induction xs arbitrary: ys) auto

lemma sort_key_rel_aux:
  assumes \<open>list_all2 R_elem xs ys\<close> \<open>list_all2 (\<lambda>x y. fx x = fy y) xs ys\<close>
  shows \<open>list_all2 R_elem (sort_key fx xs) (sort_key fy ys) \<and> list_all2 (\<lambda>x y. fx x = fy y) (sort_key fx xs) (sort_key fy ys)\<close>
  using assms
  by (induction xs arbitrary: ys) (auto intro!: insort_rel simp: list_all2_Cons1)

lemma sort_key_rel:
  assumes \<open>list_all2 R_elem xs ys\<close> \<open>list_all2 (\<lambda>x y. fx x = fy y) xs ys\<close>
  shows \<open>list_all2 R_elem (sort_key fx xs) (sort_key fy ys)\<close>
  using assms sort_key_rel_aux
  by blast

lemma \<pi>_sorted_rel: \<open>
  list_all2 
    (rel_prod state_rel (rel_prod (=) (=)))
    ((sort_dec_list_code ((Vec.empty, d_code, 0) # concat (map (dec_list_act_code) actions_nondef_code))))
    ((\<pi>_sorted w))\<close>
  using \<pi>_unsorted_rel
  unfolding sort_dec_list_code_def rel_prod_conv
  by (intro sort_key_rel) (auto simp add: list_all2_conv_all_nth)

lemma dec_list_pol_filter_aux_rel: \<open>list_all2 (rel_prod state_rel (=)) xs ys \<Longrightarrow> rel_set (state_rel) X Y \<Longrightarrow>
  list_all2 (rel_prod state_rel (=)) (dec_list_pol_filter_aux_code X xs) (dec_list_pol_filter_aux Y ys)\<close>
  apply (induction xs arbitrary: ys X Y rule: list.induct)
  subgoal by auto
  subgoal premises p
    for x xs ys X Y
    apply (cases ys; cases x)
    subgoal using p by auto
    using p(2, 3)
    apply auto
    subgoal apply (rule p(1))
      using Lifting_Set.insert_transfer[THEN rel_funD, THEN rel_funD]
      by metis+
    subgoal for s _  _ s_code t 
      using consistent_code_eq[of s_code s _ t]
      apply (cases \<open>dom t \<subseteq> dom s\<close>)
       apply (cases \<open>\<exists>t_code \<in> X. state_rel t_code t\<close>)
      apply (metis Scope.subset_correct local.Vec.scope_correct local.Vec.scope_invar local.Vec.state_rel_idx local.Vec.state_rel_invar)
      by (auto dest: rel_setD2)
    subgoal for y _ _ x_code t_code
      using p(2)
      apply auto
       apply (cases \<open>\<exists>t \<in> Y. state_rel t_code t\<close>)
      using Scope.subset_correct apply force
      by (auto dest: rel_setD1)
    subgoal apply (rule p(1))
      using Lifting_Set.insert_transfer[THEN rel_funD, THEN rel_funD]
      by metis+
    done
  done

lemma dec_list_pol_impl_correct: 
  \<open>list_all2 (rel_prod state_rel (=)) (dec_list_pol_code) (dec_list_pol_filter (dec_list_pol w))\<close>
  unfolding dec_list_pol_def dec_list_pol_code_def Let_def dec_list_pol_filter_def
  apply (rule dec_list_pol_filter_aux_rel)
  using \<pi>_sorted_rel  Lifting_Set.empty_transfer
  unfolding dec_list_pol_code_def dec_list_pol_def 
  by (auto intro!: list_rel_mapI)

end
end
