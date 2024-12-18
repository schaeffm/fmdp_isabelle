theory Inst_Code
  imports 
    Code_Setup
    Factored_LP_Code
    "../algorithm/Inst"
begin

type_synonym var_code_ty = \<open>(nat option list \<times> nat \<times> bool, nat option list) var_code\<close>

locale InstCodeDefs =
  MDPCodeDefs sr_ops _ _ _ _ pmf_set_ops +
  STE: ScopedFnToErealDefs ste_ops sr_ops er_ops +
  Coeffs: CoeffsDefs constr_map_ops
  for
    sr_ops :: \<open>('f, 'v, 'natset) scoped_fn_real_ops\<close> and
    ste_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
    er_ops and
    pmf_set_ops :: "(nat, 'pmf_set) oset_ops" and
    constr_map_ops :: \<open>(var_code_ty, real, 'm) map_ops\<close> +
  fixes
    g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'f\<close> and

    ts_code :: \<open>'v list\<close> and \<comment> \<open>partial states in decision list prefix\<close>
    t_code :: \<open>'v\<close> and \<comment> \<open>current (partial) state\<close>
    a_code :: \<open>nat\<close> \<comment> \<open>current action\<close>
begin

definition \<open>show_state x = Vec.vec_to_list x\<close>
lemmas refl[of show_state, cong]

print_locale FactoredLPCodeDefs
sublocale FactoredLPCodeDefs
  where 
    ereal_ops = er_ops and 
    to_ereal_ops = ste_ops and 
    real_ops = sr_ops and
    show_state = show_state and
    prefix_code = \<open>(show_state t_code, a_code, pos)\<close>
  for
    pos and 
    B_code 
    C_code
  by unfold_locales

definition factored_lp_code :: \<open>bool \<Rightarrow> 'f list \<Rightarrow> 'ef list \<Rightarrow> 'm Constr_Code list\<close> where
 \<open>factored_lp_code pos c b = elim_vars_code c b pos\<close>
          
definition \<open>bellman_diff_code (i :: nat) = (SR.diff (h_code i) (SR.scale (g_cache i a_code) l_code))\<close>
lemmas refl[where t = \<open>bellman_diff_code\<close>, cong]

definition \<open>hg_inst_code i = SR.inst (bellman_diff_code i) t_code\<close>
lemmas refl[where t = \<open>hg_inst_code\<close>, cong]

definition \<open>C_code = map hg_inst_code [0..<h_dim_code]\<close>
lemmas refl[where t = \<open>C_code\<close>, cong]

definition \<open>neg_C_code = map (\<lambda>f. SR.scale f (-1)) C_code\<close>
lemmas refl[where t = \<open>neg_C_code\<close>, cong]

definition \<open>C'_code = C_code\<close>
lemmas refl[where t = \<open>C'_code\<close>, cong]

definition \<open>neg_C'_code = neg_C_code\<close>
lemmas refl[where t = \<open>neg_C'_code\<close>, cong]

definition \<open>r_inst_code i = SR.inst (rewards_code a_code i) t_code\<close>
lemmas refl[where t = \<open>r_inst_code\<close>, cong]

definition \<open>b_code = map r_inst_code [0..<reward_dim_code a_code]\<close>
lemmas refl[where t = \<open>b_code\<close>, cong]

definition \<open>neg_b_code = map (\<lambda>f. SR.scale f (-1)) b_code\<close>
lemmas refl[where t = \<open>neg_b_code\<close>, cong]

definition \<open>\<I>'_code = map (\<lambda>t'. STE.SE.inst (STE.SE.ind t') t_code) ts_code\<close>
lemmas refl[where t = \<open>\<I>'_code\<close>, cong]

definition \<open>b'_code = map STE.to_ereal b_code @  \<I>'_code\<close>
lemmas refl[where t = \<open>b'_code\<close>, cong]

definition \<open>neg_b'_code = map STE.to_ereal neg_b_code @ \<I>'_code\<close>
lemmas refl[where t = \<open>neg_b'_code\<close>, cong]

definition \<open>\<Omega>_pos_code = factored_lp_code True C'_code neg_b'_code\<close>
lemmas refl[where t = \<open>\<Omega>_pos_code\<close>, cong]

definition \<open>\<Omega>_neg_code = factored_lp_code False neg_C'_code b'_code\<close>
lemmas refl[where t = \<open>\<Omega>_neg_code\<close>, cong]

definition \<open>\<Omega>_code = \<Omega>_pos_code @ \<Omega>_neg_code\<close>
lemmas refl[where t = \<open>\<Omega>_code\<close>, cong]

end

locale InstCode =
  InstCodeDefs 
  where 
    sr_ops = sr_ops and 
    sp_ops = sp_ops and
    er_ops = er_ops and
     constr_map_ops = constr_map_ops+
    MDPCode
  where 
    sr_ops = sr_ops +
    STE: ScopedFnToEreal ste_ops sr_ops er_ops
    + 
Coeffs constr_map_ops
  for 
    sr_ops
    er_ops
    constr_map_ops

locale InstCode_Transfer = 
  MDP_Code_Transfer +
  InstCodeDefs +
  STE: ScopedFnToEreal ste_ops sr_ops er_ops +
  fixes
    ts :: \<open>nat state list\<close> and
    t :: \<open>nat state\<close> and
    a :: nat
begin

definition \<open>t_rel = state_rel t_code t\<close>
definition \<open>a_rel = rel_on nat_rel actions a_code a\<close>
definition \<open>ts_rel = list_all2 state_rel ts_code ts\<close>

definition \<open>g_rel \<longleftrightarrow> g_cache = g_code\<close>

definition \<open>inst_rel \<longleftrightarrow> t_rel \<and> ts_rel \<and> a_rel \<and> g_rel\<close>

print_locale Factored_LP_Code_Transfer
sublocale Factored_LP_Code_Transfer
  where
    real_ops = sr_ops and
    ereal_ops = er_ops and
    to_ereal_ops = ste_ops and
    show_state = show_state and
    prefix_code = \<open>(show_state t_code, a_code, pos)\<close> and
    prefix = \<open>((t, a), pos)\<close> and
    dims = dims and
    doms = doms and
    prefix_\<alpha> = \<open>\<lambda>(t, a, pos). (((\<lambda>i. if i < dims then t ! i else None), a), pos)\<close> and
    prefix_invar = \<open>\<lambda>(t, a, pos). length t = dims\<close>
  for 
    B_code
    C_code C B pos
  apply unfold_locales
  by (auto intro!: inj_onI List.nth_equalityI) meson

lemma partial_vecs_eq[simp]: \<open>partial_vecs = partial_states\<close>
  unfolding partial_vecs_def partial_states_def
  by auto

lemma full_vecs_eq[simp]: \<open>full_vecs = states\<close>
  unfolding full_vecs_def states_def vecs_on_def
  by auto


sublocale Factored_LP_Inst \<open>TYPE(((nat \<Rightarrow> nat option) \<times> nat) \<times> bool)\<close> \<open>TYPE(nat)\<close>.

print_locale Process_Branch_Consts
sublocale PB?: Process_Branch_Consts
  where
    rewards = rewards and
    transitions = transitions and
    doms = doms and

    inv_constr = inv_constr and
    union_constr = union_constr and
    empty_constr = empty_constr and 
    constr_set = constr_set and
    privates = privates and
    factored_lp = \<open>\<lambda>pos B C. (elim_vars B C pos, {v. v = ((t, a), pos)})\<close>
  by unfold_locales

lemma map_eq_domI: 
  assumes \<open>\<And>i. i \<in> dom x \<union> dom y \<Longrightarrow> x i = y i\<close>
  shows \<open>x = y\<close>
proof -
  have \<open>x i = y i\<close> for i
    apply (cases \<open>i \<in> dom x\<close>; cases \<open>i \<in> dom y\<close>)
  using assms domIff
  by (fastforce intro!: ext)+
  thus ?thesis 
    by auto
qed

lemma show_state_correct: \<open>Vec.invar x \<Longrightarrow> Vec.invar y \<Longrightarrow> (Vec.\<alpha> x = Vec.\<alpha> y) = (show_state x = show_state y)\<close>
  unfolding show_state_def Vec.vec_to_list_def
  using Vec.scope_invar_subs 
  by (auto intro!: map_eq_domI)

end

locale InstCode_Transfer' = 
  InstCode_Transfer +
  MDP_Code_Transfer_Rel +
  assumes 
    a: \<open>a \<in> actions\<close> and
    t : \<open>t \<in> partial_states\<close> and
    ts : \<open>set ts \<subseteq> partial_states\<close>
begin

print_locale Process_Branch_Consts
sublocale PB?: Process_Branch_Consts
  where
    rewards = rewards and
    transitions = transitions and
    doms = doms and

    inv_constr = inv_constr and
    union_constr = union_constr and
    empty_constr = empty_constr and 
    constr_set = constr_set and
    privates = privates and
    factored_lp = \<open>\<lambda>pos B C. (elim_vars B C pos, {v. v = ((t, a), pos)})\<close>
  by unfold_locales


lemma factored_lp_spec: \<open>factored_lp_spec\<close>
  unfolding factored_lp_spec_def
proof safe
  fix 
    pos :: bool and 
    C :: \<open>(((nat \<Rightarrow> nat option) \<Rightarrow> real) \<times> nat set) list\<close> and 
    b :: \<open>(((nat \<Rightarrow> nat option) \<Rightarrow> ereal) \<times> nat set) list\<close>
  assume \<open>inv_C C\<close> \<open>inv_b b\<close>

  then interpret flp: factored_lp C b doms dims id \<open>((t, a), pos)\<close>
    using doms_fin doms_ne 
    unfolding inv_b_def inv_C_def
    apply unfold_locales
    by auto
  
  show \<open>factored_lp_constrs pos C b\<close>
    unfolding factored_lp_constrs_def
    unfolding constr_set_def sat_lp_def
    using flp.constr_set_factored_eq' a t ts
    by auto
    
  show \<open>factored_lp_inv pos C b\<close>
    unfolding factored_lp_inv_def
    unfolding inv_constr_def
    using flp.vars_elim_vars
    unfolding lp_vars_def
    by auto

  show \<open>factored_lp_privs pos C b\<close>
    unfolding factored_lp_privs_def
    unfolding privates_def by auto
qed


sublocale Process_Branch
  where 
    rewards = rewards and
    transitions = transitions and
    doms = doms and
    inv_constr = inv_constr and
    union_constr = union_constr and
    empty_constr = empty_constr and 
    constr_set = constr_set and
    privates = privates and
    factored_lp = \<open>\<lambda>pos B C. (elim_vars B C pos, {v. v = ((t, a), pos)})\<close>
  apply unfold_locales
  subgoal using union_spec by auto
  subgoal using empty_constr_spec by auto
  subgoal using factored_lp_spec by auto
  subgoal using t by blast
  subgoal using a by blast
  subgoal using ts by blast
  done
end

locale InstCode_Transfer_Rel =
  InstCode_Transfer +
  MDP_Code_Transfer_Rel +
  Coeffs: Coeffs 
  where constr_op_map_ops = constr_map_ops +
  assumes
    inst_rel: \<open>inst_rel\<close>
begin

lemma 
  t_rel: \<open>t_rel\<close> and ts_rel: \<open>ts_rel\<close> and a_rel: \<open>a_rel\<close> and g_rel: \<open>g_rel\<close>
  using inst_rel inst_rel_def 
  by auto

lemma a_code_eq[intro, simp]: \<open>a_code = a\<close>
  using a_rel unfolding a_rel_def by auto

lemma a_in_acts[intro, simp]: \<open>a \<in> actions\<close>
  using a_rel unfolding a_rel_def by auto

lemma g_cache[simp]: \<open>g_cache = g_code\<close>
  using g_rel unfolding g_rel_def by auto

lemma a_le[simp, intro]: \<open>a < actions_code\<close>  
  using a_in_acts actions_rel by blast

lemma t: \<open>t \<in> partial_states\<close>
  using t_rel unfolding t_rel_def by blast

lemma ts: \<open>set ts \<subseteq> partial_states\<close>
  using ts_rel unfolding ts_rel_def
  by (force simp: list_all2_iff  set_conv_nth)

sublocale InstCode_Transfer'
  using a_in_acts t ts
  by unfold_locales auto

lemma bellman_diff_correct:
  assumes \<open>i < h_dim\<close> \<open>x \<in> partial_states_on (h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i))\<close>  \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (bellman_diff_code i) x_code = (h i x - l * g' i a x)\<close>
  unfolding bellman_diff_code_def
  using assms
  by auto

lemma bellman_diff_invar[intro!, simp]:
  assumes \<open>i < h_dim\<close>
  shows \<open>SR.invar (bellman_diff_code i)\<close>
  using assms bellman_diff_code_def a_code_eq l_code_eq 
  by auto

lemma bellman_diff_scope[simp]:
  assumes \<open>i < h_dim\<close>
  shows \<open>SR.scoped_scope_\<alpha> (bellman_diff_code i) = h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i)\<close>
  unfolding bellman_diff_code_def using a_code_eq l_code_eq  assms by auto

lemma bellman_diff_code_rel:
  assumes \<open>i < h_dim\<close>
  shows \<open>SR.scoped_fn_state_rel (=) (bellman_diff_code i) 
    (\<lambda>x. (h i x - l * g' i a x), h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i))\<close>
  using assms
  by (auto intro!: SR.scoped_fn_state_relI rel_funI bellman_diff_correct partial_states_onI)

lemma t_state_rel: \<open>Vec.state_rel t_code t\<close>
  using t_rel 
  unfolding t_rel_def 
  by auto

lemma t_code_invar[intro]: \<open>Vec.invar t_code\<close>
  using t_state_rel 
  by auto

lemma invar_bellman_diff_inst: \<open>n < h_dim \<Longrightarrow> SR.invar (SR.inst (bellman_diff_code n) t_code)\<close>
  by blast

lemma t_code_eq[simp]: \<open>Vec.\<alpha> t_code = t\<close>
  using t_state_rel 
  by auto

lemma partial_states_add[intro]: \<open>x \<in> partial_states \<Longrightarrow> y \<in> partial_states \<Longrightarrow> x ++ y \<in> partial_states\<close>
  by auto

lemma partial_states_restr[intro]: \<open>x \<in> partial_states \<Longrightarrow> x |` X \<in> partial_states\<close>
  by blast

lemma hg_inst_rel: 
  assumes \<open>n < h_dim\<close>
  shows \<open>SR.scoped_fn_state_rel (=) (hg_inst_code n) (hg_inst n, hg_scope n)\<close>
  unfolding hg_inst_def hg_inst_code_def
  apply (rule SR.scoped_fn_state_relI)
  subgoal using assms by auto
  subgoal using assms t_code_invar by (simp add: hg_scope_def)
  using assms t_code_invar invar_bellman_diff_inst
  apply (intro rel_funI)
  unfolding hg_scope_def fst_conv instantiate_def
  subgoal for x_code x
    apply (subst SR.scoped_fn_state_rel_inst'[OF bellman_diff_code_rel, of _ t x])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      apply (rule arg_cong2[where f = \<open>(-)\<close>])
    subgoal
      apply (rule has_scope_on_eq[OF scope_hI[of _ \<open>h_scope n\<close>]])
      subgoal by blast
      subgoal by blast
      subgoal
        apply (rule partial_states_add)
        subgoal by auto
        subgoal using t by (auto intro!: partial_states_restr)
        done
      subgoal
        apply (rule partial_states_add)
        subgoal by auto
        subgoal using t by (auto intro!: partial_states_restr)
        done
      using assms t
      by (simp add: subset_iff Map.map_add_def)
    subgoal
      apply (rule arg_cong2[where f = \<open>(*)\<close>, OF refl])
      apply (intro has_scope_on_eq[OF scope_g'])
      subgoal by auto
      subgoal by auto
      subgoal by (auto intro!: partial_states_restr partial_states_add)
      subgoal by (auto intro!: partial_states_restr partial_states_add)
      by (simp add: subset_iff Map.map_add_def)
    done
  done
  done

lemma C_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) C_code C\<close>
  unfolding C_code_def C_def
  using hg_inst_rel
  by (auto intro!: list_all2_all_nthI)

lemma r_inst_rel: \<open>i < reward_dim a \<Longrightarrow> 
  SR.scoped_fn_state_rel (=) (r_inst_code i) (r_inst i, r_scope i)\<close>
  unfolding r_inst_code_def r_inst_def r_scope_def
  apply (intro SR.scoped_fn_state_relI)
  subgoal by auto
  subgoal using t_code_invar by auto
  subgoal
    apply (rule rel_funI)
    subgoal for x_code x
      supply SR.scope_eq[subst] SR.scoped_fn_state_rel_inst'[OF rewards_rel _ _ t_state_rel, of _ _ x x_code , subst]
      using t
      by (auto intro!: has_scope_on_eq[OF reward_scope]) (simp add: Map.map_add_def)
    done
  done

lemma b_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) b_code b\<close>
  unfolding b_code_def b_def
  using r_inst_rel
  by (auto intro!: rel_funI list_all2_all_nthI)

lemma scoped_fn_state_rel_neg: \<open>SR.scoped_fn_state_rel (=) f_code fs \<Longrightarrow> 
  SR.scoped_fn_state_rel (=) (SR.scale f_code (- 1)) (neg_scoped fs)\<close>
  unfolding neg_scoped_def
  by (auto intro!: SR.scoped_fn_state_relI simp: case_prod_unfold)

lemma neg_b_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) neg_b_code neg_b\<close>
  using b_rel
  unfolding neg_b_code_def neg_b_def
  by (auto intro!: list_all2_all_nthI scoped_fn_state_rel_neg)

lemma neg_C_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) neg_C_code neg_C\<close>
  using C_rel
  unfolding neg_C_code_def neg_C_def
  by (auto intro!: list_all2_all_nthI scoped_fn_state_rel_neg)

lemma scoped_state_rel_to_ereal: \<open>SR.scoped_fn_state_rel (=) f_code f \<Longrightarrow>
  (STE.SE.scoped_fn_state_rel (=)) (STE.to_ereal f_code) ((\<lambda>x. ereal (fst f x), snd f))\<close>
  by (auto intro!: STE.SE.scoped_fn_state_relI)

lemma ts_state_rel: \<open>list_all2 state_rel ts_code ts\<close>
  using ts_rel ts_rel_def by fastforce

lemma len_b[simp]: \<open>length b = reward_dim a\<close>
  unfolding b_def by auto

lemma len_b_code[simp]: \<open>length b_code = reward_dim a\<close>
  unfolding b_code_def by auto

lemma ind_apply:
 assumes "Vec.invar x"
    and "Vec.invar y"
    and "dom (Vec.\<alpha> x) \<subseteq> dom (Vec.\<alpha> y)"
  shows "STE.SE.scoped_\<alpha> (STE.SE.ind x) y = (if Vec.\<alpha> x = Vec.\<alpha> y |` dom (Vec.\<alpha> x) then - \<infinity> else 0)"
  by (meson STE.SE.ind_apply_false STE.SE.ind_apply_true assms(1) assms(2) assms(3))

lemma \<I>'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) \<I>'_code \<I>'\<close>
proof -
  {
    fix i
    assume i: \<open>i < length ts\<close>

    hence[simp]: \<open>Vec.invar (ts_code ! i)\<close>
      using ts_state_rel
      by auto

    from i have \<open>STE.SE.scoped_fn_state_rel (=) (\<I>'_code ! i) (\<I>' ! i)\<close>
      unfolding \<I>'_code_def \<I>'_def
      apply (intro STE.SE.scoped_fn_state_relI)
      subgoal using ts_state_rel list_all2_lengthD[OF ts_state_rel] by auto
      subgoal 
        using list_all2_lengthD[OF ts_state_rel] ts_state_rel
        apply safe
      supply 
        STE.SE.scope_eq[subst] 
        STE.SE.scoped_inst_scope[subst] 
        STE.SE.ind_scope[subst] 
        Vec.scope_correct[subst]
        by auto
      subgoal
      apply (rule rel_funI)
        subgoal for x_code x
          using list_all2_lengthD[OF ts_state_rel] ts_state_rel
          apply (simp add:  Factored_MDP_Thy.consistent_def)
          apply (subst STE.SE.scoped_fn_state_rel_inst[of _ \<open>(\<I> (ts ! i), dom (ts ! i))\<close> t x x_code])
            apply (auto simp: \<I>_def Vec.state_rel_idx Factored_MDP_Thy.consistent_def intro!: rel_funI STE.SE.scoped_fn_state_relI)
        subgoal
          apply (subst STE.SE.ind_apply_true)
          apply auto
          by (metis (mono_tags, opaque_lifting) Misc.restrict_map_eq(2) list_all2_nthD2 Vec.state_relD)
        subgoal
          apply (subst STE.SE.ind_apply_false)
             apply auto
          by (metis domIff list_all2_conv_all_nth Vec.some_idx Vec.state_relD Vec.state_rel_invarD subsetD)
        by (smt (verit, best) restrict_map_eq_iff domIff map_add_dom_app_simps(1) map_add_find_left restrict_in)+
      done
    done
  }
  thus ?thesis
    unfolding \<I>'_code_def \<I>'_def using ts_state_rel by (auto intro!: list_all2_all_nthI)
  qed

lemma b'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) b'_code b'\<close>
proof -
  have \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) (map STE.to_ereal b_code) (map (\<lambda>(x, y). (\<lambda>xa. ereal (x xa), y)) b)\<close>
    unfolding b'_code_def b'_def
    using b_rel
    by (auto simp: b_rel list_all2_nthD set_zip case_prod_unfold intro!: scoped_state_rel_to_ereal list_all2I)
  with \<I>'_rel
  show ?thesis
    unfolding b'_code_def b'_def
    by (auto intro!: list_all2_appendI)
qed

lemma neg_b'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) neg_b'_code neg_b'\<close>
  unfolding neg_b'_code_def neg_b'_def
  using \<I>'_rel
  using neg_b_rel
  by (auto intro!: list_all2I list_all2_appendI scoped_state_rel_to_ereal
      simp: list_all2_nthD set_zip case_prod_unfold)

definition \<open>valid_prefix_var v \<longleftrightarrow>
  (case v of var_code.var_f (t', a, pos) f x \<Rightarrow> length t' = dims)\<close>

lemma f_name_code_\<alpha>_eqD[dest]: \<open>f_name_code_\<alpha> x = f_name_code_\<alpha> y  \<Longrightarrow> x = y\<close> 
  by (cases x; cases y; auto)

lemmas refl[of var_code_\<alpha>, cong]

lemma some_the_map: \<open>i \<in> dom m \<Longrightarrow> Some (the (m i)) = m i\<close>
  by fastforce

lemma dom_t_vars: \<open>dom t \<subseteq> vars\<close>
  using t_rel
  unfolding t_rel_def
  by auto

sublocale Factored_LP_Code_Transfer_Rel
  where 
    real_ops = sr_ops and
    ereal_ops = er_ops and
    to_ereal_ops = ste_ops and
    show_state = show_state and
    prefix_code = \<open>(show_state t_code, a_code, pos)\<close> and
    prefix_\<alpha> = \<open>\<lambda>(t, a, pos). (((\<lambda>i. if i < dims then t ! i else None), a),  pos)\<close> and
    prefix = \<open>((t, a), pos)\<close> and
    prefix_invar = \<open>\<lambda>(t, a, pos). length t = dims\<close>

  for pos
  apply unfold_locales
  using show_state_correct t_code_invar  t_code_eq dom_t_vars
  unfolding show_state_def
  by (auto intro!: ext)+

context 
  fixes B C C_code B_code
  assumes h: \<open>C_rel C_code C\<close> \<open>B_rel B_code B\<close>
begin

interpretation Factored_LP_Code_Transfer_Rel'
  where 
    real_ops = sr_ops and
    ereal_ops = er_ops and
    to_ereal_ops = ste_ops and
    show_state = show_state and
    prefix_code = \<open>(show_state t_code, a_code, pos)\<close> and
    prefix_\<alpha> = \<open>\<lambda>(t, a, pos). (((\<lambda>i. if i < dims then t ! i else None), a),  pos)\<close> and
    prefix = \<open>((t, a), pos)\<close> and
    prefix_invar = \<open>\<lambda>(t, a, pos). length t = dims\<close>

  for pos
  using h
  apply unfold_locales
  using show_state_correct t_code_invar  t_code_eq dom_t_vars
 unfolding show_state_def
  by (auto intro!: ext)+

lemmas elim_vars_rel = elim_vars_rel

end


lemma C_rel': \<open>C_rel C'_code C\<close>
  using scope_inv_C
  unfolding C_rel_def inv_C_def
  by (auto simp add: subset_iff case_prod_unfold C'_code_def C_rel)

lemma neg_b_rel': \<open>B_rel neg_b'_code neg_b'\<close>
  using scope_inv_neg_b' neg_b'_rel
  unfolding B_rel_def inv_b_def
  by (auto simp add: subset_iff case_prod_unfold)

lemma neg_C_rel': \<open>C_rel neg_C'_code neg_C\<close>
  using scope_inv_neg_C
  unfolding C_rel_def inv_C_def
  by (auto simp add: subset_iff case_prod_unfold neg_C'_code_def neg_C_rel)

lemma b_rel': \<open>B_rel b'_code b'\<close>
  using scope_inv_b' b'_rel
  unfolding B_rel_def inv_b_def
  by (auto simp add: subset_iff case_prod_unfold)

lemma \<Omega>_pos_rel: \<open>constrs_rel \<Omega>_pos_code (fst \<Omega>_pos)\<close>
  unfolding \<Omega>_pos_code_def factored_lp_code_def \<Omega>_pos_def fst_conv
  using C_rel' neg_b_rel' elim_vars_rel by auto

lemma \<Omega>_neg_rel: \<open>constrs_rel \<Omega>_neg_code (fst \<Omega>_neg)\<close>
  unfolding \<Omega>_neg_code_def factored_lp_code_def \<Omega>_neg_def fst_conv
  using neg_C_rel' b_rel' elim_vars_rel by auto

lemma \<Omega>_rel: \<open>constrs_rel \<Omega>_code (fst \<Omega>)\<close>
  using \<Omega>_neg_rel \<Omega>_pos_rel Lifting_Set.union_transfer[THEN rel_funD, THEN rel_funD]
  unfolding \<Omega>_def \<Omega>_code_def \<Omega>_def constrs_rel_def union_constr_def fst_conv
  by fastforce

lemma state_relD: \<open>state_rel x y \<Longrightarrow> Vec.invar x \<and> Vec.\<alpha> x = y\<close>
  by auto

lemma partial_states_on_subs_dom: \<open>x \<in> partial_states_on X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> Y \<subseteq> dom x\<close>
  by blast

end

end