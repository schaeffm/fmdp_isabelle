theory API_Code_Rel
  imports API_Code Bellman_Err_Code Bellman_Err_Branch_Code
begin

context MDPCodeDefs
begin
definition \<open>state_repr x = Vec.insert_list Vec.empty (sorted_key_list_of_set fst (Map.graph x))\<close>
abbreviation \<open>w_rel \<equiv> (=)\<close>

definition \<open>reward_dim_abs = reward_dim_code\<close> 
definition \<open>reward_scope_abs a i = SR.scoped_scope_\<alpha> (rewards_code a i)\<close>
definition \<open>rewards_abs a i x = SR.scoped_\<alpha> (rewards_code a i) (state_repr (x |` reward_scope_abs a i))\<close>
definition \<open>actions_abs = {..<actions_code}\<close>
definition \<open>transitions_scope_abs a i = SP.scoped_scope_\<alpha> (transitions_code a i)\<close>
definition \<open>l_abs = l_code\<close>
definition \<open>h_scope_abs i = SR.scoped_scope_\<alpha> (h_code i)\<close> 
definition \<open>h_abs i x = SR.scoped_\<alpha> (h_code i) (state_repr (x |` h_scope_abs i))\<close>
definition \<open>h_dim_abs = h_dim_code\<close>
definition \<open>transitions_abs a i x = SP.Pmf.\<alpha> (SP.scoped_\<alpha> (transitions_code a i) (state_repr (x |` transitions_scope_abs a i)))\<close>
definition \<open>d_abs = d_code\<close>
definition \<open>effects_abs a = Scope.\<alpha> (effects_code a)\<close>

print_locale Factored_MDP_Consts
sublocale API_Inst: Factored_MDP_Consts
  dims
  doms
  reward_dim_abs
  rewards_abs
  reward_scope_abs
  actions_abs
  transitions_abs
  transitions_scope_abs
  l_abs
  h_dim_abs
  h_abs
  h_scope_abs
  by unfold_locales
end

context MDPCode
begin

lemma
    acts_ne: \<open>0 < actions_code\<close> and
    d_in_acts: \<open>d_code < actions_code\<close> and
    dims_code_eq[simp]: \<open>dims_code = dims\<close> and
    doms_code_eq[simp]: \<open>\<And>i. i < dims \<Longrightarrow> {..<doms_code i} = doms i\<close> and
    doms_ne: \<open>\<And>i. i < dims \<Longrightarrow> doms_code i > 0\<close> and
    dims_nz: \<open>0 < dims\<close> and
    l_lt_one: \<open>l_code < 1\<close> and
    l_nonneg: \<open>0 \<le> l_code\<close> and

    effects_invar: \<open>\<And>a. a < actions_code \<Longrightarrow> Scope.invar (effects_code a)\<close> and
    effects_d_empty: \<open>Scope.isEmpty (effects_code d_code)\<close> and

    transitions_invar[intro!]:  \<open>\<And>a i. i < dims \<Longrightarrow> a < actions_code \<Longrightarrow> SP.invar (transitions_code a i)\<close>
  using mdp_valid doms_match dims_match
  unfolding mdp_code_valid_def dims_match_def doms_match_def 
  unfolding l_valid_def dims_valid_def doms_valid_def rewards_valid_def transitions_valid_def 
    h_valid_def effects_valid_def
  by auto
  

lemma pmf_invar_transitions_code[intro!]: \<open>i < dims \<Longrightarrow> a < actions_code \<Longrightarrow> Vec.invar x \<Longrightarrow> 
  SP.scoped_scope_\<alpha> (transitions_code a i) \<subseteq> Vec.scope_\<alpha> x \<Longrightarrow> SP.Pmf.invar (SP.scoped_\<alpha> (transitions_code a i) x)\<close>
  using mdp_valid doms_match dims_match
  unfolding mdp_code_valid_def dims_match_def doms_match_def 
  unfolding  dims_valid_def doms_valid_def transitions_valid_def valid_pmf_def
  by auto

lemma finite_actions_abs[intro]: \<open>finite actions_abs\<close>
  unfolding actions_abs_def
  by auto

lemma actions_abs_ne: \<open>actions_abs \<noteq> {}\<close>
  unfolding actions_abs_def
  using acts_ne
  by auto

lemma doms_fin[intro!]: \<open>i < dims \<Longrightarrow> finite (doms i)\<close>
  unfolding doms_code_eq[of i, symmetric]
  by blast

lemma doms_ne': \<open>i < dims \<Longrightarrow> doms i \<noteq> {}\<close>
  unfolding doms_code_eq[of i, symmetric] 
  using doms_ne
  by blast

lemma l_abs_lt_one: \<open>l_abs < 1\<close>
  unfolding l_abs_def
  using l_lt_one 
  by force

lemma l_abs_nonneg: \<open>0 \<le> l_abs\<close>
  unfolding l_abs_def
  using l_nonneg 
  by force

lemma h_code_invar[simp, intro!]: \<open>i < h_dim_code \<Longrightarrow> SR.invar (h_code i)\<close>
  using mdp_code_valid_def h_valid_def mdp_valid by blast

lemma h_scope_subs: \<open>i < h_dim_code \<Longrightarrow> SR.scoped_scope_\<alpha> (h_code i) \<subseteq> API_Inst.vars\<close>
  using mdp_code_valid_def h_valid_def mdp_valid by blast


lemma h_scope_abs_in_vars: \<open>i < h_dim_abs \<Longrightarrow> h_scope_abs i \<subseteq> API_Inst.vars\<close>
  unfolding h_dim_abs_def h_scope_abs_def
  using h_scope_subs
  by auto

lemma reward_scope_abs_in_vars: \<open>a \<in> actions_abs \<Longrightarrow> i < reward_dim_abs a \<Longrightarrow> reward_scope_abs a i \<subseteq> API_Inst.vars\<close>
  using mdp_valid
  unfolding actions_abs_def reward_dim_abs_def reward_scope_abs_def
  unfolding mdp_code_valid_def rewards_valid_def
  by auto

lemma transitions_scope_abs_in_vars: \<open>a \<in> actions_abs \<Longrightarrow> i < dims \<Longrightarrow> transitions_scope_abs a i \<subseteq> API_Inst.vars\<close> 
  using mdp_valid
  unfolding transitions_scope_abs_def actions_abs_def
  unfolding mdp_code_valid_def transitions_valid_def
  by auto

lemma states_finite_dom:
  assumes \<open>x \<in> API_Inst.partial_states\<close> 
  shows \<open>finite (dom x)\<close>
  using assms by auto

lemma state_repr_invar[intro!]:
  assumes \<open>x \<in> API_Inst.partial_states\<close> 
  shows \<open>Vec.invar (state_repr x)\<close>
  using assms states_finite_dom unfolding state_repr_def
  supply folding_Map_graph.set_sorted_key_list_of_set[of _ x, subst]
  apply auto
  unfolding Map.graph_def 
  by auto


lemma insert_list_empty[simp]: 
  \<open>distinct (map fst xs) \<Longrightarrow> set xs \<subseteq> {(k, v). v \<in> doms k \<and> k < dims} \<Longrightarrow> 
  Vec.\<alpha> (Vec.insert_list Vec.empty xs) = map_of xs\<close>
  apply (subst Vec.idx_insert_list)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (induction xs) auto
  done
  

lemma map_eq_if_graph_eq: \<open>Map.graph m = Map.graph m' \<Longrightarrow> m = m'\<close> 
  apply (auto intro!: ext simp: Map.graph_def map_to_set_def[symmetric])
  by (metis  map_to_set_inverse)

lemma state_finite_graph: \<open>x \<in> API_Inst.partial_states \<Longrightarrow> finite (Map.graph x)\<close>
  by auto

lemma abstr_state_repr[simp]:
  assumes \<open>x \<in> API_Inst.partial_states\<close>
  shows \<open>Vec.\<alpha> (state_repr x) = x\<close>
  using assms states_finite_dom unfolding state_repr_def
  apply (subst insert_list_empty)
  using folding_Map_graph.distinct_sorted_key_list_of_set state_finite_graph
 supply graph_map_of_if_distinct_dom[subst]
    apply (auto dest!: in_graphD simp: folding_Map_graph.sorted_key_list_of_set[OF subset_refl])
  apply (auto intro!: map_eq_if_graph_eq)
  using folding_Map_graph.distinct_sorted_key_list_of_set apply blast
    apply (subst (asm) folding_Map_graph.set_sorted_key_list_of_set[of _ x])
      apply auto
  using folding_Map_graph.distinct_sorted_key_list_of_set apply blast
    apply (subst folding_Map_graph.set_sorted_key_list_of_set[of _ x])
  by auto

lemma partial_states_restr[simp]: \<open>x \<in> API_Inst.partial_states \<Longrightarrow> x |` X \<in> API_Inst.partial_states\<close>
  by blast

lemma h_abs_scoped:
  assumes \<open>i < h_dim_abs\<close> 
  shows \<open>has_scope_on (h_abs i) API_Inst.partial_states (h_scope_abs i)\<close>
proof (rule has_scope_onI)
  fix d d'
  note h_dim_abs_def[simp]
  assume d: \<open>d \<in> API_Inst.partial_states\<close> and d': \<open>d' \<in> API_Inst.partial_states\<close> 
    and ds_eq: \<open>(\<And>j. j \<in> h_scope_abs i \<Longrightarrow> d j = d' j)\<close> 
  have \<open>d |` h_scope_abs i = d' |` h_scope_abs i\<close>
     using ds_eq by blast
  thus \<open>h_abs i d = h_abs i d'\<close>
    unfolding h_abs_def
    by auto
qed

lemma rewards_scoped:
  \<open>a \<in> actions_abs \<Longrightarrow> i < reward_dim_abs a \<Longrightarrow> 
  has_scope_on (rewards_abs a i) API_Inst.partial_states (reward_scope_abs a i)\<close>
  apply (rule has_scope_onI)
  unfolding rewards_abs_def
  by (metis map_restr_same_eqI)

lemma transitions_scoped:
  \<open>a \<in> actions_abs \<Longrightarrow> i < dims \<Longrightarrow> 
  has_scope_on (transitions_abs a i) API_Inst.partial_states (transitions_scope_abs a i)\<close>
  apply (rule has_scope_onI)
  unfolding transitions_abs_def
  by (metis map_restr_same_eqI)

lemma transitions_abs_in_doms:
  assumes \<open>a \<in> actions_abs\<close> \<open>i < dims\<close> 
    \<open>x \<in> API_Inst.partial_states_on (transitions_scope_abs a i)\<close> 
  shows \<open>set_pmf (transitions_abs a i x) \<subseteq> doms i\<close>
proof -

  have x_partial[simp, intro]: \<open>x |` transitions_scope_abs a i \<in> API_Inst.partial_states\<close>
    using assms by blast
  let ?x = \<open>state_repr (x |` transitions_scope_abs a i)\<close>

  have x_invar[intro]: \<open>Vec.invar ?x\<close>
    by blast


  have scope_x_sup: \<open>SP.scoped_scope_\<alpha> (transitions_code a i) \<subseteq> Vec.scope_\<alpha> ?x\<close>
    using assms transitions_scope_abs_def x_invar x_partial 
    by auto
    
  have \<open>set_pmf (transitions_abs a i x) \<subseteq> SP.Pmf.Set.\<alpha> (SP.Pmf.supp (SP.scoped_\<alpha> (transitions_code a i) (state_repr (x |` transitions_scope_abs a i))))\<close>
    unfolding transitions_abs_def
    apply (rule SP.Pmf.supp_sup)
    apply (rule pmf_invar_transitions_code)
    subgoal using assms by auto
    subgoal using assms actions_abs_def by auto
    subgoal
      using assms
      by auto
    subgoal
      using assms scope_x_sup by auto
    done
  also have \<open>\<dots> \<subseteq> doms i\<close>
    using mdp_valid scope_x_sup assms
    unfolding mdp_code_valid_def transitions_valid_def valid_pmf_def actions_abs_def
    by blast
  finally show ?thesis .
qed

print_locale Factored_MDP
sublocale API_Inst: Factored_MDP
  dims
  doms
  reward_dim_abs
  reward_scope_abs
  actions_abs
  transitions_abs
  transitions_scope_abs
  l_abs
  h_dim_abs
  h_abs
  h_scope_abs
  rewards_abs
  apply unfold_locales
  subgoal using transitions_abs_in_doms .
  subgoal using transitions_scoped .
  subgoal using transitions_scope_abs_in_vars .
  subgoal using finite_actions_abs .
  subgoal using actions_abs_ne .
  subgoal using doms_fin .
  subgoal using doms_ne' .
  subgoal using dims_nz .
  subgoal using rewards_scoped .
  subgoal using reward_scope_abs_in_vars .
  subgoal using h_abs_scoped .
  subgoal using h_scope_abs_in_vars .
  subgoal using l_abs_lt_one .
  subgoal using l_abs_nonneg .
  done

lemma d_abs_act: \<open>d_abs \<in> actions_abs\<close>
  unfolding d_abs_def actions_abs_def
  using d_in_acts by force

lemma notin_effects_default: \<open>i < dims \<Longrightarrow> a \<in> actions_abs \<Longrightarrow> \<exists>x\<in>API_Inst.partial_states. 
  transitions_abs a i x \<noteq> transitions_abs d_abs i x \<Longrightarrow> i \<in> effects_abs a\<close>
  unfolding transitions_abs_def effects_abs_def actions_abs_def transitions_scope_abs_def d_abs_def
  using effects_invar
  using mdp_valid
  unfolding mdp_code_valid_def effects_valid_def
  apply (cases \<open>i \<in> API_Inst.vars - Scope.\<alpha> (effects_code a)\<close>)
  by auto

lemma effects_d_abs: \<open>effects_abs d_abs = {}\<close>
  unfolding effects_abs_def d_abs_def
  using mdp_valid
  unfolding mdp_code_valid_def effects_valid_def
  by auto

lemma reward_dim_abs_ge_default: \<open>a \<in> actions_abs \<Longrightarrow> reward_dim_abs d_abs \<le> reward_dim_abs a\<close>
  unfolding reward_dim_abs_def actions_abs_def d_abs_def
  using mdp_valid
  unfolding mdp_code_valid_def rewards_valid_def
  by auto

lemma rewards_abs_eq:
  \<open>a \<in> actions_abs \<Longrightarrow> i < reward_dim_abs d_abs \<Longrightarrow> rewards_abs a i = rewards_abs d_abs i\<close>
unfolding reward_dim_abs_def rewards_abs_def actions_abs_def d_abs_def reward_scope_abs_def
  using mdp_valid
  unfolding mdp_code_valid_def rewards_valid_def
  by auto

lemma rewards_scopes_abs_eq:
  \<open>a \<in> actions_abs \<Longrightarrow> i < reward_dim_abs d_abs \<Longrightarrow> reward_scope_abs a i = reward_scope_abs d_abs i\<close>
  unfolding reward_dim_abs_def rewards_abs_def actions_abs_def d_abs_def reward_scope_abs_def
  using mdp_valid
  unfolding mdp_code_valid_def rewards_valid_def
  by auto

print_locale Factored_MDP_Default
sublocale API_Inst: Factored_MDP_Default
  dims
  doms
  reward_dim_abs
  rewards_abs
  reward_scope_abs
  actions_abs
  transitions_scope_abs
  l_abs
  h_dim_abs
  h_abs
  h_scope_abs
  d_abs
  effects_abs
  transitions_abs 
  apply unfold_locales
  subgoal using d_abs_act .
  subgoal using notin_effects_default .
  subgoal using effects_d_abs .
  subgoal using reward_dim_abs_ge_default .
  subgoal using rewards_abs_eq .
  subgoal using rewards_scopes_abs_eq .
  done


lemma nat_rel_self[intro, simp]: \<open>Rel_Util.nat_rel x x\<close>
  unfolding nat_rel_def
  by auto

lemma lt_doms_code_iff[simp]: \<open>j < dims \<Longrightarrow> i < doms_code j \<longleftrightarrow> i \<in> doms j\<close>
  using doms_code_eq
  by blast



sublocale MDP_Code_Rel: MDP_Code_Transfer
where sp_ops = sp_ops
  and vec_ops = vec_ops
    and set_ops = set_ops
    and sp_pmf_ops = sp_pmf_ops
    and pmf_set_ops = pmf_set_ops
    and dims_code = dims_code
    and doms_code = doms_code
    and rewards_code = rewards_code
    and reward_dim_code = reward_dim_code
    and actions_code = actions_code
    and d_code = d_code
    and transitions_code = transitions_code
    and l_code = l_code
    and h_code = h_code
    and h_dim_code = h_dim_code
    and effects_code = effects_code
    and sr_ops = sr_ops
    and dims = dims
    and reward_dim = reward_dim_abs
    and reward_scope = reward_scope_abs
    and actions = actions_abs
    and transitions_scope = transitions_scope_abs
    and l = l_abs
    and h = h_abs
    and h_scope = h_scope_abs
    and h_dim = h_dim_abs
    and rewards = rewards_abs
    and transitions = transitions_abs
    and effects = effects_abs
    and doms = doms
    and d = d_abs
  by unfold_locales

lemma dims_rels: \<open>MDP_Code_Rel.dims_rels\<close>
  unfolding MDP_Code_Rel.dims_rels_def MDP_Code_Rel.doms_rel_def MDP_Code_Rel.dims_rel_def
  by auto

lemma actions_rels: \<open>MDP_Code_Rel.actions_rels\<close>
  unfolding MDP_Code_Rel.actions_rels_def  MDP_Code_Rel.actions_rel_def MDP_Code_Rel.d_rel_def MDP_Code_Rel.effects_rel_def
  unfolding actions_abs_def d_abs_def effects_abs_def
  using effects_invar
  by auto

lemma h_scoped_fn_rel: \<open>y < h_dim_code \<Longrightarrow> SR.scoped_fn_state_rel (=) (h_code y) (h_abs y, h_scope_abs y)\<close>
  unfolding h_abs_def h_scope_abs_def
  using MDP_Code_Rel.state_rel_partialD
  apply (auto intro!: SR.scoped_fn_state_relI rel_funI SR.scoped_\<alpha>)  
  by blast+

lemma h_rels: \<open>MDP_Code_Rel.h_rels\<close>
  unfolding MDP_Code_Rel.h_rels_def MDP_Code_Rel.h_dim_rel_def MDP_Code_Rel.h_rel_def
  unfolding h_dim_abs_def
  using h_scoped_fn_rel
  by auto

lemma rewards_code_invar[intro!, simp]: \<open>a < actions_code \<Longrightarrow> i < reward_dim_code a \<Longrightarrow> SR.invar (rewards_code a i)\<close>
  using mdp_valid
  unfolding mdp_code_valid_def rewards_valid_def
  by auto

lemma reward_rels: \<open>MDP_Code_Rel.reward_rels\<close>
  unfolding MDP_Code_Rel.reward_rels_def MDP_Code_Rel.rewards_rel_def MDP_Code_Rel.reward_dim_rel_def MDP_Code_Rel.l_rel_def
  unfolding l_abs_def reward_dim_abs_def rewards_abs_def reward_scope_abs_def actions_abs_def
  using MDP_Code_Rel.state_rel_partialD
  apply (auto intro!: fun_relI' rel_funI SR.scoped_fn_state_relI  SR.scoped_\<alpha>)
  by blast+


lemma pmf_set_imp_supp: \<open>x \<in> set_pmf (SP.Pmf.\<alpha> p) \<Longrightarrow> SP.Pmf.invar p \<Longrightarrow>
       x \<in> SP.Pmf.Set.\<alpha> (SP.Pmf.supp p)\<close>
  using SP.Pmf.supp_sup by blast

lemma pmf_rel_transitions:
  assumes a: \<open>a < actions_code\<close> and i: \<open>i < dims\<close> and x: \<open>MDP_Code_Rel.state_rel x_code x\<close>
  and dom: \<open>SP.scoped_scope_\<alpha> (transitions_code a i) \<subseteq> dom x\<close>
  shows \<open>SP.Pmf.pmf_rel (=) (SP.scoped_\<alpha> (transitions_code a i) x_code)
        (SP.Pmf.\<alpha> (SP.scoped_\<alpha> (transitions_code a i) (state_repr (x |` SP.scoped_scope_\<alpha> (transitions_code a i)))))\<close>
proof -

  have *[simp]: \<open>Vec.\<alpha> (state_repr (x |` SP.scoped_scope_\<alpha> (transitions_code a i))) = (x |` SP.scoped_scope_\<alpha> (transitions_code a i))\<close>
    using assms
    by (auto intro!: SP.scoped_\<alpha>)

  have [simp]: \<open>SP.scoped_\<alpha> (transitions_code a i) (state_repr (x |` SP.scoped_scope_\<alpha> (transitions_code a i)))
    = SP.scoped_\<alpha> (transitions_code a i) x_code\<close>
    using assms transitions_invar
    by (auto intro!: SP.scoped_\<alpha>)

  show ?thesis
    unfolding SP.Pmf.pmf_rel_def
    using assms SP.Pmf.prob_at_correct[subst]
    apply (auto intro!: pmf_set_imp_supp simp: transitions_invar)
    by (metis Pmf.supp_invar SP.Pmf local.Vec.scope_correct local.Vec.state_rel_iff pmf_invar_transitions_code)
qed

lemma transitions_rel: \<open>MDP_Code_Rel.transitions_rel\<close>
  unfolding MDP_Code_Rel.transitions_rel_def
  unfolding actions_abs_def transitions_scope_abs_def transitions_abs_def
  using pmf_rel_transitions transitions_invar
  by (auto intro!: rel_funI SP.scoped_fn_state_relI)

lemma mdp_rels: \<open>MDP_Code_Rel.MDP_rels\<close>
  unfolding MDP_Code_Rel.MDP_rels_def
  using dims_rels actions_rels h_rels reward_rels transitions_rel
  by auto

sublocale MDP_Code_Rel: MDP_Code_Transfer_Rel
where sp_ops = sp_ops
  and vec_ops = vec_ops
    and set_ops = set_ops
    and sp_pmf_ops = sp_pmf_ops
    and pmf_set_ops = pmf_set_ops
    and dims_code = dims_code
    and doms_code = doms_code
    and rewards_code = rewards_code
    and reward_dim_code = reward_dim_code
    and actions_code = actions_code
    and d_code = d_code
    and transitions_code = transitions_code
    and l_code = l_code
    and h_code = h_code
    and h_dim_code = h_dim_code
    and effects_code = effects_code
    and sr_ops = sr_ops
    and dims = dims
    and reward_dim = reward_dim_abs
    and reward_scope = reward_scope_abs
    and actions = actions_abs
    and transitions_scope = transitions_scope_abs
    and l = l_abs
    and h = h_abs
    and h_scope = h_scope_abs
    and h_dim = h_dim_abs
    and rewards = rewards_abs
    and transitions = transitions_abs
    and effects = effects_abs
    and doms = doms
    and d = d_abs
  apply unfold_locales
  using mdp_rels .


end


context APICodeDefs
begin

definition \<open>\<epsilon>_abs = \<epsilon>_code\<close>
definition \<open>t_max_abs = t_max_code\<close>

print_locale  APICodeTransfer
sublocale MDP_Code_Rel: APICodeTransfer
where sp_ops = sp_ops
    and vec_ops = vec_ops
    and set_ops = set_ops
    and sp_pmf_ops = sp_pmf_ops
    and pmf_set_ops = pmf_set_ops
    and dims_code = dims_code
    and doms_code = doms_code
    and rewards_code = rewards_code
    and reward_dim_code = reward_dim_code
    and actions_code = actions_code
    and d_code = d_code
    and transitions_code = transitions_code
    and l_code = l_code
    and h_code = h_code
    and h_dim_code = h_dim_code
    and effects_code = effects_code
    and sr_ops = sr_ops
    and dims = dims
    and reward_dim = reward_dim_abs
    and reward_scope = reward_scope_abs
    and actions = actions_abs
    and transitions_scope = transitions_scope_abs
    and l = l_abs
    and h = h_abs
    and h_scope = h_scope_abs
    and h_dim = h_dim_abs
    and rewards = rewards_abs
    and transitions = transitions_abs
    and effects = effects_abs
    and doms = doms
    and d = d_abs

    and ste_ops = ste_ops
    and constr_map_ops = constr_map_ops
    and er_ops = er_ops
    and minimize = minimize
  
    and \<epsilon> = \<epsilon>_abs 
    and t_max = t_max_abs
  by unfold_locales
end

context APICode
begin

interpretation MDP_Code_Rel: APICodeTransfer
where sp_ops = sp_ops
    and vec_ops = vec_ops
    and set_ops = set_ops
    and sp_pmf_ops = sp_pmf_ops
    and pmf_set_ops = pmf_set_ops
    and dims_code = dims_code
    and doms_code = doms_code
    and rewards_code = rewards_code
    and reward_dim_code = reward_dim_code
    and actions_code = actions_code
    and d_code = d_code
    and transitions_code = transitions_code
    and l_code = l_code
    and h_code = h_code
    and h_dim_code = h_dim_code
    and effects_code = effects_code
    and sr_ops = sr_ops
    and dims = dims
    and reward_dim = reward_dim_abs
    and reward_scope = reward_scope_abs
    and actions = actions_abs
    and transitions_scope = transitions_scope_abs
    and l = l_abs
    and h = h_abs
    and h_scope = h_scope_abs
    and h_dim = h_dim_abs
    and rewards = rewards_abs
    and transitions = transitions_abs
    and effects = effects_abs
    and doms = doms
    and d = d_abs

    and ste_ops = ste_ops
    and constr_map_ops = constr_map_ops
    and er_ops = er_ops
    and minimize = minimize
  
    and \<epsilon> = \<epsilon>_abs 
    and t_max = t_max_abs
  apply unfold_locales
  done

lemma api_rels: \<open>MDP_Code_Rel.api_rels\<close>
  unfolding MDP_Code_Rel.api_rels_def
  unfolding \<epsilon>_abs_def t_max_abs_def
  by auto

sublocale MDP_Code_Rel: APICodeTransferRel
where sp_ops = sp_ops
    and vec_ops = vec_ops
    and set_ops = set_ops
    and sp_pmf_ops = sp_pmf_ops
    and pmf_set_ops = pmf_set_ops
    and dims_code = dims_code
    and doms_code = doms_code
    and rewards_code = rewards_code
    and reward_dim_code = reward_dim_code
    and actions_code = actions_code
    and d_code = d_code
    and transitions_code = transitions_code
    and l_code = l_code
    and h_code = h_code
    and h_dim_code = h_dim_code
    and effects_code = effects_code
    and sr_ops = sr_ops
    and dims = dims
    and reward_dim = reward_dim_abs
    and reward_scope = reward_scope_abs
    and actions = actions_abs
    and transitions_scope = transitions_scope_abs
    and l = l_abs
    and h = h_abs
    and h_scope = h_scope_abs
    and h_dim = h_dim_abs
    and rewards = rewards_abs
    and transitions = transitions_abs
    and effects = effects_abs
    and doms = doms
    and d = d_abs

    and ste_ops = ste_ops
    and constr_map_ops = constr_map_ops
    and er_ops = er_ops
    and minimize = minimize

    and \<epsilon> = \<epsilon>_abs
    and t_max = t_max_abs
  using api_rels
  by unfold_locales auto

(* this is the main result *)
(* thm MDP_Code_Rel.api_rel *)


end

end
