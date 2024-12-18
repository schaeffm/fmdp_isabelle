theory Bellman_Err_Branch_Code
  imports 
    "../algorithm/Bellman_Err_Branch" 
    Code_Setup 
    Variable_Elim_Code
begin 

section \<open>Code for the Bellman Error Branch Computation\<close>
subsection \<open>Util\<close>

lemma map_add_app_eqI[intro]:
  assumes
    \<open>i \<in> dom n \<Longrightarrow> y = n i\<close>
    \<open>i \<notin> dom n \<Longrightarrow> i \<in> dom m \<Longrightarrow> y = m i\<close>
    \<open>i \<notin> dom n \<Longrightarrow> i \<notin> dom m \<Longrightarrow> y = None\<close>
  shows
  \<open>(m ++ n) i = y\<close>
  using assms
  by (cases \<open>(m ++ n) i\<close>) auto+

lemmas map_add_app_eqI[symmetric, intro]


locale BellmanErrBranchCodeDefs =
  MDPCodeDefs 
  where
    sr_ops = sr_ops and
    vec_ops = vec_ops and
    set_ops = set_ops and
    sp_ops = sp_ops and
    sp_pmf_ops = sp_pmf_ops
    + STE: ScopedFnToEreal to_ereal_ops sr_ops _ vec_ops set_ops
for 
  sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" 
  and sp_ops :: \<open>('sp, 'state, 'pmf, 'natset) scoped_fn_basic_ops\<close>
  and vec_ops 
  and set_ops
  and sp_pmf_ops ::  "('pmf, nat, 'pmf_set) pmf_ops" 
  and to_ereal_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" +
fixes
    g_cache :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'f\<close> and
    w_code :: \<open>weights\<close> and \<comment> \<open>current weights for basis functions h\<close>
    ts_code :: \<open>'state list\<close> and \<comment> \<open>partial states in decision list prefix\<close>
    t_code :: \<open>'state\<close> and \<comment> \<open>current (partial) state\<close>
    a_code :: \<open>nat\<close> \<comment> \<open>current action\<close>
begin

text\<open>construct functions C\<close>
definition \<open>bellman_diff_code (i :: nat) = 
  (SR.scale (SR.diff (h_code i) (SR.scale (g_cache i a_code) l_code)) (w_code i))\<close>
lemmas refl[where t = \<open>bellman_diff_code\<close>, cong]

\<comment> \<open>w i * (h i - l * g i a)\<close>
definition \<open>hg_inst_code i = SR.scoped_eval (SR.inst (bellman_diff_code i) t_code)\<close>
lemmas refl[where t = \<open>hg_inst_code\<close>, cong]

definition \<open>C_code = map hg_inst_code [0..<h_dim_code]\<close>
lemmas refl[where t = \<open>C_code\<close>, cong]

definition \<open>neg_C_code = map (\<lambda>f. SR.scale f (-1)) C_code\<close>
lemmas refl[where t = \<open>neg_C_code\<close>, cong]

definition \<open>C'_code = map STE.to_ereal C_code\<close>
lemmas refl[where t = \<open>C'_code\<close>, cong]

definition \<open>neg_C'_code = map STE.to_ereal neg_C_code\<close>
lemmas refl[where t = \<open>neg_C'_code\<close>, cong]

definition \<open>r_inst_code i = SR.scoped_eval (SR.inst (rewards_code a_code i) t_code)\<close>
lemmas refl[where t = \<open>r_inst_code\<close>, cong]

definition \<open>b_code = map r_inst_code [0..<reward_dim_code a_code]\<close>
lemmas refl[where t = \<open>b_code\<close>, cong]

definition \<open>neg_b_code = map (\<lambda>f. SR.scale f (-1)) b_code\<close>
lemmas refl[where t = \<open>neg_b_code\<close>, cong]

definition \<open>\<I>'_code = map (\<lambda>t'. STE.SE.scoped_eval (STE.SE.inst (STE.SE.ind t') t_code)) ts_code\<close>
lemmas refl[where t = \<open>\<I>'_code\<close>, cong]

definition \<open>b'_code = map STE.to_ereal b_code @ \<I>'_code\<close>
lemmas refl[where t = \<open>b'_code\<close>, cong]

definition \<open>neg_b'_code = map STE.to_ereal neg_b_code @ \<I>'_code\<close>
lemmas refl[where t = \<open>neg_b'_code\<close>, cong]

print_locale Variable_Elim_Code_Consts
sublocale VE_Code:
  Variable_Elim_Code_Consts
  \<open>(STE.scoped_state_ereal_ops)\<close>
  vec_ops
  set_ops
  pmf_set_ops
  dims
  doms
  dims_code
  doms_code
  fs \<open>[0..<dims_code]\<close>
  for fs
  by unfold_locales

definition \<open>\<epsilon>_pos_code = VE_Code.elim_max_code (C'_code @ neg_b'_code)\<close>
lemmas refl[where t = \<open>\<epsilon>_pos_code\<close>, cong]

definition \<open>\<epsilon>_neg_code = VE_Code.elim_max_code (neg_C'_code @ b'_code)\<close>
lemmas refl[where t = \<open>\<epsilon>_neg_code\<close>, cong]

text \<open>optimization vs. @{term \<epsilon>_max_code_eq}, recomputes less\<close>
definition \<open>\<epsilon>_max_code = (
  let 
    C_code = map hg_inst_code [0..<h_dim_code];
    neg_C_code = map (\<lambda>f. SR.scale f (-1)) C_code;
    C'_code = map STE.to_ereal C_code;
    neg_C'_code = map STE.to_ereal neg_C_code;
    b_code = map r_inst_code [0..<reward_dim_code a_code];
    neg_b_code = map (\<lambda>f. SR.scale f (-1)) b_code;
    \<I>'_code = map (\<lambda>t'. STE.SE.scoped_eval (STE.SE.inst (STE.SE.ind t') t_code)) ts_code;
    b'_code = map STE.to_ereal b_code @ \<I>'_code;
    neg_b'_code = map STE.to_ereal neg_b_code @ \<I>'_code;
    \<epsilon>_pos_code = VE_Code.elim_max_code (C'_code @ neg_b'_code);
    \<epsilon>_neg_code = VE_Code.elim_max_code (neg_C'_code @ b'_code)
  in
  max \<epsilon>_pos_code \<epsilon>_neg_code)\<close>
lemmas refl[where t = \<open>\<epsilon>_max_code\<close>, cong]

lemma \<epsilon>_max_code_eq: \<open>\<epsilon>_max_code = max \<epsilon>_pos_code \<epsilon>_neg_code\<close>
  unfolding \<epsilon>_max_code_def \<epsilon>_pos_code_def \<epsilon>_neg_code_def 
    C'_code_def C_code_def neg_C'_code_def neg_C_code_def 
    neg_b'_code_def neg_b_code_def b_code_def b'_code_def
    \<I>'_code_def Let_def
  by blast
end

locale BellmanErrBranchCode = 
  BellmanErrBranchCodeDefs
  where 
    sr_ops = sr_ops and 
    vec_ops = vec_ops and 
    set_ops = set_ops and 
    to_ereal_ops = to_ereal_ops and
    ereal_ops = ereal_ops +
  MDPCode
  where
    sr_ops = sr_ops and
    vec_ops = vec_ops and 
    set_ops = set_ops 
    +
  STE: ScopedFnToEreal to_ereal_ops sr_ops ereal_ops vec_ops set_ops
for 
  sr_ops :: "('f, 'state, 'natset) scoped_fn_real_ops" and 
  to_ereal_ops :: "('f, 'ef) scoped_fn_to_ereal_ops" and
  ereal_ops and
  vec_ops and
  set_ops

locale Bellman_Err_Branch_Code_Transfer =
  MDP_Code_Transfer
  where
    rewards = rewards and
    transitions = transitions and
    doms = doms +
    BellmanErrBranchCodeDefs where doms = doms
  for
    doms :: \<open>nat \<Rightarrow> nat set\<close> and
    rewards :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> real\<close> and 
    transitions :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat pmf" +
fixes 
  w :: \<open>nat \<Rightarrow> real\<close> and
  ts :: \<open>nat state list\<close> and 
  t :: \<open>nat state\<close> and
  a :: nat
begin

sublocale Variable_Elimination_Consts \<F> dims id doms for \<F> .

sublocale Bellman_Err_Branch_Consts
  where 
    rewards = rewards and
    transitions = transitions and
    doms = doms and
    variable_elim = elim_max
  by unfold_locales

definition \<open>w_rel' = w_rel w_code w\<close>
lemmas refl[of w_rel', cong]

definition \<open>t_rel = state_rel t_code t\<close>
lemmas refl[of t_rel, cong]

definition \<open>a_rel = rel_on nat_rel actions a_code a\<close>
lemmas refl[of a_rel, cong]

definition \<open>ts_rel = list_all2 state_rel ts_code ts\<close>
lemmas refl[of ts_rel, cong]

definition \<open>g_rel \<longleftrightarrow> g_cache = g_code\<close>
lemmas refl[of g_rel, cong]

definition \<open>bellman_err_branch_rel \<longleftrightarrow> w_rel' \<and> t_rel \<and> ts_rel \<and> a_rel \<and> g_rel\<close>
lemmas refl[of bellman_err_branch_rel, cong]
end

locale Bellman_Err_Branch_Code_Transfer_Rel =
  Bellman_Err_Branch_Code_Transfer +
  BellmanErrBranchCode +
  MDP_Code_Transfer_Rel +
   assumes 
     bellman_err_branch_rel: \<open>bellman_err_branch_rel\<close>
begin

sublocale
    Bellman_Err_Branch
  where 
    rewards = rewards and
    transitions = transitions and
    doms = doms and
    variable_elim = elim_max
  by unfold_locales

lemma 
  w_rel: \<open>w_rel'\<close> and t_rel: \<open>t_rel\<close> and ts_rel: \<open>ts_rel\<close> and a_rel: \<open>a_rel\<close> and g_rel: \<open>g_rel\<close>
  using bellman_err_branch_rel bellman_err_branch_rel_def 
  by auto

lemma a_code_eq[intro, simp]: \<open>a_code = a\<close>
  using a_rel unfolding a_rel_def by auto

lemma a_in_acts[intro, simp]: \<open>a \<in> actions\<close>
  using a_rel unfolding a_rel_def by auto

lemma w_code_eq [intro, simp]: \<open>i < h_dim \<Longrightarrow> w_code i = w i\<close>
  using w_rel unfolding w_rel'_def w_rel_def by auto

lemma g_cache[simp]: \<open>g_cache = g_code\<close>
  using g_rel unfolding g_rel_def by auto

lemma a_le[simp, intro]: \<open>a < actions_code\<close>  
  using a_in_acts actions_rel by blast

lemma state_relD: \<open>state_rel x y \<Longrightarrow> Vec.invar x \<and> Vec.\<alpha> x = y\<close>
  by auto

lemma partial_states_on_subs_dom: \<open>x \<in> partial_states_on X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> Y \<subseteq> dom x\<close>
  by blast

lemma bellman_diff_correct:
  assumes \<open>i < h_dim\<close> \<open>x \<in> partial_states_on (h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i))\<close>  \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (bellman_diff_code i) x_code = w i * (h i x - l * g' i a x)\<close>
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
    (\<lambda>x. w i * (h i x - l * g' i a x), h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i))\<close>
  using assms
  by (auto intro!: SR.scoped_fn_state_relI rel_funI bellman_diff_correct partial_states_onI)

lemma invar_t[intro, simp]: \<open>Vec.invar t_code\<close>
  using t_rel unfolding t_rel_def by auto

lemma partial_state_ts[intro, simp]:
  \<open>set ts \<subseteq> partial_states\<close>
  using ts_rel unfolding ts_rel_def
  by (fastforce simp: in_set_conv_nth)

lemma invar_ts[intro, simp]: \<open>t' \<in> set ts_code \<Longrightarrow> Vec.invar t'\<close>
  unfolding in_set_conv_nth 
  using ts_rel ts_rel_def 
  by blast

lemma C_inv[simp, intro!]: \<open>i < h_dim \<Longrightarrow> SR.invar (C_code ! i)\<close>
  unfolding C_code_def
  using bellman_diff_invar invar_ts
  by (auto simp: hg_inst_code_def)

lemma t_code_eq_t[simp, intro]: \<open>state_rel t_code t\<close>
  using t_rel unfolding t_rel_def
  by auto

lemma scope_t[simp]: \<open>dom (Vec.\<alpha> t_code) = dom t\<close>
  by auto

lemma t_partial: \<open>t \<in> partial_states\<close>
  using t_code_eq_t by blast

lemma partial_states_add[intro]: \<open>x \<in> partial_states \<Longrightarrow> y \<in> partial_states \<Longrightarrow> x ++ y \<in> partial_states\<close>
  by auto

lemma partial_states_restr[intro]: \<open>x \<in> partial_states \<Longrightarrow> x |` X \<in> partial_states\<close>
  by blast

lemma hg_inst_rel:
  assumes \<open>i < h_dim\<close>
  shows \<open>SR.scoped_fn_state_rel (=) (hg_inst_code i) (hg_inst w t a i, hg_scope t a i)\<close>
proof -
  have \<open>h_scope i \<union> \<Gamma>\<^sub>a a (h_scope i) - dom t \<subseteq> dom y \<Longrightarrow>
           SR.scoped_\<alpha> ((SR.inst (bellman_diff_code i) t_code)) x = w i * (h i (y ++ t) - l * g' i a (y ++ t))\<close> if \<open>state_rel x y\<close> for x y
    using assms that t_partial
    by (subst SR.scoped_fn_state_rel_inst[OF bellman_diff_code_rel _ that t_code_eq_t])
      (auto intro!:  arg_cong2[where f = \<open>(-)\<close>] 
        has_scope_on_eq[OF scope_g'] 
        has_scope_on_eq[OF scope_hI[of _ \<open>h_scope i\<close>]] 
        partial_states_add map_add_app_eqI[symmetric] iff del: domIff)
 thus ?thesis
    using assms
  unfolding hg_inst_def hg_inst_code_def hg_scope_def
  by (auto intro!: SR.scoped_fn_state_relI)
qed

lemma C_rel:
  shows \<open>list_all2 (SR.scoped_fn_state_rel (=)) C_code (C w t a)\<close>
  unfolding C_code_def C_def
  using hg_inst_rel
  by (auto intro!: list_all2_all_nthI)

lemma C_scope':
  assumes \<open>i < h_dim\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (C_code ! i) = snd (C w t a ! i)\<close>
  using assms hg_inst_rel[OF assms]
  unfolding C_def C_code_def 
  by auto

lemma C_scope[simp]:
  assumes \<open>i < h_dim\<close>
  shows \<open>SR.scoped_scope_\<alpha> (C_code ! i) = hg_scope t a i\<close>
  unfolding C_scope'[OF assms] C_def
  using assms
  by auto

lemma C_snd[simp]: 
  assumes \<open>i < h_dim\<close>
  shows \<open>snd (C w t a! i) = hg_scope t a i\<close>
  using assms unfolding C_def by (auto simp: hg_inst_def hg_scope_def)

lemma len_C[simp]: \<open>length (C w t a) = h_dim\<close>
  unfolding C_def by auto

lemma neg_C_snd[simp]: 
  assumes \<open>i < h_dim\<close>
  shows \<open>snd (neg_C w t a! i) = hg_scope t a i\<close>
  using assms unfolding neg_C_def neg_scoped_def 
  by (auto simp: case_prod_unfold)

lemma hg_inst_code_eq[simp]: \<open>
    i < h_dim \<Longrightarrow>
    hg_scope t a i \<subseteq> dom x \<Longrightarrow>
    state_rel x_code x \<Longrightarrow> (SR.scoped_\<alpha> (hg_inst_code i) x_code) = hg_inst w t a i x\<close>
  using hg_inst_rel[of i]
  by (auto elim!: SR.scoped_fn_state_relE rel_funE)

lemma C_apply[simp]:
  assumes \<open>i < h_dim\<close> \<open>hg_scope t a i \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (C_code ! i) x_code = fst (C w t a ! i) x\<close>
  unfolding C_code_def C_def
  using assms 
  by auto

lemma len_C_code[simp]: \<open>length C_code = h_dim\<close>
  using C_code_def by auto

lemma len_neg_C_code[simp]: \<open>length neg_C_code = h_dim\<close>
  using neg_C_code_def by auto

lemma neg_C_inv[simp, intro!]: \<open>i < h_dim \<Longrightarrow> SR.invar (neg_C_code ! i)\<close>
  unfolding neg_C_code_def
  by auto

lemma C'_inv[simp, intro!]: \<open>i < h_dim \<Longrightarrow> STE.SE.invar (C'_code ! i)\<close>
  unfolding C'_code_def 
  by simp

lemma C'_scope[simp]:
  assumes \<open>i < h_dim\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> (C'_code ! i) = hg_scope t a i\<close>
  unfolding C'_code_def using C_scope assms STE.to_ereal_scope 
  by auto

lemma C'_scope'[simp]:
  assumes \<open>i < h_dim\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> (C'_code ! i) = snd (C w t a ! i)\<close>
  using assms C_scope' by auto 

lemma C'_apply[simp]:
  assumes \<open>i < h_dim\<close> \<open>snd (C w t a ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>STE.SE.scoped_\<alpha> (C'_code ! i) x_code = fst (C w t a ! i) x\<close>
  unfolding C'_code_def
  using assms
  by auto

lemma neg_C_rel:
  shows \<open>list_all2 (SR.scoped_fn_state_rel (=)) neg_C_code (neg_C w t a)\<close>
  unfolding neg_C_code_def neg_C_def
  using C_rel
  by (auto intro!: rel_funI simp: list_all2_conv_all_nth)

lemma neg_C_scope[simp]:
  assumes \<open>i < h_dim\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (neg_C_code ! i) = hg_scope t a i\<close>
  using C_scope 
  unfolding neg_C_code_def
  by (auto simp: assms)

lemma neg_C_scope'[simp]:
  assumes \<open>i < h_dim\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (neg_C_code ! i) = snd (neg_C w t a ! i)\<close>
  using assms C_scope' 
  unfolding neg_C_def 
  by auto

lemma neg_C_apply[simp]:
  assumes \<open>i < h_dim\<close> \<open>snd (neg_C w t a ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (neg_C_code ! i) x_code = fst (neg_C w t a ! i) x\<close>
  unfolding neg_C_def neg_C_code_def
  using assms
  by auto

lemma neg_C'_inv[simp, intro!]: \<open>i < h_dim \<Longrightarrow> STE.SE.invar (neg_C'_code ! i)\<close>
  unfolding neg_C'_code_def C'_code_def neg_C_code_def
  by simp

lemma neg_C'_scope[simp]:
  assumes \<open>i < h_dim\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> (neg_C'_code ! i) = hg_scope t a i\<close>
  using assms neg_C'_code_def neg_C_inv neg_C_scope
  by auto

lemma neg_C'_scope'[simp]:
  assumes \<open>i < h_dim\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> ((neg_C'_code ! i)) = snd (neg_C w t a ! i)\<close>
  using assms neg_C_scope' 
  by auto

lemma length_neg_C[simp]: \<open>length (neg_C w t a) = h_dim\<close>
  using len_C 
  unfolding neg_C_def 
  by auto

lemma neg_C'_apply[simp]:
  assumes \<open>i < h_dim\<close> \<open>snd (neg_C w t a ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>STE.SE.scoped_\<alpha> (neg_C'_code ! i) x_code = fst (neg_C w t a ! i) x\<close>
  using neg_C'_code_def assms 
  by auto

lemma snd_b[simp]: \<open>i < reward_dim a \<Longrightarrow> snd (b t a ! i) = r_scope t a i\<close>
  unfolding b_def by auto

lemma r_inst_inv[simp, intro!]: \<open>i < reward_dim a \<Longrightarrow> SR.invar (r_inst_code i)\<close>
  by (auto simp: r_inst_code_def)

lemma rewards_code_scope[simp]: 
  \<open>i < reward_dim a \<Longrightarrow> SR.scoped_scope_\<alpha> (rewards_code a i) = reward_scope a i\<close>
  using reward_rels reward_scope_eq
  by auto

lemma r_inst_scope[simp]:
  assumes \<open>i < reward_dim a\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (r_inst_code i) = reward_scope a i - dom t\<close>
  using assms
  unfolding r_inst_code_def
  by auto

lemma r_inst_scope'[simp]:
  assumes \<open>i < reward_dim a\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (r_inst_code i) = snd (b t a ! i)\<close>
  unfolding b_def
  using assms
  by (auto simp: r_scope_def)

lemma scoped_fn_state_rel_rewards:
  assumes \<open>i < reward_dim a\<close>
  shows \<open>SR.scoped_fn_state_rel (=) (rewards_code a_code i) (rewards a i, reward_scope a i)\<close>
  using assms
  by auto

lemma r_inst_apply:
  assumes \<open>i < reward_dim a\<close> \<open>r_scope t a i \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (r_inst_code i) x_code = fst (b (t |` reward_scope a i) a ! i) x\<close>
  using assms  scoped_fn_state_rel_rewards 
  by (auto simp: r_scope_def r_inst_code_def b_def r_inst_def intro!: SR.scoped_fn_state_rel_inst')


lemma r_inst_apply'[simp]:
  assumes \<open>i < reward_dim a\<close> \<open>r_scope t a i \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (r_inst_code i) x_code = fst (b t a ! i) x\<close>
  unfolding r_inst_apply[OF assms] b_def r_inst_def
  using assms t_partial
  by (auto intro!: map_add_app_eqI has_scope_on_eq[OF reward_scope])

lemma length_b_code[simp]: \<open>length b_code = reward_dim a\<close>
  unfolding b_code_def
  by auto

lemma b_inv[simp, intro!]: \<open>i < reward_dim a \<Longrightarrow> SR.invar (b_code ! i)\<close>
  unfolding b_code_def 
  using r_inst_inv a_code_eq 
  by auto

lemma b_scope[simp]:
  assumes \<open>i < reward_dim a\<close> 
  shows \<open>SR.scoped_scope_\<alpha> ((b_code ! i)) = reward_scope a i - dom t\<close>
  using assms b_code_def 
  by auto

lemma b_scope'[simp]:
  assumes \<open>i < reward_dim a\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (b_code ! i) = snd (b t a ! i)\<close>
  using assms r_inst_scope'
  by auto

lemma b_apply:
  assumes \<open>i < reward_dim a\<close> \<open>r_scope t a i \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (b_code ! i) x_code = fst (b (t |` reward_scope a i) a ! i) x\<close>
  using assms r_inst_apply
  unfolding b_code_def 
  by auto

lemma b_apply'[simp]:
  assumes \<open>i < reward_dim a\<close> \<open>r_scope t a i \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (b_code ! i) x_code = fst (b t a ! i) x\<close>
  unfolding b_apply[OF assms] b_def r_inst_def
  using assms t_partial
  by (auto intro!: map_add_app_eqI has_scope_on_eq[OF reward_scope])

lemma neg_b_inv[simp, intro!]: \<open>i < reward_dim a \<Longrightarrow> SR.invar (neg_b_code ! i)\<close>
  unfolding neg_b_code_def
  by fastforce

lemma neg_b_scope[simp]:
  assumes \<open>i < reward_dim a\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (neg_b_code ! i) = reward_scope a i - dom t\<close>
  using b_code_def neg_b_code_def length_b_code assms 
  by force

lemma neg_b_scope'[simp]:
  assumes \<open>i < reward_dim a\<close> 
  shows \<open>SR.scoped_scope_\<alpha> (neg_b_code ! i) = snd (neg_b t a ! i)\<close>
  using assms b_def neg_b_def r_inst_scope' neg_b_def b_def 
  by force

lemma neg_b_apply[simp]:
  assumes \<open>i < reward_dim a\<close> \<open>snd (neg_b t a ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>SR.scoped_\<alpha> (neg_b_code ! i) x_code = fst (neg_b t a ! i) x\<close>
  using assms 
  unfolding neg_b_def neg_b_code_def
  by (auto simp: r_scope_def uminus_ereal.simps[symmetric] b_def)

lemma ts_rel_list[intro]: \<open>list_all2 state_rel ts_code ts\<close>
  using ts_rel ts_rel_def 
  by blast

lemma len_ts[simp]: \<open>length ts_code = length ts\<close>
  using ts_rel_list 
  by blast

lemma scope_ts[simp]: \<open>i < length ts \<Longrightarrow> dom (Vec.\<alpha> (ts_code ! i)) = dom (ts ! i)\<close>
  using ts_rel_list
  by auto

(* indicator functions *)
lemma \<I>'_inv[simp, intro!]: \<open>i < length ts \<Longrightarrow> STE.SE.invar (\<I>'_code ! i)\<close>
  by (auto simp: \<I>'_code_def)
  
lemma \<I>'_scope:
  assumes \<open>i < length ts\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> (\<I>'_code ! i) = dom (ts ! i) - dom t\<close>
  unfolding \<I>'_code_def 
  using assms 
  by auto

lemma \<I>'_scope'[simp]:
  assumes \<open>i < length ts\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> (\<I>'_code ! i) = snd (\<I>' ts t ! i)\<close>
  using assms \<I>'_scope
  unfolding \<I>'_def 
  by auto

lemma state_invar_ts_nth[simp, intro!]: \<open>i < length ts \<Longrightarrow> Vec.invar (ts_code ! i)\<close>
  by auto

lemma ind_scoped_\<alpha>[simp]: \<open>Vec.invar x \<Longrightarrow>
  Vec.invar y \<Longrightarrow>
  dom (Vec.\<alpha> x) \<subseteq> dom (Vec.\<alpha> y) \<Longrightarrow>
  STE.SE.scoped_\<alpha> (STE.SE.ind x) y = (if Vec.\<alpha> x = Vec.\<alpha> y |` dom (Vec.\<alpha> x) then -\<infinity> else 0)\<close>
  by (simp add: STE.SE.ind_apply_false[of x y] STE.SE.ind_apply_true[of x y])

sublocale STE.SE: States_Code_Transfer dims doms doms_code dims_code
  by unfold_locales

lemma eR_scoped_fn_state_rel_ind:
  assumes \<open>i < length ts\<close> \<open>i < length ts\<close>
  shows \<open>STE.SE.scoped_fn_state_rel (=) (STE.SE.ind (ts_code ! i)) 
  (\<lambda>x. if consistent x (ts ! i) then - \<infinity> else 0, dom (ts ! i))\<close>
  using assms ts_rel_list[unfolded list_all2_conv_all_nth]
  by (fastforce intro!: STE.SE.scoped_fn_state_relI rel_funI simp: consistent_def)

lemma scoped_ind_eq:
  assumes \<open>i < length ts\<close> \<open>i < length ts\<close> \<open>dom (ts ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>STE.SE.scoped_\<alpha> (STE.SE.ind (ts_code ! i)) x_code =
  fst (\<lambda>x. if consistent x (ts ! i) then - \<infinity> else 0, dom (ts ! i)) x\<close>
  using assms
  by (intro STE.SE.scoped_fn_state_rel_eq[OF _ eR_scoped_fn_state_rel_ind]) auto

lemma restr_add_restr: \<open>(x ++ y |` m) |` m = (x ++ y) |` m\<close>
  by force
lemma scoped_inst_ind_t:
  assumes \<open>i < length ts\<close> \<open>state_rel x_code x\<close> \<open>dom (ts ! i) - dom t \<subseteq> dom x\<close>
  shows \<open>STE.SE.scoped_\<alpha> ((STE.SE.inst (STE.SE.ind (ts_code ! i)) t_code)) x_code = 
  fst (\<lambda>x. if consistent x (ts ! i) then - \<infinity> else 0, dom (ts ! i)) (x ++ t)\<close>
  supply scoped_ind_eq[of _ \<open>x ++ (t |` dom (ts ! i))\<close>, subst] STE.SE.scoped_inst_\<alpha>[subst]
  using assms
  by (auto simp: consistent_def restr_add_restr t_code_eq_t[THEN state_relD] 
      intro!: Vec.vec_inst_rel' iff del: domIff)

lemma \<I>'_apply[simp]:
  assumes \<open>i < length ts\<close> \<open>snd (\<I>' ts t ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>STE.SE.scoped_\<alpha> (\<I>'_code ! i) x_code = fst (\<I>' ts t ! i) x\<close>
  using assms
  unfolding \<I>'_code_def \<I>'_def
  by (auto simp: scoped_inst_ind_t)

lemma length_b'[simp]: \<open>length (b' t a ts) = length (b t a) + length (\<I>' ts t)\<close>
  unfolding b'_def by auto

lemma length_b[simp]: \<open>length (b t a) = reward_dim a\<close>
  unfolding b_def by auto

lemma length_neg_b[simp]: \<open>length (neg_b t a) = reward_dim a\<close>
  unfolding neg_b_def by auto

lemma b_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) b_code (b t a)\<close>
  unfolding list_all2_conv_all_nth
  by (fastforce simp: r_scope_def)

lemma b_rel': \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) (map STE.to_ereal b_code) (b t a)\<close>
  unfolding list_all2_conv_all_nth
  by (fastforce simp: r_scope_def case_prod_unfold)

lemma neg_b_rel: \<open>list_all2 (SR.scoped_fn_state_rel (=)) neg_b_code (neg_b t a)\<close>
proof -
  have \<open>SR.scoped_fn_state_rel (\<lambda>x. (=) (x)) (SR.scale (b_code ! i) (- 1)) (neg_scoped (b t a ! i))\<close>
    if \<open>SR.scoped_fn_state_rel (\<lambda>x. (=) (x)) ((b_code ! i)) ((b t a ! i))\<close> \<open>i < length (b t a)\<close>
    for i
    using that by (fastforce simp: case_prod_unfold r_scope_def)
  thus ?thesis
  using b_rel
  unfolding neg_b_code_def neg_b_def 
  by (auto simp: list_all2_conv_all_nth)
qed  

lemma neg_b_rel': \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) (map STE.to_ereal neg_b_code) (neg_b t a)\<close>
  using neg_b_rel neg_b_scope'
  by (auto simp: case_prod_unfold list_all2_conv_all_nth intro!: STE.SE.scoped_fn_state_relI)
  
lemma len_\<I>'_code[simp]: \<open>length \<I>'_code = length (\<I>' ts t)\<close>
  unfolding \<I>'_code_def \<I>'_def 
  by auto

lemma len_\<I>'[simp]: \<open>length (\<I>' ts t) = length ts\<close>
  unfolding \<I>'_def by auto

lemma \<I>'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) \<I>'_code (\<I>' ts t)\<close>
  using \<I>'_scope'
  by (auto simp: list_all2_conv_all_nth intro!: STE.SE.scoped_fn_state_relI)

lemma b'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) b'_code (b' t a ts)\<close>
  unfolding b'_code_def b'_def
  using b_rel' \<I>'_rel
  by (auto simp: list_all2_iff)
  
lemma b'_inv[simp, intro!]: \<open>i < length (b' t a ts) \<Longrightarrow> STE.SE.invar (b'_code ! i)\<close>
  using b'_rel
  by auto

lemma b'_scope[simp]:
  assumes \<open>i < length (b' t a ts)\<close> 
  shows \<open>STE.SE.scoped_scope_\<alpha> (b'_code ! i) = snd (b' t a ts ! i)\<close>
  using b'_rel assms
  by fastforce
  
lemma b'_apply[simp]:
  assumes \<open>i < length (b' t a ts)\<close> \<open>snd (b' t a ts ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>STE.SE.scoped_\<alpha> (b'_code ! i) x_code = fst (b' t a ts ! i) x\<close>
  using assms b'_rel
  by (auto simp: list_all2_conv_all_nth)

lemma neg_b'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) neg_b'_code (neg_b' t a ts)\<close>
  unfolding neg_b'_code_def neg_b'_def
  using neg_b_rel' \<I>'_rel
  by (fastforce simp: list_all2_iff)

lemma neg_b'_inv[simp, intro!]: \<open>i < length (neg_b' t a ts) \<Longrightarrow> STE.SE.invar (neg_b'_code ! i)\<close>
  using neg_b'_rel by auto

lemma in_sr_scope[dest]: \<open>k \<in> dom (Vec.\<alpha> (ts_code ! j)) \<Longrightarrow> j < length ts \<Longrightarrow> k < dims\<close>
  using partial_state_ts nth_mem
  by (auto simp del: partial_state_ts)

lemma neg_b'_scope'[simp]:
  assumes \<open>i < length (neg_b' t a ts)\<close>
  shows \<open>STE.SE.scoped_scope_\<alpha> (neg_b'_code ! i) = snd (neg_b' t a ts ! i)\<close>
  using assms neg_b'_rel
  by fastforce

lemma neg_b'_apply[simp]:
  assumes \<open>i < length (neg_b' t a ts)\<close> \<open>snd (neg_b' t a ts ! i) \<subseteq> dom x\<close> \<open>state_rel x_code x\<close>
  shows \<open>STE.SE.scoped_\<alpha> (neg_b'_code ! i) x_code = fst (neg_b' t a ts ! i) x\<close>
  using assms neg_b'_rel 
  by (auto simp: list_all2_conv_all_nth)

(* variable elimination *)

lemma len_C'[simp]: \<open>length C'_code = h_dim\<close>
  unfolding C'_code_def by auto

lemma len_neg_b'[simp]: \<open>length (neg_b' t a ts) = length (neg_b t a) + length (\<I>' ts t)\<close>
  by (auto simp: neg_b'_def)

lemma C'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel ((=))) C'_code (C w t a)\<close>
  using C_rel 
  by (auto simp: list_all2_conv_all_nth case_prod_unfold intro!: STE.SE.scoped_fn_state_relI)

lemma len_neg_C'_code[simp]: \<open>length neg_C'_code = length (neg_C w t a)\<close>
  unfolding neg_C'_code_def by simp

lemma neg_C'_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel ((=))) neg_C'_code (neg_C w t a)\<close>
  by (auto simp: list_all2_conv_all_nth case_prod_unfold intro!: STE.SE.scoped_fn_state_relI)

lemma Cb_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) (C'_code @ neg_b'_code) (C w t a @ neg_b' t a ts)\<close>
  using C'_rel neg_b'_rel
  by (auto simp: list_all2_iff)

lemma neg_Cb_rel: \<open>list_all2 (STE.SE.scoped_fn_state_rel (=)) (neg_C'_code @ b'_code) (neg_C w t a @ b' t a ts)\<close>
  using neg_C'_rel b'_rel
  by (auto simp: list_all2_iff)

lemma neg_C_b'_valid: \<open>scope_inv (neg_C w t a @ b' t a ts)\<close>
  using scope_inv_neg_C[of t a w] scope_inv_b'[of t a ts] t_partial scope_inv_append 
  by auto

lemma C_neg_b'_valid: \<open>scope_inv (C w t a @ neg_b' t a ts)\<close>
  using scope_inv_C[of t a w] scope_inv_neg_b'[of t a ts] t_partial scope_inv_append 
  by auto

interpretation PmfSet: StdOSet SP.Pmf.dom_ops
  using SP.Pmf.set .

interpretation VE_Code_Invar: Variable_Elim_Code_Transfer
  dims_code
  doms_code

    \<open>(C'_code @ neg_b'_code)\<close>
    \<open>[0..<dims_code]\<close>

    vec_ops
    set_ops
    pmf_set_ops
    dims
    doms
    id
    \<open>ereal_ops\<close>
    \<open>(C w t a @ neg_b' t a ts)\<close>
  using doms_ne doms_fin C_neg_b'_valid neg_C_b'_valid
  unfolding scope_inv_def partial_states_def 
  by unfold_locales (auto simp: case_prod_unfold)

interpretation neg_VE_Code_Invar: Variable_Elim_Code_Transfer
  dims_code
    doms_code
    \<open>(neg_C'_code @ b'_code)\<close>
    \<open>[0..<dims_code]\<close>
    vec_ops
    set_ops
    pmf_set_ops
    dims
    doms
    id
    ereal_ops
    \<open>(neg_C w t a @ b' t a ts)\<close>
  using doms_ne doms_fin C_neg_b'_valid neg_C_b'_valid
  unfolding scope_inv_def partial_states_def 
  apply unfold_locales
  by (auto simp: case_prod_unfold)

lemma \<O>_rel: \<open>VE_Code_Invar.\<O>_rel\<close>
    unfolding VE_Code_Invar.\<O>_rel_def
    by (auto simp: and_rel_def)

lemma doms_rel: \<open>doms_rel\<close>
  using dims_rels 
  by blast

lemma dims_rel: \<open>dims_rel\<close>
  using dims_rels
  by blast

lemma \<F>_rel: \<open>VE_Code_Invar.\<F>_rel\<close>
  using Cb_rel
  unfolding VE_Code_Invar.\<F>_rel_def list_all2_iff
  by (auto simp: case_prod_unfold) 

lemma neg_\<F>_rel: \<open>neg_VE_Code_Invar.\<F>_rel\<close>
    unfolding neg_VE_Code_Invar.\<F>_rel_def
    using neg_Cb_rel
    by (auto simp: Ball_def set_zip list_all2_iff case_prod_unfold)

lemma full_vecs_states[simp]: \<open>full_vecs = states\<close>
  by (auto simp: full_vecs_def partial_vecs_def 
      states_def partial_states_def vecs_on_def case_prod_unfold)

lemma \<epsilon>_pos_code_eq[simp]: \<open>\<epsilon>_pos_code = \<epsilon>_pos w t a ts\<close>
  unfolding \<epsilon>_pos_code_def \<epsilon>_pos_def VE_Code_Invar.elim_max_eq[OF \<O>_rel doms_rel \<F>_rel dims_rel] ..

lemma \<epsilon>_neg_code_eq[simp]: \<open>\<epsilon>_neg_code = \<epsilon>_neg w t a ts\<close>
  unfolding \<epsilon>_neg_code_def \<epsilon>_neg_def neg_VE_Code_Invar.elim_max_eq[OF \<O>_rel doms_rel neg_\<F>_rel dims_rel] ..

lemma \<epsilon>_max_code_eq[simp]: \<open>\<epsilon>_max_code = \<epsilon>_max w t a ts\<close>
  unfolding \<epsilon>_max_code_eq \<epsilon>_max_def
  by auto

end

end