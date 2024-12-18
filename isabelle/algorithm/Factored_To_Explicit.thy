theory Factored_To_Explicit
  imports Factored_MDP
begin

section \<open>Conversion of factored to explicit MDPs\<close>
text \<open>We represent a factored MDP as an explicit MDP, where each state is a list.\<close>
context Factored_MDP_Consts
begin
definition "to_expl s = map (the o s) [0..<dims]"
lemmas refl[of to_expl, cong]

definition "from_expl s = map_of (List.enumerate 0 s)"
lemmas refl[of from_expl, cong]

definition \<open>states_expl = to_expl ` states\<close>
lemmas refl[of states_expl, cong]

definition transition_expl :: "('x list \<times> 'a) \<Rightarrow> ('x list) pmf" where
  "transition_expl sa = (
    if (fst sa) \<in> states_expl then
      list_pmf (map (\<lambda>i. transitions (snd sa) i (from_expl (fst sa))) [0..<dims])
    else 
      return_pmf (fst sa))"
lemmas refl[of transition_expl, cong]

definition reward_expl:: "('x list \<times> 'a) \<Rightarrow> real" where
  "reward_expl sa = (case sa of (s,a) \<Rightarrow> (let s_factored = from_expl s in
    if s \<in> states_expl \<and> a \<in> actions then reward a s_factored else 0))"
lemmas refl[of reward_expl, cong]

definition \<open>actions_expl s = actions\<close>
lemmas refl[of actions_expl, cong]
end

context Factored_MDP
begin
lemmas to_expl_eq = to_expl_def

lemma length_to_expl[simp]: \<open>length (to_expl s) = dims\<close>
  unfolding to_expl_eq
  by auto

lemma to_expl_nth[simp]: \<open>i < dims \<Longrightarrow> to_expl s ! i = the (s i)\<close>
  unfolding to_expl_eq
  by auto

lemmas from_expl_eq = from_expl_def

lemma from_to [simp]: \<open>x \<in> states \<Longrightarrow> from_expl (to_expl x) = x\<close>
  unfolding from_expl_eq to_expl_eq
  by (force intro!: ext elim!: statesE simp: map_of_enumerate)

lemma inj_to_expl: \<open>inj_on to_expl states\<close>
  using from_to inj_on_inverseI
  by blast

lemma in_states_expl_iff: \<open>x \<in> states_expl \<longleftrightarrow> x \<in> to_expl ` states\<close>
  by (auto simp: states_expl_def)

lemma in_states_expl[intro]: \<open>x \<in> states \<Longrightarrow> to_expl x \<in> states_expl\<close>
  using in_states_expl_iff
  by fastforce

lemma in_states_expl'[dest]: "x \<in> states_expl \<Longrightarrow> from_expl x \<in> states"
  using in_states_expl_iff 
  by force

lemma finite_states_expl: "finite states_expl"
  using fin_states
  by (simp add: states_expl_def)

lemma states_expl_ne: "states_expl \<noteq> {}"
  using in_states_expl_iff states_ne
  by auto

lemma states_explE[elim]: 
  assumes \<open>xs \<in> states_expl\<close>
    obtains \<open>length xs = dims\<close> \<open>\<And>i. i < dims \<Longrightarrow> xs ! i \<in> doms i\<close>
  using assms
  unfolding states_expl_def
  by force

lemma to_from [simp]: \<open>x \<in> states_expl \<Longrightarrow> to_expl (from_expl x) = x\<close>
  unfolding from_expl_eq to_expl_eq
  by (auto simp: map_upt_eqI map_of_enumerate)

lemma states_explI[intro]: 
  assumes \<open>length xs = dims\<close> \<open>\<And>i. i < dims \<Longrightarrow> xs ! i \<in> doms i\<close> 
  shows \<open>xs \<in> states_expl\<close>
  using assms
  unfolding states_expl_def to_expl_def
  by (auto simp: from_expl_eq image_iff map_of_enumerate map_upt_eqI 
      intro!: Factored_MDP_Consts.statesI bexI[of _ \<open>from_expl xs\<close>] 
      split: if_splits)

lemma states_explicit_alt: 
  \<open>states_expl = {xs. length xs = dims \<and> (\<forall>i < dims. xs ! i \<in> doms i)}\<close> (is \<open>?L = ?R\<close>)
  using Factored_MDP_axioms
  by (auto intro!: Factored_MDP.states_explI)

lemma transition_expl_pmf:
  assumes \<open>a \<in> actions\<close> \<open>s \<in> states\<close> \<open>s' \<in> states\<close>
  shows \<open>pmf (transition_expl (to_expl s, a)) (to_expl s') = (\<Prod>i < dims. pmf (transitions a i s) (the (s' i)))\<close>
  unfolding transition_expl_def
  using assms
  by (auto simp: pmf_list_pmf)

lemma reward_expl_eq[simp]:
  assumes \<open>s \<in> states\<close> \<open>a \<in> actions\<close>
  shows \<open>reward_expl (to_expl s, a) = reward a s\<close>
  unfolding reward_expl_def
  using assms
  by auto

lemma reward_expl_eq'[simp]:
  assumes \<open>s \<in> states_expl\<close> \<open>a \<in> actions\<close>
  shows \<open>reward_expl (s, a) = reward a (from_expl s)\<close>
  using assms
  by (subst reward_expl_eq[symmetric]) auto

lemma reward_expl_zero[simp]:
  assumes \<open>\<not> a \<in> actions \<or> s \<notin> states_expl\<close>
  shows \<open>reward_expl (s, a) = 0\<close>
  using reward_expl_def assms
  by auto

lemma fin_range: "finite (range reward_expl)"
proof -
  have "range (reward_expl) \<subseteq> insert 0 ((\<lambda>(s,a). reward a (from_expl s)) ` (states_expl \<times> actions))"
    by (fastforce intro!: reward_expl_zero simp: image_iff)
  then show ?thesis
    by (rule finite_subset) (auto intro!: actions_fin finite_states_expl)
qed

lemmas actions_expl_def[simp]

subsection \<open>Instantiation as an explicit MDP\<close>
lemma expl_MDP: \<open>MDP_reward_disc actions_expl reward_expl l\<close>
  using actions_ne fin_range disc_lt_one disc_nonneg
  by unfold_locales auto

sublocale E : MDP_reward_disc actions_expl transition_expl reward_expl l
  using expl_MDP .
end
end