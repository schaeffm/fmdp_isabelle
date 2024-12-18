theory Factored_MDP
  imports
    "HOL-Probability.Probability"
    "Explicit-MDPs.MDP_reward"
    Util
begin
chapter \<open>Factored MDPs\<close>
text \<open>We introduce factored MDPs with discounted rewards.\<close>

type_synonym 'x state = "nat \<rightharpoonup> 'x"
type_synonym weights = "nat \<Rightarrow> real"

text \<open>Constant locale for simpler instantiations.\<close>
locale Factored_MDP_Consts =
  fixes
    dims :: nat and \<comment> \<open>Number of state variables\<close>
    doms :: \<open>nat \<Rightarrow> 'x :: countable set\<close> and \<comment> \<open>Domain of each state variable\<close>

reward_dim :: \<open>'a ::countable \<Rightarrow> nat\<close> and
\<comment> \<open>number of rewards for action\<close>
rewards :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'x state \<Rightarrow> real\<close> and 
\<comment> \<open>rewards a i x: reward i for action a in state x\<close>
reward_scope :: \<open>'a \<Rightarrow> nat \<Rightarrow> nat set\<close> and
\<comment> \<open>variables the reward function depends upon\<close>

actions :: \<open>'a set\<close> and
\<comment> \<open>finite, nonempty set of actions\<close>

transitions :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'x state \<Rightarrow> 'x pmf\<close> and
\<comment> \<open>pmf transitions a i x y: probability that next state at dim i will be y, for action x.\<close>
transitions_scope :: \<open>'a \<Rightarrow> nat \<Rightarrow> nat set\<close> and
\<comment> \<open>scopes of the transition functions\<close>

l :: real and
\<comment> \<open>discount factor < 1\<close>

h_dim :: \<open>nat\<close> and
\<comment> \<open>number of basis functions\<close>
h :: \<open>nat \<Rightarrow> 'x state \<Rightarrow> real\<close> and
\<comment> \<open>basis functions, estimate value function\<close>
h_scope :: \<open>nat \<Rightarrow> nat set\<close>
\<comment> \<open>scopes of the basis functions\<close>
begin

section \<open>Variables\<close>
abbreviation \<open>vars \<equiv> {..<dims}\<close>

lemma fin_vars_subs[dest]: \<open>X \<subseteq> vars \<Longrightarrow> finite X\<close>
  using finite_nat_iff_bounded 
  by blast

section \<open>States\<close>
text \<open>A state is a map from variable indices to variable assignments.
For a partial state, the domain of the state has to be a subset of the variables, 
and all variables have to be assigned a valid value.
A state is a partial state where all variables are in the domain.
There are also variants where at least this set or exactly this set is assigned.\<close>

definition \<open>partial_states = {x. \<forall>(i, j) \<in> Map.graph x. i \<in> vars \<and> j \<in> doms i}\<close>
lemmas refl[of partial_states, cong]

definition \<open>states = partial_states \<inter> {x. dom x = vars}\<close>
lemmas refl[of states, cong]

definition \<open>partial_states_on X = partial_states \<inter> {x. X \<subseteq> dom x}\<close>
lemmas refl[of partial_states_on, cong]

definition \<open>partial_states_on_eq X = partial_states \<inter> {x. X = dom x}\<close>
lemmas refl[of partial_states_on_eq, cong]

subsection \<open>Partial States\<close>
lemma partial_statesI[intro]: 
  assumes
    \<open>\<And>y i. x i = Some y \<Longrightarrow> i \<in> vars\<close>
    \<open>\<And>y i. x i = Some y \<Longrightarrow> y \<in> doms i\<close>
  shows 
    \<open>x \<in> partial_states\<close>
  unfolding partial_states_def
  using assms
  by (auto dest: in_graphD)

lemma partial_statesI2: 
  assumes \<open>dom x \<subseteq> vars\<close> and \<open>\<And>i. i \<in> dom x \<Longrightarrow> the (x i) \<in> doms i\<close>
  shows \<open>x \<in> partial_states\<close>
  using assms
  by (fastforce intro!: partial_statesI)

lemma partial_statesE[elim]: 
  assumes \<open>x \<in> partial_states\<close>
  obtains \<open>\<And>i y. x i = Some y \<Longrightarrow> y \<in> doms i \<and> i \<in> vars\<close>
  using assms
  unfolding partial_states_def
  by (fastforce intro: in_graphI)

lemma partial_statesE2: 
  assumes \<open>x \<in> partial_states\<close>
  obtains \<open>dom x \<subseteq> vars\<close>  \<open>\<And>i. i \<in> dom x \<Longrightarrow> the (x i) \<in> doms i\<close>
  using assms
  by fastforce

lemma partial_states_domD[dest]: 
  assumes \<open>x \<in> partial_states\<close>
  shows \<open>dom x \<subseteq> vars\<close>
  using assms
  by auto

lemma in_partial_states_iff: 
  \<open>x \<in> partial_states \<longleftrightarrow> (\<forall>i. case x i of None \<Rightarrow> True | Some y \<Rightarrow> i \<in> vars \<and> y \<in> doms i)\<close>
  by (auto split: option.splits)

subsection \<open>States\<close>
lemma statesI[intro]: 
  assumes
    \<open>\<And>i. x i = None \<Longrightarrow> i \<notin> vars\<close>
    \<open>\<And>i y. x i = Some y \<Longrightarrow> i \<in> vars \<and> y \<in> doms i\<close>
  shows \<open>x \<in> states\<close>
  using assms
  unfolding states_def
  by auto

lemma statesI2:
  assumes
    \<open>dom x = vars\<close>
    \<open>\<And>i. i \<in> dom x \<Longrightarrow> the (x i) \<in> doms i\<close>
  shows \<open>x \<in> states\<close>
  using assms
  unfolding states_def
  by (blast intro!: partial_statesI2)

lemma statesE[elim]:
  assumes \<open>x \<in> states\<close> 
  obtains
    \<open>\<And>i. x i = None \<Longrightarrow> i \<notin> vars\<close>
    \<open>\<And>i y. x i = Some y \<Longrightarrow> i \<in> vars \<and> y \<in> doms i\<close>
  using assms
  unfolding states_def
  by auto

lemma states_imp_partial:
  assumes \<open>x \<in> states\<close>
  shows \<open>x \<in> partial_states\<close>
  using assms
  by blast

lemma states_domD[dest]: \<open>x \<in> states \<Longrightarrow> dom x = vars\<close>
  by blast

lemma in_states_iff: \<open>x \<in> states \<longleftrightarrow> 
  (\<forall>i. case x i of None \<Rightarrow> i \<notin> vars | Some y \<Rightarrow> (i \<in> vars \<and> y \<in> doms i))\<close>
  by (auto split: option.splits)

subsection \<open>States defined on at least a subset of variables\<close>
lemma partial_states_onI[intro]: 
  assumes 
    \<open>\<And>i y. x i = Some y \<Longrightarrow> i \<in> vars \<and> y \<in> doms i\<close>
    \<open>\<And>i. x i = None \<Longrightarrow> i \<notin> X\<close>
  shows \<open>x \<in> partial_states_on X\<close>
  unfolding partial_states_on_def
  using assms
  by blast

lemma partial_states_onE[elim]: 
  assumes \<open>x \<in> partial_states_on X\<close>
  obtains
    \<open>\<And>i y. x i = Some y \<Longrightarrow> i \<in> vars \<and> y \<in> doms i\<close>
    \<open>\<And>i. x i = None \<Longrightarrow> i \<notin> X\<close>
  using assms
  unfolding partial_states_on_def
  by blast

lemma partial_states_on_domD[dest]: 
  assumes \<open>x \<in> partial_states_on X\<close>
  shows \<open>dom x \<subseteq> vars\<close>
  using assms
  by auto

lemma in_partial_states_on_iff: 
  \<open>x \<in> partial_states_on X \<longleftrightarrow> (\<forall>i. case x i of None \<Rightarrow> i \<notin> X | Some y \<Rightarrow> (i \<in> vars \<and> y \<in> doms i))\<close>
  by (auto split: option.splits)

subsection \<open>States defined on exactly a subset of variables\<close>
lemma partial_states_on_eqI[intro]: 
  assumes 
    \<open>\<And>i y. x i = Some y \<Longrightarrow> y \<in> doms i \<and> i \<in> X\<close>    
    \<open>\<And>i. x i = None \<Longrightarrow> i \<notin> X\<close>
    \<open>X \<subseteq> vars\<close>
  shows \<open>x \<in> partial_states_on_eq X\<close>
  unfolding partial_states_on_eq_def
  using assms
  by blast

lemma partial_states_on_eqE[elim]: 
  assumes \<open>x \<in> partial_states_on_eq X\<close>
  obtains
    \<open>\<And>i y. x i = Some y \<Longrightarrow> y \<in> doms i \<and> i \<in> X\<close>    
    \<open>\<And>i. x i = None \<Longrightarrow> i \<notin> X\<close>
    \<open>X \<subseteq> vars\<close>
  using assms
  unfolding partial_states_on_eq_def
  by blast

lemma partial_states_on_eq_domD[dest]: 
  assumes \<open>x \<in> partial_states_on_eq X\<close>
  shows \<open>dom x = X\<close>
  using assms
  by blast

lemma in_partial_states_on_eq_iff: \<open>x \<in> partial_states_on_eq X \<longleftrightarrow> (X \<subseteq> vars \<and>
  (\<forall>i. case x i of None \<Rightarrow> i \<notin> X | Some y \<Rightarrow> (i \<in> X \<and> y \<in> doms i)))\<close>
  by (force split: option.splits elim!: partial_states_on_eqE intro!: partial_states_on_eqI)+

lemma partial_states_on_eq_imp_partial: \<open>x \<in> partial_states_on_eq X \<Longrightarrow> x \<in> partial_states\<close>
  using partial_states_on_eqE 
  by blast

lemma restr_partial_states_on_eqI:
  assumes \<open>X \<subseteq> vars\<close> \<open>x \<in> partial_states_on X\<close>
  shows \<open>x |` X \<in> partial_states_on_eq X\<close>
  unfolding restrict_map_def
  using assms
  by (auto elim!: partial_states_onE split: if_splits)

definition \<open>some_state = (SOME x. x \<in> states)\<close>

definition \<open>reward a x = (\<Sum>i < reward_dim a. rewards a i x)\<close>

end

locale Factored_MDP = Factored_MDP_Consts
  where 
    rewards = rewards
  for 
    rewards :: \<open>'a::countable \<Rightarrow> nat \<Rightarrow> 'x::countable state \<Rightarrow> real\<close> +
  assumes
    transitions_closed:
    \<open>\<And>a i x.
        a \<in> actions \<Longrightarrow>
        i < dims \<Longrightarrow>
        x \<in> partial_states_on (transitions_scope a i) \<Longrightarrow>
        set_pmf (transitions a i x) \<subseteq> doms i\<close> and \<comment> \<open>transitions go to domains\<close>
    transitions_scope: 
    \<open>\<And>a i.
        a \<in> actions \<Longrightarrow>
        i < dims \<Longrightarrow>
        has_scope_on (transitions a i) partial_states (transitions_scope a i)\<close> and
    \<comment> \<open>the transition functions have the specified scopes\<close>
    transitions_scope_dims:
    \<open>\<And>a i.
        a \<in> actions \<Longrightarrow>
        i < dims \<Longrightarrow> transitions_scope a i \<subseteq> {..<dims}\<close> and
    \<comment> \<open>the scopes are valid\<close>
    actions_fin: \<open>finite actions\<close> and
    actions_ne: \<open>actions \<noteq> {}\<close> and
    \<comment> \<open>finite, nonempty action sets\<close>

doms_fin: \<open>\<And>i. i < dims \<Longrightarrow> finite (doms i)\<close> and
doms_ne: \<open>\<And>i. i < dims \<Longrightarrow> doms i \<noteq> {}\<close> and
\<comment> \<open>finite, nonempty domains\<close>

dims_pos: \<open>dims > 0\<close> and
\<comment> \<open>there exists a domain\<close>

reward_scope: 
\<open>\<And>a i. 
        a \<in> actions \<Longrightarrow>
        i < reward_dim a \<Longrightarrow>
        has_scope_on (rewards a i) partial_states (reward_scope a i)\<close> and
reward_scope_dims:
\<open>\<And>a i.
        a \<in> actions \<Longrightarrow>
        i < reward_dim a \<Longrightarrow> reward_scope a i \<subseteq> {..<dims}\<close> and
\<comment> \<open>the reward functions are proper scoped functions\<close>

h_scope:
\<open>\<And>i. 
        i < h_dim \<Longrightarrow> 
        has_scope_on (h i) partial_states (h_scope i)\<close> and
h_scope_dims:
\<open>\<And>i. i < h_dim \<Longrightarrow> h_scope i \<subseteq> {..<dims}\<close> and
\<comment> \<open>the basis functions are proper scoped functions\<close>

disc_lt_one: \<open>l < 1\<close> and
disc_nonneg: \<open>l \<ge> 0\<close> \<comment> \<open>valid discount factor\<close>

begin
section \<open>Basic Properties\<close>
subsection \<open>States\<close>
lemma partial_states_eq_Un: 
  \<open>partial_states = (\<Union>x \<in> {x. x \<subseteq> vars}. partial_states_on_eq x)\<close> (is \<open>?L = ?R\<close>)
proof -
  have \<open>x \<in> ?L \<Longrightarrow> x \<in> ?R\<close> for x 
    by (auto intro!: exI[of _ \<open>dom x\<close>])
  moreover have \<open>?R \<subseteq> ?L\<close> 
    by auto
  ultimately show ?thesis 
    by auto
qed

lemma fin_partial_states_eq:
  assumes \<open>X \<subseteq> vars\<close>
  shows \<open>finite (partial_states_on_eq X)\<close>
proof -
  have \<open>partial_states_on_eq X \<subseteq> {x. dom x \<subseteq> X \<and> ran x \<subseteq> (\<Union>i \<in> X. doms i)}\<close> (is \<open>?L \<subseteq> ?R\<close>)
    by (auto elim!: ranE)
  moreover have \<open>finite ?R\<close>
    using assms fin_vars_subs doms_fin
    by (intro finite_set_of_finite_maps') auto
  ultimately show ?thesis
    using finite_subset 
    by fastforce
qed

lemma fin_partial_states: \<open>finite partial_states\<close>
  using partial_states_eq_Un fin_partial_states_eq
  by auto

lemma fin_states: \<open>finite states\<close>
  by (rule finite_subset[OF _ fin_partial_states]) fast

lemma states_ne: \<open>states \<noteq> {}\<close>
proof -
  have \<open>(\<lambda>i. if i < dims then Some (SOME x. x \<in> doms i) else None) \<in> states\<close>
    using doms_ne
    by (auto simp: some_in_eq intro!: statesI split: if_splits)
  thus ?thesis
    by auto
qed

lemma some_in_states: \<open>some_state \<in> states\<close>
  unfolding some_state_def
  using states_ne some_in_eq by auto

lemma partial_states_on_states:
  assumes \<open>x \<in> states\<close> \<open>X \<subseteq> {..<dims}\<close>
  shows \<open>x \<in> partial_states_on X\<close>
  using assms 
  by blast

subsection \<open>Basis Functions\<close>
lemma h_scopeD[dest]: \<open>j \<in> h_scope i \<Longrightarrow> i < h_dim \<Longrightarrow> j < dims\<close>
  using h_scope_dims 
  by auto

lemma scope_hI[intro]: \<open>i < h_dim \<Longrightarrow> h_scope i \<subseteq> R \<Longrightarrow> has_scope_on (h i) partial_states R\<close>
  using has_scope_on_subs[OF h_scope] 
  by auto

lemma scope_h_states_I[intro]: \<open>i < h_dim \<Longrightarrow> h_scope i \<subseteq> R \<Longrightarrow> has_scope_on (h i) states R\<close>
  using states_imp_partial 
  by auto

subsection \<open>Rewards\<close>
lemma reward_scopeD [dest]:
  assumes \<open>j \<in> reward_scope a i\<close>
    and \<open>a \<in> actions\<close>
    and \<open>i < reward_dim a\<close>
  shows \<open>j < dims\<close>
  using assms reward_scope_dims
  by auto

lemma scope_rewardI [intro]:
  assumes \<open>i < reward_dim a\<close>
    and \<open>a \<in> actions\<close>
    and \<open>reward_scope a i \<subseteq> R\<close>
  shows \<open>has_scope_on (rewards a i) partial_states R\<close>
  using assms reward_scope
  by auto

lemma scope_reward_states_I [intro]:
  assumes \<open>i < reward_dim a\<close>
    and \<open>a \<in> actions\<close>
    and \<open>reward_scope a i \<subseteq> R\<close>
  shows \<open>has_scope_on (rewards a i) states R\<close>
  using assms states_imp_partial
  by auto


subsection \<open>Domains\<close>
lemmas doms_fin[intro]

subsection \<open>Transitions\<close>
lemma transitions_scopeD [dest]:
  assumes \<open>j \<in> transitions_scope a i\<close>
    and \<open>i < dims\<close>
    and \<open>a \<in> actions\<close>
  shows \<open>j < dims\<close>
  using assms transitions_scope_dims
  by auto

lemma transitionsD [dest]:
  assumes \<open>x' \<in> set_pmf (transitions a i x)\<close>
    and \<open>a \<in> actions\<close>
    and \<open>i < dims\<close>
    and \<open>x \<in> partial_states_on (transitions_scope a i)\<close>
  shows \<open>x' \<in> doms i\<close>
  using assms transitions_closed
  by blast

lemma transitionsD'[dest]:
  assumes \<open>x' \<in> set_pmf (transitions a i x)\<close>
    and \<open>a \<in> actions\<close>
    and \<open>i < dims\<close>
    and \<open>x \<in> states\<close>
  shows \<open>x' \<in> doms i\<close>
  using assms
  by blast

lemma scope_transitionsI [intro]:
  assumes \<open>i < dims\<close>
    and \<open>a \<in> actions\<close>
    and \<open>transitions_scope a i \<subseteq> R\<close>
  shows \<open>has_scope_on (transitions a i) partial_states R\<close>
  using assms has_scope_on_subs[OF transitions_scope]
  by auto

subsection \<open>Rewards\<close>

lemmas reward_eq = reward_def
end
end