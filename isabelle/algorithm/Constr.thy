theory Constr
  imports "Complex_Main"
begin

chapter \<open>Abstract Linear Programs and Solution Spaces\<close>
type_synonym weights = \<open>nat \<Rightarrow> real\<close>

locale Constr_Consts =
fixes
\<comment> \<open>invariant of constraints\<close>
inv_constr :: \<open>'cs \<Rightarrow> bool\<close> and

\<comment> \<open>ability to union constraints\<close>
union_constr :: \<open>'cs \<Rightarrow> 'cs \<Rightarrow> 'cs\<close> and

\<comment> \<open>private variables\<close>
privates :: \<open>'cs \<Rightarrow> 'p set\<close> and

\<comment> \<open>empty constraints\<close>
empty_constr :: \<open>'cs\<close> and

\<comment> \<open>set of values that satisfy constraints\<close>
constr_set :: \<open>'cs \<Rightarrow> (real \<times> weights) set\<close>
begin

text \<open>As long as the private variables are disjoint, the union of two constraints works as expected.\<close>
definition \<open>union_spec \<longleftrightarrow> 
  (\<forall>cs cs' x. inv_constr cs \<longrightarrow> inv_constr cs' \<longrightarrow> disjnt (privates cs) (privates cs') \<longrightarrow> 
    (inv_constr (union_constr cs cs') \<and> 
      privates (union_constr cs cs') = privates cs \<union> privates cs' \<and>
      (x \<in> constr_set (union_constr cs cs') \<longleftrightarrow> 
      x \<in> constr_set cs \<and> x \<in> constr_set cs')))\<close>
lemmas refl[of union_spec, cong]

context
  fixes cs cs'
  assumes h: union_spec \<open>inv_constr cs\<close> \<open>inv_constr cs'\<close> \<open>disjnt (privates cs) (privates cs')\<close>
begin

lemma privates_union_constr[simp]: \<open>privates (union_constr cs cs') = privates cs \<union> privates cs'\<close>
  using h union_spec_def
  by auto

lemma inv_union_constr[simp, intro]: \<open>inv_constr (union_constr cs cs')\<close>
  using h union_spec_def 
  by auto

lemma set_union_constr[simp]: \<open>constr_set (union_constr cs cs') = constr_set cs \<inter> constr_set cs'\<close>
  using h union_spec_def
  by auto
end

definition \<open>empty_constr_spec \<longleftrightarrow>
  inv_constr empty_constr \<and>
  privates empty_constr = {} \<and>
  constr_set empty_constr = UNIV\<close>

context
  assumes h: empty_constr_spec
begin

lemma privates_empty_constr[simp]: \<open>privates empty_constr = {}\<close>
  using h empty_constr_spec_def
  by auto

lemma inv_empty_constr[simp, intro]: \<open>inv_constr empty_constr\<close>
  using h empty_constr_spec_def
  by auto

lemma set_empty_constr[simp]: \<open>constr_set empty_constr = UNIV\<close>
  using h empty_constr_spec_def
  by auto
end

definition \<open>is_arg_min' cs = (\<lambda>(\<phi>, w). (\<phi>,w) \<in> constr_set cs \<and> (\<forall>\<phi>' w'. (\<phi>', w') \<in> constr_set cs \<longrightarrow> \<phi> \<le> \<phi>'))\<close>

context
  fixes cs min_sol
  assumes h: \<open>inv_constr cs\<close> \<open>is_arg_min' cs min_sol\<close>
begin

lemma minimize_in_constr:
  \<open>min_sol \<in> constr_set cs\<close>
  using is_arg_min'_def h by auto

lemma fst_minimize_le:
  assumes \<open>\<phi>w \<in>constr_set cs\<close>
  shows \<open>fst (min_sol) \<le> fst \<phi>w\<close>
  using h assms
  unfolding is_arg_min'_def
  by (metis (mono_tags, lifting) prod.split_sel)

lemma fst_minimize_le':
  assumes \<open>(\<phi>', snd min_sol) \<in> constr_set cs\<close>
  shows \<open>fst (min_sol) \<le> \<phi>'\<close>
  using fst_minimize_le assms by auto
end
end

locale Constr_API = 
  Constr_Consts +
  assumes
    union_spec: union_spec and
    empty_constr_spec: empty_constr_spec
begin

lemma set_empty_constr[simp]: \<open>constr_set empty_constr = UNIV\<close>
  using empty_constr_spec unfolding empty_constr_spec_def
  by auto

lemma inv_empty_constr[simp, intro]: \<open>inv_constr empty_constr\<close>
  using empty_constr_spec unfolding empty_constr_spec_def
  by auto

definition \<open>disj_priv c1 c2 = disjnt (privates c1) (privates c2)\<close>

lemma privs_constr_union[simp]: 
  \<open>inv_constr cs \<Longrightarrow> inv_constr cs' \<Longrightarrow> disj_priv cs cs' \<Longrightarrow>
  privates (union_constr cs cs') = privates cs \<union> privates cs'\<close>
  using union_spec unfolding union_spec_def disj_priv_def
  by auto

lemma inv_constr_union[intro!]: \<open>
  inv_constr cs \<Longrightarrow> 
  inv_constr cs' \<Longrightarrow> 
  disj_priv cs cs' \<Longrightarrow> 
  inv_constr (union_constr cs cs')\<close>
  using union_spec unfolding union_spec_def disj_priv_def
  by auto

lemma union_constr_set[simp]: 
  \<open>inv_constr cs \<Longrightarrow> 
  inv_constr cs' \<Longrightarrow> 
  disj_priv cs cs' \<Longrightarrow> 
  constr_set (union_constr cs cs') = (constr_set cs \<inter> constr_set cs')\<close>
  using union_spec_def union_spec unfolding disj_priv_def by auto
end
end