theory Variable_Elim_Code
  imports 
    Code_Setup 
    "collections/Scoped_Fn_Rel" 
    "../algorithm/Variable_Elim"
begin

section \<open>Util\<close>

instance ereal:: monoid_add
  by standard

definition \<open>unzip xs = (map fst xs, map snd xs)\<close>

fun max_list_aux where
\<open>max_list_aux f m [] = m\<close> | 
\<open>max_list_aux f m (x#xs) = max_list_aux f (max (f x) m) xs\<close>

fun max_list where
\<open>max_list f [] = undefined\<close> |
\<open>max_list f (x#xs) = max_list_aux f (f x) xs\<close>

lemma max_list_aux_cong: \<open>(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> max_list_aux f acc xs = max_list_aux g acc xs\<close>
  by (induction xs arbitrary: acc) auto

lemma max_list_cong: \<open>(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> max_list f xs = max_list g xs\<close>
  by (induction xs) (auto intro: max_list_aux_cong)

lemma max_list_eq_Max[simp]:
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>max_list f xs = Max (f ` set xs)\<close>
proof -
  have *: \<open>max_list_aux f x xs = Max (insert x (f ` set xs))\<close> for x xs
  proof (induction xs arbitrary: x)
    case (Cons a xs)
    then show ?case
      by (cases xs) (auto simp: max.commute, metis max.assoc max.commute)
  qed auto
  show ?thesis 
    using assms *[of \<open>f (hd xs)\<close> \<open>tl xs\<close>]
    by (cases xs) auto
qed

section \<open>Variable Elimination Code Equations\<close>
datatype ('v, 'y, 's) max_fn = 
    Max_Fn nat \<open>('v, 'y, 's) max_fn list\<close> (scope_max: \<open>'s\<close>)
    | Max_Base \<open>'v \<Rightarrow> 'y\<close> (scope_max: 's)

locale Variable_Elim_Code_Consts =
  SE: ScopedFn ops vec_ops set_ops dims doms +
  Set: StdOSet pmf_set_ops for
  ops :: \<open>('f, 'v, ereal, 'nat_set, 'more_scoped) scoped_fn_basic_ops_scheme\<close>
  and vec_ops :: \<open>('v, nat, 'nat_set) vec_ops\<close>
  and set_ops :: \<open>(nat, 'nat_set) oset_ops\<close>
  and pmf_set_ops :: \<open>(nat, 'pmf_set) oset_ops\<close>
  and dims doms
 +
  fixes
    dims_code :: nat and
    doms_code :: \<open>nat \<Rightarrow> nat\<close> and
    \<F>_code :: \<open>'f list\<close> and
    \<O>_code :: \<open>nat list\<close>
begin

definition \<open>elim_step_code iF = (
  let
    (i, F) = iF;
    l = \<O>_code ! i;
    (E, E') = partition (\<lambda>sf. SE.Scope.memb l (SE.scope sf)) F;
    E_s = map SE.scope E;
    ds = [0..<doms_code l];
    e = (\<lambda>x. max_list (\<lambda>x\<^sub>l. \<Sum>f \<leftarrow> E. (SE.scoped_\<alpha> f (SE.Vec.update x l x\<^sub>l))) ds);
    scope_e = SE.Scope.delete l (SE.Scope.Union_sets E_s);
    e_fn = SE.scoped_eval (SE.from_fn scope_e e)
  in
    (i + 1, e_fn # E')
  )\<close>

lemma fst_elim_step_code[simp]: \<open>fst (elim_step_code p) = fst p + 1\<close>
  unfolding elim_step_code_def Let_def case_prod_unfold
  by simp

definition \<open>elim_aux_code = (elim_step_code ^^ dims_code) (0, \<F>_code)\<close>
lemmas refl[of elim_aux_code, cong]
definition \<open>elim_max_code = (\<Sum>f \<leftarrow> snd elim_aux_code. SE.scoped_\<alpha> f (SE.Vec.empty))\<close>
lemmas refl[of elim_max_code, cong]
end

locale Variable_Elim_Code = 
  Variable_Elim_Code_Consts se_ops vec_ops set_ops pmf_set_ops dims doms +
  ScopedFn se_ops vec_ops set_ops dims doms +
  StdOSet pmf_set_ops
  for se_ops vec_ops set_ops pmf_set_ops dims doms

locale Variable_Elim_Code_Transfer =
  States_Code_Transfer
  dims
  doms
  doms_code
  dims_code +
  Variable_Elim_Code 
  where se_ops = se_ops +
  Variable_Elimination
    where \<F> = \<F>
for 
    se_ops :: \<open>('f, 'v, ereal, 'nat_set, 'more_sr_ops) scoped_fn_basic_ops_scheme\<close> and
    \<F> :: \<open>(((nat \<Rightarrow> nat option) \<Rightarrow> ereal) \<times> nat set) list\<close>
begin

interpretation States_Code_Transfer
  dims
  doms
  doms_code
  dims_code
  .

definition \<open>\<F>'_rel f_code f = list_all2 (SE.scoped_fn_state_rel (=)) f_code f\<close>

definition \<open>\<F>_rel \<longleftrightarrow>
  list_all2 (SE.scoped_fn_state_rel (=)) \<F>_code \<F>\<close>

definition \<open>\<O>_rel \<longleftrightarrow> rel_fun (and_rel (=) (\<lambda>x y. y < dims)) (=) ((!) \<O>_code) \<O>\<close>

lemmas \<O>_rel_def[iff]

lemma \<O>_le_dims[intro!, simp]: \<open>i < dims \<Longrightarrow> \<O> i < dims\<close>
  using bij_betwE[OF \<O>_bij] by auto

context
  assumes \<open>\<O>_rel\<close> \<open>doms_rel\<close> \<open>\<F>_rel\<close> \<open>dims_rel\<close>
begin

lemma dims_eq_n[intro, simp]: \<open>dims_code = dims\<close>
  using \<open>dims_rel\<close> unfolding dims_rel_def by auto

lemma \<O>_code_eq[simp]: \<open>i < dims \<Longrightarrow> \<O>_code ! i = \<O> i\<close>
  using \<open>\<O>_rel\<close> by auto

lemma valid_input_fn_alt:
  assumes \<open>\<And>v v'. 
  SE.Vec.invar v \<Longrightarrow> SE.Vec.invar v' \<Longrightarrow> 
  SE.Scope.\<alpha> s \<subseteq> dom (SE.Vec.\<alpha> v) \<Longrightarrow> SE.Scope.\<alpha> s \<subseteq> dom (SE.Vec.\<alpha> v') \<Longrightarrow> 
  SE.Vec.\<alpha> v |` SE.Scope.\<alpha> s = SE.Vec.\<alpha> v' |` SE.Scope.\<alpha> s \<Longrightarrow>
  f v = f v'\<close>
  \<open>SE.Scope.invar s\<close>
shows \<open>SE.valid_input_fn s f\<close>
  unfolding SE.valid_input_fn_def
  using assms
  by blast

lemma doms_code_upt[simp]: \<open>i < dims \<Longrightarrow> {..< doms_code i} = doms i\<close>
  using \<open>doms_rel\<close> 
  unfolding doms_rel_def 
  by auto

lemma doms_code_card[simp]: \<open>i < dims \<Longrightarrow> doms_code i = card (doms i)\<close>
  by (metis card_lessThan doms_code_upt)

lemma card_doms_doms[simp]: \<open>j < dims \<Longrightarrow> {..<card(doms j)} = doms j\<close>
  using doms_code_card doms_code_upt 
  by presburger

lemma le_card_in_doms[simp, intro]: \<open>j < dims \<Longrightarrow> i < card (doms j) \<Longrightarrow> i \<in> doms j\<close>
  using card_doms_doms 
  by blast

lemma map_upd_eqI: \<open>m |` (-{k}) = m' |` (-{k}) \<Longrightarrow> m(k \<mapsto> v) = m'(k \<mapsto> v)\<close>
  by fastforce

lemma map_upd_notdom_eqI: \<open>m = m' \<Longrightarrow> k \<notin> dom m \<Longrightarrow> m(k \<mapsto> v) = m'(k \<mapsto> v)\<close>
  by fastforce


lemma \<F>'_rel_snd_elim_step:
  assumes \<open>\<F>'_rel f_code f\<close> \<open>i < dims\<close>
  shows \<open>\<F>'_rel (snd (elim_step_code (i, f_code))) (snd (elim_step (i, f)))\<close>
proof -
  have len_f_eq[simp]: \<open>length f_code = length f\<close>
    using assms 
    unfolding \<F>'_rel_def 
    by auto

  have f_code_rel: \<open>SE.scoped_fn_state_rel (=) (f_code ! j) (f ! j)\<close> if \<open>j < length f\<close> for j
    using assms that 
    unfolding \<F>'_rel_def 
    by auto

  hence invar_f_code: \<open>SE.invar ((f_code ! j))\<close> if \<open>j < length f\<close> for j
    using assms that 
    by auto

  hence invar_f_code': \<open>SE.invar (f_elem)\<close> if \<open>f_elem \<in> set f_code\<close> for f_elem
    using assms that
    by (metis all_nth_imp_all_set len_f_eq)

  have list_rel_notin: \<open>(\<O> i) \<in> SE.scoped_scope_\<alpha> (f_code ! i) \<longleftrightarrow> (\<O> i) \<in> snd (f ! i)\<close>
    if \<open>i < length f\<close> for i
    using f_code_rel that 
    by fastforce

  
  have list_rel_notin: \<open>\<F>'_rel (filter (\<lambda>x. (\<O> i) \<notin> SE.scoped_scope_\<alpha> x) f_code) (filter (\<lambda>x. (\<O> i) \<notin> snd x) f)\<close>
    using assms 
    unfolding \<F>'_rel_def 
    by (auto intro!: list_rel_filterI)

  define l where \<open>l = \<O> i\<close>
  define E_code where \<open>E_code = fst (partition (\<lambda>sf. SE.Scope.memb ((\<O>_code ! i)) (SE.scope sf)) f_code)\<close>
  define E where \<open>E = filter (\<lambda>f. l \<in> snd f) f\<close>

  have E_rel: \<open>\<F>'_rel E_code E\<close>
    using assms
    unfolding E_code_def E_def \<F>'_rel_def l_def
    by (auto intro!: list_rel_filterI)

  define E'_code where \<open>E'_code = snd (partition (\<lambda>sf. SE.Scope.memb ((\<O>_code ! i)) (SE.scope sf)) f_code)\<close>
  define E' where \<open>E' = filter (\<lambda>f. l \<notin> snd f) f\<close>

  have E'_rel: \<open>\<F>'_rel E'_code E'\<close>
    using assms 
    unfolding E'_code_def E'_def \<F>'_rel_def l_def
    by (auto intro!: list_rel_filterI)

  define E_s_code where \<open>E_s_code = map SE.scope E_code\<close>
  define ds_code where \<open>ds_code = [0..<(doms_code l)]\<close>

  define e_code where \<open>e_code = (\<lambda>x. max_list (\<lambda>x\<^sub>l. \<Sum>f \<leftarrow> E_code. (SE.scoped_\<alpha> f (SE.Vec.update x l x\<^sub>l))) ds_code)\<close>
  define e where \<open>e = (\<lambda>x. MAX x\<^sub>l\<in>doms l. \<Sum>f\<leftarrow>E. fst f (x(l \<mapsto> x\<^sub>l)))\<close>

  define scope_e_code where \<open>scope_e_code = SE.Scope.delete l (SE.Scope.Union_sets E_s_code)\<close>
  define scope_e where \<open>scope_e = \<Union> (snd ` set E) - {l}\<close>

  have invar_f_code[simp]: \<open>f' \<in> set f_code \<Longrightarrow> SE.invar f'\<close> for f'
    using assms 
    by (metis \<F>'_rel_def in_set_conv_nth list_all2_conv_all_nth SE.scoped_fn_state_rel_invarD)

  hence invar_Es[simp]: \<open>f' \<in> set E_code \<Longrightarrow> SE.invar f'\<close> \<open>f' \<in> set E'_code \<Longrightarrow> SE.invar f'\<close> for f'
    using assms 
    unfolding E_code_def E'_code_def
    by auto

  have E_rel': \<open>SE.scoped_fn_state_rel (=) (E_code ! i) (E ! i)\<close> if \<open>i < length E\<close> for i
    using that 
    by (meson E_rel \<F>'_rel_def list_all2_nthD2)

  have E'_rel': \<open>SE.scoped_fn_state_rel (=) (E'_code ! i) (E' ! i)\<close> if \<open>i < length E'\<close> for i
    using that 
    by (meson E'_rel \<F>'_rel_def list_all2_nthD2)

  have \<open>SE.scoped_scope_\<alpha> (f_code ! i) = snd (f ! i)\<close> if \<open>i < length f\<close>
    using that f_code_rel SE.scoped_fn_state_rel_scope_eq
    by blast

  have invar_scope_e: \<open>SE.Scope.invar scope_e_code\<close>
    unfolding scope_e_code_def E_s_code_def
    by auto

  have invar_E_code[dest, simp]: \<open>x \<in> set E_code \<Longrightarrow> SE.invar x\<close> for x
    by auto

  hence scope_invar_E_code: \<open>x \<in> SE.scope ` set E_code \<Longrightarrow> SE.Scope.invar x\<close> for x
    by auto

  have E_scope_facts: 
    \<open>SE.scoped_scope_\<alpha> (E_code ! i) = snd (E ! i)\<close> \<open>SE.invar (E_code ! i)\<close> if \<open>i < length E\<close> for i
    using that E_rel' SE.scoped_fn_state_rel_scope_eq 
    by fastforce+

  have len_E[simp]: \<open>length E_code = length E\<close>
    using E_rel \<F>'_rel_def 
    by auto

  have E_scope_eq': \<open>SE.scope_\<alpha> (E_code ! i) = snd (E ! i)\<close> if \<open>i < length E\<close> for i
    using that E_scope_facts[of i]
    by auto


  hence E_s_scope_eq': \<open>SE.Scope.\<alpha> (E_s_code ! i) = snd (E ! i)\<close> if \<open>i < length E\<close> for i
    using that E_scope_facts[of i]
    using E_s_code_def by force


  have invar_union_E_s[simp, intro]: \<open>SE.Scope.invar (SE.Scope.Union_sets E_s_code)\<close>
    unfolding E_s_code_def 
    by auto

  have invar_E_s: \<open>X \<in> set E_s_code \<Longrightarrow> SE.Scope.invar X\<close> for X
    unfolding E_s_code_def
    by auto

  have len_E_s_code[simp]: \<open>length E_s_code = length E\<close>
    unfolding E_s_code_def 
    by auto
    
  have \<open>(SE.Scope.\<alpha> ` set E_s_code) = snd ` set E\<close>
    unfolding E_s_code_def image_image set_map
    using E_scope_facts
    by (fastforce simp: image_iff in_set_conv_nth)    

  hence Union_E_s[simp]: \<open>SE.Scope.\<alpha> (SE.Scope.Union_sets E_s_code) = \<Union>(snd ` set E)\<close>
    using invar_E_s
    by auto

  have scope_e_code[simp]: \<open>SE.Scope.\<alpha> scope_e_code = scope_e\<close>
    unfolding scope_e_code_def scope_e_def
    by simp

  have \<open>SE.Scope.set_rel scope_e_code scope_e\<close>
    using invar_scope_e 
    by auto

  define e_fn_code where \<open>e_fn_code = SE.scoped_eval (SE.from_fn scope_e_code e_code)\<close>
  define e_fn where \<open>e_fn = (e, scope_e)\<close>

  have scope_in_E: \<open>g \<in> set E_code \<Longrightarrow> SE.scoped_scope_\<alpha> g \<subseteq> insert l scope_e\<close> for g
    unfolding scope_e_def
    by (force simp: in_set_conv_nth E_rel'[THEN SE.scoped_fn_state_rel_scope_eq])

  have [simp]: \<open>l < dims\<close>
    unfolding l_def
    using assms
    by auto

  have set_ds_code[simp]: \<open>set ds_code = doms l\<close>
    unfolding ds_code_def
    using \<open>l < dims\<close> atLeast_upt doms_code_upt by presburger


  have [simp]: \<open>SE.valid_input_fn scope_e_code e_code\<close>
  proof (rule valid_input_fn_alt, goal_cases)
    case (1 v v')
    then show ?case
      unfolding e_code_def
      by (intro max_list_cong sum_list_map_cong SE.scoped_\<alpha>) 
        (auto dest: scope_in_E[THEN subsetD] intro!: map_upd_notdom_eqI iff del: domIff)
  qed (auto simp: scope_e_code_def)

  have e_fn_invar[simp]: \<open>SE.invar e_fn_code\<close>
    unfolding e_fn_code_def by auto

  have invar_e_code[simp, intro]: \<open>SE.invar (SE.from_fn scope_e_code e_code)\<close>
    by auto

  have e_fn_code_set_rel: \<open>SE.Scope.set_rel (SE.scope e_fn_code) (snd e_fn)\<close>
    unfolding e_fn_code_def e_fn_def by auto

  have e_fn_code_set_eq[simp]: \<open>SE.scoped_scope_\<alpha> (e_fn_code) = scope_e\<close>
    unfolding e_fn_code_def e_fn_def by auto

  have \<open>ds_code \<noteq> []\<close>
    using domains_ne 
    by (auto simp flip: List.set_empty)
    
  note l_def[simp]

    have e_code_rel: \<open>e_code x_code = e x\<close> if \<open>SE.Vec.state_rel x_code x\<close> \<open>scope_e \<subseteq> dom x\<close> for x_code x
      using that
    unfolding e_code_def e_def scope_e_def
    using assms \<open>ds_code \<noteq> []\<close> domains_ne domains_fin
    by (fastforce simp: sum_list_sum_nth intro!: Max_cong sum.cong SE.scoped_fn_state_rel_eq[OF _ E_rel'])

  have e_fn_rel: \<open>SE.scoped_fn_state_rel (=) e_fn_code e_fn\<close>
      unfolding e_fn_code_def e_fn_def
    using e_fn_code_set_rel e_code_rel
      by (auto intro!: SE.scoped_fn_state_relI)

  have snd_code_eq: \<open>snd (elim_step_code (i, f_code)) = e_fn_code # E'_code\<close>
    unfolding elim_step_code_def Let_def e_fn_code_def scope_e_code_def E_s_code_def E_code_def 
      e_code_def ds_code_def  E'_code_def
    using assms
    by auto

  have snd_eq: \<open>snd (elim_step (i, f)) = e_fn # E'\<close>
    unfolding elim_step_def case_prod_unfold Let_def e_fn_def scope_e_def l_def E_def e_def  E'_def
    using assms
    by simp

  show \<open>\<F>'_rel (snd (elim_step_code (i, f_code))) (snd (elim_step (i, f)))\<close>
    unfolding snd_code_eq snd_eq 
    using e_fn_rel E'_rel \<F>'_rel_def by auto
qed

lemma pair_\<F>'_rel_elim_step:
  assumes \<open>rel_prod (=) \<F>'_rel cfg_code cfg\<close> \<open>fst cfg < dims\<close>
  shows \<open>rel_prod (=) \<F>'_rel (elim_step_code cfg_code) (elim_step cfg)\<close>
  using assms \<F>'_rel_snd_elim_step
  unfolding elim_step_code_def elim_step_def
  by (auto simp: Let_def case_prod_unfold)

lemma \<F>'_rel_init: \<open>\<F>'_rel \<F>_code \<F>\<close>
  using \<open>\<F>_rel\<close>
  unfolding \<F>_rel_def \<F>'_rel_def
  by auto

lemma fst_elim_aux_code_n[simp]: \<open>fst elim_aux_code = dims\<close>
  unfolding elim_aux_code_def 
  unfolding dims_eq_n
  by (induction dims) auto

lemma pair_\<F>'_rel_pow:
  assumes \<open>i + fst \<F>' \<le> dims\<close> \<open>rel_prod (=) \<F>'_rel \<F>_code' \<F>'\<close>
  shows \<open>rel_prod (=) \<F>'_rel ((elim_step_code ^^ i) \<F>_code')  ((elim_step ^^ i) \<F>')\<close>
  using assms pair_\<F>'_rel_elim_step
  by (induction i) (auto simp: fst_elim_step_pow)

lemma pair_\<F>'_rel_elim_aux: \<open>rel_prod (=) \<F>'_rel elim_aux_code elim_aux\<close> 
  unfolding elim_aux_code_def elim_aux_def 
  unfolding dims_eq_n
  using \<F>'_rel_init
  by (auto intro!: pair_\<F>'_rel_pow)

lemma elim_max_eq: \<open>elim_max_code = elim_max\<close>
  using pair_\<F>'_rel_elim_aux 
  unfolding \<F>'_rel_def elim_max_code_def elim_max_def sum_list_sum_nth
  by (auto intro!: sum.cong SE.scoped_fn_state_rel_eq simp: scope_elim_aux_empty' case_prod_unfold)
end
end
end
