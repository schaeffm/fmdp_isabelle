theory Vec_Inst
  imports 
    Vec_Code 
    "HOL-Library.IArray"
begin

locale Vec_Inst =
  S: NatSet set_ops 
  for set_ops +
  fixes
    dims :: nat and
    doms :: \<open>nat \<Rightarrow> nat\<close>
begin

definition [icf_rec_def]:  \<open>vec_ops = \<lparr>
  vec_op_\<alpha> = (\<lambda>(v, s) i. if S.memb i s then Some (IArray.sub v i) else None),
  vec_op_scope = snd,
  vec_op_idx = (\<lambda>(v, s) i. (IArray.sub v i)),
  vec_op_invar = (\<lambda>(v, s). IArray.length v = dims \<and> S.invar s \<and> S.ball s (\<lambda>i. i < dims) \<and> S.ball s (\<lambda>i. IArray.sub v i < doms i)),
  vec_op_empty = (IArray.of_fun (\<lambda>_. 0) dims, S.empty ()),
  vec_op_update = (\<lambda>(v, s) i y. (IArray (list_update (IArray.list_of v) i (y)), S.ins i s)),
  vec_op_restr = (\<lambda>(v, s) s'. (v, S.inter s s'))
\<rparr>\<close>

sublocale Vec
  where
    vec_ops = vec_ops and
    set_ops = set_ops and
    doms = \<open>(\<lambda>i. {..<doms i})\<close> and dims = dims
  unfolding vec_ops_def
  by unfold_locales (auto simp: restrict_map_def nth_list_update' split: if_splits)+
end
end