(* uses Isabelle2017 and autocorres version 1.0 *)
theory myGraph
  imports 
  "checker-verification/Library/Autocorres_Misc"
  "checker-verification/Witness_Property/Connected_Components"
begin
(* Parse the input file. *)
install_C_file "Graph_copy.c"

autocorres "Graph_copy.c"

context Graph_copy begin

thm "is_wellformed_body_def"
thm "trian_body_def"
thm "just_body_def"
thm "no_path_body_def"
thm "pos_cost_body_def"
thm "check_basic_just_sp_body_def"
thm "check_sp_body_def"

thm "is_wellformed'_def"
thm "trian'_def"
thm "just'_def"
thm "no_path'_def"
thm "pos_cost'_def"
thm "check_basic_just_sp'_def"
thm "check_sp'_def"

(*Implementation Graph Types*)

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> 32 word"
type_synonym INum = "IVertex \<Rightarrow> 32 word"
type_synonym IDist = "IVertex \<Rightarrow> 32 word"
type_synonym ICost = "IVertex \<Rightarrow> 32 word"
type_synonym IGraph = "32 word \<times> 32 word \<times> (IEdge_Id \<Rightarrow> IEdge)"

abbreviation 
  ivertex_cnt :: "IGraph \<Rightarrow> 32 word"
where 
  "ivertex_cnt G \<equiv> fst G"

abbreviation 
  iedge_cnt :: "IGraph \<Rightarrow> 32 word"
where 
  "iedge_cnt G \<equiv> fst (snd G)"

abbreviation 
  iedges :: "IGraph \<Rightarrow> IEdge_Id \<Rightarrow> IEdge"
where 
  "iedges G \<equiv> snd (snd G)"

(* Make List - makes a list containing the result of a function *)
fun 
  bool::"32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

fun 
  mk_list' :: "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> 'b list" 
where 
  "mk_list' n f = map f  (map of_nat [0..<n])"

fun 
  mk_list'_temp :: "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b list" 
where 
  "mk_list'_temp 0 _ _ = []" |
  "mk_list'_temp (Suc x) f i = (f (of_nat i)) # mk_list'_temp x f (Suc i)"

(* Make graph lists *)
fun
  mk_iedge_list :: "IGraph \<Rightarrow> IEdge list"
where 
  "mk_iedge_list G = mk_list' (unat (iedge_cnt G)) (iedges G)"

fun 
  mk_inum_list :: "IGraph \<Rightarrow> INum \<Rightarrow> 32 word list"
where 
  "mk_inum_list G num = mk_list' (unat (ivertex_cnt G)) num"
  
fun 
  mk_ipedge_list :: "IGraph \<Rightarrow> IPEdge \<Rightarrow> 32 word list"
where
  "mk_ipedge_list G pedge = mk_list' (unat (ivertex_cnt G)) pedge"

fun
  mk_idist_list :: "IGraph \<Rightarrow> IDist \<Rightarrow> 32 word list"
where
  "mk_idist_list G dis = mk_list' (unat (ivertex_cnt G)) dis"

fun
  mk_icost_list :: "IGraph \<Rightarrow> ICost \<Rightarrow> 32 word list"
where
  "mk_icost_list G cost = mk_list' (unat (iedge_cnt G)) cost"

(* Equate to Implementation *)

lemma sint_ucast: 
  "sint (ucast (x ::word32) :: sword32) = sint x"
  by (clarsimp simp: sint_uint uint_up_ucast is_up)

fun
  to_edge :: "IEdge \<Rightarrow> IEdge_C"
where
  "to_edge (u,v) = IEdge_C u v"

lemma s_C_pte[simp]:
  "first_C (to_edge e) = fst e"
  by (cases e) auto

lemma t_C_pte[simp]:
  "second_C (to_edge e) = snd e"
  by (cases e) auto

definition is_graph where
  "is_graph h iG p \<equiv>
    is_valid_IGraph_C h p \<and> 
    ivertex_cnt iG = num_vertices_C (heap_IGraph_C h p) \<and> 
    iedge_cnt iG = num_edges_C (heap_IGraph_C h p) \<and>
    arrlist (heap_IEdge_C h) (is_valid_IEdge_C h)
      (map to_edge (mk_iedge_list iG)) (arcs_C (heap_IGraph_C h p))"

definition 
  "is_numm h iG iN (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_inum_list iG iN) p"

definition
  "is_pedge h iG iP (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_ipedge_list iG iP) p"

definition
  "is_dist h iG iD (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_idist_list iG iD) p"

definition 
  "is_cost h iG iC p \<equiv> arrlist (heap_w32 h) (is_valid_w32 h) (mk_icost_list iG iC) p"

(* Abstract Graph *)

definition 
  no_loops :: "('a, 'b) pre_digraph \<Rightarrow> bool" 
where
  "no_loops G \<equiv> \<forall>e \<in> arcs G. tail G e \<noteq> head G e"

definition 
  abs_IGraph :: "IGraph \<Rightarrow> (32 word, 32 word) pre_digraph" 
where
  "abs_IGraph G \<equiv> \<lparr> verts = {0..<ivertex_cnt G}, arcs = {0..<iedge_cnt G},
    tail = fst o iedges G, head = snd o iedges G \<rparr>"

lemma verts_absI[simp]: "verts (abs_IGraph G) = {0..<ivertex_cnt G}"
  and edges_absI[simp]: "arcs (abs_IGraph G) = {0..<iedge_cnt G}"
  and start_absI[simp]: "tail (abs_IGraph G) e = fst (iedges G e)"
  and target_absI[simp]: "head (abs_IGraph G) e = snd (iedges G e)"
  by (auto simp: abs_IGraph_def)

definition 
  abs_pedge :: "(32 word \<Rightarrow> 32 word) \<Rightarrow> 32 word \<Rightarrow> 32 word option" 
where
  "abs_pedge p \<equiv> (\<lambda>v. if sint (p v) < 0 then None else Some (p v))"

lemma None_abs_pedgeI[simp]: 
  "((abs_pedge p) v = None) = (sint (p v) < 0)"
  using abs_pedge_def by auto

lemma Some_abs_pedgeI[simp]: 
  "(\<exists>e. (abs_pedge p) v = Some e) = (sint (p v) \<ge> 0)"
  using None_not_eq None_abs_pedgeI 
  by (metis abs_pedge_def linorder_not_le option.simps(3))
    
(*Helper Lemmas*)

lemma wellformed_iGraph:
  assumes "wf_digraph (abs_IGraph G)"
  shows "\<And>e. e < iedge_cnt G \<Longrightarrow> 
        fst (iedges G e) < ivertex_cnt G \<and> 
        snd (iedges G e) < ivertex_cnt G" 
  using assms unfolding wf_digraph_def by simp

lemma unat_image_upto:
  fixes n :: "32 word"
  shows "unat ` {0..<n} = {unat 0..<unat n}" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"  
  proof 
    fix i assume a: "i \<in> ?B"
    then obtain i':: "32 word" where ii: "i=  unat i'"
      by (metis atLeastLessThan_iff le_unat_uoi less_or_eq_imp_le)
    then have "i' \<in> {0..<n}" 
      using a word_less_nat_alt by auto
    thus  "i \<in> ?A" using ii by fast
  qed
next
  show "?A \<subseteq> ?B"
  proof
     fix i assume a: "i \<in> ?A"
    then obtain i':: "32 word" where ii: "i=  unat i'" by blast
    then have "i' \<in> {0..<n}" using a by force
    thus  "i \<in> ?B"   
      by (metis Un_iff atLeast0LessThan ii ivl_disj_un(8) 
          lessThan_iff unat_0 unat_mono word_zero_le)
  qed
qed

lemma path_length:
  assumes "vpath p (abs_IGraph iG)"
  shows "vwalk_length p < unat (ivertex_cnt iG)" 
proof -
  have pne: "p \<noteq> []" and dp: "distinct p" using assms by fast+
  have "unat (ivertex_cnt iG) = card (unat ` {0..<(fst iG)})"  
    using unat_image_upto by simp
  then have "unat (ivertex_cnt iG) = card ((verts (abs_IGraph iG)))"  
     by (simp add: inj_on_def card_image)
  hence "length p  \<le> unat (ivertex_cnt iG)" 
      by (metis finite_code card_mono vwalk_def
          distinct_card[OF dp] vpath_def assms)
  hence "length p - 1 < unat (ivertex_cnt iG)" 
    by (metis pne Nat.diff_le_self le_neq_implies_less 
        less_imp_diff_less minus_eq one_neq_zero length_0_conv)
  thus "vwalk_length p < unat (fst iG)"
    using  assms 
    unfolding vpath_def vwalk_def by simp
qed

lemma ptr_coerce_ptr_add_uint[simp]:
  "ptr_coerce (p +\<^sub>p uint x) =  p +\<^sub>p  (uint x)"
  by auto

lemma pedge_num_dist_heap:
  "\<lbrakk>arrlist (\<lambda>p. heap_w32 h p) (\<lambda>p. is_valid_w32 h p) 
  (map (iL \<circ> of_nat) [0..<unat n]) l; i < n\<rbrakk> \<Longrightarrow>
    iL i = heap_w32 h (l +\<^sub>p int (unat i))" 
  apply (subgoal_tac 
  "heap_w32 h (l +\<^sub>p int (unat i)) = map (iL \<circ> of_nat) [0..<unat n] ! unat i") 
   apply (subgoal_tac "map (iL \<circ> of_nat) [0..<unat n] ! unat i = iL i") 
    apply fastforce
   apply (metis (hide_lams, mono_tags) unat_mono word_unat.Rep_inverse 
    minus_nat.diff_0 nth_map_upt o_apply plus_nat.add_0)
  apply (simp add: arrlist_nth_value unat_mono)
  done

lemma pedge_num_dist_heap_ptr_coerce:
  "\<lbrakk>arrlist (\<lambda>p. heap_w32 h (ptr_coerce p)) (\<lambda>p. is_valid_w32 h (ptr_coerce p)) 
  (map (iL \<circ> of_nat) [0..<unat n]) l; i < n; 0 \<le> i\<rbrakk> \<Longrightarrow>
    iL i = heap_w32 h (ptr_coerce (l +\<^sub>p int (unat i)))" 
  apply (subgoal_tac 
  "heap_w32 h (ptr_coerce (l +\<^sub>p int (unat i))) = map (iL \<circ> of_nat) [0..<unat n] ! unat i") 
   apply (subgoal_tac "map (iL \<circ> of_nat) [0..<unat n] ! unat i = iL i") 
    apply fastforce
   apply (metis (hide_lams, mono_tags) unat_mono word_unat.Rep_inverse 
    minus_nat.diff_0 nth_map_upt o_apply plus_nat.add_0)
  apply (drule arrlist_nth_value[where i="int (unat i)"], (simp add:unat_mono)+)
  done

lemma edge_heap:
  "\<lbrakk> arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep;
  e < m\<rbrakk> \<Longrightarrow> to_edge ((iedges iG) e) = h (ep +\<^sub>p (int (unat e)))" 
  apply (subgoal_tac "h (ep +\<^sub>p (int (unat e))) = 
  (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ! unat e")
   apply (subgoal_tac "to_edge ((iedges iG) e) = 
   (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ! unat e")
    apply presburger 
   apply (metis (hide_lams, mono_tags) length_map length_upt o_apply
      map_upt_eq_vals_D minus_nat.diff_0 unat_mono word_unat.Rep_inverse)
  apply (fastforce simp: unat_mono arrlist_nth_value)
  done


lemma head_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  snd ((iedges iG) e) = second_C (h (ep +\<^sub>p (uint e)))" 
  using edge_heap to_edge.simps t_C_pte by (metis uint_nat)

lemma tail_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  fst ((iedges iG) e) =  first_C (h (ep +\<^sub>p  (uint e)))" 
  using edge_heap to_edge.simps s_C_pte uint_nat by metis

thm "is_wellformed'_def"

definition is_wellformed_inv :: "IGraph \<Rightarrow> 32 word \<Rightarrow> bool" where
  "is_wellformed_inv G i \<equiv> \<forall>k < i. ivertex_cnt G > fst (iedges G k)
        \<and> ivertex_cnt G > snd (iedges G k)"

lemma is_wellformed_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g) \<rbrace>
   is_wellformed' g
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> is_wellformed_inv iG (iedge_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: is_wellformed'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(ee, s). unat (iedge_cnt iG - ee)" and
        I="\<lambda>ee s. P s \<and> is_wellformed_inv iG ee \<and> 
                   ee \<le> iedge_cnt iG \<and> 
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g"])
  apply (simp add: skipE_def)
  apply wp
  unfolding is_graph_def is_wellformed_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, safe, simp_all add: arrlist_nth)
         apply (rule_tac x = "ee" in exI)
         apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) \<le> fst (snd (snd iG) ee)")
          apply force
         apply (subgoal_tac "first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint ee)) = fst (snd (snd iG) ee)")
          apply simp
         apply (subst tail_heap[where iG=iG], simp)
          apply blast
         apply blast
        apply(rule_tac x = "ee" in exI)
        apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) \<le> snd (snd (snd iG) ee)")
         apply force
        apply (subgoal_tac "second_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint ee)) = snd (snd (snd iG) ee)")
         apply simp
        apply (subst head_heap[where iG=iG], simp)
         apply blast
        apply blast
       apply (metis edge_heap s_C_pte le_cases le_step uint_nat word_le_less_eq)
      apply (metis head_heap le_step not_less)
     apply (simp add: le_step word_not_le)
  using le_step not_less 
     apply blast
    apply (metis (mono_tags, hide_lams) diff_diff_add diff_self_eq_0 eq_iff_diff_eq_0 measure_unat not_less0 word_less_nat_alt zero_less_diff)
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
  apply wp
  apply fast
  done

definition trian_inv :: "IGraph \<Rightarrow> IDist \<Rightarrow> ICost \<Rightarrow> 32 word \<Rightarrow> bool" where
  "trian_inv G d c m \<equiv> 
    \<forall>i < m. d (snd (iedges G i)) \<le> d (fst (iedges G i)) + c i"

lemma trian_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c)\<rbrace>
   trian' g d c
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> trian_inv iG iD iC (iedge_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: trian'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(ee, s). unat (iedge_cnt iG - ee)" and
        I="\<lambda>ee s. P s \<and> trian_inv iG iD iC ee \<and> 
                   ee \<le> iedge_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and> 
                   is_graph s iG g \<and>
                   is_dist s iG iD d \<and>
                   is_cost s iG iC c"])
  apply (simp add: skipE_def)
  apply wp
  unfolding is_graph_def is_dist_def is_cost_def trian_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, safe, simp_all add: arrlist_nth)
          prefer 9
          apply wp
          apply fast
         prefer 8
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
        prefer 3
  using le_step not_less 
        apply blast
       prefer 3
       apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
      prefer 3
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
      apply (metis tail_heap wellformed_iGraph uint_nat word_less_nat_alt)
     prefer 4
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
     apply (metis head_heap wellformed_iGraph uint_nat word_less_nat_alt)
    prefer 3
    apply (rule_tac i="uint ee" in arrlist_nth_valid, simp+)
    apply (simp add:uint_nat)
  using word_less_nat_alt
    apply blast
   apply (rule_tac x = "ee" in exI)
   apply (rule conjI, simp+)
   apply (subst pedge_num_dist_heap_ptr_coerce[where l=d and iL=iD])
      apply fast
     apply (subst head_heap[where iG=iG], simp+)
     apply (metis head_heap wellformed_iGraph, simp+)
   apply (subst pedge_num_dist_heap_ptr_coerce[where l=d and iL=iD])
      apply fast
     apply (subst tail_heap[where iG=iG], simp+)
     apply (metis tail_heap wellformed_iGraph, simp+)
   apply (drule wellformed_iGraph[where G=iG])
    apply simp+
   apply (subst head_heap[where iG=iG], simp+)
   apply (subst tail_heap[where iG=iG], simp+)
   apply clarsimp
   apply (subgoal_tac "heap_w32 s (ptr_coerce (d +\<^sub>p int (unat (second_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint ee))))))
             > heap_w32 s (ptr_coerce (d +\<^sub>p int (unat (first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint ee)))))) + iC ee")
    apply simp+
   apply (subst pedge_num_dist_heap[where l=c and iL=iC])
     apply simp+
   apply (metis uint_nat)
  
  apply (subst pedge_num_dist_heap_ptr_coerce[where l=d and iL=iD])
     apply fast
    apply (subst head_heap[where iG=iG], simp+)
  using le_step less_trans 
     apply blast
    apply (metis (no_types, hide_lams) head_heap wellformed_iGraph le_step less_trans)
  using word_zero_le 
   apply blast
  apply (subst pedge_num_dist_heap_ptr_coerce[where l=d and iL=iD])
     apply fast
    apply (subst tail_heap[where iG=iG], simp+)
  using le_step less_trans
     apply blast
    apply (metis (no_types, hide_lams) tail_heap wellformed_iGraph le_step less_trans)
   apply simp
  apply (subst pedge_num_dist_heap[where l=c and iL=iC])
    apply (simp add: uint_nat)+
  using le_step less_trans
   apply blast
  apply (subst head_heap[where iG=iG], simp+)
  using le_step less_trans 
   apply blast
  apply (subst tail_heap[where iG=iG], simp+)
  using le_step less_trans 
   apply blast

  apply (simp add: uint_nat unat_mono)+
  apply (frule_tac i="fst (snd (snd iG) i)" in pedge_num_dist_heap_ptr_coerce[where l=d and iL=iD])
    apply (metis (no_types, hide_lams) wellformed_iGraph le_step less_trans)
   apply force
  apply (drule_tac i="snd (snd (snd iG) i)" in pedge_num_dist_heap_ptr_coerce[where l=d and iL=iD])
    apply (metis (no_types, hide_lams) wellformed_iGraph le_step less_trans)
   apply force
  apply (drule_tac i="ee" in pedge_num_dist_heap[where l=c and iL=iC])
   apply simp
  apply (frule_tac e="ee" in tail_heap[where iG=iG])
   apply simp
  apply (drule_tac e="ee" in wellformed_iGraph[where G=iG])
   apply simp+
  apply (drule_tac e="ee" in head_heap[where iG=iG])
   apply simp+
  apply (simp add: uint_nat unat_mono)+

  sorry

definition just_inv :: 
  "IGraph \<Rightarrow> IDist \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> INum \<Rightarrow> IPEdge \<Rightarrow> 32 word \<Rightarrow> bool" where
  "just_inv G d c s n p k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> n v \<ge> 0 \<longrightarrow>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        d v = d (fst (iedges G e)) + c e \<and>
        n v = n (fst (iedges G e)) + 1)"

lemma just_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          sc < ivertex_cnt iG \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   just' g d c sc n p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> just_inv iG iD iC sc iN iP (ivertex_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: just'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(vv, s). unat (ivertex_cnt iG - vv)" and
        I="\<lambda>vv s. P s \<and> just_inv iG iD iC sc iN iP vv \<and>
                   vv \<le> ivertex_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   is_dist s iG iD d \<and>
                   is_cost s iG iC c \<and>
                   sc < ivertex_cnt iG \<and>
                   is_numm s iG iN n \<and>
                   is_pedge s iG iP p"])
  apply (simp add: skipE_def)
  apply wp
  unfolding is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def just_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, simp_all add: arrlist_nth, safe)
                                                       apply (metis pedge_num_dist_heap_ptr_coerce uint_nat word_not_le word_zero_le)
                                                      apply (metis (no_types) head_heap pedge_num_dist_heap_ptr_coerce uint_nat word_zero_le)
                                                     prefer 52
                                                     apply wp
                                                     apply force
                                                    prefer 51
                                                    apply force
                                                   prefer 50
                                                   apply (rule_tac i="(uint sc)" in arrlist_nth_valid, simp+)
                                                   apply (simp add: uint_nat word_less_def)
                                                  prefer 49
                                                  apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
                                                 prefer 48
                                                 apply argo
                                                prefer 47
                                                apply argo
                                               prefer 46
                                               apply argo
                                              prefer 45
                                              apply argo
                                             prefer 44
                                             apply argo
                                            prefer 43
                                            apply (metis (mono_tags, hide_lams) le_step not_less)
                                           prefer 42
  using le_step 
                                           apply blast
                                          prefer 41
  using le_step 
                                          apply blast
                                         prefer 40
  using le_step
                                        apply blast
                                       prefer 39
  using le_step 
                                       apply auto[1]
                                      prefer 38
                                      apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
                                      apply (simp add: uint_nat word_less_def)
                                     prefer 37
                                     apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
                                     apply (simp add: uint_nat word_less_def)
                                    prefer 36
                                    apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
                                   prefer 35
                                   apply argo
                                  prefer 34
                                  apply argo
                                 prefer 33
                                 apply presburger
                                prefer 32
                                apply argo
                               prefer 31
                               apply argo
                              prefer 30
                              apply presburger
                             prefer 29
                             apply (metis (mono_tags, hide_lams) le_step not_less)
                            prefer 28
                            prefer 27
                            prefer 26
                            prefer 25
                            prefer 24
                            apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
                            apply (simp add: uint_nat word_less_def)
                           prefer 23
                           prefer 22
                           prefer 21
                           apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
                           apply (simp add: uint_nat word_less_def)
                          prefer 20
                          apply (metis (mono_tags, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
                         prefer 19
                         apply argo
                        prefer 18
                        apply argo
                       prefer 17
                       apply presburger
                      prefer 16
                      apply argo
                      prefer 15
                      apply argo
                     prefer 14
                     apply argo
                    prefer 13
                    apply (metis le_step not_less)
                   prefer 12
                   prefer 11
                   apply (metis (no_types) edge_heap pedge_num_dist_heap_ptr_coerce t_C_pte le_step not_less uint_nat word_zero_le)
                  prefer 10
                  apply (metis (no_types) pedge_num_dist_heap_ptr_coerce le_step not_less uint_nat word_zero_le)
                 prefer 9
  text "sledgehammer"
                      
  sorry

(* define something that shows the dist and num arrays are actually what it represents
   and not some random array that happens to correspond to the structure of either arrays *)

definition no_path_inv :: "IGraph \<Rightarrow> IDist \<Rightarrow> INum \<Rightarrow> 32 word \<Rightarrow> bool" where
  "no_path_inv G d n k \<equiv>  \<forall>v < k. (d v < 0 \<longleftrightarrow> n v < 0)"

lemma no_path_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n)\<rbrace>
   no_path' g d n
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> no_path_inv iG iD iN (ivertex_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: no_path'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(vv, s). unat (ivertex_cnt iG - vv)" and
        I="\<lambda>vv s. P s \<and> no_path_inv iG iD iN vv \<and> 
                   vv \<le> ivertex_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and> 
                   is_graph s iG g \<and>
                   is_dist s iG iD d \<and>
                   is_numm s iG iN n"])
  apply (simp add: skipE_def)
  apply wp
  unfolding is_graph_def is_dist_def is_numm_def no_path_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, safe, simp_all add: arrlist_nth)
           prefer 10
           apply wp
           apply fast
          prefer 9
          apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
          apply (simp add: uint_nat word_less_def)
         prefer 6
  using le_step not_less 
         apply blast
        prefer 6
        apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
       prefer 2
  using le_step not_less 
       apply blast
      prefer 2
      apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
     prefer 2
     apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
     apply (simp add:uint_nat word_less_def)
    prefer 3
    apply(rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
    apply (simp add:uint_nat word_less_def)
   prefer 2
   apply (simp add:sint_ucast)
   apply (subgoal_tac "sint (heap_w32 s (ptr_coerce (d +\<^sub>p uint vv))) < 0")
    apply force
   apply (thin_tac "\<not> sint (heap_w32 s (ptr_coerce (d +\<^sub>p uint vv))) < 0")

(*
  apply (subst "sint_eq_uint")
  apply (rule not_msb_from_less)
  find_theorems(99) "sint _ = uint _"
  find_theorems "msb"
*) 
  
  sorry

definition pos_cost_inv :: "IGraph \<Rightarrow> ICost \<Rightarrow> 32 word \<Rightarrow> bool" where
  "pos_cost_inv G c m \<equiv>  \<forall>e < m. c e \<ge> 0"

lemma pos_cost_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_cost s iG iC c)\<rbrace>
   pos_cost' g c
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> pos_cost_inv iG iC (iedge_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: pos_cost'_def)
  apply (subst whileLoop_add_inv [where
        M="\<lambda>(ee, s). unat (iedge_cnt iG - ee)" and
        I="\<lambda>ee s. P s \<and> pos_cost_inv iG iC ee \<and>
                   ee \<le> iedge_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   is_cost s iG iC c"])
  apply wp
  unfolding is_graph_def is_cost_def pos_cost_inv_def
    apply (simp split: if_split_asm, safe, simp_all add: arrlist_nth)
  using le_step not_less 
     apply blast
    apply (subgoal_tac "num_edges_C (heap_IGraph_C s g) - ee \<noteq> 0")
     apply simp
     apply (subgoal_tac "\<And>w wa. (w::32 word) - wa = 0 \<or> unat (w - 1 - wa) < unat (w - wa)")
      apply (subgoal_tac "unat (num_edges_C (heap_IGraph_C s g) - 1 - ee) < unat (num_edges_C (heap_IGraph_C s g) - ee)")
       apply (subgoal_tac "unat (num_edges_C (heap_IGraph_C s g) - (ee + 1)) < unat (num_edges_C (heap_IGraph_C s g) - ee)")
        apply (simp add: add.commute diff_diff_add)
       apply (simp add: diff_add_eq_diff_diff_swap)
      apply fastforce
     apply (metis (no_types) add.commute diff_diff_add measure_unat)
    apply simp
   apply (rule_tac i="(uint ee)" in arrlist_nth_valid, simp+)
   apply (simp add: uint_nat word_less_def)
  apply wp
  apply fast
  done

end

end