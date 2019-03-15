(* uses Isabelle2017 and autocorres version 1.0 *)
theory ShortestPathCVerification
  imports 
  "checker-verification/Library/Autocorres_Misc"
  "checker-verification/Witness_Property/Connected_Components"
  "checker-verification/Witness_Property/ShortestPath"
begin
(* Parse the input file. *)
install_C_file "shortest_path_checker.c"

autocorres "shortest_path_checker.c"

context shortest_path_checker begin

thm "is_wellformed_body_def"
thm "trian_body_def"
thm "just_body_def"
thm "no_path_body_def"
thm "check_basic_just_sp_body_def"
thm "check_sp_body_def"

thm "is_wellformed'_def"
thm "trian'_def"
thm "just'_def"
thm "no_path'_def"
thm "check_basic_just_sp'_def"
thm "check_sp'_def"

(*Implementation Graph Types*)

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> 32 word" 
type_synonym IEInt = "IVertex \<Rightarrow> (32 word \<times> 32 word)"
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

abbreviation 
  val :: "IEInt \<Rightarrow> IVertex \<Rightarrow> 32 word"
where 
  "val f v \<equiv> fst (f v)"

fun 
  bool::"32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

abbreviation 
  is_inf ::  "IEInt \<Rightarrow> IVertex \<Rightarrow> bool"
where 
  "is_inf f v \<equiv> bool (snd (f v))"

(* Make List - makes a list containing the result of a function *)

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
  mk_inum_list :: "IGraph \<Rightarrow> IEInt \<Rightarrow> (32 word \<times> 32 word) list"
where 
  "mk_inum_list G num = mk_list' (unat (ivertex_cnt G)) num"
  
fun 
  mk_ipedge_list :: "IGraph \<Rightarrow> IPEdge \<Rightarrow> 32 word list"
where
  "mk_ipedge_list G pedge = mk_list' (unat (ivertex_cnt G)) pedge"

fun
  mk_idist_list :: "IGraph \<Rightarrow> IEInt \<Rightarrow> (32 word \<times> 32 word) list"
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

fun
  to_eint :: "(32 word \<times> 32 word) \<Rightarrow> EInt_C"
where
  "to_eint p = EInt_C (fst p) (snd p)"

lemma val_C_pte[simp]:
  "val_C (to_eint p) = fst p"
  by (case_tac "p") auto

lemma isInf_C_pte[simp]:
  "isInf_C (to_eint p) = snd p"
  by (cases p) auto

definition is_graph where
  "is_graph h iG p \<equiv>
    is_valid_IGraph_C h p \<and> 
    ivertex_cnt iG = num_vertices_C (heap_IGraph_C h p) \<and> 
    iedge_cnt iG = num_edges_C (heap_IGraph_C h p) \<and>
    arrlist (heap_IEdge_C h) (is_valid_IEdge_C h)
      (map to_edge (mk_iedge_list iG)) (arcs_C (heap_IGraph_C h p))"

definition 
  "is_numm h iG iN p \<equiv> 
        arrlist (\<lambda>p. heap_EInt_C h p) (\<lambda>p. is_valid_EInt_C h p) 
        (map to_eint (mk_inum_list iG iN)) p"

definition
  "is_pedge h iG iP  (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_ipedge_list iG iP) p"

definition
  "is_dist h iG iD p \<equiv> 
        arrlist (\<lambda>p. heap_EInt_C h p) (\<lambda>p. is_valid_EInt_C h p) 
        (map to_eint (mk_idist_list iG iD)) p"


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
  "abs_pedge p v \<equiv> if sint (p v) < 0 then None else Some (p v)"

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

lemma heap_ptr_coerce:
  "\<lbrakk>arrlist (\<lambda>p. h (ptr_coerce p)) (\<lambda>p. v (ptr_coerce p)) 
  (map (iL \<circ> of_nat) [0..<unat n]) l; i < n; 0 \<le> i\<rbrakk> \<Longrightarrow>
    iL i = h (ptr_coerce (l +\<^sub>p int (unat i)))" 
  apply (subgoal_tac 
  "h (ptr_coerce (l +\<^sub>p int (unat i))) = map (iL \<circ> of_nat) [0..<unat n] ! unat i") 
   apply (subgoal_tac "map (iL \<circ> of_nat) [0..<unat n] ! unat i = iL i") 
    apply fastforce
   apply (metis (hide_lams, mono_tags) unat_mono word_unat.Rep_inverse 
    minus_nat.diff_0 nth_map_upt o_apply plus_nat.add_0)
  apply (drule arrlist_nth_value[where i="int (unat i)"], (simp add:unat_mono)+)
  done

lemma arrlist_heap:
  "\<lbrakk>arrlist h v (map (iL \<circ> of_nat) [0..<unat n]) l; 
  i < n\<rbrakk> \<Longrightarrow>
    iL i = h (l +\<^sub>p int (unat i))" 
  apply (subgoal_tac 
  "h (l +\<^sub>p int (unat i)) = map (iL \<circ> of_nat) [0..<unat n] ! unat i") 
   apply (subgoal_tac "map (iL \<circ> of_nat) [0..<unat n] ! unat i = iL i") 
    apply fastforce
   apply (metis (hide_lams, mono_tags) unat_mono word_unat.Rep_inverse 
    minus_nat.diff_0 nth_map_upt o_apply plus_nat.add_0)
  apply (simp add: arrlist_nth_value unat_mono)
  done

lemma two_comp_arrlist_heap:
  "\<lbrakk> arrlist h v (map (f \<circ> (iL \<circ> of_nat)) [0..<unat n]) l;
  i < n\<rbrakk> \<Longrightarrow> f (iL i) = h (l +\<^sub>p (int (unat i)))" 
  using arrlist_heap 
  by (metis (no_types, hide_lams) comp_apply comp_assoc)

lemma two_comp_to_eint_arrlist_heap:
  "\<lbrakk> arrlist h v (map (to_eint \<circ> (iL \<circ> of_nat)) [0..<unat n]) l;
  i < n\<rbrakk> \<Longrightarrow> to_eint (iL i) = h (l +\<^sub>p (int (unat i)))" 
  using arrlist_heap 
  by (metis (no_types, hide_lams) comp_apply comp_assoc)

lemma two_comp_to_edge_arrlist_heap:
  "\<lbrakk> arrlist h v (map (to_edge \<circ> (iL \<circ> of_nat)) [0..<unat n]) l;
  i < n\<rbrakk> \<Longrightarrow> to_edge (iL i) = h (l +\<^sub>p (int (unat i)))" 
  using arrlist_heap 
  by (metis (no_types, hide_lams) comp_apply comp_assoc)
 
lemma head_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  snd ((iedges iG) e) = second_C (h (ep +\<^sub>p (uint e)))" 
  using two_comp_arrlist_heap to_edge.simps t_C_pte by (metis uint_nat)

lemma tail_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  fst ((iedges iG) e) =  first_C (h (ep +\<^sub>p  (uint e)))" 
  using two_comp_arrlist_heap to_edge.simps s_C_pte uint_nat by metis

lemma val_heap:
  "\<lbrakk>arrlist h v (map (to_eint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  val f e = val_C (h (ep +\<^sub>p (uint e)))" 
  using two_comp_arrlist_heap to_eint.simps val_C_pte by (metis uint_nat)

lemma is_inf_heap:
  "\<lbrakk>arrlist h v (map (to_eint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  is_inf f e = bool (isInf_C (h (ep +\<^sub>p (uint e))))" 
  using two_comp_arrlist_heap to_eint.simps isInf_C_pte by (metis uint_nat)

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
         apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) \<le> fst (snd (snd iG) ee)", force)
         apply (subgoal_tac "first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint ee)) = fst (snd (snd iG) ee)", simp)
         apply (subst tail_heap[where iG=iG], simp, blast+)
        apply(rule_tac x = "ee" in exI)
        apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) \<le> snd (snd (snd iG) ee)", force)
        apply (subgoal_tac "second_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint ee)) = snd (snd (snd iG) ee)", simp)
        apply (subst head_heap[where iG=iG], simp, blast+)
       apply (metis two_comp_arrlist_heap s_C_pte le_cases le_step uint_nat word_le_less_eq)
      apply (metis head_heap le_step not_less)
     apply (simp add: le_step word_not_le) (* slow *)
  using le_step not_less 
     apply blast
    apply (metis (mono_tags, hide_lams) diff_diff_add diff_self_eq_0 eq_iff_diff_eq_0 measure_unat not_less0 word_less_nat_alt zero_less_diff)
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
  apply wp
  apply fast
  done

definition trian_inv :: "IGraph \<Rightarrow> IEInt \<Rightarrow> ICost \<Rightarrow> 32 word \<Rightarrow> bool" where
  "trian_inv G d c m \<equiv> 
    \<forall>i < m. val d (snd (iedges G i)) \<le> val d (fst (iedges G i)) + c i"

lemma trian_inv_step:
  assumes i_less_max: "i < max_word"
  shows "trian_inv G d c (i + 1) \<longleftrightarrow> trian_inv G d c i
    \<and> val d (snd (iedges G i)) \<le> val d (fst (iedges G i)) + c i"
  unfolding trian_inv_def 
  by (metis (no_types) i_less_max less_irrefl less_x_plus_1)

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
          apply (rule_tac x="ee " in exI)
          apply (rule conjI, simp+)
          apply (subst arrlist_heap[where l=c and iL=iC], blast+)
          apply (subst val_heap, blast, metis wellformed_iGraph)+
          apply (subst head_heap, blast, blast)+
          apply (subst tail_heap, blast, blast)+
          apply (simp add: uint_nat)
         apply (subst arrlist_heap[where l=c and iL=iC], simp)
  using le_step less_trans 
          apply blast
         apply (subst val_heap, blast, metis (mono_tags, hide_lams) IGraph_C.exhaust le_step less_trans num_edges_C.num_edges_C_def wellformed_iGraph)+
         apply (subst head_heap, blast)+
  using le_step less_trans 
          apply blast
         apply (subst tail_heap, blast)+
  using le_step less_trans 
          apply blast
         apply (subgoal_tac "i < num_edges_C (heap_IGraph_C s g)")
          apply (subgoal_tac "\<And>w. \<not> w < num_edges_C (heap_IGraph_C s g) \<or> heap_w32 s (c +\<^sub>p uint w) = iC w")
           apply (subgoal_tac "\<And>w. \<not> w < num_edges_C (heap_IGraph_C s g) \<or> heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint w) = to_edge (snd (snd iG) w)")
            apply (subgoal_tac "\<And>w. \<not> w < fst iG \<or> val_C (heap_EInt_C s (d +\<^sub>p uint w)) = fst (iD w)")
             apply (subgoal_tac "\<And>w. \<not> w < num_edges_C (heap_IGraph_C s g) \<or> snd (snd (snd iG) w) < fst iG")
              apply (subgoal_tac "\<And>w. \<not> w < num_edges_C (heap_IGraph_C s g) \<or> fst (snd (snd iG) w) < fst iG")
               apply (subgoal_tac "val_C (heap_EInt_C s (d +\<^sub>p int (unat (second_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint i)))))) \<le> val_C (heap_EInt_C s (d +\<^sub>p int (unat (first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint i)))))) + heap_w32 s (c +\<^sub>p int (unat i))")
                apply (simp add: uint_nat)
               apply (subgoal_tac "\<forall>w. val_C (heap_EInt_C s (d +\<^sub>p int (unat w))) = fst (iD w) \<or> \<not> w < fst iG")
                apply (subgoal_tac "val_C (heap_EInt_C s (d +\<^sub>p int (unat (second_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p int (unat i))))))) \<le> val_C (heap_EInt_C s (d +\<^sub>p int (unat (first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p int (unat i))))))) + iC i")
                 apply (subgoal_tac "val_C (heap_EInt_C s (d +\<^sub>p int (unat (second_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint i)))))) \<le> val_C (heap_EInt_C s (d +\<^sub>p int (unat (first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint i)))))) + heap_w32 s (c +\<^sub>p int (unat i))")
                  apply (simp add:uint_nat)+
                apply (metis (no_types, hide_lams) le_step word_not_le)
               apply (metis uint_nat)
              apply (simp add: wf_digraph_def)
             apply (simp add: wf_digraph_def)
            apply (simp add: val_heap)
           apply (simp add: two_comp_to_edge_arrlist_heap uint_nat)
          apply (metis arrlist_heap uint_nat)
  using le_step less_trans       
         apply blast
  using le_step not_less
        apply blast
        apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
       apply (metis (full_types) tail_heap wellformed_iGraph uint_nat word_less_nat_alt)
      apply (rule_tac i="uint ee" in arrlist_nth_valid, simp+)
      apply (simp add:uint_nat)  
  using word_less_nat_alt
      apply blast
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
     apply (metis head_heap wellformed_iGraph uint_nat word_less_nat_alt)
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
   apply wp
   apply fast
  done


definition just_inv :: 
  "IGraph \<Rightarrow> IEInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> 32 word \<Rightarrow> bool" where
  "just_inv G d c s n p k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> \<not> is_inf n v \<longrightarrow> 0 \<le> sint (p v) \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        val d v = val d (fst (iedges G e)) + c e \<and>
        val n v = val n (fst (iedges G e)) + 1)"

lemma just_inv_step:
  assumes v_less_max: "v < max_word"
  shows "just_inv G d c s n p (v + 1) \<longleftrightarrow> just_inv G d c s n p v
    \<and> (v \<noteq> s \<and>  \<not> is_inf n v \<longrightarrow> 0 \<le> sint (p v) \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and> 
        v = snd (iedges G e) \<and>
        val d v = val d (fst (iedges G e)) +  c e \<and>
        val n v = val n (fst (iedges G e)) +  1))"
  unfolding just_inv_def using v_less_max  
  by (force simp: less_x_plus_1) 
  
lemma just_inv_le:
  assumes leq: "j \<le> i" 
  assumes just_i: "just_inv G d c s n p i"
  shows "just_inv G d c s n p j"
  using assms 
  by (induct j) (auto simp add: just_inv_def)

lemma not_just_verts:
  fixes G R c d n p s v
  assumes v_less_max: "v < max_word"
  assumes "v < ivertex_cnt G"
  assumes "v \<noteq> s \<and> \<not> is_inf n v \<and> 0 \<le> sint (p v) \<and>
        (iedge_cnt G \<le> p v \<or>
        snd (iedges G (p v)) \<noteq> v \<or> 
        val d v \<noteq> 
          val d (fst (iedges G (p v))) + c (p v) \<or> 
        val n v \<noteq> val n (fst (iedges G (p v))) + 1)"
  shows "\<not> just_inv G d c s n p (ivertex_cnt G)"
proof (rule notI)
  assume jv: "just_inv G d c s n p (ivertex_cnt G)"
  have "just_inv G d c s n p (v + 1)"
    by (metis le_step order.asym word_not_le just_inv_le[OF _ jv] assms(2))
  then have "(v \<noteq> s \<and> \<not> is_inf n v \<longrightarrow> 
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and> 
        v = snd (iedges G e) \<and>
        val d v = val d (fst (iedges G e)) + c e \<and>
        val n v = val n (fst (iedges G e)) + 1))"
    unfolding just_inv_def
    using v_less_max just_inv_step
    by (auto simp add : less_x_plus_1)
  with assms show False by force
qed

lemma parent_dist_eq:
  fixes vv :: "32 word" and s :: lifted_globals
  assumes a1: "arrlist (heap_EInt_C s) (is_valid_EInt_C s) (map (to_eint \<circ> (iD \<circ> of_nat)) [0..<unat (num_vertices_C (heap_IGraph_C s g))]) d"
  assumes a2: "fst iG = num_vertices_C (heap_IGraph_C s g)"
  assumes a3: "\<not> num_edges_C (heap_IGraph_C s g) \<le> heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))"
  assumes a4: "arrlist (\<lambda>p. heap_w32 s (ptr_coerce p)) (\<lambda>p. is_valid_w32 s (ptr_coerce p)) (map (iP \<circ> of_nat) [0..<unat (num_vertices_C (heap_IGraph_C s g))]) p"
  assumes a5: "fst (snd iG) = num_edges_C (heap_IGraph_C s g)"
  assumes a6: "vv < num_vertices_C (heap_IGraph_C s g)"
  assumes a7: "arrlist (heap_IEdge_C s) (is_valid_IEdge_C s) (map (to_edge \<circ> (snd (snd iG) \<circ> of_nat)) [0..<unat (num_edges_C (heap_IGraph_C s g))]) (arcs_C (heap_IGraph_C s g))"
  assumes a8: "wf_digraph (abs_IGraph iG)"
  shows "fst (iD (fst (snd (snd iG) (iP vv)))) = val_C (heap_EInt_C s (d +\<^sub>p uint (first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint (heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))))))))"
proof -
  have "\<forall>w. heap_w32 s (ptr_coerce (p +\<^sub>p int (unat w))) = iP w \<or> \<not> w < fst iG"
    using a4 a2 by (metis (no_types) heap_ptr_coerce word_zero_le)
  then show "fst (iD (fst (snd (snd iG) (iP vv)))) = val_C (heap_EInt_C s (d +\<^sub>p uint (first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint (heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))))))))"
    using a8 a7 a6 a5 a3 a2 a1 by (metis not_le shortest_path_checker.tail_heap shortest_path_checker.val_heap shortest_path_checker.wellformed_iGraph uint_nat)
qed

lemma pedge_size:
  fixes vv :: "32 word" and s :: lifted_globals and v :: "32 word"
  assumes a1: "arrlist (\<lambda>p. heap_w32 s (ptr_coerce p)) (\<lambda>p. is_valid_w32 s (ptr_coerce p)) (map (iP \<circ> of_nat) [0..<unat (num_vertices_C (heap_IGraph_C s g))]) p"
  assumes a2: "fst iG = num_vertices_C (heap_IGraph_C s g)"
  assumes a3: "vv < num_vertices_C (heap_IGraph_C s g)"
  assumes a4: "v < vv + 1"
  assumes a5: "\<forall>v<vv. snd (iN v) = 0 \<longrightarrow> v = sc \<or> fst (iD v) = fst (iD (fst (snd (snd iG) (iP v)))) + iC (iP v) \<and> v = snd (snd (snd iG) (iP v)) \<and> iP v < num_edges_C (heap_IGraph_C s g) \<and> 0 \<le> sint (iP v) \<and> fst (iN v) = fst (iN (fst (snd (snd iG) (iP v)))) + 1"
  assumes a6: "snd (iN v) = 0"
  assumes a7: "v \<noteq> sc"
  assumes a8: "\<not> num_edges_C (heap_IGraph_C s g) \<le> heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))"
  shows "heap_w32 s (ptr_coerce (p +\<^sub>p int (unat v))) < num_edges_C (heap_IGraph_C s g)"
proof -
  have "\<forall>w. w < fst iG \<or> \<not> w < vv"
    using a3 a2 by force
  then show "heap_w32 s (ptr_coerce (p +\<^sub>p int (unat v))) < num_edges_C (heap_IGraph_C s g)"
    using a8 a7 a6 a5 a4 a2 a1 by (metis (no_types) heap_ptr_coerce le_step not_le uint_nat word_zero_le)
qed

lemma first_edge_val:
  fixes vv :: "32 word" and s :: lifted_globals and v :: "32 word"
  assumes a1: "arrlist (\<lambda>p. heap_w32 s (ptr_coerce p)) (\<lambda>p. is_valid_w32 s (ptr_coerce p)) (map (iP \<circ> of_nat) [0..<unat (num_vertices_C (heap_IGraph_C s g))]) p"
  assumes a2: "fst iG = num_vertices_C (heap_IGraph_C s g)"
  assumes a3: "arrlist (heap_IEdge_C s) (is_valid_IEdge_C s) (map (to_edge \<circ> (snd (snd iG) \<circ> of_nat)) [0..<unat (num_edges_C (heap_IGraph_C s g))]) (arcs_C (heap_IGraph_C s g))"
  assumes a4: "fst (snd iG) = num_edges_C (heap_IGraph_C s g)"
  assumes a5: "wf_digraph (abs_IGraph iG)"
  assumes a6: "\<forall>v<vv. snd (iN v) = 0 \<longrightarrow> v = sc \<or> fst (iD v) = fst (iD (fst (snd (snd iG) (iP v)))) + iC (iP v) \<and> v = snd (snd (snd iG) (iP v)) \<and> iP v < num_edges_C (heap_IGraph_C s g) \<and> 0 \<le> sint (iP v) \<and> fst (iN v) = fst (iN (fst (snd (snd iG) (iP v)))) + 1"
  assumes a7: "snd (iN v) = 0"
  assumes a8: "v \<noteq> sc"
  assumes a9: "\<not> num_edges_C (heap_IGraph_C s g) \<le> heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))"
  assumes a10: "v < vv + 1"
  assumes "vv < num_vertices_C (heap_IGraph_C s g)"
  shows "first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint (heap_w32 s (ptr_coerce (p +\<^sub>p int (unat v)))))) < num_vertices_C (heap_IGraph_C s g)"
proof -
  have "\<forall>w. heap_w32 s (ptr_coerce (p +\<^sub>p int (unat w))) = iP w \<or> \<not> w < fst iG"
    using a2 a1 by (metis (no_types) heap_ptr_coerce word_zero_le)
  then show "first_C (heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint (heap_w32 s (ptr_coerce (p +\<^sub>p int (unat v)))))) < num_vertices_C (heap_IGraph_C s g)"
    using a10 a9 a8 a7 a6 a5 a4 a3 a2 by (metis le_step not_le shortest_path_checker.tail_heap shortest_path_checker.wellformed_iGraph uint_nat)
qed

lemma  word32_minus_comm: "(x:: 32 word) - y - z = x - z - y" by simp

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
    apply (simp split: if_split_asm, simp_all add: arrlist_nth)
    apply (safe)
                                        apply (rule_tac x=vv in exI)
                                        apply (rule conjI, metis (no_types, lifting) not_le arrlist_heap sint_ucast uint_nat, simp)
                                        apply (metis (no_types, hide_lams) bool.simps is_inf_heap)
                                       apply (rule_tac x=vv in exI)
                                       apply (rule conjI, metis (no_types) heap_ptr_coerce not_le uint_nat word_zero_le, simp)
                                       apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
                                      apply (rule_tac x=vv in exI)
                                      apply (rule conjI, metis (no_types) head_heap heap_ptr_coerce uint_nat word_zero_le, simp)
                                      apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
                                     apply (rule_tac x=vv in exI)
                                     apply (rule conjI, simp)
                                      apply (subgoal_tac "fst (iD vv) \<noteq> fst (iD (fst (snd (snd iG) (iP vv)))) + iC (iP vv)")
                                       apply blast
                                      apply clarsimp
                                      apply (erule notE[where R=False and P="val_C _ = val_C _ + _"])
                                      apply (frule_tac e=vv in val_heap[where f=iD], simp)
                                      apply (subgoal_tac "iC (iP vv) =
                                                          heap_w32 s 
                                                  (c +\<^sub>p uint (heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))))") 
                                      apply (simp add: parent_dist_eq)
                                      apply (subgoal_tac "iP vv = (heap_w32 s (ptr_coerce (p +\<^sub>p uint vv)))")
                                       apply (subgoal_tac "\<And>w. \<not> w < num_edges_C (heap_IGraph_C s g) \<or> heap_w32 s (c +\<^sub>p uint w) = iC w")
                                        apply (subgoal_tac "\<And>w. \<not> w < num_edges_C (heap_IGraph_C s g) \<or> heap_IEdge_C s (arcs_C (heap_IGraph_C s g) +\<^sub>p uint w) = to_edge (snd (snd iG) w)")
                                         apply force
                                        apply (simp add: two_comp_to_edge_arrlist_heap uint_nat)
                                       apply (simp add: uint_nat)
  using arrlist_heap
                                       apply force
                                      apply (metis (no_types) heap_ptr_coerce uint_nat word_zero_le)

                                     apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
                                    apply (rule_tac x=vv in exI)
                                    apply (rule conjI, metis (no_types) heap_ptr_coerce tail_heap val_heap wellformed_iGraph uint_nat word_zero_le, simp)
                                    apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
                                   apply (subgoal_tac "0 \<le> sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (ptr_coerce (p +\<^sub>p int (unat vv))))::32 signed word)")
                                    apply (subgoal_tac "0 \<le> sint (iP v)")
                                     apply blast
  using heap_ptr_coerce le_step sint_ucast
                                    apply fastforce
                                   apply (simp add: uint_nat)
                                  apply (metis (no_types) heap_ptr_coerce le_step not_le uint_nat word_zero_le)
                                 apply (metis (no_types) head_heap heap_ptr_coerce le_step not_le uint_nat word_zero_le)
                                 defer
                                apply (subgoal_tac "\<forall>w. heap_w32 s (ptr_coerce (p +\<^sub>p int (unat w))) = iP w \<or> \<not> w < fst iG")
                                 apply (metis (no_types, hide_lams) le_step not_le tail_heap val_heap wellformed_iGraph uint_nat)
                                apply (metis heap_ptr_coerce word_zero_le)
  using inc_le
                               apply blast
                              defer
                              apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                             apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                             apply (metis (no_types, hide_lams) not_le s_C_pte wellformed_iGraph two_comp_to_edge_arrlist_heap word_less_nat_alt)
                            apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                           apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                          apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                          apply (metis (no_types, hide_lams) not_le s_C_pte wellformed_iGraph two_comp_to_edge_arrlist_heap word_less_nat_alt)
                         apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                        apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                       apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
                      apply (metis le_step isInf_C_pte two_comp_to_eint_arrlist_heap)
                     apply (subst heap_ptr_coerce[where l=p and iL=iP])
                        apply fast
                       apply (metis le_step wellformed_iGraph)
                      apply fastforce
                     apply (subgoal_tac "\<not> bool (isInf_C (heap_EInt_C s (n +\<^sub>p uint vv))) \<or> bool (snd (iN vv))")
                      apply (subgoal_tac "heap_w32 s (ptr_coerce (p +\<^sub>p int (unat v))) < num_edges_C (heap_IGraph_C s g)")
                       apply blast
                      apply (metis (no_types) le_step bool.elims(2) bool.elims(3) heap_ptr_coerce wellformed_iGraph word_zero_le)
  using is_inf_heap
                     apply blast
                    apply (subst heap_ptr_coerce[where l=p and iL=iP])
                       apply fast
                      apply (metis le_step wellformed_iGraph)
                     apply fastforce
                    apply (subgoal_tac "\<not> bool (isInf_C (heap_EInt_C s (n +\<^sub>p uint vv))) \<or> bool (snd (iN vv))")
                     apply (subgoal_tac "v = snd (snd (snd iG) (heap_w32 s (ptr_coerce (p +\<^sub>p int (unat v)))))")
                      apply metis
                     apply (metis (no_types) le_step bool.elims(2) bool.elims(3) heap_ptr_coerce wellformed_iGraph word_zero_le)
  using is_inf_heap 
                    apply blast
                   apply (metis (mono_tags, hide_lams) le_step isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
                  apply (metis (no_types, hide_lams) le_step bool.simps is_inf_heap)
  using inc_le
                 apply blast
                defer
                apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
                apply (metis uint_nat word_less_def)
               apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
               apply (metis uint_nat word_less_def)
  using le_step
              apply blast
  using le_step
             apply blast
            apply (metis (no_types, hide_lams) le_step)
  using le_step
           apply blast
  using le_step
          apply blast
  using inc_le
         apply blast
        defer
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
      apply wp
      apply fast
     apply (case_tac "v = vv")  
      apply (subst heap_ptr_coerce[where l=p and iL=iP])
        apply fast
       apply metis
      apply fastforce
     apply (subst heap_ptr_coerce[where l=p and iL=iP])
        apply fast
       apply metis
      apply fastforce 
     apply (subst arrlist_heap[where l=c and iL=iC])
       apply simp
      apply (metis (no_types) not_le uint_nat)
     apply clarsimp
     apply (subst tail_heap, blast)+
      apply (simp add: pedge_size)
     apply (subst val_heap, blast)+
  using le_step less_trans
      apply blast
     apply (subst val_heap, blast)+
      apply (simp add: first_edge_val)
     apply (simp add: uint_nat)
     apply (subgoal_tac "v < vv")  
      apply (frule_tac x=v in spec, clarsimp)
     using le_step apply blast 
     apply simp
     apply (subst unat_mono)
      apply (case_tac "vv = sc", simp_all)
     apply (case_tac "num_vertices_C (heap_IGraph_C s g) > 1") prefer 2 
      apply (metis (mono_tags, hide_lams) add.left_neutral not_le plus_one_helper word_gt_a_gt_0 word_le_less_eq)
     defer
     apply (subst unat_mono)
      apply (case_tac "vv = sc", simp_all)
     apply (case_tac "num_vertices_C (heap_IGraph_C s g) > 1") prefer 2 
      apply (metis (mono_tags, hide_lams) add.left_neutral not_le plus_one_helper word_gt_a_gt_0 word_le_less_eq)
     defer
     apply (case_tac "num_vertices_C (heap_IGraph_C s g) > 1") prefer 2
        apply (metis (mono_tags, hide_lams) add.left_neutral cancel_comm_monoid_add_class.diff_cancel 
                     diff_zero not_le plus_one_helper word_gt_a_gt_0 word_le_less_eq word_less_nat_alt)
       apply (rule unat_mono) 
       apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) -  sc - 1 < 
                      num_vertices_C (heap_IGraph_C s g) - sc") 
        apply (simp add: diff_diff_add)
       apply (metis add_0_left diff_add_cancel less_irrefl word_overflow)
apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) -  vv - 1 < 
                      num_vertices_C (heap_IGraph_C s g) - vv") 
        apply (simp add: diff_diff_add)
      apply (metis add_0_left diff_add_cancel less_irrefl word_overflow)
      apply (subgoal_tac "num_vertices_C (heap_IGraph_C s g) -  vv - 1 < 
                      num_vertices_C (heap_IGraph_C s g) - vv") 
        apply (simp add: diff_diff_add)
       apply (metis add_0_left diff_add_cancel less_irrefl word_overflow)
     using diff_diff_add word32_minus_comm  
     done

definition no_path_inv :: "IGraph \<Rightarrow> IEInt \<Rightarrow> IEInt \<Rightarrow> 32 word \<Rightarrow> bool" where
  "no_path_inv G d n k \<equiv>  \<forall>v < k. (is_inf d v \<longleftrightarrow> is_inf n v)"

lemma no_path_inv_step:
  assumes v_less_max: "v < max_word"
  shows "no_path_inv G d n (v + 1) \<longleftrightarrow> no_path_inv G d n v
    \<and> (is_inf d v \<longleftrightarrow> is_inf n v)"
  unfolding no_path_inv_def
  using v_less_max  
  by (force simp: less_x_plus_1) 

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
               apply (metis (no_types, hide_lams) bool.simps is_inf_heap)
              apply (metis (no_types, hide_lams) le_step bool.simps is_inf_heap)
             apply (metis (no_types, hide_lams) le_step bool.simps is_inf_heap)
  using le_step not_less
            apply blast
           apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
          apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
          apply (simp add:uint_nat word_less_def)
         apply (metis (no_types, hide_lams) bool.simps is_inf_heap)
        apply (metis (no_types, hide_lams) le_step bool.simps is_inf_heap)
       apply (metis (no_types, hide_lams) le_step bool.simps is_inf_heap)
  using le_step not_less
      apply blast
     apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
    apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
    apply (simp add:uint_nat word_less_def)
   apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+)
   apply (simp add:uint_nat word_less_def)
  apply wp
  apply fast
  done

end

end