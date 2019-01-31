(* uses Isabelle2017 and autocorres version 1.0 *)
theory shortest_path_neg
  imports 
  "checker-verification/Library/Autocorres_Misc"
  "checker-verification/Witness_Property/Connected_Components"
begin
(* Parse the input file. *)

install_C_file "shortest_path_neg.c"

autocorres "shortest_path_neg.c"

context shortest_path_neg begin

subsection {* Definitions *}

(* non-negative cost *)
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

(* general cost *)

thm "s_assums_body_def"
thm "parent_num_assms_body_def"
thm "no_p_edge_body_def"
thm "source_val_body_def"
thm "no_edge_Vm_Vf_body_def"
thm "awalk_body_def"
thm "awalk_cost_body_def"
thm "C_se_body_def"
thm "int_neg_cyc_body_def"
thm "shortest_paths_locale_step1_body_def"
thm "shortest_paths_locale_step2_body_def"
thm "shortest_paths_locale_step3_body_def"

thm "s_assums'_def"
thm "parent_num_assms'_def"
thm "no_p_edge'_def"
thm "source_val'_def"
thm "no_edge_Vm_Vf'_def"
thm "awalk'_def"
thm "awalk_cost'_def"
thm "C_se'_def"
thm "int_neg_cyc'_def"
thm "shortest_paths_locale_step1'_def"
thm "shortest_paths_locale_step2'_def"
thm "shortest_paths_locale_step3'_def"

subsection {* Implementation Graph Types *}

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> 32 word"
type_synonym INum = "IVertex \<Rightarrow> 32 word"
type_synonym IDist = "IVertex \<Rightarrow> 32 word \<times> 32 word"
type_synonym ICost = "IEdge_Id \<Rightarrow> 32 word"
type_synonym IGraph = "32 word \<times> 32 word \<times> (IEdge_Id \<Rightarrow> IEdge)"

abbreviation ivertex_cnt :: "IGraph \<Rightarrow> 32 word"
where 
  "ivertex_cnt G \<equiv> fst G"

abbreviation iedge_cnt :: "IGraph \<Rightarrow> 32 word"
where 
  "iedge_cnt G \<equiv> fst (snd G)"

abbreviation iedges :: "IGraph \<Rightarrow> IEdge_Id \<Rightarrow> IEdge"
where 
  "iedges G \<equiv> snd (snd G)"

(* Make List - makes a list containing the result of a function *)
fun bool::"32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

fun mk_list' :: "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> 'b list" 
where 
  "mk_list' n f = map f  (map of_nat [0..<n])"

fun mk_list'_temp :: "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b list" 
where 
  "mk_list'_temp 0 _ _ = []" |
  "mk_list'_temp (Suc x) f i = (f (of_nat i)) # mk_list'_temp x f (Suc i)"

subsection {* Make graph lists *}

fun mk_iedge_list :: "IGraph \<Rightarrow> IEdge list"
where 
  "mk_iedge_list G = mk_list' (unat (iedge_cnt G)) (iedges G)"

fun mk_inum_list :: "IGraph \<Rightarrow> INum \<Rightarrow> 32 word list"
where 
  "mk_inum_list G num = mk_list' (unat (ivertex_cnt G)) num"
  
fun mk_ipedge_list :: "IGraph \<Rightarrow> IPEdge \<Rightarrow> 32 word list"
where
  "mk_ipedge_list G pedge = mk_list' (unat (ivertex_cnt G)) pedge"

fun mk_icost_list :: "IGraph \<Rightarrow> ICost \<Rightarrow> 32 word list"
where                
  "mk_icost_list G cost = mk_list' (unat (iedge_cnt G)) cost"

fun mk_idist_list :: "IGraph \<Rightarrow> IDist \<Rightarrow> (32 word \<times> 32 word) list" 
where                         
  "mk_idist_list G dis = mk_list' (unat (ivertex_cnt G)) dis"
                             
subsection {* Equate to Implementation *}
fun to_edge :: "IEdge \<Rightarrow> Edge_C"
where
  "to_edge (u,v) = Edge_C u v"

fun to_enat :: "(32 word \<times> 32 word) \<Rightarrow> enat_C"
where
  "to_enat (a,b) = enat_C (scast a) (scast b)"

lemma first_C_pte[simp]:
  "first_C (to_edge e) = fst e"
  by (cases e) auto

lemma second_C_pte[simp]:
  "second_C (to_edge e) = snd e"
  by (cases e) auto

lemma val_C_pte[simp]:
  "val_C (to_enat n) = scast (fst n)"
  by (cases n) auto

lemma inf_status_C_pte[simp]:
  "inf_status_C (to_enat n) = scast (snd n)"
  by (cases n) auto

definition is_graph 
  where
  "is_graph h iG p \<equiv>
    is_valid_Graph_C h p \<and> 
    ivertex_cnt iG = num_vertices_C (heap_Graph_C h p) \<and> 
    iedge_cnt iG = num_edges_C (heap_Graph_C h p) \<and>
    arrlist (heap_Edge_C h) (is_valid_Edge_C h)
      (map to_edge (mk_iedge_list iG)) (arcs_C (heap_Graph_C h p))"

definition is_numm 
  where
  "is_numm h iG iN p \<equiv> arrlist (heap_w32 h) (is_valid_w32 h) (mk_inum_list iG iN) p"

definition is_pedge
  where
  "is_pedge h iG iP (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_ipedge_list iG iP) p"

definition is_cost
  where
  "is_cost h iG iC (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_icost_list iG iC) p"

definition is_dist
  where
  "is_dist h iG iD (p:: enat_C ptr) \<equiv> arrlist (\<lambda>p. heap_enat_C h (ptr_coerce p))
        (\<lambda>p. is_valid_enat_C h (ptr_coerce p)) (map to_enat (mk_idist_list iG iD)) p"

subsection {* Abstract Graph *}

definition no_loops :: "('a, 'b) pre_digraph \<Rightarrow> bool" 
where
  "no_loops G \<equiv> \<forall>e \<in> arcs G. tail G e \<noteq> head G e"

definition abs_IGraph :: "IGraph \<Rightarrow> (32 word, 32 word) pre_digraph"
where
  "abs_IGraph G \<equiv> \<lparr> verts = {0..<ivertex_cnt G}, arcs = {0..<iedge_cnt G},
    tail = fst o iedges G, head = snd o iedges G \<rparr>"

lemma verts_absI[simp]: "verts (abs_IGraph G) = {0..<ivertex_cnt G}"
  and edges_absI[simp]: "arcs (abs_IGraph G) = {0..<iedge_cnt G}"
  and start_absI[simp]: "tail (abs_IGraph G) e = fst (iedges G e)"
  and target_absI[simp]: "head (abs_IGraph G) e = snd (iedges G e)"
  by (auto simp: abs_IGraph_def)

definition abs_pedge :: "(32 word \<Rightarrow> 32 word) \<Rightarrow> 32 word \<Rightarrow> 32 word option"
where
  "abs_pedge p \<equiv> (\<lambda>v. if sint (p v) < 0 then None else Some (p v))"

lemma None_abs_pedgeI[simp]: 
  "((abs_pedge p) v = None) = (sint (p v) < 0)"
  using abs_pedge_def by auto

lemma Some_abs_pedgeI[simp]: 
  "(\<exists>e. (abs_pedge p) v = Some e) = (sint (p v) \<ge> 0)"
  using None_not_eq None_abs_pedgeI 
  by (metis abs_pedge_def linorder_not_le option.simps(3))
    
subsection {* Helper Lemmas *}

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
  using edge_heap to_edge.simps second_C_pte by (metis uint_nat)

lemma tail_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  fst ((iedges iG) e) =  first_C (h (ep +\<^sub>p  (uint e)))" 
  using edge_heap to_edge.simps first_C_pte uint_nat by metis

subsection {* Verification *}

definition is_wellformed_inv :: "IGraph \<Rightarrow> 32 word \<Rightarrow> bool" 
  where
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
                   is_graph s iG g"])
  apply (simp add: skipE_def)
  apply wp
  unfolding is_graph_def is_wellformed_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, safe, simp_all add: arrlist_nth)
         apply (rule_tac x = "ee" in exI)
         apply (subgoal_tac "num_vertices_C (heap_Graph_C s g) \<le> fst (snd (snd iG) ee)")
          apply force
         apply (subgoal_tac "first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)) = fst (snd (snd iG) ee)")
          apply simp
         apply (subst tail_heap[where iG=iG], simp)
          apply blast
         apply blast
        apply(rule_tac x = "ee" in exI)
        apply (subgoal_tac "num_vertices_C (heap_Graph_C s g) \<le> snd (snd (snd iG) ee)")
         apply force
        apply (subgoal_tac "second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)) = snd (snd (snd iG) ee)")
         apply simp
        apply (subst head_heap[where iG=iG], simp)
         apply blast
        apply blast
       apply (metis edge_heap first_C_pte le_cases le_step uint_nat word_le_less_eq)
      apply (metis head_heap le_step not_less)
     apply (simp add: le_step word_not_le)
  using le_step not_less 
     apply blast
    apply (metis (mono_tags, hide_lams) diff_diff_add diff_self_eq_0 eq_iff_diff_eq_0 measure_unat not_less0 word_less_nat_alt zero_less_diff)
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
  apply wp
  apply fast
  done

definition trian_inv :: "IGraph \<Rightarrow> IDist \<Rightarrow> ICost \<Rightarrow> 32 word \<Rightarrow> bool" 
  where
  "trian_inv G d c m \<equiv> 
    \<forall>i < m. snd (d (snd (iedges G i))) = 0 \<and> 
            snd (d (fst (iedges G i))) = 0 \<and> 
            fst (d (snd (iedges G i))) \<le> fst (d (fst (iedges G i))) + c i"

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
                    apply (rule_tac x = "ee" in exI)
                    apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = inf_status_C (heap_enat_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
  
          
  
  sorry

end

end