(* uses Isabelle2017 and autocorres version 1.0 *)
theory ShortestPathCVerification
  imports 
  "checker-verification/Library/Autocorres_Misc"
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
  is_inf ::  "IEInt \<Rightarrow> IVertex \<Rightarrow> 32 word"
where 
  "is_inf f v \<equiv>  (snd (f v))"

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

lemma long_ucast:
  "unat (ucast (x ::word32) :: word64) = unat x"
  by (simp add: is_up uint_up_ucast unat_def)


fun
  to_edge :: "IEdge \<Rightarrow> Edge_C"
where
  "to_edge (u,v) = Edge_C u v"

lemma s_C_pte[simp]:
  "first_C (to_edge e) = fst e"
  by (cases e) auto

lemma t_C_pte[simp]:
  "second_C (to_edge e) = snd e"
  by (cases e) auto

fun cast_long :: "32 word \<Rightarrow> 64 word"
  where 
  "cast_long x = ucast x"

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
    is_valid_Graph_C h p \<and> 
    ivertex_cnt iG = num_vertices_C (heap_Graph_C h p) \<and> 
    iedge_cnt iG = num_edges_C (heap_Graph_C h p) \<and>
    arrlist (heap_Edge_C h) (is_valid_Edge_C h)
      (map to_edge (mk_iedge_list iG)) (arcs_C (heap_Graph_C h p))"

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

(* Lemmas for unat and of_nat *)
lemma eq_of_nat_conv:
  assumes "unat w1 = n"
  shows "w2 = of_nat n \<longleftrightarrow> w2 = w1"
  using assms by auto

(* More Lemmas for unat and of_nat *)
lemma less_unat_plus1: 
  assumes "a < unat (b + 1)"
  shows "a < unat b \<or> a = unat b"
  apply (subgoal_tac  "b + 1 \<noteq> 0 ")
  using assms unat_minus_one add_diff_cancel 
  by fastforce+

lemma unat_minus_plus1_less:
  fixes a b
  assumes "a < b"
  shows "unat (b - (a + 1)) < unat (b - a)"
  by (metis (no_types) ab_semigroup_add_class.add_ac(1) right_minus_eq measure_unat
      add_diff_cancel2 assms is_num_normalize(1) zadd_diff_inverse linorder_neq_iff)

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
  abs_ICost :: "(IEdge_Id \<Rightarrow> 32 word) \<Rightarrow> IEdge_Id \<Rightarrow> real"
where
  "abs_ICost c e \<equiv> real (unat (c e))"

definition
  abs_IDist :: "(32 word \<Rightarrow> (32 word \<times> 32 word)) \<Rightarrow> 32 word \<Rightarrow> ereal"
where
  "abs_IDist d v \<equiv> if snd (d v) \<noteq> 0 then PInfty else 
         real (unat (fst (d v)))"

definition
  abs_INum :: "(32 word \<Rightarrow> (32 word \<times> 32 word)) \<Rightarrow> 32 word \<Rightarrow> enat"
where
  "abs_INum n v \<equiv> if snd (n v) \<noteq> 0 then \<infinity> else unat (fst (n v))"

definition 
  abs_IPedge :: "(32 word \<Rightarrow> 32 word) \<Rightarrow> 32 word \<Rightarrow> 32 word option" 
where
  "abs_IPedge p v \<equiv> if sint (p v) < 0 then None else Some (p v)"

lemma None_abs_pedgeI[simp]: 
  "(abs_IPedge p v = None) = (sint (p v) < 0)"
  using abs_IPedge_def by auto

lemma Some_abs_pedgeI[simp]: 
  "(\<exists>e. abs_IPedge p v = Some e) = (sint (p v) \<ge> 0)"
  using None_not_eq None_abs_pedgeI 
  by (metis abs_IPedge_def linorder_not_le option.simps(3))
    
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
  is_inf f e =  isInf_C (h (ep +\<^sub>p (uint e)))" 
  using two_comp_arrlist_heap to_eint.simps isInf_C_pte by (metis uint_nat)

thm "is_wellformed'_def"

definition is_wellformed_inv :: "IGraph \<Rightarrow> 32 word \<Rightarrow> bool" where
  "is_wellformed_inv G i \<equiv> \<forall>k < i. ivertex_cnt G > fst (iedges G k)
                                 \<and> ivertex_cnt G > snd (iedges G k)"

lemma is_wellformed_spc':
  "\<lbrace> P and 
     (\<lambda>s. (*wf_digraph (abs_IGraph iG) \<and>*) (* really? :) *)
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
         apply (subgoal_tac "num_vertices_C (heap_Graph_C s g) \<le> fst (snd (snd iG) ee)", force)
         apply (subgoal_tac "first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)) = fst (snd (snd iG) ee)", simp)
         apply (subst tail_heap[where iG=iG], simp, blast+)
        apply(rule_tac x = "ee" in exI)
        apply (subgoal_tac "num_vertices_C (heap_Graph_C s g) \<le> snd (snd (snd iG) ee)", force)
        apply (subgoal_tac "second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)) = snd (snd (snd iG) ee)", simp)
        apply (subst head_heap[where iG=iG], simp, blast+)
       apply (metis two_comp_arrlist_heap s_C_pte le_cases le_step uint_nat word_le_less_eq)
      apply (metis head_heap le_step not_less)
     apply (metis le_step word_not_le)
    apply (metis (mono_tags, hide_lams) diff_diff_add diff_self_eq_0 eq_iff_diff_eq_0 measure_unat not_less0 word_less_nat_alt zero_less_diff)
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
  apply wp 
  apply fast
  done

definition trian_inv :: "IGraph \<Rightarrow> IEInt \<Rightarrow> ICost \<Rightarrow> 32 word \<Rightarrow> bool" where
  "trian_inv G d c m \<equiv> 
    \<forall>i < m. is_inf d (fst (iedges G i)) = 0 \<longrightarrow> 
     (is_inf d (snd (iedges G i)) = 0 \<and> 
      (* val d (fst (iedges G i)) + c i \<ge> val d (fst (iedges G i)) \<and> *)
     cast_long (val d (snd (iedges G i))) \<le> cast_long (val d (fst (iedges G i))) + cast_long (c i))"

lemma trian_inv_step:
  assumes i_less_max: "i < (max_word::32 word)"
  shows "trian_inv G d c (i + 1) \<longleftrightarrow> trian_inv G d c i \<and>
  (is_inf d (fst (iedges G i)) = 0 \<longrightarrow> is_inf d (snd (iedges G i)) = 0 \<and>
  (*val d (fst (iedges G i)) + c i \<ge> val d (fst (iedges G i)) \<and> *)
  cast_long (val d (snd (iedges G i))) \<le> cast_long (val d (fst (iedges G i))) + cast_long (c i))"
  unfolding trian_inv_def
  by (metis (no_types) i_less_max less_irrefl less_x_plus_1)

lemma trian_inv_le:
  assumes leq: "j \<le> i" 
  assumes trian_i: "trian_inv G d c i"
  shows "trian_inv G d c j"
  using assms 
  by (induct j) (auto simp add: trian_inv_def)

lemma cost_abs_C_equiv:
  fixes ee :: "32 word" and s :: lifted_globals
  assumes a1: "arrlist (heap_w32 s) (is_valid_w32 s) (map (iC \<circ> of_nat) [0..<unat (num_edges_C (heap_Graph_C s g))]) c"
  assumes a2: "fst (snd iG) = num_edges_C (heap_Graph_C s g)"
  assumes a3: "ee < num_edges_C (heap_Graph_C s g)"
  shows "iC ee = heap_w32 s (c +\<^sub>p int (unat (ee)))"
proof -
  show ?thesis
    using a1 a3 arrlist_heap by blast
qed

lemma enat_abs_C_equiv:
  fixes ee :: "32 word" and s :: lifted_globals
  assumes a1: "ee < num_edges_C (heap_Graph_C s g)"
  assumes a2: "arrlist (heap_EInt_C s) (is_valid_EInt_C s) (map (to_eint \<circ> (iL \<circ> of_nat)) [0..<unat (num_vertices_C (heap_Graph_C s g))]) l"
  assumes a3: "fst iG = num_vertices_C (heap_Graph_C s g)"
  assumes a4: "fst (snd iG) = num_edges_C (heap_Graph_C s g)"
  assumes a5: "arrlist (heap_Edge_C s) (is_valid_Edge_C s) (map (to_edge \<circ> (snd (snd iG) \<circ> of_nat)) [0..<unat (num_edges_C (heap_Graph_C s g))]) (arcs_C (heap_Graph_C s g))"
  assumes a6: "\<forall>ee < num_edges_C (heap_Graph_C s g). fst (snd (snd iG) ee) < num_vertices_C (heap_Graph_C s g)"
  shows "fst (iL (fst (snd (snd iG) ee))) = val_C (heap_EInt_C s (l +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))"
proof -
  show ?thesis using a6 a5 a4 a3 a2 a1 s_C_pte two_comp_to_edge_arrlist_heap two_comp_to_eint_arrlist_heap val_C_pte by metis
qed

declare if_bool_eq_conj [[simp add]]
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
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, simp_all add: arrlist_nth)
    apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI)
       apply fast
      apply (unfold trian_inv_def is_dist_def is_cost_def is_graph_def)[1]
      apply clarsimp
      apply (rule_tac x=ee in exI)
      apply safe[1]
       apply (metis is_inf_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
      apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = isInf_C (heap_EInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
       apply argo
      apply (subst is_inf_heap, fastforce)
       apply (subst head_heap, fastforce, fastforce)
       apply (metis head_heap wellformed_iGraph)
      apply (subst head_heap, fastforce, fastforce)
      apply fast
     apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI)
        apply fast
       apply (unfold trian_inv_def is_dist_def is_cost_def is_graph_def)[1]
       apply clarsimp
       apply (rule_tac x=ee in exI)
       apply safe[1]
        apply (subst is_inf_heap, fastforce)
         apply (metis wellformed_iGraph)
        apply (subst tail_heap, fastforce, fastforce)
        apply blast
       apply (subgoal_tac "UCAST(32 \<rightarrow> 64) (fst (iD (snd (snd (snd iG) ee)))) = UCAST(32 \<rightarrow> 64) (val_C (heap_EInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee))))))")
        apply (subgoal_tac "UCAST(32 \<rightarrow> 64) (fst (iD (fst (snd (snd iG) ee)))) + UCAST(32 \<rightarrow> 64) (iC ee) = 
                            UCAST(32 \<rightarrow> 64) (val_C (heap_EInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))) + UCAST(32 \<rightarrow> 64) (heap_w32 s (c +\<^sub>p uint ee))")
         apply fastforce
        apply (subst tail_heap, fastforce, fastforce)
        apply (subst val_heap, fastforce)
         apply (metis s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
        apply (simp add: cost_abs_C_equiv uint_nat)
       apply (subst head_heap, fastforce, fastforce)
       apply (subst val_heap, fastforce)
        apply (metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
       apply blast
      apply (rule conjI, rule impI, rule conjI)
        apply fastforce
       apply (rule conjI)
        apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
         apply (subgoal_tac "ee < (max_word::32 word)") 
          apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
          apply clarsimp
          apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1] 
          apply clarsimp
          apply (subst tail_heap, fastforce, fastforce)
          apply (subst head_heap, fastforce, fastforce)
          apply (simp add: cost_abs_C_equiv)
          apply (subst is_inf_heap, fastforce)
           apply (metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
          apply (subst val_heap, fastforce)
           apply (metis wellformed_iGraph)
          apply (subst head_heap, fastforce, fastforce)
          apply (subst val_heap, fastforce) 
           apply (metis s_C_pte two_comp_to_edge_arrlist_heap uint_nat wellformed_iGraph)
          apply (rule conjI, blast, simp add: uint_nat)
         apply (simp add:less_le not_le, meson less_le max_word_max not_le)
        apply (simp add: inc_le is_graph_def, blast intro: inc_le)
       apply (metis (mono_tags) inc_le is_graph_def unat_minus_plus1_less)
      apply (rule conjI)
       apply (unfold wf_digraph_def trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
       apply (metis s_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt)
      apply (rule conjI)
       apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
      apply (rule conjI)
       apply (unfold wf_digraph_def trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
       apply (metis t_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt)
      apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
     apply (unfold wf_digraph_def trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+) 
     apply (metis t_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt)
    apply (rule conjI, rule impI, rule conjI)
      apply fastforce
     apply (rule conjI)
      apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
       apply (subgoal_tac "ee < (max_word::32 word)") 
        apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
        apply clarsimp
        apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1] 
        apply clarsimp
        apply (subst tail_heap, fastforce, fastforce)
        apply (subst head_heap, fastforce, fastforce)
        apply (simp add: cost_abs_C_equiv)
        apply (subst is_inf_heap, fastforce)
         apply (metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
        apply (subst val_heap, fastforce)
         apply (metis wellformed_iGraph)
        apply (subst head_heap, fastforce, fastforce)
        apply (subst val_heap, fastforce) 
         apply (metis s_C_pte two_comp_to_edge_arrlist_heap uint_nat wellformed_iGraph)
        apply (rule conjI, metis is_inf_heap tail_heap wellformed_iGraph)
        apply (metis is_inf_heap tail_heap wellformed_iGraph)
       apply (simp add:less_le not_le, meson less_le max_word_max not_le)
      apply (simp add: inc_le is_graph_def, blast intro: inc_le)
     apply (metis (mono_tags) inc_le is_graph_def unat_minus_plus1_less)
    apply (rule conjI)
     apply (unfold wf_digraph_def trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
     apply (metis s_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt)
    apply (rule conjI)
     apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+) 
    apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
   apply (simp add: is_graph_def)
  apply wp
  apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
  apply force
  done

definition just_inv :: 
  "IGraph \<Rightarrow> IEInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> 32 word \<Rightarrow> bool" where
  "just_inv G d c s n p k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> is_inf n v = 0 \<longrightarrow> 0 \<le> sint (p v) \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        is_inf d v = 0 \<and>
        is_inf d (fst (iedges G e)) = 0 \<and>
        (* val d (fst (iedges G e)) \<le> val d (fst (iedges G e)) + c e \<and> *)
        cast_long (val d v) = cast_long (val d (fst (iedges G e))) + cast_long (c e) \<and>
        is_inf n (fst (iedges G e)) = 0 \<and>
        (* val n (fst (iedges G e)) \<le> val n (fst (iedges G e)) + 1 \<and> *)
        (*val n v < ivertex_cnt G \<and> *)
        cast_long (val n v) = cast_long (val n (fst (iedges G e))) + 1)"

lemma just_inv_step:
  assumes v_less_max: "v < (max_word::32 word)"
  shows "just_inv G d c s n p (v + 1) \<longleftrightarrow> just_inv G d c s n p v
    \<and> (v \<noteq> s \<and> is_inf n v = 0 \<longrightarrow> 0 \<le> sint (p v) \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and> 
        v = snd (iedges G e) \<and>
        is_inf d v = 0 \<and>
        is_inf d (fst (iedges G e)) = 0 \<and>
        (* val d (fst (iedges G e)) \<le> val d (fst (iedges G e)) + c e \<and> *)
        cast_long (val d v) = cast_long (val d (fst (iedges G e))) + cast_long (c e) \<and>
        is_inf n (fst (iedges G e)) = 0 \<and>
        (* val n (fst (iedges G e)) \<le> val n (fst (iedges G e)) + 1 \<and> *)
        (* val n v < ivertex_cnt G \<and> *)
        cast_long (val n v) = cast_long (val n (fst (iedges G e))) + 1))"
  unfolding just_inv_def using v_less_max  
  by (force simp: less_x_plus_1)
  
lemma just_inv_le:
  assumes leq: "j \<le> i" 
  assumes just_i: "just_inv G d c s n p i"
  shows "just_inv G d c s n p j"
  using assms 
  by (induct j) (auto simp add: just_inv_def)

lemma pedge_abs_C_equiv:
  fixes vv :: "32 word" and s :: lifted_globals
  assumes a1: "arrlist (\<lambda>p. heap_w32 s (ptr_coerce p)) (\<lambda>p. is_valid_w32 s (ptr_coerce p)) (map (iP \<circ> of_nat) [0..<unat (num_vertices_C (heap_Graph_C s g))]) p"
  assumes a2: "fst iG = num_vertices_C (heap_Graph_C s g)"
  assumes a3: "vv < num_vertices_C (heap_Graph_C s g)"
  shows "iP (vv) = heap_w32 s (ptr_coerce (p +\<^sub>p int (unat vv)))"
proof -
  have "\<forall>w. heap_w32 s (ptr_coerce (p +\<^sub>p int (unat w))) = iP w \<or> \<not> w < fst iG"
    using a2 a1 heap_ptr_coerce unat_0 by fastforce
  show ?thesis
    using a1 a3 arrlist_heap by blast
qed

lemma  word32_minus_comm: "(x:: 32 word) - y - z = x - z - y" by simp

lemma just_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   just' g d c sc n p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> just_inv iG iD iC sc iN iP (ivertex_cnt iG)) \<rbrace>!"
  sorry
  apply (clarsimp simp: just'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(vv, s). unat (ivertex_cnt iG - vv)" and
        I="\<lambda>vv s. P s \<and> just_inv iG iD iC sc iN iP vv \<and>
                   vv \<le> ivertex_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   is_dist s iG iD d \<and>
                   is_cost s iG iC c \<and>
                   is_numm s iG iN n \<and>
                   is_pedge s iG iP p"])
  apply (simp add: skipE_def)
  apply wp
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, simp_all add: arrlist_nth)
    apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
       apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
       apply (metis isInf_C_pte sint_ucast two_comp_to_eint_arrlist_heap not_le heap_ptr_coerce word_zero_le)
      apply (rule impI, rule conjI)
       apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
       apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
       apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap not_le heap_ptr_coerce word_zero_le)
      apply (rule conjI, rule impI, rule conjI)
        apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
        apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
        apply (metis (no_types) isInf_C_pte two_comp_to_eint_arrlist_heap heap_ptr_coerce word_zero_le two_comp_to_edge_arrlist_heap t_C_pte)
       apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI)
          apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply meson
         apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
         apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
         apply (metis (no_types) isInf_C_pte two_comp_to_eint_arrlist_heap)
        apply (rule conjI, rule impI, rule conjI)
          apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
          apply (metis (no_types) isInf_C_pte two_comp_to_eint_arrlist_heap heap_ptr_coerce word_zero_le two_comp_to_edge_arrlist_heap s_C_pte)
         apply (rule conjI, rule impI, rule conjI)
           apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
           apply (rule conjI)
            apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap)
           apply (rule impI)+
           apply (simp add: pedge_abs_C_equiv)
           apply (simp add: enat_abs_C_equiv)
           apply (simp add: cost_abs_C_equiv)

  apply (subst val_heap, blast, blast) sledgehammer
  apply (metis two_comp_to_eint_arrlist_heap val_C_pte)

          apply (rule conjI, rule impI, rule conjI)
            apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
            apply (rule conjI)
             apply (subst is_inf_heap, blast, blast)
             apply (simp add: pedge_abs_C_equiv)
             apply (simp add: uint_nat)
           apply (rule impI)+
            apply (simp add: pedge_abs_C_equiv enat_abs_C_equiv cost_abs_C_equiv)
            apply (subst val_heap, blast, blast, simp add:uint_nat)
            apply (metis two_comp_to_eint_arrlist_heap val_C_pte)
           apply (rule conjI, rule impI, rule conjI)
             apply (rule impI, rule conjI)
              apply blast
             apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
             apply (rule conjI)
              apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap)
             apply clarsimp
             apply (subgoal_tac "snd (iN (fst (snd (snd iG) (iP vv)))) = isInf_C (heap_EInt_C s (n +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat (heap_w32 s (ptr_coerce (p +\<^sub>p int (unat vv)))))))))))")
              apply argo
             apply (simp add: pedge_abs_C_equiv)
             apply (simp add: enat_abs_C_equiv)
             apply (drule tail_heap, blast)
             apply (simp add:uint_nat)
             apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap)
            apply (rule conjI, rule impI, rule conjI)
              apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
              apply (rule conjI)
               apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap)
              apply (rule impI)+
              apply (simp add: pedge_abs_C_equiv)
              apply (simp add: enat_abs_C_equiv)
             apply (rule conjI, rule impI, rule conjI)
               apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp, rule_tac x=vv in exI, simp add: uint_nat)
               apply (rule conjI)
                apply (metis isInf_C_pte two_comp_to_eint_arrlist_heap)
               apply (rule impI)+
               apply (simp add: pedge_abs_C_equiv)
               apply (simp add: enat_abs_C_equiv)
               apply (metis two_comp_to_eint_arrlist_heap s_C_pte val_C_pte)
              apply (rule conjI, rule impI, rule conjI)
                apply meson
               apply (rule conjI)
                apply (subgoal_tac " vv + 1 \<le> fst iG")
                 apply (subgoal_tac "vv < (max_word::32 word)") 
                  apply (drule just_inv_step[where d=iD and G=iG and c=iC and p=iP and n=iN and s=sc])
                  apply clarsimp
                  apply (unfold just_inv_def is_graph_def is_cost_def is_dist_def is_numm_def is_pedge_def)[1]
                  apply clarsimp
                  apply (simp add:uint_nat)
                  apply (rule conjI)
                   apply (metis not_le heap_ptr_coerce sint_ucast word_zero_le)
                  apply (rule conjI)
                   apply (metis not_le heap_ptr_coerce word_zero_le)
                  apply (rule conjI)
                   apply (metis (no_types) not_le heap_ptr_coerce t_C_pte two_comp_to_edge_arrlist_heap word_zero_le)
                  apply (rule conjI)
                   apply (simp add: pedge_abs_C_equiv)
                   apply (subst is_inf_heap, blast)
                    apply fast
                   apply (metis uint_nat)
                  apply (rule conjI)
                   apply (simp add: pedge_abs_C_equiv)
                   apply (subst tail_heap, blast, simp)
                   apply (subst is_inf_heap, blast)
                    apply (metis le_eq_less_or_eq nat_neq_iff tail_heap wellformed_iGraph word_le_nat_alt word_less_nat_alt)
                   apply (metis uint_nat)
                  apply (rule conjI)
                   apply (simp add: pedge_abs_C_equiv, simp add: cost_abs_C_equiv)
                   apply (subst tail_heap, blast, simp)
                   apply (subst tail_heap, blast, simp)
                   apply (subst val_heap, blast, metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)+
                   apply (simp add: uint_nat)
                  apply (rule conjI)
                   apply (simp add: pedge_abs_C_equiv, simp add: cost_abs_C_equiv)
                   apply (subst tail_heap, blast, simp)
                   apply (subst val_heap, blast, metis (no_types, hide_lams), simp add: uint_nat)
                   apply (subst val_heap, blast, metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add: uint_nat)
                  apply (rule conjI) 
                   apply (simp add:pedge_abs_C_equiv)
                   apply (subst tail_heap, blast, simp)
                   apply (subst is_inf_heap, blast, metis le_eq_less_or_eq nat_neq_iff tail_heap wellformed_iGraph word_le_nat_alt word_less_nat_alt, simp add:uint_nat)
                  apply (rule conjI)
                   apply (simp add: pedge_abs_C_equiv, simp add: cost_abs_C_equiv)
                   apply (subst tail_heap, blast, simp)+
                   apply (subst val_heap, blast, metis not_le tail_heap wellformed_iGraph, simp add:uint_nat)
                   apply (subst val_heap, blast, metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add:uint_nat)
                  apply (simp add: pedge_abs_C_equiv, simp add: cost_abs_C_equiv)
                  apply (subst tail_heap, blast, simp)+
                  apply (subst val_heap, blast, metis, simp add:uint_nat)
                  apply (subst val_heap, blast, metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add:uint_nat)
                 apply (simp add:less_le not_le, meson less_le max_word_max not_le)
                apply (simp add: inc_le is_graph_def)
                apply (unfold just_inv_def is_graph_def is_cost_def is_dist_def is_numm_def is_pedge_def)[1]
                apply (blast intro: inc_le)
               apply (metis (no_types, hide_lams) inc_le is_graph_def unat_minus_plus1_less)
              apply (rule conjI)
               apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp simp: if_bool_eq_conj)+
               apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
              apply (rule conjI)
               apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp simp: if_bool_eq_conj)+
               apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
               apply (metis s_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt not_le)
              apply (rule conjI)
               apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp simp: if_bool_eq_conj)+
               apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
              apply (simp add: is_graph_def word_less_nat_alt not_le, blast+)
             apply (rule conjI)
              apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
              apply (metis s_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt not_le)
             apply (rule conjI)
              apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
             apply (metis is_graph_def)
            apply (rule conjI)
             apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
             apply (metis not_le s_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt)
            apply (rule conjI)
             apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
            apply (metis is_graph_def)
           apply (rule conjI)
            apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+) 
           apply (rule conjI)
            apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+) 
           apply (rule conjI)
            apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
            apply (metis s_C_pte two_comp_to_edge_arrlist_heap word_less_nat_alt not_le)
           apply (rule conjI)
            apply (unfold is_graph_def just_inv_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
           apply (simp add: is_graph_def word_less_nat_alt not_le, blast+)
          apply (rule conjI)
           apply (unfold is_cost_def is_pedge_def is_graph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
          apply (simp add: word_le_nat_alt)
          apply (rule conjI)
           apply (unfold is_dist_def is_pedge_def is_graph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
           apply (metis (no_types, lifting) not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph word_less_nat_alt)
          apply (rule conjI)
           apply (unfold is_pedge_def is_graph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
          apply (simp add: is_graph_def word_less_nat_alt not_le, blast+)
         apply (rule conjI)
          apply (unfold is_dist_def is_pedge_def is_graph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
          apply (metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph word_less_nat_alt)
         apply (rule conjI)
          apply (unfold is_pedge_def is_graph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
         apply (simp add: is_graph_def word_less_nat_alt not_le, blast+)
        apply (unfold is_dist_def is_pedge_def is_graph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
       apply (rule conjI)
        apply (unfold is_dist_def is_pedge_def is_graph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
       apply (simp add: is_graph_def word_less_nat_alt not_le, blast+)+
     apply (rule conjI, rule impI, rule conjI)
       apply meson
      apply (rule conjI)
       apply (subgoal_tac " vv + 1 \<le> fst iG")
        apply (subgoal_tac "vv < (max_word::32 word)") 
         apply (drule just_inv_step[where d=iD and G=iG and c=iC and p=iP and n=iN and s=sc])
         apply (unfold just_inv_def is_graph_def is_cost_def is_dist_def is_numm_def is_pedge_def)[1]
         apply clarsimp
         apply (metis is_inf_heap)
        apply (simp add:less_le not_le, meson less_le max_word_max not_le)
       apply (simp add: inc_le is_graph_def)
       apply (unfold just_inv_def is_graph_def is_cost_def is_dist_def is_numm_def is_pedge_def)[1]
       apply (blast intro: inc_le)
      apply (metis (no_types, hide_lams) inc_le is_graph_def unat_minus_plus1_less)
     apply (rule conjI)
      apply (unfold is_numm_def is_pedge_def is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
     apply clarsimp
     apply (unfold is_pedge_def is_graph_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
    apply safe[1]
        apply (subgoal_tac " sc + 1 \<le> fst iG")
         apply (subgoal_tac "sc < (max_word::32 word)") 
          apply (drule just_inv_step[where d=iD and G=iG and c=iC and p=iP and n=iN and s=sc])
          apply (unfold just_inv_def is_graph_def is_cost_def is_dist_def is_numm_def is_pedge_def)[1]
          apply clarsimp
         apply (simp add:less_le not_le, meson less_le max_word_max not_le)
        apply (simp add: inc_le is_graph_def) 
       apply (simp add: inc_le is_graph_def) 
      apply (simp add: unat_minus_plus1_less is_graph_def)
     apply (unfold is_graph_def)[1]
     apply blast
    apply (unfold is_graph_def is_pedge_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
   apply (metis is_graph_def word_le_less_eq)
  apply (unfold just_inv_def is_graph_def)[1] 
  apply wp
  apply fastforce
  done

definition no_path_inv :: "IGraph \<Rightarrow> IEInt \<Rightarrow> IEInt \<Rightarrow> 32 word \<Rightarrow> bool" where
  "no_path_inv G d n k \<equiv>  \<forall>v < k. (is_inf d v \<noteq> 0 \<longleftrightarrow> is_inf n v \<noteq> 0)"

lemma no_path_inv_step:
  assumes v_less_max: "v < max_word"
  shows "no_path_inv G d n (v + 1) \<longleftrightarrow> no_path_inv G d n v
    \<and> (is_inf d v \<noteq> 0 \<longleftrightarrow> is_inf n v \<noteq> 0)"
  unfolding no_path_inv_def
  using v_less_max  
  by (force simp: less_x_plus_1) 

lemma no_path_spc':
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
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
                   is_graph s iG g \<and>
                   is_dist s iG iD d \<and>
                   is_numm s iG iN n"])
  apply (simp add: skipE_def)
  apply wp
  unfolding is_graph_def is_dist_def is_numm_def no_path_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: if_split_asm, safe, simp_all add: arrlist_nth)
              apply (metis (no_types, hide_lams) is_inf_heap)
             apply (metis (no_types, hide_lams) is_inf_heap)
            apply (metis (no_types, hide_lams) le_step is_inf_heap)
           apply (metis (no_types, hide_lams) le_step is_inf_heap)
          apply (metis le_step not_less)
         apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
        apply (metis (no_types, hide_lams) le_step is_inf_heap)
       apply (metis (no_types, hide_lams) le_step is_inf_heap)
      apply (simp add: inc_le word_less_nat_alt)
     apply (metis (no_types, hide_lams) diff_diff_add eq_iff_diff_eq_0 measure_unat word_not_le)
    apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+, simp add: uint_nat word_less_def)
   apply (rule_tac i="(uint vv)" in arrlist_nth_valid, simp+, simp add: uint_nat word_less_def)
  apply wp
  apply fast
  done

lemma wf_inv_is_fin_digraph: 
   "fin_digraph (abs_IGraph G) \<longleftrightarrow> is_wellformed_inv G (iedge_cnt G)"
    unfolding is_wellformed_inv_def fin_digraph_def fin_digraph_axioms_def
      wf_digraph_def no_loops_def 
    by auto

lemma unat_simp: 
  "\<And>x y:: 32 word. unat (x + y) \<ge> unat x \<longleftrightarrow> 
      unat (x + y) = unat x + unat y"
  using unat_plus_simple word_le_nat_alt by blast

lemma unat_simp_2:
  "\<And>x y :: 32 word. unat (x + y) = unat x + unat y \<longrightarrow> unat x + unat y \<ge> unat x"
  by simp

lemma unat_leq_plus:
  fixes x y z :: "32 word"
  assumes a1: "x \<le> y + z"
  shows "unat x \<le> unat y + unat z" 
  by (simp add: assms word_unat_less_le)

lemma unat_leq_plus_64:
  fixes x y z :: "64 word"
  assumes a1: "x \<le> y + z"
  shows "unat x \<le> unat y + unat z" 
  by (simp add: assms word_unat_less_le)

lemma real_unat_leq_plus:
  fixes x y z :: "32 word"
  assumes a1: "x \<le> y + z"
  shows "real (unat x) \<le> real (unat y) + real (unat z)" 
  using assms unat_leq_plus by fastforce

lemma real_unat_leq_plus_64:
  fixes x y z :: "64 word"
  assumes a1: "x \<le> y + z"
  shows "real (unat x) \<le> real (unat y) + real (unat z)" 
  using assms unat_leq_plus_64 by fastforce

lemma real_nat:
  fixes x y z :: "nat"
  assumes a1: "real x \<le> real y + real z"
  shows "x \<le> y + z"
  using assms by linarith

lemma unat_leq_trian_plus:
  fixes x y z :: "32 word"
  assumes a1: "unat x \<le> unat y + unat z"
  assumes a2: "unat y + unat z \<ge> unat y"
  assumes a3: "unat (y + z) \<ge> unat y"
  shows "x \<le> y + z"
  using a1 a3 unat_simp word_le_nat_alt by fastforce

lemma unat_leq_plus_unats:
  fixes x y z :: "32 word"
  assumes a1: "unat x \<le> unat (y + z)"
  shows "x \<le> y + z"
proof -
  have f1: "unat x \<le> unat y + unat z"
    using a1 by (meson not_le unat_leq_plus word_less_nat_alt)
  then show ?thesis
    by (simp add: assms word_le_nat_alt)
qed

lemma unat_plus_leq_unats:
  fixes y z :: "32 word"
  assumes a1: "unat y + unat z \<le> unat (max_word :: 32 word)"
  shows "unat y + unat z \<le> unat (y + z)"
  using a1 
  by unat_arith

lemma trian_imp_valid:
  fixes x y z :: "32 word"
  assumes a1: "real (unat y) + real (unat z) \<le> real (unat (max_word :: 32 word)) \<and> real(unat x) \<le> real (unat y) + real (unat z)"
  shows "unat y + unat z \<le> unat (max_word::32 word)"
  using a1 by linarith

lemma c: "UCAST(32 \<rightarrow> 64) (x::word32) = cast_long x"
  by simp

lemma cast_long_max: "unat (cast_long (x::32 word)) \<le> unat (max_word::word32)"
  using word_le_nat_alt long_ucast by auto

lemma cast_long_max_extend: "unat (cast_long (x::32 word)) \<le> unat (max_word::word64)"
  using word_le_nat_alt by blast

lemma trian_64_reverse:
  fixes x y z :: "word32"
  assumes a1: "UCAST(32 \<rightarrow> 64) x \<le> UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z"
  shows "unat x \<le> unat y + unat z"
  by (metis (no_types, hide_lams) assms is_up len_of_word_comparisons(2) unat_leq_plus_64 uint_up_ucast unat_def)
  

lemma trian_64:
  fixes x y z :: "word32"
  assumes a1: "unat x \<le> unat y + unat z"
  shows "UCAST(32 \<rightarrow> 64) x \<le> UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z"
  sorry
(*
proof -
  have "UCAST(32 \<rightarrow> 64) y \<le> UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z"
  proof -
    {
      have "y \<le> (max_word :: word32)" by simp
      then have "UCAST(32 \<rightarrow> 64) y \<le> UCAST (32 \<rightarrow> 64) (max_word :: word32)"
        by (simp add: is_up uint_up_ucast unat_def word_le_nat_alt)
      moreover have "z \<le> (max_word :: word32)" by simp
      then have "UCAST(32 \<rightarrow> 64) z \<le> UCAST(32 \<rightarrow> 64) (max_word :: word32)" 
        by (simp add: is_up uint_up_ucast unat_def word_le_nat_alt)
      moreover have "UCAST(32 \<rightarrow> 64) (max_word :: word32) + UCAST(32 \<rightarrow> 64) (max_word :: word32) \<le> (max_word::word64)"
        by blast
      then have "UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z \<le> (max_word :: word64)"
        by blast
      then have "unat (UCAST(32 \<rightarrow> 64) y) + unat (UCAST(32 \<rightarrow> 64) z) \<le> unat (max_word :: word64)"
        try0 sledgehammer
      
    }
  qed
qed sorry
proof -
  have f1: "UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z \<le> (max_word :: word64)"
    by simp
  have test32: "(max_word::word32) = (0xFFFFFFFF::word32)"
    by (simp add: max_word_eq)
  then have test32_unat: "unat (max_word::word32) = unat (0xFFFFFFFF::word32)"
    by argo
  have test64: "(max_word::word64) = (0xFFFFFFFFFFFFFFFF::word64)"
    by (simp add: max_word_eq)
  then have test64_unat: "unat (max_word::word64) = unat (0xFFFFFFFFFFFFFFFF::word64)"
    by argo
  have upcast: "unat (0xFFFFFFFF::word32) = unat (0xFFFFFFFF::word64)"
    by fastforce
  have upcast_high_val: "unat (max_word::word32) = unat (0x00000000FFFFFFFF::word64)"
    using test32 test32_unat test64 test64_unat upcast
    by argo
  then have val: "unat (max_word::word32) + unat (max_word::word32) = unat (0x00000001FFFFFFFE::word64)"
    by simp
  have f2: "unat (max_word:: word32) \<le> unat (max_word:: word64)"
    by (metis max_word_max long_ucast word_le_nat_alt)
  have f3: "unat (a::word32) \<le> unat (max_word:: word32)"
    using word_le_nat_alt by blast
  then have f4: "unat (a::word32) \<le> unat (max_word:: word64)"
    using f2 by linarith
  have f5: "unat (max_word::word32) + unat (max_word::word32) \<le> unat (max_word::word64)"
    using f1 f2 f3 f4 val
    by (metis max_word_max word_le_nat_alt)
  have eq: "unat (UCAST(32 \<rightarrow> 64) x) \<le> unat (UCAST(32 \<rightarrow> 64) y) + unat (UCAST(32 \<rightarrow> 64) z)"
    using a1 long_ucast by simp
  have cast: "unat (UCAST(32 \<rightarrow> 64) a) \<le> unat (max_word::word32)"
    by (simp add: f3 long_ucast)
  have final: "unat y + unat z \<le> unat (max_word :: word64)"
    by (metis (no_types, hide_lams) add_mono_thms_linordered_semiring(1) f5 order_trans cast_long.elims cast_long_max long_ucast)
  have ?thesis *)

lemma just_64:
  fixes x y z :: "word32"
  shows "(UCAST(32 \<rightarrow> 64) x = UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z) = (unat x = unat y + unat z)"
proof -
  have "(UCAST(32 \<rightarrow> 64) x = UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z) \<longrightarrow> unat x = unat y + unat z"
    by (metis (mono_tags, hide_lams) is_up le_add_same_cancel1 len_of_word_comparisons(2) trian_64 uint_up_ucast unat_def unat_plus_simple zero_le)
  moreover 
  have "unat x = unat y + unat z \<longrightarrow> (UCAST(32 \<rightarrow> 64) x = UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z)"
    by (metis (mono_tags, hide_lams) is_up len_of_word_comparisons(2) uint_up_ucast unat_def word_arith_nat_add word_unat.Rep_inverse)
  ultimately show ?thesis by blast
qed
  
lemma fin_digraph_is_wellformed_inv:  "fin_digraph (abs_IGraph G) \<longleftrightarrow> is_wellformed_inv G (iedge_cnt G)" 
  unfolding is_wellformed_inv_def fin_digraph_def fin_digraph_axioms_def wf_digraph_def no_loops_def 
  by auto

lemma basic_just_sp_eq_invariants_imp:
"\<And>G d c s n p. 
    (is_wellformed_inv G (iedge_cnt G) \<and> 
    is_inf d s = 0 \<and>
    val d s \<le> 0 \<and>
    trian_inv G d c (iedge_cnt G) \<and> 
    just_inv G d c s n p (ivertex_cnt G))
    \<longleftrightarrow>
    basic_just_sp_pred 
    (abs_IGraph G) (abs_IDist d) 
    (abs_ICost c) s (abs_INum n) (abs_IPedge p) 
    "
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?ac = "abs_ICost c"
  let ?an = "abs_INum n"  
  let ?ap = "abs_IPedge p"
  have "fin_digraph (abs_IGraph G) \<longleftrightarrow> is_wellformed_inv G (iedge_cnt G)"
    by (rule fin_digraph_is_wellformed_inv)
  moreover
  have trian1: "trian_inv G d c (iedge_cnt G) \<longleftrightarrow>
   (\<forall>e. e \<in> arcs ?aG \<longrightarrow> 
    is_inf d (tail ?aG e) = 0 \<longrightarrow>
    is_inf d (head ?aG e) = 0 \<and> 
   (*(val d (tail ?aG e) \<le> val d (tail ?aG e) + (c e)) \<and>*)
   (cast_long (val d (head ?aG e)) \<le> cast_long (val d (tail ?aG e)) + cast_long (c e)))"
    by (simp add: trian_inv_def)
  then have "trian_inv G d c (iedge_cnt G) \<longleftrightarrow>
   (\<forall>e. e \<in> arcs ?aG \<longrightarrow>
    ?ad (head ?aG e) \<le> ?ad (tail ?aG e) + ?ac e)"
    apply safe
    (* program implies maths *)
      apply (simp add: trian_inv_def abs_IDist_def abs_ICost_def)
      apply clarsimp
      apply (metis real_unat_leq_plus_64 long_ucast)
    (* maths implies program *)
     apply (simp add: trian_inv_def abs_IDist_def abs_ICost_def)
     apply clarsimp
     apply (erule_tac x=e in allE)
     apply (simp add: real_unat_leq_plus_64 long_ucast)
    apply (simp add: trian_inv_def abs_IDist_def abs_ICost_def)
    apply clarsimp
    apply safe
       apply fastforce
      apply fastforce
     apply (subgoal_tac "(if snd (d (snd (snd (snd G) ia))) \<noteq> 0 then PInfty else ereal (real (unat (fst (d (snd (snd (snd G) ia))))))) \<le> 
                         (if False then PInfty else ereal (real (unat (fst (d (fst (snd (snd G) ia))))))) + ereal (real (unat (c ia)))")
      apply (subgoal_tac "\<not> True \<or> snd (d (snd (snd (snd G) ia))) = 0")
       apply meson
      apply force
     apply presburger
    apply (erule_tac x="ia" in allE)
    apply clarsimp
    apply (subgoal_tac "\<And>e. \<not> PInfty \<le> e \<or> e = PInfty")
     apply (subgoal_tac "snd (d (snd (snd (snd G) ia))) = 0 \<or> ereal (real (unat (fst (d (fst (snd (snd G) ia))))) + real (unat (c ia))) = PInfty")
      apply (simp add:trian_64)
     apply presburger
    apply (metis (full_types) ereal_infty_less_eq(1) infinity_ereal_def)
    done
  moreover have "just_inv G d c s n p (ivertex_cnt G) \<longleftrightarrow>
    (\<forall>v. v \<in> verts ?aG \<and>
      v \<noteq> s \<and> is_inf n v = 0 \<longrightarrow> 0 \<le> sint (p v) \<and>
    (\<exists>e. p v = e \<and> e \<in> arcs ?aG \<and>
      v = head ?aG e \<and>
      is_inf d v = 0 \<and>
      is_inf d (tail ?aG e) = 0 \<and>
      cast_long (val d v) = cast_long (val d (tail ?aG e)) + cast_long (c e) \<and>
      is_inf n (tail ?aG e) = 0 \<and>
      (* val n v < ivertex_cnt G \<and> *)
      cast_long (val n v) = cast_long (val n (tail ?aG e)) + 1))"
    using just_inv_def
    by auto
  then have "just_inv G d c s n p (ivertex_cnt G) \<longleftrightarrow>
    (\<forall>v. v \<in> verts ?aG \<and>
      v \<noteq> s \<and> ?an v \<noteq> \<infinity> \<longrightarrow> 
    (\<exists>e. ?ap v = Some e \<and> e \<in> arcs ?aG \<and>
      v = head ?aG e \<and> 
      ?ad v = ?ad (tail ?aG e) + (?ac e) \<and>
      ?an v = ?an (tail ?aG e) + enat 1))"
    apply safe
    (* program implies maths *)
    apply clarsimp
      apply (unfold abs_IPedge_def abs_INum_def)[1]
      apply (erule_tac x=v in allE)
       apply clarsimp
       apply (rule conjI)
        apply (meson enat.distinct(2) not_le)
      apply (rule impI)
      apply (unfold abs_IDist_def abs_ICost_def)[1]
      apply clarsimp
      apply (safe, simp_all)
    using just_64 apply force
    apply (subgoal_tac "UCAST(32 \<rightarrow> 64) (fst (n v)) \<noteq> (0::64 word)")
     apply (metis (no_types) add.commute enat.distinct(2) enat.inject long_ucast unatSuc)
      apply (metis add.commute le_add_same_cancel1 lt1_neq0 trian_64 ucast_1 zero_le)
    (* maths implies program *)
     apply (unfold just_inv_def abs_IPedge_def)[1]
     apply clarsimp
     apply (erule_tac x=v in allE)
     apply (simp add: shortest_path_checker.abs_INum_def)
    apply safe
          apply (unfold abs_INum_def abs_IPedge_def)[1]
          apply (subgoal_tac "\<forall>na w. (((w = s \<or> enat (unat (fst (n w))) \<noteq> enat na) \<or> snd (n w) \<noteq> 0) \<or> \<not> w < fst G) \<or> \<not> sint (p w) < 0")
           apply (subgoal_tac "\<forall>na w. (((Some (p w) = Some (esk1_1 w) \<or> w = s) \<or> enat (unat (fst (n w))) \<noteq> enat na) \<or> snd (n w) \<noteq> 0) \<or> \<not> w < fst G")
            apply (subgoal_tac "\<forall>na. (if snd (n (fst (snd (snd G) (esk1_1 v)))) \<noteq> 0 
                                      then \<infinity> else enat (unat (fst (n (fst (snd (snd G) (esk1_1 v))))))) + enat (Suc 0) = enat (unat (fst (n v))) \<or> enat (unat (fst (n v))) \<noteq> enat na")
             apply (subgoal_tac "p v = esk1_1 v")
              apply (subgoal_tac "snd (n (fst (snd (snd G) (esk1_1 v)))) = 0")
               apply argo
    using enat.distinct(2) plus_enat_simps(2)
              apply force
             apply blast
            apply fastforce
           apply fastforce
          apply (metis (no_types) option.simps(3))
         defer
         defer
         defer
         apply (unfold abs_INum_def abs_IPedge_def)[1]
         apply (metis option.sel option.simps(3))
        apply (unfold abs_INum_def abs_IPedge_def)[1]
        apply (metis option.sel option.simps(3))
       apply (unfold abs_INum_def abs_IPedge_def)[1]
       apply (erule_tac x=v in allE)
       apply safe[1]
        apply force
       apply clarsimp
  sorry
  moreover have "(is_inf d s = 0 \<and> (is_inf d s = 0 \<longrightarrow> val d s \<le> 0)) \<longleftrightarrow> abs_IDist d s \<le> 0"
    unfolding abs_IDist_def
    by (simp add: unat_eq_zero)
ultimately
   show "?thesis G d c s n p"
   unfolding 
    basic_just_sp_pred_def 
    basic_just_sp_pred_axioms_def 
    basic_sp_def basic_sp_axioms_def
   by meson
qed

lemma shortest_path_pos_cost_pred_eq_invariants':
"\<And>G d c s n p.
    (abs_IDist d) s = 0 \<and>
    s < ivertex_cnt G \<and>
    (is_wellformed_inv G (iedge_cnt G) \<and> 
    trian_inv G d c (iedge_cnt G) \<and> 
    just_inv G d c s n p (ivertex_cnt G) \<and> 
    no_path_inv G d n (ivertex_cnt G))
    \<longrightarrow>
    shortest_path_pos_cost_pred (abs_IGraph G) (abs_IDist d) (abs_ICost c) s (abs_INum n) (abs_IPedge p)"
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?ac = "abs_ICost c"
  let ?an = "abs_INum n"  
  let ?ap = "abs_IPedge p"
  have no_path_assms: "no_path_inv G d n (ivertex_cnt G) \<longrightarrow> 
    (\<forall>v < fst G. (is_inf d v \<noteq> 0 \<longleftrightarrow> is_inf n v \<noteq> 0))"
    by (simp add:no_path_inv_def)
  then have "no_path_inv G d n (ivertex_cnt G) \<longrightarrow> 
    (\<forall>v. v \<in> verts ?aG \<longrightarrow> (?ad v \<noteq> PInfty \<longleftrightarrow> ?an v \<noteq> PInfty))"
    unfolding no_path_inv_def abs_IDist_def abs_INum_def by simp
  moreover have "(\<forall>e. e \<in> arcs ?aG \<longrightarrow> 0 \<le> ?ac e)"
    unfolding abs_ICost_def by force
ultimately 
  show "?thesis G d c s n p"
  unfolding 
    basic_just_sp_pred_def 
    basic_just_sp_pred_axioms_def 
    basic_sp_def basic_sp_axioms_def
    shortest_path_pos_cost_pred_def
    shortest_path_pos_cost_pred_axioms_def
  using basic_just_sp_eq_invariants_imp
  apply (clarsimp, safe)
         apply (simp add: fin_digraph_is_wellformed_inv)
        apply (simp add: abs_IDist_def abs_ICost_def trian_inv_def, blast intro: real_unat_leq_plus_64)
       apply (simp add: abs_IPedge_def abs_IDist_def just_inv_def, metis PInfty_eq_infinity less_le order.asym no_path_assms)
      apply (simp add: abs_IPedge_def abs_IDist_def just_inv_def, metis (no_types) enat.distinct(2) not_le abs_INum_def)
     apply (simp add: abs_IPedge_def abs_IDist_def abs_ICost_def just_inv_def, safe)
          apply (metis no_path_assms not_le)
         apply (simp add: no_path_inv_def abs_INum_def, (auto)[1])
        apply (metis no_path_assms not_le)
       apply (metis no_path_assms)
      apply (simp add: no_path_inv_def abs_INum_def, (auto)[1])
     apply (metis (no_types) no_path_assms of_nat_add unat_plus_simple)
    apply (simp add: abs_IPedge_def abs_INum_def just_inv_def, metis (no_types, hide_lams) add.commute add.right_neutral enat.distinct(2) enat.inject not_le unatSuc word_le_0_iff word_less_1)
   apply (simp add: no_path_inv_def abs_IDist_def abs_INum_def, force)
  apply (simp add: no_path_inv_def abs_IDist_def abs_INum_def, force)
  done
qed

definition basic_just_sp_inv :: 
  "IGraph \<Rightarrow> IEInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> bool" where
  "basic_just_sp_inv G d c s n p \<equiv>
       (is_wellformed_inv G (iedge_cnt G) \<and>
        val d s = 0 \<and>
        is_inf d s = 0 \<and>
        trian_inv G d c (iedge_cnt G) \<and> 
        just_inv G d c s n p (ivertex_cnt G))"

lemma check_basic_just_sp_spc_intermediate:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   check_basic_just_sp' g d c sc n p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
        basic_just_sp_inv iG iD iC sc iN iP)\<rbrace>!"
  apply (clarsimp simp: check_basic_just_sp'_def basic_just_sp_inv_def)
  apply wp
  apply (rule_tac P1=" P and 
    (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_wellformed_inv iG (iedge_cnt iG) \<and>
          val iD sc = 0 \<and>
          is_inf iD sc = 0 \<and>
          trian_inv iG iD iC (iedge_cnt iG))" 
     in validNF_post_imp[OF _ just_spc']) 
     apply fastforce
    apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_wellformed_inv iG (iedge_cnt iG) \<and>
          val iD sc = 0 \<and>
          is_inf iD sc = 0)"
     in validNF_post_imp[OF _ trian_spc']) 
     using fin_digraph_def fin_digraph_axioms_def
       apply (fastforce simp: wf_inv_is_fin_digraph)
     defer
  apply (rule_tac P' = " P and
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p) " and 
         P1 = " P and (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p) " and 
Q' = "\<lambda>ret' s. if ret' = 0 then ((\<lambda>_. P) And (\<lambda>rr s. (rr \<noteq> 0) = (is_wellformed_inv iG (fst (snd iG)) \<and> fst (iD sc) = 0 \<and> snd (iD sc) = 0 \<and> trian_inv iG iD iC (fst (snd iG)) \<and> just_inv iG iD iC sc iN iP (fst iG)))) 0 s
               else (\<lambda> r s. P s \<and> is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_wellformed_inv iG (iedge_cnt iG) ) ret' s "
     in validNF_pre_post_imp[OF is_wellformed_spc'])
       apply fastforce
     apply fastforce
       apply wp
     apply safe
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (subgoal_tac "fst (iD sc) = val_C (heap_EInt_C s (d +\<^sub>p uint sc))")
        apply fastforce
       apply (unfold is_dist_def is_graph_def is_wellformed_inv_def)[1]
     (*apply (subst val_heap, force, force)*)
     apply (subst val_heap, force) defer
       apply blast
      apply (rule impI, rule conjI)
       apply clarsimp
       apply (subgoal_tac "snd (iD sc) = isInf_C (heap_EInt_C s (d +\<^sub>p uint sc))")
        apply fastforce
       apply (unfold is_dist_def is_graph_def is_wellformed_inv_def)[1]
        (*apply (subst is_inf_heap, force, force)*)
        apply (subst is_inf_heap, force) defer
       apply blast
      apply (rule impI, rule conjI)
       apply (unfold is_dist_def is_graph_def is_wellformed_inv_def)[1]
         (*apply (subst val_heap, force, force)*)
         apply (subst val_heap, force) defer
       apply clarsimp
       apply (simp add: less_le)
      apply (rule conjI)
       apply (unfold is_dist_def is_graph_def is_wellformed_inv_def)[1]
         (*apply (subst is_inf_heap, force, force)*)
         apply (subst is_inf_heap, force) defer
       apply clarsimp
      apply (simp add: less_le)
      apply (metis fin_digraph_is_wellformed_inv fin_digraph_def)
     apply (unfold is_dist_def is_graph_def is_wellformed_inv_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
   sorry

definition basic_sp_inv :: 
  "IGraph \<Rightarrow> IEInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> bool" where
  "basic_sp_inv G d c s n p \<equiv>
       (basic_just_sp_inv G d c s n p \<and>
        s < ivertex_cnt G \<and>
        val d s = 0 \<and>
        no_path_inv G d n (ivertex_cnt G)\<and>
        (\<forall>e < ivertex_cnt G. 0 \<le> c e))"

lemma shortest_path_pos_cost_spc:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   check_sp' g d c sc n p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow>
       basic_sp_inv iG iD iC sc iN iP)\<rbrace>!"
  apply (clarsimp simp: check_sp'_def basic_sp_inv_def)
  apply wp
  apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          basic_just_sp_inv iG iD iC sc iN iP \<and>
          sc < ivertex_cnt iG \<and>
          val iD sc = 0)" 
     in validNF_post_imp[OF _ no_path_spc'])
     apply fastforce
  apply (rule_tac P= "P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          (* sc < ivertex_cnt iG \<and> *)
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          basic_just_sp_inv iG iD iC sc iN iP \<and>
          sc < ivertex_cnt iG)" 
     in validNF_post_imp)
     apply fastforce
    apply wp
    apply safe
     apply (clarsimp simp: if_bool_eq_conj)+
     apply safe
      apply (subgoal_tac "fst (iD sc) = val_C (heap_EInt_C s (d +\<^sub>p uint sc))")
       apply argo
      apply (unfold is_dist_def)[1]
      apply (subst val_heap, simp+)
  apply (unfold is_dist_def)[1]
     apply (subst val_heap, simp+)
    apply (unfold is_graph_def is_dist_def)[1]
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
   defer
  apply (rule_tac P' = " P and
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p) " and 
         P1 = " P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p) " and 
Q' = "\<lambda>ret' s. if ret' = 0 then ((\<lambda>_. P) And (\<lambda>rr s. (rr \<noteq> 0) = (basic_just_sp_inv iG iD iC sc iN iP \<and> sc < fst iG \<and> fst (iD sc) = 0 \<and> no_path_inv iG iD iN (fst iG)))) 0 s else
     (\<lambda> r s. P s \<and> is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          basic_just_sp_inv iG iD iC sc iN iP) ret' s"
     in validNF_pre_post_imp[OF check_basic_just_sp_spc_intermediate])
    apply fastforce
   apply fastforce
  apply wp
  apply safe
    apply (simp add: is_graph_def)+
  done


lemma shortest_path_pos_cost_imp_correct:
"\<And>G d c s n p . 
  shortest_path_pos_cost_pred (abs_IGraph G) d c s n p \<longrightarrow>
   (\<forall>v \<in> verts (abs_IGraph G).
   d v = wf_digraph.\<mu> (abs_IGraph G) c s v)"
using shortest_path_pos_cost_pred.correct_shortest_path_pred by fast


end

end