(* uses Isabelle2019 and autocorres version 1.6 *)
theory ShortestPathNegCVerification
  imports
  "HOL-Library.Option_ord"
  "Library/Autocorres_Misc"
  "ShortestPath/ShortestPathNeg"
begin

install_C_file "shortest_path_neg_checker.c"

autocorres "shortest_path_neg_checker.c"

context shortest_path_neg_checker begin

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> IEdge_Id"
type_synonym IENInt = "IVertex \<Rightarrow> (32 signed word \<times> 32 signed word)"
type_synonym IEInt = "IVertex \<Rightarrow> (32 word \<times> 32 word)"
type_synonym ICost = "IEdge_Id \<Rightarrow> 32 signed word"
type_synonym IGraph = "32 word \<times> 32 word \<times> (IEdge_Id \<Rightarrow> IEdge)"

abbreviation ivertex_cnt :: 
  "IGraph \<Rightarrow> 32 word"
where 
  "ivertex_cnt G \<equiv> fst G"

abbreviation iedge_cnt :: 
"IGraph \<Rightarrow> 32 word"
where 
  "iedge_cnt G \<equiv> fst (snd G)"

abbreviation iedges :: 
  "IGraph \<Rightarrow> IEdge_Id \<Rightarrow> IEdge"
where 
  "iedges G \<equiv> snd (snd G)"

abbreviation val_d :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> int"
where 
  "val_d f v \<equiv> sint (fst (f v))"

abbreviation val_n :: 
  "IEInt \<Rightarrow> IVertex \<Rightarrow> 32 word"
where 
  "val_n f v \<equiv> fst (f v)"

fun bool :: 
  "32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

abbreviation is_inf_d :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> int"
where 
  "is_inf_d f v \<equiv>  sint (snd (f v))"

abbreviation is_inf_n :: 
  "IEInt \<Rightarrow> IVertex \<Rightarrow> 32 word"
where 
  "is_inf_n f v \<equiv>  (snd (f v))"

(* Make List - makes a list containing the result of a function *)

fun mk_list' :: 
  "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> 'b list" 
where 
  "mk_list' n f = map f (map of_nat [0..<n])"

fun mk_list'_int :: 
  "nat \<Rightarrow> (32 signed word \<Rightarrow> 'b) \<Rightarrow> 'b list" 
where 
  "mk_list'_int n f = map f (map of_int [0..<n])"

fun mk_list'_temp :: 
  "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b list" 
where 
  "mk_list'_temp 0 _ _ = []" |
  "mk_list'_temp (Suc x) f i = (f (of_nat i)) # mk_list'_temp x f (Suc i)"

(* Make graph lists *)
fun mk_iedge_list :: 
  "IGraph \<Rightarrow> IEdge list"
where 
  "mk_iedge_list G = mk_list' (unat (iedge_cnt G)) (iedges G)"

fun mk_inum_list :: 
  "IGraph \<Rightarrow> IEInt \<Rightarrow> (32 word \<times> 32 word) list"
where 
  "mk_inum_list G num = mk_list' (unat (ivertex_cnt G)) num"
  
fun mk_ipedge_list :: 
  "IGraph \<Rightarrow> IPEdge \<Rightarrow> 32 word list"
where
  "mk_ipedge_list G pedge = mk_list' (unat (ivertex_cnt G)) pedge"

fun mk_idist_list :: 
  "IGraph \<Rightarrow> IENInt \<Rightarrow> (32 signed word \<times> 32 signed word) list"
where
  "mk_idist_list G dis = mk_list' (unat (ivertex_cnt G)) dis"

fun mk_icost_list :: 
  "IGraph \<Rightarrow> ICost \<Rightarrow> 32 signed word list"
where
  "mk_icost_list G cost = mk_list' (unat (iedge_cnt G)) cost"

(* Equate to Implementation *)

lemma sint_ucast: 
  "sint (ucast (x ::word32) :: sword32) = sint x"
  by (clarsimp simp: sint_uint uint_up_ucast is_up)

lemma long_ucast:
  "unat (ucast (x ::word32) :: word64) = unat x"
  by (simp add: is_up uint_up_ucast unat_def)

fun to_edge :: 
  "IEdge \<Rightarrow> Edge_C"
where
  "to_edge (u,v) = Edge_C u v"

lemma s_C_pte[simp]:
  "first_C (to_edge e) = fst e"
  by (cases e) auto

lemma t_C_pte[simp]:
  "second_C (to_edge e) = snd e"
  by (cases e) auto

fun cast_long :: 
  "32 word \<Rightarrow> 64 word"
where 
  "cast_long x = ucast x"

fun cast_signed_long ::
  "32 signed word \<Rightarrow> 64 signed word"
  where
  "cast_signed_long x = scast x"

fun to_enint :: 
  "(32 signed word \<times> 32 signed word) \<Rightarrow> ENInt_C"
where
  "to_enint p = ENInt_C (fst p) (snd p)"

fun to_eint :: 
  "(32 word \<times> 32 word) \<Rightarrow> EInt_C"
where
  "to_eint p = EInt_C (fst p) (snd p)"

lemma EInt_val_C_pte[simp]:
  "EInt_C.val_C (to_eint p) = fst p"
  by (case_tac "p") auto

lemma EInt_isInf_C_pte[simp]:
  "EInt_C.isInf_C (to_eint p) = snd p"
  by (cases p) auto

lemma ENInt_val_C_pte[simp]:
  "ENInt_C.val_C (to_enint p) = fst p"
  by (case_tac "p") auto

lemma ENInt_isInf_C_pte[simp]:
  "ENInt_C.isInf_C (to_enint p) = snd p"
  by (cases p) auto

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
  "is_numm h iG iN p \<equiv> 
        arrlist (\<lambda>p. heap_EInt_C h p) (\<lambda>p. is_valid_EInt_C h p) 
        (map to_eint (mk_inum_list iG iN)) p"

definition is_pedge
where
  "is_pedge h iG iP (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_ipedge_list iG iP) p"

definition is_dist
where
  "is_dist h iG iD p \<equiv> 
        arrlist (\<lambda>p. heap_ENInt_C h p) (\<lambda>p. is_valid_ENInt_C h p) 
        (map to_enint (mk_idist_list iG iD)) p"
                              
(* the following needs clarification... *)
definition is_cost
where
  "is_cost h iG iC (p :: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. UCAST(32 \<rightarrow> 32 signed) (heap_w32 h (ptr_coerce p))) 
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_icost_list iG iC) p"

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

definition no_loops :: 
  "('a, 'b) pre_digraph \<Rightarrow> bool" 
where
  "no_loops G \<equiv> \<forall>e \<in> arcs G. tail G e \<noteq> head G e"

definition abs_IGraph :: 
  "IGraph \<Rightarrow> (32 word, 32 word) pre_digraph" 
where
  "abs_IGraph G \<equiv> \<lparr> verts = {0..<ivertex_cnt G}, arcs = {0..<iedge_cnt G},
    tail = fst o iedges G, head = snd o iedges G \<rparr>"

lemma verts_absI[simp]: "verts (abs_IGraph G) = {0..<ivertex_cnt G}"
  and edges_absI[simp]: "arcs (abs_IGraph G) = {0..<iedge_cnt G}"
  and start_absI[simp]: "tail (abs_IGraph G) e = fst (iedges G e)"
  and target_absI[simp]: "head (abs_IGraph G) e = snd (iedges G e)"
  by (auto simp: abs_IGraph_def)

definition abs_ICost :: 
  "(IEdge_Id \<Rightarrow> 32 signed word) \<Rightarrow> IEdge_Id \<Rightarrow> real"
where
  "abs_ICost c e \<equiv> real_of_int (sint (c e))"

definition abs_IDist :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> ereal"
where
  "abs_IDist d v \<equiv> if sint (snd (d v)) > 0 then PInfty
         else if sint (snd (d v)) < 0 then MInfty else
         real_of_int (sint (fst (d v)))"

definition abs_INum :: 
  "IEInt \<Rightarrow> IVertex \<Rightarrow> enat"
where
  "abs_INum n v \<equiv> if snd (n v) \<noteq> 0 then \<infinity> else unat (fst (n v))"

definition abs_IPedge :: 
  "IPEdge \<Rightarrow> IVertex \<Rightarrow> 32 word option" 
where
  "abs_IPedge p v \<equiv> if msb (p v) then None else Some (p v)"

lemma None_abs_pedgeI[simp]:
  "(abs_IPedge p v = None) = msb (p v)"
  using abs_IPedge_def by auto

lemma Some_abs_pedgeI[simp]: 
  "(\<exists>e. abs_IPedge p v = Some e) =  (~ (msb (p v)))"
  using None_not_eq None_abs_pedgeI 
  by (metis abs_IPedge_def)

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
  assumes a1: "real (unat y) + real (unat z) \<le> real (unat (max_word :: 32 word)) \<and> 
               real(unat x) \<le> real (unat y) + real (unat z)"
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
  by (metis (no_types, hide_lams) assms is_up len_of_word_comparisons(2) unat_leq_plus_64 
            uint_up_ucast unat_def)

lemma unat_plus_less_two_power_length:
  assumes len: "len_of TYPE('a::len) < len_of TYPE('b::len)"
  shows "unat (C:: 'a word) + unat (D:: 'a word) < (2::nat) ^ LENGTH('b)"
proof -
  have bounded: "uint C < 2 ^ LENGTH('a)" "uint D < (2 :: int) ^ LENGTH('a)"
    by (insert uint_bounded)
have unat_bounded: "unat C < 2 ^ LENGTH('a)" "unat D < (2 :: nat) ^ LENGTH('a)"
  by simp+
  have suc_leq: "Suc (len_of (TYPE('a)::'a itself)) \<le> len_of (TYPE('b)::'b itself)"
    using len Suc_leI by blast
  then have two_power_suc_leq: "(2::nat) ^ (len_of (TYPE('a)::'a itself) + 1) \<le> 
        2 ^ len_of (TYPE('b)::'b itself)"
    by (metis (no_types) One_nat_def add.right_neutral add_Suc_right 
             power_increasing_iff rel_simps(49) rel_simps(9))
  have "(2::nat) ^ (LENGTH ('a) + 1) = (2 ^ LENGTH ('a)) + (2 ^ LENGTH ('a))" 
    by auto
  then have "unat (C:: 'a word) + unat (D:: 'a word) < (2::nat) ^ (LENGTH ('a) + 1)"
    using unat_bounded by linarith  
  thus ?thesis using two_power_suc_leq 
    by linarith
qed

lemma abstract_val_ucast_add_strict_upcast:
    "\<lbrakk> len_of TYPE('a::len) < len_of TYPE('b::len);
       abstract_val P C' unat C; abstract_val P D' unat D \<rbrakk>
            \<Longrightarrow>  abstract_val P (C' + D') unat 
                    ((ucast (C :: 'a word) :: 'b word) +
                      ucast (D :: 'a word) :: 'b word)"
  apply (clarsimp simp: is_up unat_ucast_upcast ucast_def )
  apply (clarsimp simp:  word_of_int_def unat_word_ariths(1))
  apply (frule unat_plus_less_two_power_length[where C=C and D=D]) 
  by (metis (mono_tags, hide_lams) unat_of_nat_eq 
        add.right_neutral zero_less_power
        unat_plus_less_two_power_length uint_inverse 
        uint_mod_same uint_nat unat_of_nat zero_less_numeral) 
lemmas word_add_strict_up_cast_no_overflow_32_64 = 
      abstract_val_ucast_add_strict_upcast
        [unfolded abstract_val_def,
          OF word_abs_base(18) impI, where P=True, simplified]
lemma word_add_cast_up_no_overflow: 
  "unat y + unat z = unat (UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z)"
  using word_add_strict_up_cast_no_overflow_32_64 by blast
  
lemma add_ucast_no_overflow_64: (* add_ucast_no_overflow *)
  fixes x y z :: "word32"
  assumes a1: "unat x \<le> unat y + unat z"
  shows "(UCAST(32 \<rightarrow> 64) x) \<le> (UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z)"
  apply (insert a1) 
  apply (subgoal_tac "unat (UCAST(32 \<rightarrow> 64) x) \<le> 
                      unat (UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z)")
   using word_le_nat_alt apply blast
  apply (subst word_add_cast_up_no_overflow[symmetric])
  using long_ucast by auto

lemma add_ucast_no_overflow_unat:
  fixes x y z :: "word32"
  shows "(UCAST(32 \<rightarrow> 64) x = UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z) = 
         (unat x = unat y + unat z)"
proof -
  have "(UCAST(32 \<rightarrow> 64) x = UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z) \<longrightarrow> 
         unat x = unat y + unat z"
    by (metis (mono_tags, hide_lams) is_up le_add_same_cancel1 
              len_of_word_comparisons(2) add_ucast_no_overflow_64 uint_up_ucast unat_def 
              unat_plus_simple zero_le)
  moreover 
  have "unat x = unat y + unat z \<longrightarrow> 
        (UCAST(32 \<rightarrow> 64) x = UCAST(32 \<rightarrow> 64) y + UCAST(32 \<rightarrow> 64) z)"
    by (metis (mono_tags, hide_lams) is_up len_of_word_comparisons(2) 
              uint_up_ucast unat_def word_arith_nat_add word_unat.Rep_inverse)
  ultimately show ?thesis by blast
qed

lemma signed_overflow:
  fixes x :: "32 signed word" and y :: "32 signed word"
  shows "sint(x) + sint(y) \<le> 9223372036854775807"
proof-
  have "sint(x) \<le> 2147483647"
    using INT_MAX_def by auto
  then have "sint(y) \<le> 2147483647"
    using INT_MAX_def by auto
  then have "sint(x) + sint(y) \<le> 4294967294"
    using \<open>sint x \<le> 2147483647\<close> by linarith
  show ?thesis
    using \<open>sint x + sint y \<le> 4294967294\<close> by linarith
qed

lemma signed_underflow:
  fixes x :: "32 signed word" and y :: "32 signed word"
  shows "-9223372036854775808 \<le> sint(x) + sint(y)"
proof-
  have "-2147483648 \<le> sint(x)"
    using INT_MIN_def by auto
  then have "-2147483648 \<le> sint(y)"
    using INT_MIN_def by auto
  then have "-4294967296 \<le> sint(x) + sint(y)"
    using \<open>- 2147483648 \<le> sint x\<close> by linarith
  show ?thesis
    using \<open>-4294967296 \<le> sint(x) + sint(y)\<close> by linarith
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

lemma arrlist_d_heap:
  "\<lbrakk>arrlist h v (map (iL \<circ> (of_int \<circ> int)) [0..<unat n]) l; 
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

lemma two_comp_to_enint_arrlist_d_heap:
  "\<lbrakk> arrlist h v (map (to_enint \<circ> (iL \<circ> (of_int \<circ> int))) [0..<unat n]) l;
  i < n\<rbrakk> \<Longrightarrow> to_enint (iL i) = h (l +\<^sub>p (int (unat i)))" 
  using arrlist_d_heap
  by (metis (no_types, hide_lams) comp_apply comp_assoc)
 
lemma head_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  snd ((iedges iG) e) = second_C (h (ep +\<^sub>p (uint e)))" 
  using two_comp_arrlist_heap to_edge.simps t_C_pte by (metis uint_nat)

lemma tail_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  fst ((iedges iG) e) =  first_C (h (ep +\<^sub>p  (uint e)))" 
  using two_comp_arrlist_heap to_edge.simps s_C_pte uint_nat by metis

lemma val_n_heap:
  "\<lbrakk>arrlist h v (map (to_eint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  val_n f e = EInt_C.val_C (h (ep +\<^sub>p (uint e)))" 
  using two_comp_arrlist_heap to_eint.simps EInt_val_C_pte by (metis uint_nat)

lemma is_inf_n_heap:
  "\<lbrakk>arrlist h v (map (to_eint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  is_inf_n f e =  EInt_C.isInf_C (h (ep +\<^sub>p (uint e)))" 
  using two_comp_arrlist_heap to_eint.simps EInt_isInf_C_pte by (metis uint_nat)

lemma val_d_heap:
  "\<lbrakk>arrlist h v (map (to_enint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  val_d f e = sint (ENInt_C.val_C (h (ptr_coerce (ep +\<^sub>p (uint e)))))"
  using to_eint.simps ENInt_val_C_pte 
  by (metis int_unat ptr_coerce_id two_comp_arrlist_heap)

lemma is_inf_d_heap:
  "\<lbrakk>arrlist h v (map (to_enint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  is_inf_d f e =  sint (ENInt_C.isInf_C (h (ep +\<^sub>p (uint e))))"
  using to_eint.simps  ENInt_isInf_C_pte
  by (metis int_unat two_comp_arrlist_heap)

definition is_wellformed_inv :: "IGraph \<Rightarrow> 32 word \<Rightarrow> bool" where
  "is_wellformed_inv G i \<equiv> \<forall>k < i. ivertex_cnt G > fst (iedges G k)
                                 \<and> ivertex_cnt G > snd (iedges G k)"

declare arrlist_nth [simp]
declare if_split_asm [split]

lemma is_wellformed_spc':
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g) \<rbrace>
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
     apply (simp, safe) 
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
         apply simp
        apply (metis (mono_tags, hide_lams) diff_diff_add 
                diff_self_eq_0 eq_iff_diff_eq_0 measure_unat not_less0 
                word_less_nat_alt zero_less_diff)
       apply (simp add: uint_nat unat_mono)+
   apply wp 
  apply simp
  done

definition trian_inv :: "IGraph \<Rightarrow> IENInt \<Rightarrow> ICost \<Rightarrow> 32 word \<Rightarrow> bool" where
  "trian_inv G d c m \<equiv> 
    \<forall>i < m. (is_inf_d d (fst (iedges G i)) = 0 \<longrightarrow> 
              (is_inf_d d (snd (iedges G i)) \<le> 0 \<and> (is_inf_d d (snd (iedges G i)) = 0 \<longrightarrow> 
              val_d d (snd (iedges G i)) \<le> val_d d (fst (iedges G i)) + sint (c i)))) \<and>
            (is_inf_d d (fst (iedges G i)) < 0 \<longrightarrow> is_inf_d d (snd (iedges G i)) < 0)"

lemma trian_inv_step:
  assumes i_less_max: "i < (max_word::32 word)"
  shows "trian_inv G d c (i + 1) \<longleftrightarrow> trian_inv G d c i \<and>
  ((is_inf_d d (fst (iedges G i)) = 0 \<longrightarrow> 
     (is_inf_d d (snd (iedges G i)) \<le> 0 \<and> (is_inf_d d (snd (iedges G i)) = 0 \<longrightarrow> 
     val_d d (snd (iedges G i)) \<le> val_d d (fst (iedges G i)) + sint (c i)))) \<and>
   (is_inf_d d (fst (iedges G i)) < 0 \<longrightarrow> is_inf_d d (snd (iedges G i)) < 0))"
  unfolding trian_inv_def apply safe
  by (metis i_less_max less_x_plus_1 max_word_max not_le)+

lemma trian_inv_le:
  assumes leq: "j \<le> i" 
  assumes trian_i: "trian_inv G d c i"
  shows "trian_inv G d c j"
  using assms 
  by (induct j) (auto simp add: trian_inv_def)

lemma cost_abs_C_equiv:
  fixes ee :: "32 word" and s :: lifted_globals
  assumes a1: "arrlist (\<lambda>p. UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) p))) 
                       (\<lambda>p. is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) p)) (map (iC \<circ> of_nat) 
                        [0..<unat (num_edges_C (heap_Graph_C s g))]) c"
  assumes a2: "fst (snd iG) = num_edges_C (heap_Graph_C s g)"
  assumes a3: "ee < num_edges_C (heap_Graph_C s g)"
  shows "iC ee = UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (c +\<^sub>p uint ee)))"
proof -
  show ?thesis
    by (metis (no_types) a1 a3 arrlist_heap uint_nat)
qed
lemma enat_abs_C_equiv:
  fixes ee :: "32 word" and s :: lifted_globals
  assumes a1: "ee < num_edges_C (heap_Graph_C s g)"
  assumes a2: "arrlist (heap_EInt_C s) (is_valid_EInt_C s) (map (to_eint \<circ> (iL \<circ> of_nat)) 
               [0..<unat (num_vertices_C (heap_Graph_C s g))]) l"
  assumes a3: "fst iG = num_vertices_C (heap_Graph_C s g)"
  assumes a4: "fst (snd iG) = num_edges_C (heap_Graph_C s g)"
  assumes a5: "arrlist (heap_Edge_C s) (is_valid_Edge_C s) (map (to_edge \<circ> (snd (snd iG) \<circ> of_nat)) 
               [0..<unat (num_edges_C (heap_Graph_C s g))]) (arcs_C (heap_Graph_C s g))"
  assumes a6: "\<forall>ee < num_edges_C (heap_Graph_C s g). fst (snd (snd iG) ee) < num_vertices_C (heap_Graph_C s g)"
  shows "fst (iL (fst (snd (snd iG) ee))) = 
         val_C (heap_EInt_C s (l +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))"
proof -
  show ?thesis using a6 a5 a4 a3 a2 a1 s_C_pte two_comp_to_edge_arrlist_heap two_comp_to_eint_arrlist_heap EInt_val_C_pte by metis
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
     apply simp
     apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI)
        apply fast
       apply (unfold trian_inv_def is_dist_def is_cost_def is_graph_def)[1]
       apply clarsimp
       apply (rule_tac x=ee in exI)
       apply safe[1]
            apply (metis (no_types, hide_lams) is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat Word_Lemmas.sint_0)
           apply (metis not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
          apply (metis not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
         apply (subgoal_tac "snd (iD (fst (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
          apply simp
         apply (metis (no_types, hide_lams) Word_Lemmas.sint_0 is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
    (*apply (metis is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)*)
        apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
         apply simp
        apply (metis not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
       apply (metis not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
      apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI)
          apply blast
         apply (unfold trian_inv_def is_dist_def is_cost_def is_graph_def)[1]
         apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))) = 0")
          apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))) = 0") apply clarsimp
           apply (rule_tac x=ee in exI)
           apply (rule conjI)
            apply blast
           apply (rule disjI1)
           apply (rule conjI)
            apply (subgoal_tac "snd (iD (fst (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
             apply simp
            apply (metis (no_types, hide_lams) Word_Lemmas.sint_0 is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
           apply (rule impI, rule conjI)
            apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
             apply simp
            apply (metis (no_types, hide_lams) Word_Lemmas.sint_0 is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
           apply (subgoal_tac "heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee) = to_edge (snd (snd iG) ee)")
            apply (metis not_le ptr_coerce_id cost_abs_C_equiv s_C_pte t_C_pte val_d_heap wellformed_iGraph)
           apply(simp add: two_comp_to_edge_arrlist_heap uint_nat)
          apply argo
         apply simp
        apply (rule conjI, rule impI, rule conjI)
          apply blast
         apply rule
          apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
           apply (subgoal_tac "ee < (max_word::32 word)") 
            apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
            apply clarsimp
            apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1] 
            apply clarsimp
            apply (subgoal_tac "heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee) = to_edge (snd (snd iG) ee)")
             apply (subgoal_tac "fst (snd (snd iG) ee) < fst iG")
              apply (subgoal_tac "snd (snd (snd iG) ee) < fst iG")
               apply (metis Word.sint_0 less_irrefl not_le ptr_coerce_id s_C_pte t_C_pte cost_abs_C_equiv is_inf_d_heap val_d_heap)
              apply (metis wellformed_iGraph)
             apply (metis wellformed_iGraph)
            apply (metis two_comp_to_edge_arrlist_heap uint_nat)
           apply (simp add:less_le not_le, meson less_le max_word_max not_le)
          apply (simp add: inc_le is_graph_def, blast intro: inc_le)
         apply rule
          apply (metis inc_le is_graph_def)
         apply rule
          apply blast
         apply rule
          apply blast
         apply rule
          apply blast
         apply rule
          apply (metis (no_types, hide_lams) is_graph_def shortest_path_neg_checker.unat_minus_plus1_less)
         apply rule
          apply (simp add: is_graph_def)
          apply argo
         apply rule
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply rule
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (simp add: is_graph_def)
         apply (force simp: signed_overflow)
        apply rule
         apply (force simp: signed_overflow)
        apply rule
         apply (force simp: signed_underflow)
        apply rule
         apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply rule+
         apply blast
        apply rule
         apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
          apply (subgoal_tac "ee < (max_word::32 word)") 
           apply (subst trian_inv_step, blast) 
           apply (rule conjI, blast) 
           apply (rule conjI, rule impI, rule conjI)
             apply (clarsimp, unfold is_graph_def is_dist_def)[1]
             apply (subgoal_tac "snd (iD (fst (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
              apply (simp, metis not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
             apply (simp add: uint_nat)
            apply (unfold is_graph_def is_dist_def is_cost_def)[1]
            apply (subgoal_tac "sint (snd (iD (snd (snd (snd iG) ee)))) \<noteq> 0")
             apply blast
            apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
             apply (simp add:uint_nat)
            apply clarsimp
            apply (metis t_C_pte word_sint.Rep_inject is_inf_d_heap two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
           apply (subgoal_tac "snd (iD (fst (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))")
            apply simp
           apply (unfold is_graph_def is_dist_def, clarsimp)[1]
           apply (metis s_C_pte word_sint.Rep_inject is_inf_d_heap two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
          apply (metis max_word_max not_le word_le_less_eq)
         apply (metis inc_le is_graph_def)
        apply rule
         apply (metis inc_le is_graph_def)
        apply (rule, blast)
        apply (rule, blast)
        apply (rule, blast)
        apply (rule, metis (no_types, hide_lams) is_graph_def unat_minus_plus1_less)
        apply (rule, fastforce simp: is_graph_def)
        apply rule
         apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply rule
         apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (fastforce simp: is_graph_def)
       apply rule
        apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply rule
        apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply (fastforce simp: is_graph_def)
      apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply rule+
         apply blast
        apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
        apply clarsimp
        apply (rule_tac x=ee in exI)
        apply rule
         apply blast
        apply (metis not_le is_inf_d_heap s_C_pte t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
       apply rule+
         apply blast
        apply rule
         apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
          apply (subgoal_tac "ee < (max_word::32 word)") 
           apply (subst trian_inv_step, blast) 
           apply (rule conjI, blast) 
           apply (subgoal_tac "sint (snd (iD (fst (snd (snd iG) ee)))) < 0")
            apply (subgoal_tac "sint (snd (iD (snd (snd (snd iG) ee)))) < 0")
             apply linarith
            apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))")
             apply presburger
            apply (unfold is_graph_def is_cost_def is_dist_def)[1]
            apply clarsimp
            apply (metis is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat word_sint.Rep_inject)
           apply (subgoal_tac "snd (iD (fst (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))")
            apply argo
           apply (unfold is_graph_def is_cost_def is_dist_def)[1]
           apply clarsimp
           apply (metis (no_types, hide_lams) is_inf_d_heap wellformed_iGraph tail_heap uint_nat word_sint.Rep_inject)
          apply (metis max_word_max not_le word_le_less_eq)
         apply (metis inc_le is_graph_def)
        apply (rule, metis inc_le is_graph_def)
        apply (metis (no_types, hide_lams) is_graph_def unat_minus_plus1_less)
       apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply rule+
        apply blast
       apply rule
        apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
         apply (subgoal_tac "ee < (max_word::32 word)") 
          apply (subst trian_inv_step, blast) 
          apply (rule conjI, blast) 
          apply (subgoal_tac "sint (snd (iD (fst (snd (snd iG) ee)))) > 0")
           apply linarith
          apply (subgoal_tac "snd (iD (fst (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))")
           apply (unfold is_graph_def is_cost_def is_dist_def)[1]
           apply clarsimp
           apply (simp add: less_le)
          apply (unfold is_graph_def is_cost_def is_dist_def)[1]
          apply clarsimp
          apply (metis is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat word_sint.Rep_inject)
         apply (metis max_word_max not_le word_le_less_eq)
        apply (metis inc_le is_graph_def)
       apply (rule, metis inc_le is_graph_def)
       apply (metis (no_types, hide_lams) is_graph_def unat_minus_plus1_less)
      apply rule
       apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (subgoal_tac  "\<not> ee < fst (snd iG)")
     apply (subgoal_tac "fst (snd iG) = ee")
      apply simp
     apply (metis word_le_less_eq)
    apply (metis is_graph_def)
   apply wp
  apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
  apply force
  done

definition just_inv :: 
  "IGraph \<Rightarrow> IENInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> 32 word \<Rightarrow> bool" where
  "just_inv G d c s n p k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> is_inf_n n v = 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        (is_inf_d d v > 0 \<longleftrightarrow> is_inf_d d (fst (iedges G e)) > 0) \<and>
        (is_inf_d d v < 0 \<longleftrightarrow> is_inf_d d (fst (iedges G e)) < 0) \<and>
        (is_inf_d d v = 0 \<longrightarrow> 
         val_d d v = val_d d (fst (iedges G e)) + sint (c e)) \<and>
        is_inf_n n (fst (iedges G e)) = 0 \<and>
        cast_long (val_n n v) = cast_long (val_n n (fst (iedges G e))) + 1)"

lemma just_inv_step:
  assumes v_less_max: "v < (max_word::32 word)"
  shows "just_inv G d c s n p (v + 1) \<longleftrightarrow> just_inv G d c s n p v
    \<and> (v \<noteq> s \<and> is_inf_n n v = 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and> 
        v = snd (iedges G e) \<and>
        (is_inf_d d v > 0 \<longleftrightarrow> is_inf_d d (fst (iedges G e)) > 0) \<and>
        (is_inf_d d v < 0 \<longleftrightarrow> is_inf_d d (fst (iedges G e)) < 0) \<and>
        (is_inf_d d v = 0 \<longrightarrow>
         val_d d v = val_d d (fst (iedges G e)) + sint (c e)) \<and>
        is_inf_n n (fst (iedges G e)) = 0 \<and>
        cast_long (val_n n v) = cast_long (val_n n (fst (iedges G e))) + 1))"
  unfolding just_inv_def apply safe
  by (metis less_x_plus_1 max_word_max not_le v_less_max)+
                  
  
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
  shows "iP vv = heap_w32 s (ptr_coerce (p +\<^sub>p int (unat vv)))"
proof - 
  have "\<forall>w. heap_w32 s (ptr_coerce (p +\<^sub>p int (unat w))) = iP w \<or> \<not> w < fst iG"
    using a2 a1 heap_ptr_coerce unat_0 by fastforce
  show ?thesis
    using a1 a3 arrlist_heap by blast
qed

lemma pedge_abs_C_equiv_2:
  fixes vv :: "32 word" and s :: lifted_globals
  assumes a1: "arrlist (\<lambda>p. heap_w32 s (ptr_coerce p)) (\<lambda>p. is_valid_w32 s (ptr_coerce p)) (map (iP \<circ> of_nat) [0..<unat (num_vertices_C (heap_Graph_C s g))]) p"
  assumes a2: "fst iG = num_vertices_C (heap_Graph_C s g)"
  assumes a3: "vv < num_vertices_C (heap_Graph_C s g)"
  shows "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))"
proof - 
  have "\<forall>w. heap_w32 s (ptr_coerce (p +\<^sub>p int (unat w))) = iP w \<or> \<not> w < fst iG"
    using a2 a1 heap_ptr_coerce unat_0 by fastforce
  show ?thesis
    by (metis (no_types) a1 a3 int_unat arrlist_heap)
qed

lemma pedge_abs_C_equiv_sint:
  fixes vv :: "32 word" and s :: lifted_globals
  assumes a1: "is_graph s iG g"
  assumes a2: "vv < num_vertices_C (heap_Graph_C s g)"
  assumes a3: "arrlist (\<lambda>p. heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) p)) (\<lambda>p. is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) p)) (map (iP \<circ> of_nat) [0..<unat (fst iG)]) p"
  shows "sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))::32 signed word) = sint (iP vv)"
proof -
  have "num_vertices_C (heap_Graph_C s g) = fst iG"
    using a1 by (simp add: is_graph_def)
  then show ?thesis
    using a3 a2 by (metis (no_types) pedge_abs_C_equiv sint_ucast uint_nat)
qed

lemma  valid_pedge:
  fixes vv :: "32 word" and s :: lifted_globals
  assumes a1: "is_graph s iG g"
  assumes a2: "vv < fst iG \<longrightarrow> vv \<noteq> sc \<and> snd (iN vv) = 0 \<longrightarrow> 0 \<le> sint (iP vv) \<and> iP vv < fst (snd iG) \<and> vv = snd (snd (snd iG) (iP vv)) \<and> (0 < sint (snd (iD vv))) = (0 < sint (snd (iD (fst (snd (snd iG) (iP vv)))))) \<and> (sint (snd (iD vv)) < 0) = (sint (snd (iD (fst (snd (snd iG) (iP vv))))) < 0) \<and> (snd (iD vv) = 0 \<longrightarrow> sint (fst (iD vv)) = sint (fst (iD (fst (snd (snd iG) (iP vv))))) + sint (iC (iP vv))) \<and> snd (iN (fst (snd (snd iG) (iP vv)))) = 0 \<and> UCAST(32 \<rightarrow> 64) (fst (iN vv)) = UCAST(32 \<rightarrow> 64) (fst (iN (fst (snd (snd iG) (iP vv))))) + (1::64 word)"
  assumes a3: "vv \<noteq> sc"
  assumes a4: "vv < num_vertices_C (heap_Graph_C s g)"
  assumes a5: "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = 0"
  assumes a6: "arrlist (heap_EInt_C s) (is_valid_EInt_C s) (map (to_eint \<circ> (iN \<circ> of_nat)) [0..<unat (fst iG)]) n"
  shows "iP vv < num_edges_C (heap_Graph_C s g)"
  by (metis (no_types, hide_lams) a1 a2 a3 a4 a5 a6 is_graph_def is_inf_n_heap)

lemma is_inf_distance_eq:
  fixes vv :: "32 word" and s :: lifted_globals
  assumes a1: "\<not> num_edges_C (heap_Graph_C s g) \<le> heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))"
  assumes a2: "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))"
  assumes a3: "arrlist (heap_ENInt_C s) (is_valid_ENInt_C s) (map (to_enint \<circ> (iD \<circ> of_nat)) [0..<unat (num_vertices_C (heap_Graph_C s g))]) d"
  assumes b1: "fst iG = num_vertices_C (heap_Graph_C s g)"
  assumes a4: "arrlist (heap_Edge_C s) (is_valid_Edge_C s) (map (to_edge \<circ> (snd (snd iG) \<circ> of_nat)) [0..<unat (num_edges_C (heap_Graph_C s g))]) (arcs_C (heap_Graph_C s g))"
  assumes b2:"\<forall>e<num_edges_C (heap_Graph_C s g). fst (snd (snd iG) e) < num_vertices_C (heap_Graph_C s g)"
  shows "ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))))) = snd (iD (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))))"
proof -
  show ?thesis
    using a4 a3 a2 a1 b2 by (metis not_le is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap uint_nat word_sint.Rep_inject)
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
     apply simp
     apply rule+
         apply blast
        apply safe[1]
        apply (unfold just_inv_def is_pedge_def is_numm_def, clarsimp)[1]
        apply (erule_tac x=vv in allE)
        apply (simp add: is_graph_def is_inf_n_heap pedge_abs_C_equiv_sint)
       apply rule+
         apply blast
        apply safe[1]
        apply (unfold just_inv_def is_pedge_def is_numm_def, clarsimp)[1]
        apply (erule_tac x=vv in allE)
        apply (subgoal_tac "num_vertices_C (heap_Graph_C s g) = fst iG")
         apply (subgoal_tac "\<forall>w f p. (((snd (iN vv) = 0 \<or> vv = w) \<or> f vv < num_edges_C (heap_Graph_C s p)) \<or> 
                             \<not> is_graph s iG p) \<or> \<not> vv < num_vertices_C (heap_Graph_C s p)")
          apply (subgoal_tac "num_edges_C (heap_Graph_C s g) = fst (snd iG)")
           apply (metis (no_types) not_le arrlist_heap uint_nat)
          apply (force simp: is_graph_def)
         apply (metis is_inf_n_heap)
        apply (force simp: is_graph_def)
       apply rule+
          apply blast
         apply (unfold just_inv_def is_pedge_def is_numm_def is_graph_def, clarsimp)[1]
         apply (rule_tac x=vv in exI)
         apply (rule, blast)
         apply (rule, blast)
         apply rule+
          apply (simp add: is_graph_def is_inf_n_heap)
         apply rule+ 
          apply (metis (no_types) heap_ptr_coerce two_comp_to_edge_arrlist_heap t_C_pte uint_nat word_zero_le)
         apply (metis (no_types) heap_ptr_coerce t_C_pte two_comp_to_edge_arrlist_heap uint_nat word_zero_le)
        apply rule+
           apply blast
          apply (unfold is_dist_def just_inv_def is_numm_def is_pedge_def is_graph_def)[1]
          apply (clarsimp, rule_tac x=vv in exI)
          apply (rule, blast)
          apply (rule, blast)
          apply rule+
           apply (metis EInt_isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
          apply rule+ 
           apply (subgoal_tac "\<not> 0 < sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
            apply (simp add: is_inf_d_heap uint_nat)
           apply (metis (no_types) heap_ptr_coerce is_inf_d_heap s_C_pte wellformed_iGraph 
      two_comp_to_edge_arrlist_heap uint_nat word_zero_le)
          apply (subgoal_tac "0 < sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
           apply (simp add: is_inf_d_heap uint_nat)
          apply (metis (no_types) heap_ptr_coerce is_inf_d_heap s_C_pte wellformed_iGraph 
      two_comp_to_edge_arrlist_heap uint_nat word_zero_le)
         apply rule+
             apply blast 
            apply simp+
          apply rule+
             apply blast
            apply (unfold is_dist_def just_inv_def is_numm_def is_pedge_def is_cost_def is_graph_def)[1]
            apply (clarsimp, rule_tac x=vv in exI)
            apply (rule, blast)
            apply (rule, blast)
            apply rule+
             apply (metis EInt_isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
            apply rule+
             apply (subgoal_tac "heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p int (unat vv))) = iP vv")
              apply (metis (no_types) EInt_isInf_C_pte s_C_pte two_comp_to_eint_arrlist_heap wellformed_iGraph 
      two_comp_to_edge_arrlist_heap uint_nat)
             apply (metis (no_types) heap_ptr_coerce word_zero_le)
            apply (metis is_inf_d_heap)
           apply rule+
              apply blast
             apply (unfold is_dist_def just_inv_def is_numm_def is_pedge_def is_graph_def)[1]
             apply (clarsimp, rule_tac x=vv in exI)
             apply (rule, blast)
             apply (rule, blast)
             apply rule
              apply (metis EInt_isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
             apply (rule impI)+
             apply (rule disjI2)+
             apply (subgoal_tac "(EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint vv))) = (fst (iN vv))")
              apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
               apply (subgoal_tac "(EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p 
                                    uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))))))))) = 
                                    (fst (iN (fst (snd (snd iG) (iP vv)))))")
                apply argo
               apply (metis (no_types, hide_lams) EInt_val_C_pte tail_heap two_comp_to_eint_arrlist_heap wellformed_iGraph uint_nat)
              apply (metis (no_types) heap_ptr_coerce uint_nat word_zero_le)
             apply (metis EInt_val_C_pte two_comp_to_eint_arrlist_heap uint_nat)
            apply rule+
              apply blast
             apply rule
              apply (subgoal_tac " vv + 1 \<le> fst iG")
               apply (subgoal_tac "vv < (max_word::32 word)")
                apply (subst just_inv_step, blast)
                apply (rule conjI, blast)
                apply clarsimp
                apply rule
                 apply (subgoal_tac "sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                      (p +\<^sub>p uint vv)))) = sint (iP vv)")
                  apply linarith
                 apply (simp add: is_pedge_def pedge_abs_C_equiv_sint)
                apply rule
                 apply (unfold is_pedge_def is_graph_def)[1]
                 apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                  apply simp
                 apply (fastforce intro: pedge_abs_C_equiv_2)
                apply rule
                 apply (unfold is_pedge_def is_graph_def)[1]
apply (subgoal_tac "snd (snd (snd iG) (iP vv)) = second_C (heap_Edge_C s
                              (arcs_C (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s 
                              (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))")
                  apply argo
                 apply (subgoal_tac "iP vv = heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))")
                  apply (subst head_heap[where iG=iG], fastforce, force)
                  apply argo
                 apply (fastforce intro: pedge_abs_C_equiv_2)
                apply rule+
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
                    apply argo
                   apply (unfold is_graph_def is_dist_def is_pedge_def wf_digraph_def)[1]
                   apply (subst tail_heap, force, simp)
                   apply (subst is_inf_d_heap, simp)
                    apply (simp add:uint_nat)
                    apply (metis not_le s_C_pte two_comp_to_edge_arrlist_heap)
                   apply argo
                  apply (unfold is_pedge_def is_graph_def)[1] 
                  apply (fastforce intro: pedge_abs_C_equiv_2)
                 apply (unfold is_dist_def is_graph_def)[1]
                 apply (subst is_inf_d_heap, fastforce, blast)
                 apply blast
                apply rule
                 apply (unfold is_graph_def is_dist_def is_pedge_def wf_digraph_def)[1]
                 apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                  apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
                   apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
                    apply linarith
                  apply (subst is_inf_d_heap, simp, blast)
                   apply blast
                  apply clarsimp
                  apply (subst tail_heap, blast, simp)
                  apply (metis (mono_tags, hide_lams) not_le is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap 
                         uint_nat word_sint.Rep_inject)
                 apply (fastforce intro: pedge_abs_C_equiv_2)
                apply rule
                 apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
                  apply fastforce
                 apply (unfold is_graph_def is_dist_def is_pedge_def wf_digraph_def)[1]
                 apply (subst is_inf_d_heap, simp, blast)
                 apply blast
                apply rule
                 apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                  apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p 
                                      uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))))) = 
                                      snd (iN (fst (snd (snd iG) (iP vv))))")
                   apply simp
                  apply (unfold is_graph_def is_numm_def is_pedge_def wf_digraph_def)[1]
                  apply (subst tail_heap, force, simp)
                  apply (subst is_inf_n_heap, simp) 
                   apply clarsimp
                   apply (metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap uint_nat)
                  apply argo
                 apply (unfold is_graph_def is_numm_def is_pedge_def wf_digraph_def)[1]
                 apply (fastforce intro: pedge_abs_C_equiv_2)
                 apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                  apply (subgoal_tac "EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p 
                                      uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))))) = 
                                      fst (iN (fst (snd (snd iG) (iP vv))))")
                  apply (subgoal_tac "EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint vv)) = fst (iN vv)")
                   apply argo
                  apply (unfold is_graph_def is_numm_def is_pedge_def wf_digraph_def)[1]
                  apply (subst val_n_heap, simp, blast, blast)
                 apply clarsimp
                 apply (unfold is_graph_def is_numm_def is_pedge_def wf_digraph_def)[1]
                 apply (subst tail_heap, force, simp)
                 apply (subst val_n_heap, simp)
                  apply clarsimp
                  apply (metis (no_types, hide_lams) not_le s_C_pte two_comp_to_edge_arrlist_heap uint_nat)
                 apply blast
                apply (unfold is_graph_def is_numm_def is_pedge_def wf_digraph_def)[1]
                apply (fastforce intro: pedge_abs_C_equiv_2)
                apply (metis max_word_max not_le word_le_less_eq)
               apply (metis inc_le is_graph_def)
              apply (metis (no_types, hide_lams) inc_le is_graph_def unat_minus_plus1_less)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
            apply rule
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply rule
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
           apply rule
            apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply rule
            apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply rule
            apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
         apply rule+
           apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
           apply clarsimp
           apply (erule_tac x=vv in allE)
           apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
            apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
             apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
              apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
               apply (metis Word.sint_0 less_le not_le word_sint.Rep_inject)
              apply (subst is_inf_n_heap, blast, blast, blast)
             apply (subst is_inf_d_heap, blast, blast, blast)
            apply clarsimp
            apply (subst tail_heap, blast, simp)
            apply (blast intro: is_inf_distance_eq)
           apply (blast intro: pedge_abs_C_equiv_2)
          apply rule+
             apply simp+
           apply rule+
             apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
             apply clarsimp
             apply (erule_tac x=vv in allE)
             apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
              apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
               apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                  (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                  (p +\<^sub>p uint vv)))))))) = snd (iN (fst (snd (snd iG) (iP vv))))")
                apply argo
               apply (metis (no_types, hide_lams) EInt_isInf_C_pte tail_heap two_comp_to_eint_arrlist_heap uint_nat)
              apply (subst is_inf_n_heap, blast, blast, blast)
             apply (blast intro: pedge_abs_C_equiv_2)
            apply rule+
              apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
             apply clarsimp
              apply (erule_tac x=vv in allE)
              apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
               apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
               apply (subgoal_tac "EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint vv)) = fst (iN vv)")
                apply (subgoal_tac "EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                    (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                    (p +\<^sub>p uint vv)))))))) = fst (iN (fst (snd (snd iG) (iP vv))))")
                  apply argo
                 apply (metis (no_types, hide_lams) EInt_val_C_pte tail_heap two_comp_to_eint_arrlist_heap uint_nat)
                apply (metis EInt_val_C_pte two_comp_to_eint_arrlist_heap uint_nat)
               apply (metis EInt_isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
              apply (blast intro: pedge_abs_C_equiv_2)
             apply rule+
               apply (subgoal_tac " vv + 1 \<le> fst iG")
                apply (subgoal_tac "vv < (max_word::32 word)")
                 apply (subst just_inv_step, blast)
                 apply (rule conjI, blast)
                 apply clarsimp
                 apply rule
                  apply (subgoal_tac "sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                      (p +\<^sub>p uint vv)))) = sint (iP vv)")
                   apply linarith
                  apply (simp add: is_pedge_def pedge_abs_C_equiv_sint)
                 apply rule
                  apply (unfold is_pedge_def is_graph_def)[1]
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply simp
                  apply (fastforce intro: pedge_abs_C_equiv_2)
                 apply rule
                  apply (unfold is_pedge_def is_graph_def)[1]
                  apply (subgoal_tac "snd (snd (snd iG) (iP vv)) = second_C (heap_Edge_C s
                              (arcs_C (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s 
                              (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))")
                   apply argo
                  apply (subgoal_tac "iP vv = heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))")
                   apply (subst head_heap[where iG=iG], fastforce, force)
                   apply argo
                  apply (fastforce intro: pedge_abs_C_equiv_2)
                 apply rule
                  apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
                    apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
                     apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
                      apply linarith
                     apply argo
                    apply (subst is_inf_d_heap, simp, blast, blast)
                   apply clarsimp
                   apply (subst tail_heap, blast, simp)
                   apply (metis not_le is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap uint_nat word_sint.Rep_inject)
                  apply (force intro: pedge_abs_C_equiv_2)
                 apply rule
                  apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
                    apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
                     apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
                      apply linarith
                     apply argo
                    apply (subst is_inf_d_heap, simp, blast, blast)
                   apply clarsimp
                   apply (subst tail_heap, blast, simp)
                   apply (metis not_le is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap uint_nat word_sint.Rep_inject)
                  apply (force intro: pedge_abs_C_equiv_2)
                 apply rule+
                  apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply clarsimp
                   apply (subst tail_heap, fastforce, simp)
                   apply (subst val_d_heap, blast, blast)
                   apply (subst val_d_heap, blast)
                    apply (metis Word.sint_0 shortest_path_neg_checker.is_inf_d_heap uint_eq_0 uint_lt_0)
                   apply (metis Word.sint_0 is_inf_d_heap uint_eq_0 uint_lt_0)
                  apply (force intro: pedge_abs_C_equiv_2)
                 apply rule
                  apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply clarsimp
                   apply (subst tail_heap, fastforce, simp)
                   apply (subst is_inf_n_heap, simp)
                    apply (metis not_le tail_heap)
                   apply blast
                  apply (force intro: pedge_abs_C_equiv_2)
                 apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                 apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                  apply clarsimp
                  apply (subst tail_heap, force, simp)
                  apply (subst val_n_heap, simp, blast)
                  apply (subst val_n_heap, simp)
                   apply (metis not_le tail_heap)
                  apply blast
                 apply (force intro: pedge_abs_C_equiv_2)
                apply (metis max_word_max not_le word_le_less_eq)
               apply (simp add: inc_le is_graph_def)
              apply (simp add: inc_le is_graph_def unat_minus_plus1_less)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
            apply rule
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply rule
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply rule+
             apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_pedge_def is_numm_def)[1]
             apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
              apply (subgoal_tac "snd (iN vv) = EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p int (unat vv)))")
               apply (subgoal_tac "sint (snd (iD vv)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
                apply (subgoal_tac "sint (fst (iD vv)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
                 apply (subgoal_tac "sint (fst (iD (fst (snd (snd iG) (iP vv))))) = 
                                    sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat (first_C (heap_Edge_C s 
                                      (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat (heap_w32 s 
                                      (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p int (unat vv))))))))))))") 
                  apply (subgoal_tac "sint (iC (iP vv)) = sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (c +\<^sub>p int (unat (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p int (unat vv)))))))))") 
                   apply simp
                   apply clarsimp
                  apply (metis cost_abs_C_equiv int_unat)
                 apply (subst tail_heap, force, metis)
                 apply (subst val_d_heap, simp)
                  apply (clarsimp, metis tail_heap wellformed_iGraph) 
                 apply (simp add: int_unat)
                apply (subst val_d_heap, simp, blast)
                apply (simp add: int_unat)  
               apply (subst is_inf_d_heap, simp, blast)
               apply (metis uint_nat)
              apply (subst is_inf_n_heap, simp, blast)
              apply (metis uint_nat)
             apply (force intro: pedge_abs_C_equiv_2)
            apply rule+
              apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_pedge_def is_numm_def)[1]
              apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
               apply (subgoal_tac "snd (iN vv) = EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p int (unat vv)))")
                apply (subgoal_tac "sint (snd (iD vv)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
                 apply (subgoal_tac "snd (iN (fst (snd (snd iG) (iP vv)))) = 
                                    EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C 
                                      (heap_Graph_C s g) +\<^sub>p int (unat (heap_w32 s 
                                      (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p int (unat vv)))))))))))")
                  apply metis
                 apply clarsimp
                 apply (subst tail_heap, blast, metis)
                 apply (subst is_inf_n_heap, blast)
                  apply (metis tail_heap wellformed_iGraph)
                 apply (simp add: uint_nat)
                apply (subst is_inf_d_heap, simp, force)
                apply (simp add: uint_nat)
               apply (subst is_inf_n_heap, simp, fast) 
               apply (simp add: uint_nat)
              apply (force intro: pedge_abs_C_equiv_2)
             apply rule+
               apply (unfold just_inv_def is_graph_def is_dist_def is_cost_def is_pedge_def is_numm_def)[1]
               apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))") 
                apply (subgoal_tac "snd (iN vv) = EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p int (unat vv)))")
                 apply (subgoal_tac "sint (snd (iD vv)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
                  apply (subgoal_tac "cast_long (fst (iN vv)) = UCAST(32 \<rightarrow> 64) (EInt_C.val_C (heap_EInt_C s (n +\<^sub>p int (unat vv))))")
                   apply (subgoal_tac "cast_long (fst (iN (fst (snd (snd iG) (iP vv))))) = UCAST(32 \<rightarrow> 64) 
                                       (EInt_C.val_C (heap_EInt_C s (n +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p int (unat (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p int (unat vv))))))))))))") 
                    apply metis
                   apply clarsimp
                   apply (subst tail_heap, blast, metis)
                   apply (subst val_n_heap, blast) 
                    apply (metis (no_types, hide_lams) s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat) 
                   apply (simp add:uint_nat)
                  apply (subst val_n_heap, simp, force)
                  apply (metis cast_long.simps uint_nat)
                 apply (subst is_inf_d_heap, simp, blast)
                 apply (simp add: uint_nat)
                apply (subst is_inf_n_heap, simp, blast)
                apply (simp add: uint_nat)
               apply (force intro: pedge_abs_C_equiv_2)
              apply rule+
                apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
                apply (subgoal_tac " vv + 1 \<le> fst iG")
                 apply (subgoal_tac "vv < (max_word::32 word)")
                  apply (subst just_inv_step, blast)
                  apply (rule conjI, blast)
                  apply clarsimp
                  apply rule+
                   apply (unfold just_inv_def)[1]
                   apply (subgoal_tac "sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                      (p +\<^sub>p uint vv)))) = sint (iP vv)")
                    apply (metis not_le uint_nat)
                   apply (metis (no_types) heap_ptr_coerce sint_ucast uint_nat word_zero_le) 
                  apply rule
                   apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                    apply (metis not_le uint_nat)
                   apply (fastforce intro: pedge_abs_C_equiv_2)
                  apply rule
                   apply (subgoal_tac "snd (snd (snd iG) (iP vv)) = second_C (heap_Edge_C s
                              (arcs_C (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s 
                              (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv)))))")
                    apply (metis uint_nat)
                   apply (subgoal_tac "iP vv = heap_w32 s (ptr_coerce (p +\<^sub>p uint vv))")
                    apply clarsimp 
                    apply (subst head_heap, blast)
                     apply (metis not_le uint_nat, fast)
                   apply (fastforce intro: pedge_abs_C_equiv_2)
                  apply rule
                   apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                   apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                    apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
                     apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
                      apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
                       apply (metis uint_nat)
                      apply (subst is_inf_n_heap, simp, blast, blast)
                     apply clarsimp
                     apply (metis Word_Lemmas.sint_0 is_inf_d_heap uint_nat)
                    apply (subst tail_heap, blast, simp) 
                     apply (metis not_le uint_nat)
                    apply (subst is_inf_d_heap, blast)
                     apply (metis (no_types, hide_lams) not_le tail_heap uint_nat) 
                    apply clarsimp
                   apply (force intro: pedge_abs_C_equiv_2)
                  apply rule
                   apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                   apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                    apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C 
                                       (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
                                       (p +\<^sub>p uint vv))))))))) = sint (snd (iD (fst (snd (snd iG) (iP vv)))))")
                     apply (subgoal_tac "sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint vv))) = sint (snd (iD vv))")
                      apply (subgoal_tac "EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint vv)) = snd (iN vv)")
                       apply (metis uint_nat) 
                      apply (subst is_inf_n_heap, blast, blast)
                      apply argo
                     apply (subst is_inf_d_heap, simp, blast, blast)
                    apply clarsimp
                    apply (subst tail_heap, blast) 
                     apply (metis not_le uint_nat)
                    apply (metis not_le is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap uint_nat word_sint.Rep_inject)
                   apply (force intro: pedge_abs_C_equiv_2)
                  apply rule+
                   apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                   apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                    apply clarsimp
                    apply (subst tail_heap, blast)
                     apply (metis not_le uint_nat)
                    apply (subst val_d_heap, blast, blast)
                    apply (subst val_d_heap, blast)
                     apply (metis (no_types, hide_lams) not_le tail_heap uint_nat)
                    apply (subgoal_tac "UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (c +\<^sub>p int (unat (iP vv))))) = iC (iP vv)")
                     apply (simp add: uint_nat)
                    apply (metis (no_types) cost_abs_C_equiv not_le uint_nat)
                   apply (force intro: pedge_abs_C_equiv_2)
                  apply rule
                   apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                   apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                    apply clarsimp
                    apply (subst tail_heap, blast)
                     apply (metis not_le uint_nat) 
                    apply (subst is_inf_n_heap, simp)
                     apply (metis (no_types, hide_lams) not_le tail_heap uint_nat)
                    apply (metis uint_nat)
                   apply (force intro: pedge_abs_C_equiv_2)
                  apply (unfold just_inv_def is_graph_def is_numm_def is_dist_def is_pedge_def wf_digraph_def)[1]
                  apply (subgoal_tac "iP vv = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint vv))")
                   apply clarsimp
                   apply (subst tail_heap, blast) 
                    apply (metis not_le uint_nat)
                   apply (subst val_n_heap, simp, blast)
                   apply (subst val_n_heap, simp)
                    apply (metis (no_types, hide_lams) not_le tail_heap uint_nat)
                   apply (metis uint_nat) 
                  apply (force intro: pedge_abs_C_equiv_2)
                 apply (metis max_word_max not_le word_le_less_eq)
                apply (simp add: inc_le is_graph_def)
               apply (simp add: inc_le is_graph_def unat_minus_plus1_less)
              apply rule
               apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp simp: if_bool_eq_conj)+
               apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
              apply rule
               apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp simp: if_bool_eq_conj)+
               apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
              apply rule
               apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
               apply (clarsimp simp: if_bool_eq_conj)+
               apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply rule
              apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
              apply (clarsimp simp: if_bool_eq_conj)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
            apply rule
             apply (blast intro: signed_overflow)
            apply rule
             apply (blast intro: signed_underflow)
            apply rule
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply rule
             apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
             apply (clarsimp simp: if_bool_eq_conj)+
             apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply rule+
             apply (unfold just_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def)[1]
             apply (subgoal_tac "snd (iN vv) = EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p int (unat vv)))")
              apply (subgoal_tac "sint (snd (iD vv)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat vv))))")
               apply (subgoal_tac "snd (iN (fst (snd (snd iG) (iP vv)))) = EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p int 
                                    (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat (heap_w32 s 
                                    (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p int (unat vv)))))))))))")
                apply presburger
               apply (subst tail_heap, force, presburger, force)
              apply (subst is_inf_d_heap, simp, blast, force)
             apply (subst is_inf_n_heap, simp, blast, force, force)
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply rule
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply rule
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply rule
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
         apply rule
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply rule
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply rule
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
        apply rule
         apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
       apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply rule+ 
        apply (metis max_word_max not_le is_inf_n_heap just_inv_step word_le_less_eq)
       apply (blast intro: inc_le shortest_path_neg_checker.unat_minus_plus1_less)
      apply rule
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply safe[1]
      apply (unfold just_inv_def, clarsimp)[1]
      apply (metis less_le less_x_plus_1 max_word_max)
        apply (simp add: inc_le is_graph_def just_inv_def)
       apply (simp add: is_graph_def unat_minus_plus1_less)
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis is_graph_def word_le_less_eq)
   apply (unfold just_inv_def is_graph_def)[1] 
   apply wp 
  apply simp
  apply (metis (no_types, hide_lams) map_map is_graph_def mk_iedge_list.simps mk_list'.simps)
  done


(* this should not be correct *)
lemma signed_word_nonzero:
  fixes a :: "32 signed word"
  shows "a \<le> 0 \<longleftrightarrow> a = 0"
  using word_le_0_iff by simp


lemma wf_inv_is_fin_digraph:
   "is_wellformed_inv G (iedge_cnt G) \<longleftrightarrow> fin_digraph (abs_IGraph G)"
    unfolding is_wellformed_inv_def fin_digraph_def fin_digraph_axioms_def
      wf_digraph_def no_loops_def 
    by auto

lemma trian_inv_eq_math:
  "trian_inv G d c (fst (snd G)) \<longleftrightarrow> 
   (\<forall>e. e \<in> arcs (abs_IGraph G) \<longrightarrow> 
    abs_IDist d (head (abs_IGraph G) e) \<le> 
    abs_IDist d (tail (abs_IGraph G) e) + ereal (abs_ICost c e))"
  apply safe
   apply (unfold abs_IDist_def abs_ICost_def abs_IGraph_def trian_inv_def)[1]
   apply (erule_tac x=e in allE)
   apply force
   apply (unfold abs_IDist_def abs_ICost_def abs_IGraph_def trian_inv_def)[1]
  apply (rule allI, clarsimp, force)
  done

lemma just_inv_eq_math: 
  "just_inv G d c s n p (ivertex_cnt G) \<longleftrightarrow> 
    (\<forall>v<fst G. v \<noteq> s \<longrightarrow>
    (\<exists>i. abs_INum n v = enat i) \<longrightarrow>
    (\<exists> e. (abs_IPedge p v) = Some e \<and>
     e < (fst (snd G)) \<and>
     v = snd (snd (snd G) e) \<and>
     abs_IDist d v =
     abs_IDist d (fst (snd (snd G) e)) +
     ereal (abs_ICost c e) \<and>
     abs_INum n v = 
     abs_INum n (fst (snd (snd G) e)) + enat (Suc 0)))"
  apply (simp add: just_inv_def)
  apply (rule iffI; clarsimp; erule_tac x=v in allE)
   apply (rule_tac x= "p v" in exI, clarsimp simp: abs_IPedge_def)
   apply (case_tac "snd (n v) = 0"; clarsimp simp: not_le word_msb_sint abs_INum_def) 
   apply (rule conjI)
    apply (simp add: add_ucast_no_overflow_unat abs_IDist_def abs_ICost_def abs_IPedge_def)
    apply force
   apply (metis (mono_tags, hide_lams) add.right_neutral add_Suc_right 
      le_add_same_cancel1 long_ucast add_ucast_no_overflow_64 unat_eq_1(2) 
      unat_plus_simple zero_le)
  apply (clarsimp simp add: abs_IPedge_def)
   apply (subgoal_tac "\<exists>i. abs_INum n v = enat i"; simp add: abs_INum_def) 
  apply (case_tac "msb (p v)"; 
      clarsimp simp: not_le word_msb_sint 
      abs_INum_def abs_IDist_def abs_ICost_def)  
    apply (case_tac "snd (n (fst (snd (snd G) (p v)))) = 0"; clarsimp) 
    apply (case_tac "snd (d v) = 0"; 
      case_tac "snd (d (fst (snd (snd G) (p v)))) = 0"; 
      clarsimp simp: add_ucast_no_overflow_unat)
    apply (metis add.commute of_nat_Suc ucast_nat_def)
   apply (metis (mono_tags, hide_lams) Word.sint_0 add.right_neutral add_Suc_right less_int_code(1) long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_unat.Rep_inject)
   apply (metis (mono_tags, hide_lams) add.right_neutral add_Suc_right long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_unat.Rep_inject)+
  done

definition basic_just_sp_inv :: 
  "IGraph \<Rightarrow> IENInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> bool" where
  "basic_just_sp_inv G d c s n p \<equiv>
       (is_wellformed_inv G (iedge_cnt G) \<and>
        is_inf_d d s \<le> 0 \<and>
        (is_inf_d d s = 0 \<longrightarrow> val_d d s \<le> 0) \<and>
        trian_inv G d c (iedge_cnt G) \<and> 
        just_inv G d c s n p (ivertex_cnt G))"

lemma check_basic_just_sp_spc_intermediate:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          sc < ivertex_cnt iG \<and> 
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   check_basic_just_sp' g d c sc n p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
        basic_just_sp_inv iG iD iC sc iN iP)\<rbrace>!"
  apply (clarsimp simp: check_basic_just_sp'_def basic_just_sp_inv_def)
  apply wp
        apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          sc < ivertex_cnt iG \<and> 
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_wellformed_inv iG (iedge_cnt iG) \<and>
          is_inf_d iD sc \<le> 0 \<and>
          (is_inf_d iD sc = 0 \<longrightarrow> val_d iD sc \<le> 0) \<and>
          trian_inv iG iD iC (iedge_cnt iG))" 
      in validNF_post_imp[OF _ just_spc'])
        apply fastforce 
       apply wp
      apply wp
      apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          sc < ivertex_cnt iG \<and> 
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_wellformed_inv iG (iedge_cnt iG) \<and>
          is_inf_d iD sc \<le> 0 \<and>
          (is_inf_d iD sc = 0 \<longrightarrow> val_d iD sc \<le> 0))"
      in validNF_post_imp[OF _ trian_spc']) 
  using fin_digraph_def fin_digraph_axioms_def
      apply (fastforce simp: wf_inv_is_fin_digraph) 
     apply wp
    apply wp
   apply (rule_tac P1 = " P and (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          sc < ivertex_cnt iG \<and> 
          is_numm s iG iN n \<and>
          is_pedge s iG iP p) "
      in validNF_post_imp[OF _ is_wellformed_spc'])
   apply clarsimp
   defer
   apply blast
  apply rule+
      apply (unfold is_graph_def is_dist_def)[1]
      apply force
     apply (unfold is_graph_def is_dist_def)[1]
     apply argo
    apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply rule+
      apply (unfold is_graph_def is_dist_def)[1]
      apply argo
     apply rule+
     apply (unfold is_graph_def is_dist_def)[1]
     apply argo
    apply rule+
      apply (unfold is_graph_def is_dist_def)[1]
      apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
       apply (subgoal_tac "sint (fst (iD sc)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
        apply linarith
       apply (subst val_d_heap, linarith, blast, fast)
      apply (subst is_inf_d_heap, fastforce, argo, simp add:uint_nat)
     apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply rule+
     apply argo
    apply argo
   apply rule+
    apply (unfold is_graph_def is_dist_def)[1]
    apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
     apply linarith
    apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
   apply rule+
    apply (unfold is_graph_def is_dist_def)[1]
    apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
     apply (subgoal_tac "sint (fst (iD sc)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))") 
      apply simp
     apply (subst val_d_heap, fastforce, argo, force) 
    apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
   apply rule
    apply (metis fin_digraph_def wf_inv_is_fin_digraph)
   apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply rule+
     apply meson
    apply (simp add: is_inf_d_heap uint_nat)
   apply rule+
    apply (unfold is_graph_def is_dist_def)[1]
    apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
     apply simp
    apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
   apply rule
    apply (unfold is_graph_def is_dist_def)[1]
    apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
     apply (subgoal_tac "sint (fst (iD sc)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))") 
      apply simp
     apply (subst val_d_heap, fastforce, argo, simp add: uint_nat) 
    apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
   apply rule
    apply (metis fin_digraph_def wf_inv_is_fin_digraph)
   apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply rule+
     apply fastforce
    apply (unfold is_graph_def is_dist_def)[1]
    apply blast
   apply rule+
     apply (unfold is_graph_def is_dist_def)[1]
     apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
      apply simp
     apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
    apply (unfold is_graph_def is_dist_def)[1]
    apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
     apply (subgoal_tac "sint (fst (iD sc)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))") 
      apply simp
     apply (subst val_d_heap, fastforce, blast, fast)   
    apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
   apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply rule+
    apply meson
   apply (unfold is_graph_def is_dist_def)[1]
   apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
    apply (subgoal_tac "sint (fst (iD sc)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))") 
     apply simp
    apply (subst val_d_heap, fastforce, argo, force) 
   apply (subst is_inf_d_heap, fastforce, argo, argo)
  apply rule+
   apply (unfold is_graph_def is_dist_def)[1]
   apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
    apply simp
   apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
  apply rule
   apply (unfold is_graph_def is_dist_def)[1]
   apply (subgoal_tac "sint (snd (iD sc)) = sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))")
    apply (subgoal_tac "sint (fst (iD sc)) = sint (ENInt_C.val_C (heap_ENInt_C s (d +\<^sub>p int (unat sc))))") 
     apply simp
    apply (subst val_d_heap, fastforce, argo, simp add:uint_nat)   
   apply (subst is_inf_d_heap, fastforce, argo, metis uint_nat)
  apply rule
   apply (metis fin_digraph_def wf_inv_is_fin_digraph)
  apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
  apply (clarsimp simp: if_bool_eq_conj)+
  apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  done

lemma basic_just_sp_eq_invariants_imp:
  "\<And>G d c s n p. 
    (is_wellformed_inv G (iedge_cnt G) \<and> 
    s < ivertex_cnt G \<and>
    is_inf_d d s \<le> 0 \<and>
    (is_inf_d d s = 0 \<longrightarrow> val_d d s \<le> 0) \<and>
    trian_inv G d c (iedge_cnt G) \<and> 
    just_inv G d c s n p (ivertex_cnt G))
    =
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
  show "?thesis G d c s n p"
    unfolding 
      basic_just_sp_pred_def 
      basic_just_sp_pred_axioms_def 
      basic_sp_def basic_sp_axioms_def
    by (auto simp: wf_inv_is_fin_digraph[where ?G=G]
        trian_inv_eq_math[where ?G=G and ?d=d and ?c=c]
        just_inv_eq_math[where ?G=G and ?d=d and ?c=c and ?s=s and ?n=n and ?p=p],
        (simp add: abs_IDist_def)+)
qed

definition s_assms_inv :: "IGraph \<Rightarrow> IVertex \<Rightarrow> IENInt \<Rightarrow> IPEdge \<Rightarrow> IEInt \<Rightarrow> bool" where
  "s_assms_inv G sc d p n \<equiv> 
      (sc < ivertex_cnt G) \<and>
      (is_inf_d d sc \<le> 0) \<and>
      (sint (p sc) < 0) \<and>
      (is_inf_n n sc = 0) \<and>
      (val_n n sc = 0)"

lemma s_assms_spc':
  "wf_digraph (abs_IGraph iG) \<Longrightarrow>
   is_graph s iG g \<Longrightarrow>
   is_dist s iG iD d \<Longrightarrow>
   is_pedge s iG iP p \<Longrightarrow>
   is_numm s iG iN n \<Longrightarrow>
   s_assms' g sc d p n s = 
   Some (if s_assms_inv iG sc iD iP iN then 1 else 0)"
  apply (clarsimp simp: s_assms'_def)
  apply (simp add: ocondition_def oguard_def ogets_def oreturn_def obind_def)
  apply rule+
       apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1] 
       apply (subgoal_tac "snd (iN sc) = EInt_C.isInf_C (heap_EInt_C s (n +\<^sub>p uint sc))")
        apply (subgoal_tac "fst (iN sc) = EInt_C.val_C (heap_EInt_C s (n +\<^sub>p uint sc))")
         apply argo
        apply (subst val_n_heap, simp, presburger, blast)
       apply (subst is_inf_n_heap, simp, presburger, blast) 
      apply (unfold is_graph_def is_numm_def)[1]
      apply blast
     apply (rule impI, rule ccontr, erule notE)
     apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  using not_le word_of_nat_le apply fastforce
    apply (rule impI, rule ccontr, erule notE)
    apply (unfold s_assms_inv_def is_graph_def is_pedge_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_of_nat_le word_unat.Rep_inverse)
   apply (rule impI, rule ccontr, erule notE)
   apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply (metis not_le word_of_nat_le word_unat.Rep_inverse)
  apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, 
      rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold is_pedge_def is_graph_def s_assms_inv_def)[1]
       apply clarsimp
       apply (subgoal_tac "iP sc = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint sc))")
        apply clarsimp
        apply (metis sint_ucast)
       apply (blast intro: pedge_abs_C_equiv_2)
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p uint sc)" in notE)
     apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (metis not_le word_less_nat_alt)
    apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) 
           (p +\<^sub>p uint sc))" in notE)
    apply (unfold s_assms_inv_def is_graph_def is_pedge_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_of_nat_le word_unat.Rep_inverse)
   apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_dist_def is_graph_def)[1]
       apply clarsimp
       apply (simp add: is_inf_d_heap)
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_dist_def is_graph_def)[1]
       apply clarsimp
       apply (simp add: is_inf_d_heap)
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p uint sc)" in notE)
     apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_graph_def)[1]
       apply fastforce
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule conjI, rule impI)
      apply (unfold s_assms_inv_def is_graph_def is_dist_def is_pedge_def is_numm_def)[1]
      apply (rule conjI)
       apply simp
      apply (rule conjI) 
       apply (subst is_inf_d_heap, simp, force, simp add: uint_nat)
      apply (rule conjI)
       apply (subgoal_tac "iP sc = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p int (unat sc)))")
        apply (simp add: sint_ucast)
       apply (subgoal_tac "int (unat sc) = uint sc")
        apply (force intro: pedge_abs_C_equiv_2)
       apply (simp add:uint_nat)
      apply (subst val_n_heap, simp, simp)
      apply (subst is_inf_n_heap, simp, simp)
      apply (simp add: uint_nat)
     apply (unfold is_graph_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p int (unat sc))" in notE)
    apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_less_nat_alt)
   apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint sc))" in notE)
   apply (unfold s_assms_inv_def is_graph_def is_pedge_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply (metis not_le word_of_nat_le word_unat.Rep_inverse)
  apply (rule impI, rule ccontr, erule notE)
  apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
  apply (clarsimp simp: if_bool_eq_conj)+
  apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply (metis not_le word_of_nat_le word_unat.Rep_inverse)
  done

lemma s_assms_eq_math:
  "s_assms_inv G sc d p n  \<longleftrightarrow> 
   (sc \<in> verts (abs_IGraph G) \<and>
    abs_IDist d sc \<noteq> \<infinity> \<and>
    abs_IPedge p sc = None \<and>
    abs_INum n sc = 0)"
  apply safe
      apply (unfold s_assms_inv_def abs_IGraph_def, clarsimp)[1]
     apply (unfold s_assms_inv_def abs_IDist_def, clarsimp)[1]
    apply (unfold s_assms_inv_def abs_IPedge_def, clarsimp)[1]
  using word_msb_sint apply blast
   apply (unfold s_assms_inv_def abs_INum_def, clarsimp, simp add: zero_enat_def)[1]
  apply (unfold s_assms_inv_def abs_IGraph_def abs_IDist_def abs_INum_def abs_IPedge_def, clarsimp)
   apply (simp add: unat_eq_zero word_msb_sint zero_enat_def)+
  done

definition parent_num_assms_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> IENInt \<Rightarrow> IPEdge \<Rightarrow> IEInt  \<Rightarrow> 32 word \<Rightarrow> bool" where
  "parent_num_assms_inv G s d p n k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> is_inf_d d v \<le> 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        is_inf_d d (fst (iedges G e)) \<le> 0 \<and>
        (is_inf_n n v = 0 \<longleftrightarrow> is_inf_n n (fst (iedges G e)) = 0) \<and>
        (is_inf_n n v = 0 \<longrightarrow>
          cast_long (val_n n v) = cast_long (val_n n (fst (iedges G e))) + 1))"

lemma parent_num_assms_inv_step:
  assumes v_less_max: "v < (max_word::32 word)"
  shows "parent_num_assms_inv G s d p n (v + 1) \<longleftrightarrow> parent_num_assms_inv G s d p n v
    \<and> (v \<noteq> s \<and> is_inf_d d v \<le> 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        is_inf_d d (fst (iedges G e)) \<le> 0 \<and>
        (is_inf_n n v = 0 \<longleftrightarrow> is_inf_n n (fst (iedges G e)) = 0) \<and>
        (is_inf_n n v = 0 \<longrightarrow>
          cast_long (val_n n v) = cast_long (val_n n (fst (iedges G e))) + 1)))"
  unfolding parent_num_assms_inv_def apply safe
  by (metis less_x_plus_1 max_word_max not_le v_less_max)+
                  
lemma parent_num_assms_le:
  assumes leq: "j \<le> i" 
  assumes parent_num_assms_i: "parent_num_assms_inv G s d p n i"
  shows "parent_num_assms_inv G s d p n j"
  using assms 
  by (induct j) (auto simp add: parent_num_assms_inv_def)

lemma parent_num_assms_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   parent_num_assms' g sc d p n
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> parent_num_assms_inv iG sc iD iP iN (ivertex_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: parent_num_assms'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(vv, s). unat (ivertex_cnt iG - vv)" and
        I="\<lambda>vv s. P s \<and> parent_num_assms_inv iG sc iD iP iN vv \<and>
                   vv \<le> ivertex_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   is_dist s iG iD d \<and>
                   is_numm s iG iN n \<and>
                   is_pedge s iG iP p"])
  apply (simp add: skipE_def)
  apply wp
     apply (subst if_bool_eq_conj)+
     apply simp
     apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI)
         apply blast
        apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
        apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (rule conjI, subst is_inf_d_heap, fast, fast, blast) 
        apply (force simp: sint_ucast pedge_abs_C_equiv_2)
       apply (rule impI, rule conjI, rule impI, rule conjI, blast)
        apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
        apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
        apply (force simp: sint_ucast pedge_abs_C_equiv_2)
       apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
         apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
         apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
         apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
         apply (clarsimp, subst (asm) (2) head_heap, blast, blast)
         apply (simp add: pedge_abs_C_equiv_2)
        apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
          apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
          apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
          apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
          apply (clarsimp, subst (asm) (7) arrlist_heap[where iL=iP], blast, fast)
          apply (subst (asm) (4) tail_heap, blast, simp add: uint_nat) 
          apply (subst (asm) (3) is_inf_d_heap, blast, metis not_le tail_heap wellformed_iGraph uint_nat, simp add: uint_nat)
         apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
           apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
           apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
           apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
           apply (clarsimp, subst arrlist_heap[where iL=iP], blast, blast, subst is_inf_n_heap, blast, blast)
           apply (subst tail_heap, blast, metis int_unat not_le, subst is_inf_n_heap, blast, metis not_le tail_heap wellformed_iGraph uint_nat, metis uint_nat)
          apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
            apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
            apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
            apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
            apply (clarsimp, subst (asm) (11) arrlist_heap[where iL=iP], blast, blast)
            apply (subst (asm) (5) tail_heap, blast, simp add: uint_nat)
            apply (subst (asm) (8) val_n_heap, blast, metis not_le tail_heap wellformed_iGraph uint_nat) 
            apply (subst (asm) (7) val_n_heap, blast, fast)
            apply (metis EInt_isInf_C_pte two_comp_to_eint_arrlist_heap uint_nat)
           apply (rule conjI, clarsimp)
            apply (rule conjI) 
             apply (subgoal_tac " vv + 1 \<le> fst iG")
              apply (subgoal_tac "vv < (max_word::32 word)")
               apply (drule parent_num_assms_inv_step[where G=iG and s=sc and d=iD and p=iP and n=iN])
               apply clarsimp
               apply (unfold is_graph_def is_dist_def is_pedge_def is_numm_def)[1] 
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, simp add: sint_ucast uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, simp add: uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst head_heap, force, simp add: uint_nat, metis uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                      subst is_inf_d_heap, simp, simp add: uint_nat, metis not_le tail_heap wellformed_iGraph uint_nat, simp add:uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                      subst is_inf_n_heap, simp, fast, subst is_inf_n_heap, simp, simp add: uint_nat, 
                      metis not_le tail_heap wellformed_iGraph uint_nat, simp add: uint_nat)
               apply (subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                      subst val_n_heap, simp, fast, subst val_n_heap, simp, simp add: uint_nat, metis not_le tail_heap wellformed_iGraph uint_nat, simp add: uint_nat)
              apply (metis max_word_max not_le word_le_less_eq)
             apply (metis inc_le is_graph_def)
            apply (rule conjI, metis inc_le is_graph_def)
            apply (rule conjI, metis is_graph_def unat_minus_plus1_less)
            apply (unfold parent_num_assms_inv_def is_graph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule conjI, unfold parent_num_assms_inv_def is_graph_def is_numm_def is_pedge_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply (metis not_le shortest_path_neg_checker.wellformed_iGraph word_less_nat_alt)
           apply (rule conjI)
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (clarsimp, rule conjI, rule impI, rule conjI)
            apply (subgoal_tac " vv + 1 \<le> fst iG")
             apply (subgoal_tac "vv < (max_word::32 word)")
              apply (drule parent_num_assms_inv_step[where G=iG and s=sc and d=iD and p=iP and n=iN])
              apply (clarsimp)
              apply (unfold is_graph_def is_dist_def is_numm_def is_pedge_def)[1]
              apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, simp add: sint_ucast uint_nat)
              apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, simp add: uint_nat)
              apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst head_heap, force, simp add: uint_nat, metis uint_nat)
              apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                     subst is_inf_d_heap, simp, simp add: uint_nat, metis not_le tail_heap wellformed_iGraph uint_nat, simp add:uint_nat)
              apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                     subst is_inf_n_heap, simp, fast, subst is_inf_n_heap, simp, simp add: uint_nat, 
                     metis not_le tail_heap wellformed_iGraph uint_nat, simp add: uint_nat)
              apply (subst is_inf_n_heap, simp, fast, simp add: uint_nat)
             apply (metis max_word_max not_le word_le_less_eq)
            apply (simp add: inc_le is_graph_def)
           apply (rule conjI, simp add: inc_le is_graph_def)
           apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
           apply (rule conjI, unfold is_graph_def is_numm_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (rule conjI, unfold is_graph_def is_dist_def is_pedge_def is_numm_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (rule conjI)
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+) 
           apply (metis not_le wellformed_iGraph word_less_nat_alt)
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (rule conjI, unfold is_graph_def is_dist_def is_pedge_def is_numm_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (metis not_le wellformed_iGraph word_less_nat_alt)
         apply (rule conjI)
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+) 
         apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule conjI, unfold is_graph_def is_dist_def is_pedge_def is_numm_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply (unfold is_graph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule conjI, rule impI)
       apply (rule conjI)
        apply (subgoal_tac " vv + 1 \<le> fst iG")
         apply (subgoal_tac "vv < (max_word::32 word)")
          apply (drule parent_num_assms_inv_step[where G=iG and s=sc and d=iD and p=iP and n=iN])
          apply clarsimp
          apply (unfold is_graph_def is_dist_def)[1]
          apply (subst (asm) (1) is_inf_d_heap, force, fast, linarith)
         apply (metis max_word_max not_le word_le_less_eq)
        apply (simp add: inc_le is_graph_def)
       apply (rule conjI, simp add: inc_le is_graph_def)
       apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
       apply (unfold is_graph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule conjI, unfold is_graph_def is_dist_def is_pedge_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply clarsimp
     apply (rule conjI)
      apply (subgoal_tac " sc + 1 \<le> fst iG")
       apply (subgoal_tac "sc < (max_word::32 word)")
        apply (drule parent_num_assms_inv_step[where G=iG and s=sc and d=iD and p=iP and n=iN])
        apply clarsimp
       apply (metis max_word_max not_le word_le_less_eq)
      apply (simp add: inc_le is_graph_def)
     apply (rule conjI, simp add: inc_le is_graph_def)
     apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
     apply (rule conjI)
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (unfold is_graph_def is_pedge_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis is_graph_def word_le_less_eq)
   apply wp
  apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def, force)
  done

lemma parent_nums_assms_inv_eq_math: 
  "parent_num_assms_inv G s d p n (ivertex_cnt G) \<longleftrightarrow> 
    (\<forall>v<fst G. v \<noteq> s \<longrightarrow>
    (\<exists>i. abs_IDist d v \<noteq> \<infinity>) \<longrightarrow>
    (\<exists> e. (abs_IPedge p v) = Some e \<and>
     e < (fst (snd G)) \<and>
     v = snd (snd (snd G) e) \<and>
     abs_IDist d (fst (snd (snd G) e)) \<noteq> \<infinity> \<and>
     abs_INum n v = 
     abs_INum n (fst (snd (snd G) e)) + enat (Suc 0)))"
  apply (simp add: parent_num_assms_inv_def)
  apply (rule iffI; clarsimp; erule_tac x=v in allE)
   apply (rule_tac x= "p v" in exI, rule conjI, clarsimp simp: abs_IPedge_def, metis abs_IDist_def infinity_ereal_def 
      not_le word_msb_sint)
   apply (case_tac "snd (n v) = 0"; clarsimp simp: not_le word_msb_sint abs_INum_def) 
    apply (rule conjI, metis abs_IDist_def infinity_ereal_def not_le)
    apply (rule impI, rule conjI, metis abs_IDist_def infinity_ereal_def not_le)
    apply (metis (mono_tags, hide_lams) abs_IDist_def PInfty_neq_ereal(1) add.right_neutral add_Suc_right ereal.distinct(5) 
      infinity_ereal_def not_le long_ucast word_add_cast_up_no_overflow unat_eq_1(2))
   apply safe[1]
       apply (fastforce simp add: abs_IDist_def)+
  apply (safe, unfold abs_IGraph_def abs_IDist_def abs_INum_def abs_IPedge_def)
               apply simp_all
       apply (simp add: word_msb_sint)+
   apply (metis (mono_tags, hide_lams) add.right_neutral add_Suc_right shortest_path_neg_checker.long_ucast shortest_path_neg_checker.word_add_cast_up_no_overflow unat_eq_1(2) word_unat.Rep_inject)+
  done

definition shortest_paths_locale_step1_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> IENInt \<Rightarrow> bool" where
  "shortest_paths_locale_step1_inv G sc n p d \<equiv>
       is_wellformed_inv G (iedge_cnt G) \<and>
       s_assms_inv G sc d p n \<and>
       parent_num_assms_inv G sc d p n (ivertex_cnt G)"

lemma shortest_paths_locale_step1_spc_intermediate:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)\<rbrace>
   shortest_paths_locale_step1' g sc n p d
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
        shortest_paths_locale_step1_inv iG sc iN iP iD)\<rbrace>!"
  apply (clarsimp simp: shortest_paths_locale_step1'_def shortest_paths_locale_step1_inv_def)
  apply wp
        apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_wellformed_inv iG (iedge_cnt iG) \<and>
          s_assms_inv iG sc iD iP iN)" 
      in validNF_post_imp[OF _ parent_num_assms_spc'])
        apply fastforce 
       apply wp
        apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p)" 
      in validNF_post_imp[OF _ is_wellformed_spc'])
   defer
  apply force
  apply clarsimp
  apply (rule conjI, rule impI, rule conjI, rule impI, rule impI, rule impI)
    apply blast
  apply (rule impI, rule conjI)
 apply (metis fin_digraph_def s_assms_spc' wf_inv_is_fin_digraph)
   apply (rule impI)
  apply (subgoal_tac "\<And>pa. \<not> wf_digraph (abs_IGraph iG) \<or> \<not> is_graph s iG pa \<or> s_assms' pa sc d p n s = Some (if True then 1 else 0)")
    apply (metis (no_types) fin_digraph_def option.sel shortest_path_neg_checker.wf_inv_is_fin_digraph zero_neq_one)
   apply (simp add: s_assms_spc')
  apply (rule impI, rule conjI, rule impI, rule impI, rule impI)
   apply blast
  apply (rule impI, rule conjI)
   apply (metis fin_digraph_def s_assms_spc' wf_inv_is_fin_digraph)
  apply rule
   apply (subgoal_tac "wf_digraph (abs_IGraph iG)")
    apply (simp add: s_assms_spc')
  apply (meson fin_digraph_def wf_inv_is_fin_digraph)
  apply (metis fin_digraph.axioms(1) shortest_path_neg_checker.wf_inv_is_fin_digraph)
  done

lemma shortest_paths_locale_step1_eq_maths:
  "\<And>G d s c n p. 
    shortest_paths_locale_step1_inv G s n p d
    =
    shortest_paths_locale_step1
    (abs_IGraph G) s (abs_INum n)
    (abs_IPedge p) (abs_IDist d)  
    "
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?ac = "abs_ICost c"
  let ?an = "abs_INum n"  
  let ?ap = "abs_IPedge p"
  show "?thesis G d c s n p"
    unfolding 
      basic_just_sp_pred_def 
      basic_just_sp_pred_axioms_def 
      basic_sp_def basic_sp_axioms_def
    by (auto simp: wf_inv_is_fin_digraph[where ?G=G]
        trian_inv_eq_math[where ?G=G and ?d=d and ?c=c]
        just_inv_eq_math[where ?G=G and ?d=d and ?c=c and ?s=s and ?n=n and ?p=p],
        (simp add: abs_IDist_def)+)
qed

end

end