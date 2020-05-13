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
  "IENInt \<Rightarrow> IVertex \<Rightarrow> 32 signed word"
where 
  "val_d f v \<equiv> fst (f v)"

abbreviation val_n :: 
  "IEInt \<Rightarrow> IVertex \<Rightarrow> 32 word"
where 
  "val_n f v \<equiv> fst (f v)"

fun bool :: 
  "32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

abbreviation is_inf_d :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> 32 signed word"
where 
  "is_inf_d f v \<equiv>  (snd (f v))"

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
        (map to_enint (mk_idist_list iG iD)) (ptr_coerce p)"
                              
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
  "(IEdge_Id \<Rightarrow> 32 word) \<Rightarrow> IEdge_Id \<Rightarrow> real"
where
  "abs_ICost c e \<equiv> real_of_int (sint (c e))"

definition abs_IDist :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> ereal"
where
  "abs_IDist d v \<equiv> if snd (d v) > 0 then PInfty
         else if snd (d v) < 0 then MInfty else
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
  val_d f e = ENInt_C.val_C (h (ptr_coerce (ep +\<^sub>p (uint e))))"
  using to_eint.simps ENInt_val_C_pte 
  by (metis int_unat ptr_coerce_id two_comp_arrlist_heap)

lemma is_inf_d_heap:
  "\<lbrakk>arrlist h v (map (to_enint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  is_inf_d f e =  ENInt_C.isInf_C (h (ep +\<^sub>p (uint e)))"
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
              sint (val_d d (snd (iedges G i))) \<le> sint (val_d d (fst (iedges G i))) + sint (c i)))) \<and>
            (is_inf_d d (fst (iedges G i)) < 0 \<longrightarrow> is_inf_d d (snd (iedges G i)) < 0)"

lemma trian_inv_step:
  assumes i_less_max: "i < (max_word::32 word)"
  shows "trian_inv G d c (i + 1) \<longleftrightarrow> trian_inv G d c i \<and>
  ((is_inf_d d (fst (iedges G i)) = 0 \<longrightarrow> 
     (is_inf_d d (snd (iedges G i)) \<le> 0 \<and> (is_inf_d d (snd (iedges G i)) = 0 \<longrightarrow> 
     sint (val_d d (snd (iedges G i))) \<le> sint (val_d d (fst (iedges G i))) + sint (c i)))) \<and>
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
  assumes a1: "arrlist (\<lambda>p. UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) p))) (\<lambda>p. is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) p)) (map (iC \<circ> of_nat) [0..<unat (num_edges_C (heap_Graph_C s g))]) c"
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
  assumes a2: "arrlist (heap_EInt_C s) (is_valid_EInt_C s) (map (to_eint \<circ> (iL \<circ> of_nat)) [0..<unat (num_vertices_C (heap_Graph_C s g))]) l"
  assumes a3: "fst iG = num_vertices_C (heap_Graph_C s g)"
  assumes a4: "fst (snd iG) = num_edges_C (heap_Graph_C s g)"
  assumes a5: "arrlist (heap_Edge_C s) (is_valid_Edge_C s) (map (to_edge \<circ> (snd (snd iG) \<circ> of_nat)) [0..<unat (num_edges_C (heap_Graph_C s g))]) (arcs_C (heap_Graph_C s g))"
  assumes a6: "\<forall>ee < num_edges_C (heap_Graph_C s g). fst (snd (snd iG) ee) < num_vertices_C (heap_Graph_C s g)"
  shows "fst (iL (fst (snd (snd iG) ee))) = val_C (heap_EInt_C s (l +\<^sub>p int (unat (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee)))))))"
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
        apply (metis is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
       apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) = ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee)))))")
        apply simp
       apply (subst is_inf_d_heap, fastforce)
        apply (subst head_heap, fastforce, fastforce)
        apply (metis head_heap wellformed_iGraph)
       apply (subst head_heap, fastforce, fastforce)
       apply simp
      apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI)
          apply fast
         apply (unfold trian_inv_def is_dist_def is_cost_def is_graph_def)[1]
         apply clarsimp
         apply (rule_tac x=ee in exI)
         apply safe[1]
          apply (subst is_inf_d_heap, fastforce)
           apply (metis wellformed_iGraph)
          apply (subst tail_heap, fastforce, fastforce)
          apply fastforce
         apply (subgoal_tac "sint (fst (iD (snd (snd (snd iG) ee)))) = 
                             sint
                             (ENInt_C.val_C (heap_ENInt_C s 
                                (d +\<^sub>p uint (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p 
                              uint ee))))))")
          apply (subgoal_tac "sint (fst (iD (fst (snd (snd iG) ee)))) + sint (iC ee)= 
                             sint
                             (ENInt_C.val_C (heap_ENInt_C s 
                                (d +\<^sub>p uint (first_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p 
                              uint ee)))))) + 
                             sint (UCAST(32 \<rightarrow> 32 signed) (heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (c +\<^sub>p uint ee))))")
           apply linarith
          apply (subst tail_heap, fastforce, fastforce)
          apply (subst val_d_heap, fastforce)
           apply (metis s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
          apply (simp add: cost_abs_C_equiv uint_nat) 
         apply (subst head_heap, fastforce, fastforce)
         apply (subst val_d_heap, fastforce)
          apply (metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat) 
         apply fastforce
        apply (rule conjI, rule impI, rule conjI)
          apply meson
         apply (rule conjI)
          apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
           apply (subgoal_tac "ee < (max_word::32 word)") 
            apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
            apply clarsimp
            apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1] 
            apply clarsimp
            apply (subgoal_tac "heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint ee) = to_edge (snd (snd iG) ee)")
             apply (subgoal_tac "fst (snd (snd iG) ee) < fst iG")
              apply (subgoal_tac "snd (snd (snd iG) ee) < fst iG")
               apply (force simp:cost_abs_C_equiv is_inf_d_heap val_d_heap)
              apply (metis wellformed_iGraph)
             apply (metis wellformed_iGraph)
            apply (metis two_comp_to_edge_arrlist_heap uint_nat)
           apply clarsimp
           apply (simp add:less_le not_le, meson less_le max_word_max not_le)
          apply (simp add: inc_le is_graph_def, blast intro: inc_le)
         apply(safe)[1]
              apply (metis inc_le is_graph_def)
             apply (metis (no_types, hide_lams) is_graph_def unat_minus_plus1_less)
            apply (fastforce simp:is_graph_def)
           apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (fastforce simp:is_graph_def)
        apply clarsimp
        defer
        apply clarsimp
        defer
        apply (unfold wf_digraph_def trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)
       apply clarsimp
       defer
       apply (subgoal_tac  "\<not> ee < fst (snd iG)")
        apply (subgoal_tac "fst (snd iG) = ee")
         apply simp
        apply (metis word_le_less_eq)
       apply (metis is_graph_def)
      apply wp
     apply (unfold trian_inv_def is_graph_def is_cost_def is_dist_def)[1]
     apply force
    apply safe[1]
       apply (force simp: signed_overflow)
      apply (force simp: signed_underflow)
     apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (unfold is_graph_def is_dist_def is_cost_def is_numm_def is_pedge_def wf_digraph_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)

   apply (rule conjI, rule impI, rule conjI)
     apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
      apply (subgoal_tac "ee < (max_word::32 word)") 
       apply (subst trian_inv_step, blast) 
       apply (rule conjI, blast)
       apply (rule conjI, rule impI, rule conjI)
  thm word_le_0_iff
(*
         apply (subgoal_tac "snd (iD (snd (snd (snd iG) ee))) < 0")
          apply fastforce
         apply (subgoal_tac " \<not> 0 < sint (ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee))))))))
                            \<and> ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee))))))) \<noteq> 0
                            \<longrightarrow>
                            ENInt_C.isInf_C (heap_ENInt_C s (d +\<^sub>p int (unat (second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p int (unat ee))))))) < 0")
          apply (unfold is_dist_def is_graph_def wf_digraph_def)[1]
          apply (subst is_inf_d_heap, force, force)
          apply (subst head_heap, force, blast)
          apply (simp only:uint_nat)
          apply blast
*)
     



  
  
  sorry

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

end

end