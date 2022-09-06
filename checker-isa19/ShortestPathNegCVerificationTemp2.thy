(* uses Isabelle2019 and autocorres version 1.6 *)
theory ShortestPathNegCVerificationTemp2
imports
  "HOL-Library.Option_ord"
  "Library/Autocorres_Misc"
  "ShortestPath/ShortestPathNeg"
begin 

install_C_file "shortest_path_neg_checker.c"
autocorres [
  scope_depth = 2,
  scope = int_neg_cyc
  ] "shortest_path_neg_checker.c"
context shortest_path_neg_checker begin


(* Implementation types *)

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> IEdge_Id"
type_synonym IENInt = "IVertex \<Rightarrow> (32 signed word \<times> 32 signed word)"
type_synonym IEInt = "IVertex \<Rightarrow> 32 word"
type_synonym ICost = "IEdge_Id \<Rightarrow> 32 signed word"
type_synonym IGraph = "32 word \<times> 32 word \<times> (IEdge_Id \<Rightarrow> IEdge)"
(* for locale 3 *)
type_synonym IPath = "IEdge_Id list"
type_synonym ICycle = "IVertex \<times> IPath"
type_synonym ICycle_Set = "ICycle list"

type_synonym IPathPtr = "32 word ptr"
type_synonym ICycle' = "IVertex \<times> 32 word \<times> IPathPtr"
type_synonym ICycle_Set' = "ICycle' list"

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

abbreviation is_inf_d :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> int"
where 
  "is_inf_d f v \<equiv>  sint (snd (f v))"

abbreviation icycle_start ::
  "ICycle \<Rightarrow> 32 word"
where
  "icycle_start C \<equiv> fst C"
(*
abbreviation icycle_length ::
  "ICycle \<Rightarrow> 32 word"
where
  "icycle_length C \<equiv> fst (snd C)"
*)
abbreviation icycle_path ::
  "ICycle \<Rightarrow> IPath"
where
  "icycle_path C \<equiv> snd C"

abbreviation icycle'_start ::
  "ICycle' \<Rightarrow> 32 word"
where
  "icycle'_start C \<equiv> fst C"

abbreviation icycle'_length ::
  "ICycle' \<Rightarrow> 32 word"
where
  "icycle'_length C \<equiv> fst (snd C)"

abbreviation icycle'_path ::
  "ICycle' \<Rightarrow> IPathPtr"
where
  "icycle'_path C \<equiv> snd (snd C)"

(* Implementation functions to lists *)

fun bool :: 
  "32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

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
  "IGraph \<Rightarrow> IEInt \<Rightarrow> 32 word list"
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

  (* Make cycle lists *)
(*
fun mk_ipath_list :: 
  "ICycle \<Rightarrow> IPath"
where 
  "mk_ipath_list C = mk_list' (unat (icycle_length C)) (icycle_path C)"
*)
fun mk_ipath_list ::
  "ICycle \<Rightarrow> IPath"
where
  "mk_ipath_list C = icycle_path C"

fun mk_ipath'_list ::
  "'a lifted_globals_scheme \<Rightarrow> ICycle' \<Rightarrow> IPath"
where
  "mk_ipath'_list h C = map (heap_w32 h) 
                         (array_addrs (icycle'_path C) (unat (icycle'_length C)))"


(*Helper word lemmas*)

lemma word_nat_simp[simp]:
  assumes "(a :: 32 word) < max_word"
  shows "unat (a + 1) = unat a + 1"
  by(insert assms less_is_non_zero_p1 word_overflow_unat, blast)

lemma word_max_limit_simp[simp]:
  "unat (x :: 32 word) \<le> unat (max_word :: 32 word)"
  using word_le_nat_alt by blast

lemma sint_ucast: 
  "sint (ucast (x ::word32) :: sword32) = sint x"
  by (clarsimp simp: sint_uint uint_up_ucast is_up)

lemma long_ucast:
  "unat (ucast (x ::word32) :: word64) = unat x"
  by (simp add: is_up uint_up_ucast unat_def)


fun cast_long :: 
  "32 word \<Rightarrow> 64 word"
where 
  "cast_long x = ucast x"

fun cast_signed_long ::
  "32 signed word \<Rightarrow> 64 signed word"
  where
  "cast_signed_long x = scast x"

(* Lemmas for unat and of_nat *)
lemma eq_of_nat_conv:
  assumes "unat w1 = n"
  shows "w2 = of_nat n \<longleftrightarrow> w2 = w1"
  using assms by auto

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
  by (metis (no_types)  right_minus_eq measure_unat
      add_diff_cancel2 assms is_num_normalize(1) zadd_diff_inverse linorder_neq_iff)





(*Helper Lemmas*)



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

lemma ptr_coerce_ptr_add_uint[simp]:
  "ptr_coerce (p +\<^sub>p uint x) =  p +\<^sub>p  (uint x)"
  by auto



(* Refinement function from implementation types using lists to C types *)
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

fun to_enint :: 
  "(32 signed word \<times> 32 signed word) \<Rightarrow> ENInt_C"
where
  "to_enint p = ENInt_C (fst p) (snd p)"

fun to_cycle ::
  "ICycle' \<Rightarrow> Cycle_C"
where
  "to_cycle C = Cycle_C (fst C) (fst (snd C)) (snd (snd C))"

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
        arrlist (heap_w32 h) (is_valid_w32 h) (mk_inum_list iG iN) p"

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
  "is_cost h iG iC (p :: 32 signed word ptr) \<equiv> 
        arrlist (\<lambda>p. UCAST(32 \<rightarrow> 32 signed) (heap_w32 h (ptr_coerce p))) 
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_icost_list iG iC) p"

fun abs_ICycle' ::  
  "'a lifted_globals_scheme \<Rightarrow> ICycle' \<Rightarrow> ICycle" 
where
  "abs_ICycle' h iC' = 
        (icycle'_start iC', 
         mk_ipath'_list h iC')"

abbreviation 
  is_path :: "'a lifted_globals_scheme \<Rightarrow> IPath \<Rightarrow> 32 word ptr \<Rightarrow> bool"
where
  "is_path h iP p \<equiv> 
        arrlist (heap_w32 h) (is_valid_w32 h) iP p"

definition 
  is_cycle' :: "'a lifted_globals_scheme \<Rightarrow> ICycle' \<Rightarrow> Cycle_C ptr \<Rightarrow> bool"
where
  "is_cycle' h iC' p \<equiv>
    is_valid_Cycle_C h p \<and> 
    icycle'_start iC' = start_C (heap_Cycle_C h p) \<and> 
    icycle'_length iC' = length_C (heap_Cycle_C h p) \<and>
    icycle'_path iC' = path_C (heap_Cycle_C h p) \<and>
    (\<forall>i<unat (icycle'_length iC'). 
       is_valid_w32 h ((icycle'_path iC') +\<^sub>p int i))"

definition 
  is_cycle :: "'a lifted_globals_scheme \<Rightarrow> ICycle \<Rightarrow> Cycle_C ptr \<Rightarrow> bool"
where
  "is_cycle h iC p \<equiv>
    is_valid_Cycle_C h p \<and> 
    icycle_start iC = start_C (heap_Cycle_C h p) \<and> 
    length (icycle_path iC) = unat (length_C (heap_Cycle_C h p)) \<and>
    is_path h (icycle_path iC) (path_C (heap_Cycle_C h p))"

definition 
  abs_ICycles' :: "'a lifted_globals_scheme \<Rightarrow> ICycle_Set' \<Rightarrow> ICycle_Set"
where                           
  "abs_ICycles' h CS' \<equiv> map (abs_ICycle' h)  CS'"

definition 
  are_cycles' :: 
  "'a lifted_globals_scheme \<Rightarrow> ICycle_Set' \<Rightarrow> Cycle_set_C ptr \<Rightarrow> bool"
where
  "are_cycles' h iCS' p \<equiv>
    is_valid_Cycle_set_C h p \<and>
    length iCS' = unat (no_cycles_C (heap_Cycle_set_C h p)) \<and> 
    arrlist (heap_Cycle_C h) (is_valid_Cycle_C h)
       (map to_cycle iCS') (cyc_obj_C (heap_Cycle_set_C h p)) \<and>
    (\<forall>i<length iCS'. 
       is_valid_w32 h (icycle'_path (iCS'! i)))"


definition 
  are_cycles'' :: 
  "'a lifted_globals_scheme \<Rightarrow> ICycle_Set' \<Rightarrow> Cycle_set_C ptr \<Rightarrow> bool"
where
  "are_cycles'' h iCS' p \<equiv>
    is_valid_Cycle_set_C h p \<and>
    length iCS' = unat (no_cycles_C (heap_Cycle_set_C h p)) \<and> 
   (\<forall>i< length iCS'. 
          is_cycle' h (iCS'!i) (cyc_obj_C (heap_Cycle_set_C h p) +\<^sub>p int i))"


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
  "ICost \<Rightarrow> IEdge_Id \<Rightarrow> real"
where
  "abs_ICost c e \<equiv> real_of_int (sint (c e))"

definition abs_IDist :: 
  "IENInt \<Rightarrow> IVertex \<Rightarrow> ereal"
where
  "abs_IDist d v \<equiv> if sint (snd (d v)) > 0 then PInfty
         else if sint (snd (d v)) < 0 then MInfty else
         real_of_int (sint (fst (d v)))"

definition abs_INum :: 
  "IEInt \<Rightarrow> IENInt \<Rightarrow> IVertex \<Rightarrow> enat"
where
  "abs_INum n d v \<equiv> if sint (snd (d v)) \<noteq> 0 then \<infinity> else unat (n v)"

definition abs_INat :: 
  "IEInt \<Rightarrow> IVertex \<Rightarrow> nat"
where
  "abs_INat n v \<equiv> unat (n v)"

definition abs_IPedge :: 
  "IPEdge \<Rightarrow> IVertex \<Rightarrow> 32 word option" 
where
  "abs_IPedge p v \<equiv> if msb (p v) then None else Some (p v)"
(*
definition abs_IPath ::
  "IPath \<Rightarrow> 32 word awalk"
where
  "abs_IPath \<equiv> id"
*)

(*
definition abs_ICycle :: 
  "ICycle_Set \<Rightarrow> (32 word \<times> (32 word awalk)) set"
where
  "abs_ICycle CS \<equiv> set (map (\<lambda> C. (icycle_start C, icycle_path C)) (icycles CS))"
*)
lemma None_abs_pedgeI[simp]:
  "(abs_IPedge p v = None) = msb (p v)"
  using abs_IPedge_def by auto

lemma Some_abs_pedgeI[simp]: 
  "(\<exists>e. abs_IPedge p v = Some e) =  (~ (msb (p v)))"
  using None_not_eq None_abs_pedgeI 
  by (metis abs_IPedge_def)



(* Helper lemmas *)
lemma wellformed_iGraph:
  assumes "wf_digraph (abs_IGraph G)"
  shows "\<And>e. e < iedge_cnt G \<Longrightarrow> 
        fst (iedges G e) < ivertex_cnt G \<and> 
        snd (iedges G e) < ivertex_cnt G" 
  using assms unfolding wf_digraph_def by simp

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

lemmas two_comp_to_edge_arrlist_heap = 
  two_comp_arrlist_heap[where f=to_edge]

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

lemma val_d_heap:
  "\<lbrakk>arrlist h v (map (to_enint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  val_d f e = sint (ENInt_C.val_C (h (ptr_coerce (ep +\<^sub>p (uint e)))))"
  using to_enint.simps ENInt_val_C_pte 
  by (metis int_unat ptr_coerce_id two_comp_arrlist_heap)

lemma is_inf_d_heap:
  "\<lbrakk>arrlist h v (map (to_enint \<circ> (f \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  is_inf_d f e =  sint (ENInt_C.isInf_C (h (ep +\<^sub>p (uint e))))"
  using to_enint.simps  ENInt_isInf_C_pte
  by (metis int_unat two_comp_arrlist_heap)

lemma arrlist_cycle_path_heap:
  "\<lbrakk>arrlist h v (icycle_path iY) p; 
   i < length (icycle_path iY)\<rbrakk> \<Longrightarrow>
    icycle_path iY !  i = h (p +\<^sub>p int i)"
  using arrlist_nth_value by fastforce


(*helpers for icycle intermediate abstraction *)

fun mk_ipath ::
  "'a lifted_globals_scheme \<Rightarrow> IPathPtr \<Rightarrow> nat \<Rightarrow> IPath"
where
  "mk_ipath h p l = map (heap_w32 h) (array_addrs p l)"


lemma array_addrs_length: "length (array_addrs p l) = l"
apply (induct l arbitrary: p) 
  by (simp add:array_addrs.simps(2)) +

lemma mk_ipath_length:
  "length (mk_ipath h p l) = l"
  using array_addrs_length 
  by auto 

lemma arrlist_next_item:
  assumes "arrlist h v (x # xs) p"
  shows "arrlist h v xs (p +\<^sub>p 1)"
  using assms by simp

lemma array_addrs_arrlist:
  "\<lbrakk>\<forall>i<n. v (p +\<^sub>p int i); xs= map h (array_addrs p n)\<rbrakk> \<Longrightarrow> arrlist h v xs p"
  apply (induct n arbitrary: p xs) 
   apply simp
  apply (simp add: array_addrs.simps(2)) 
  apply (erule_tac x="p +\<^sub>p 1" in meta_allE)
  apply (frule_tac x=0 in spec, simp)
  by force

lemma arrlist_array_addrs:
  assumes "arrlist h v xs p" 
  assumes "n = length xs"
  shows "xs= map h (array_addrs p n)"  
  using assms   
  by (induct n arbitrary: xs p, simp)
     (case_tac xs; simp add: array_addrs.simps(2))

lemma is_path_absICycle':
  "\<forall>i<unat (icycle'_length iC'). 
       is_valid_w32 h ((icycle'_path iC') +\<^sub>p int i) \<Longrightarrow>
       is_path h (icycle_path (abs_ICycle' h iC')) (icycle'_path iC')"
  by (simp add: array_addrs_arrlist)

lemma is_icycle'_is_icycle:
  "\<lbrakk>is_cycle' h iC' p\<rbrakk> \<Longrightarrow> is_cycle h (abs_ICycle' h iC') p"
  unfolding is_cycle'_def is_cycle_def 
  using is_path_absICycle' 
  by (clarsimp simp: array_addrs_length) 

lemma are_cycles_is_icycle':
  "\<lbrakk>are_cycles'' h iCS' p \<rbrakk> \<Longrightarrow> 
  \<forall>i<length iCS'.  
     is_cycle' h (iCS'!i) 
         (cyc_obj_C (heap_Cycle_set_C h p) +\<^sub>p i)"
  unfolding are_cycles''_def
  by clarsimp 

lemma are_cycles_is_icycle:
  "\<lbrakk>are_cycles'' h iCS' p \<rbrakk> \<Longrightarrow> 
  \<forall>i<length iCS'.  
     is_cycle h (abs_ICycle' h (iCS'!i)) 
         (cyc_obj_C (heap_Cycle_set_C h p) +\<^sub>p i)"
  using are_cycles_is_icycle' is_icycle'_is_icycle 
  by fast

lemma word_less_arith_simp[simp]:
  "\<lbrakk> x \<noteq> 0; (x :: 32 word) < l \<rbrakk> \<Longrightarrow> (x - 1) < l"
  by (simp add: less_1_simp)
 
lemma abs_INat_to_abs_INum:
    "shortest_paths_locale_step1
    (abs_IGraph G) s (abs_INat n)
    (abs_IPedge pred) (abs_IDist d) \<Longrightarrow> (shortest_paths_locale_step1.enum (abs_INat n) (abs_IDist d)) = (abs_INum n d)"
  using shortest_paths_locale_step1.enum_def[where
      ?G="(abs_IGraph G)" and ?s=s and ?num="(abs_INat n)" and
      ?parent_edge="(abs_IPedge pred)" and ?dist="(abs_IDist d)"]
  unfolding abs_INum_def abs_IDist_def abs_INat_def
  by auto

lemma length_abs_ICycles': "length (abs_ICycles' h iYs) = length iYs"
  unfolding abs_ICycles'_def
  by simp

definition vertex_not_in_cycles_start_inv :: 
  "ICycle_Set \<Rightarrow> IVertex \<Rightarrow> nat \<Rightarrow> bool" 
where
  "vertex_not_in_cycles_start_inv CS v k = (\<forall>i< k. v \<noteq> fst (CS!  i))"

lemma vertex_not_in_cycles_start_inv_step :
  assumes "i < length CS"
  shows "vertex_not_in_cycles_start_inv CS v (Suc i) = 
           (v\<noteq>fst (CS! i) \<and> vertex_not_in_cycles_start_inv CS v i)"
  using assms unfolding vertex_not_in_cycles_start_inv_def 
  by (simp add: antisym less_Suc_eq)

  
lemma vertex_not_in_cycles_start_inv_take :
  "i \<le> length CS \<Longrightarrow> vertex_not_in_cycles_start_inv CS v i = (v \<notin> fst `(set (take i CS)))"
  unfolding vertex_not_in_cycles_start_inv_def
  by (force dest!: nth_image[symmetric]) 

lemma are_cycles_valid:
  assumes "are_cycles'' s iCS' cse"
  assumes "i < no_cycles_C (heap_Cycle_set_C s cse)"
  shows "is_valid_Cycle_C s (cyc_obj_C (heap_Cycle_set_C s cse) +\<^sub>p uint i)"
        "is_valid_Cycle_set_C s cse"
  using assms unfolding are_cycles''_def 
  by (force dest!: spec[where x="unat i" for i] 
            simp: int_unat unat_mono is_cycle'_def)+

lemma vertex_not_in_cycles_start_spc:
  "\<lbrace> P and 
     (\<lambda>s. are_cycles'' s iCS' cse  \<and>
          iCS = abs_ICycles' s iCS') \<rbrace>
   vert_not_in_cycles_start' cse v
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         vertex_not_in_cycles_start_inv iCS v (length iCS)) \<rbrace>!"   
  (is "\<lbrace> ?pre  \<rbrace> 
       ?prog 
       \<lbrace> (\<lambda>_ s. P s) And (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow>  ?inv (?ncycles:: nat)) \<rbrace>!" )
  unfolding vert_not_in_cycles_start'_def
  apply wpsimp
    apply (subst whileLoopE_add_inv [where 
            M="\<lambda>(i, s).  ?ncycles - unat i" and
            I="\<lambda>i s. ?pre s \<and> unat i \<le> ?ncycles \<and> ?inv (unat i)"])
    apply wp
     apply (clarsimp simp: are_cycles_valid)
     apply (rule conjI; clarsimp)
      apply (unfold vertex_not_in_cycles_start_inv_def[where k = "length _"])
      apply (drule_tac x="unat i" in spec, simp add: uint_nat abs_ICycles'_def) 
      apply (simp add: are_cycles''_def is_cycle'_def)
     apply (rule conjI, metis not_le less_unat_plus1 unat_mono length_abs_ICycles' are_cycles''_def)
     apply (rule conjI)
      apply (subst unatSuc2, blast dest: less_is_non_zero_p1)
      apply (subst vertex_not_in_cycles_start_inv_step) 
       apply (simp add: word_less_nat_alt are_cycles''_def length_abs_ICycles') 
      apply (frule are_cycles_is_icycle)
      apply (simp add: is_cycle_def abs_ICycles'_def are_cycles''_def uint_nat word_less_nat_alt)
     apply (simp add: are_cycles''_def length_abs_ICycles')
     apply (metis (no_types, hide_lams) Suc_diff_Suc Suc_eq_plus1  
              add.commute add.left_neutral less_add_eq_less  less_one 
              word_less_nat_alt word_overflow_unat less_is_non_zero_p1)
     apply (case_tac " unat i = length iCS"; 
            clarsimp simp: are_cycles''_def length_abs_ICycles' word_less_nat_alt) 
    apply (fastforce simp: word_le_nat_alt vertex_not_in_cycles_start_inv_def ) 
   apply wp
  apply (clarsimp simp: vertex_not_in_cycles_start_inv_def are_cycles''_def)
  done

definition parents_not_in_cycles_start_inv :: 
  "IGraph\<Rightarrow> ICycle_Set \<Rightarrow> IPEdge \<Rightarrow> IVertex \<Rightarrow> nat \<Rightarrow> bool" 
where
  "parents_not_in_cycles_start_inv G CS p v k = 
   (\<forall>i \<le> k. vertex_not_in_cycles_start_inv CS 
               (((\<lambda>v. snd (iedges G (p v)))^^ i) v) (length CS))"

lemma parents_not_in_cycles_start_inv_stepD:
  "parents_not_in_cycles_start_inv G CS p v i \<Longrightarrow>
   vertex_not_in_cycles_start_inv CS (((\<lambda>v. snd (iedges G (p v)))^^  (Suc i)) v) (length CS) \<Longrightarrow> 
  parents_not_in_cycles_start_inv G CS p v (Suc i)"
  unfolding parents_not_in_cycles_start_inv_def 
  by (fastforce elim: le_SucE)

lemma parents_not_in_cycles_start_inv_step :
  "parents_not_in_cycles_start_inv G CS p v (Suc i) = 
           (vertex_not_in_cycles_start_inv CS 
               (((\<lambda>v. snd (iedges G (p v)))^^  (Suc i)) v) (length CS) \<and> 
           parents_not_in_cycles_start_inv G CS p v i)"
  unfolding parents_not_in_cycles_start_inv_def 
  by (fastforce elim: le_SucE)

lemma parents_not_in_cycles_start_inv_le :
  assumes "i\<le>j"
  assumes "parents_not_in_cycles_start_inv G CS p v j"
  shows "parents_not_in_cycles_start_inv G CS p v i"
  using assms 
  by (induct j) 
     (auto simp add: parents_not_in_cycles_start_inv_def)

lemmas unat_le_mono = word_le_nat_alt [THEN iffD1]
thm is_numm_def

lemma is_numm_arrlist_heap: 
  "is_numm s iG iN n \<Longrightarrow>  i < (ivertex_cnt iG) \<Longrightarrow>  iN i = heap_w32 s (n +\<^sub>p uint i)"  
by (fastforce dest!:arrlist_heap simp: is_numm_def uint_nat)

lemma is_numm_valid:
  "is_numm s iG iN n \<Longrightarrow> i < ivertex_cnt iG \<Longrightarrow> is_valid_w32 s (n +\<^sub>p uint i)"
by (fastforce dest!:arrlist_nth_valid simp: is_numm_def uint_nat word_less_def)

lemma is_dist_arrlist_is_inf:
  "is_dist s iG iD d  \<Longrightarrow> i < ivertex_cnt iG \<Longrightarrow> 
   is_inf_d iD i = sint (isInf_C (heap_ENInt_C s (d +\<^sub>p uint i)))"
by (simp add:  is_inf_d_heap is_dist_def)

lemma is_dist_valid:
  "is_dist s iG iD d  \<Longrightarrow> i < ivertex_cnt iG \<Longrightarrow> is_valid_ENInt_C s (d +\<^sub>p uint i)"
by (fastforce dest!:arrlist_nth_valid simp: is_dist_def uint_nat word_less_def)

lemma is_pedge_arrlist_eq: 
  "is_pedge s iG iP p \<Longrightarrow>i < (ivertex_cnt iG) \<Longrightarrow>  0 \<le> i \<Longrightarrow>  
     iP i = heap_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word)(p +\<^sub>p uint i))"  
by (fastforce dest!: heap_ptr_coerce simp:is_pedge_def uint_nat)

lemma is_pedge_valid:
  "is_pedge s iG iP p \<Longrightarrow>i < (ivertex_cnt iG) \<Longrightarrow>  
    is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint i))"
by (fastforce intro: arrlist_nth_valid simp: is_pedge_def uint_nat word_less_def)

lemma is_graph_head_arrlist_eq: 
  "is_graph s iG g \<Longrightarrow> e < (iedge_cnt iG) \<Longrightarrow> 
    snd (snd (snd iG) e) = second_C (heap_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint e))"     
by (fastforce simp: is_graph_def dest: head_heap)

lemma is_graph_valid_graph:
  "is_graph s iG g \<Longrightarrow> is_valid_Graph_C s g"
by (force dest!: arrlist_nth_valid simp:is_graph_def uint_nat unat_mono) 

lemma is_graph_valid_edge:
  "\<lbrakk>is_graph s iG g; e < (iedge_cnt iG)\<rbrakk> \<Longrightarrow> 
   is_valid_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint e)"
by (force dest!: arrlist_nth_valid simp:is_graph_def uint_nat unat_mono) 

lemma parent_head_in_verts:
  "\<lbrakk>wf_digraph (abs_IGraph iG); 
    v < ivertex_cnt iG;
    \<forall>i\<le>n. iP (((\<lambda>v. snd (snd (snd iG) (iP v))) ^^ unat (i::32 word)) v) < iedge_cnt iG;
    i\<le>n;
    j=unat i -1  \<rbrakk> \<Longrightarrow> 
    ((\<lambda>v. snd (iedges iG (iP v))) ^^ unat i) v < ivertex_cnt iG"
  apply (case_tac "i=0", simp)
   apply (frule_tac e1="iP (((\<lambda>v. snd (snd (snd iG) (iP v))) ^^ j) v) " in
          wellformed_iGraph[THEN conjunct2])
  apply (metis less_1_simp unat_minus_one word_le_less_eq)
  apply clarsimp
  apply (erule_tac x="i - 1" in allE)
  apply (subst (asm) unat_minus_one, simp)
  apply (frule_tac e1="iP (((\<lambda>v. snd (snd (snd iG) (iP v))) ^^ j) v) " in
          wellformed_iGraph[THEN conjunct2])
  apply (simp add: less_1_simp word_le_less_eq)
  apply (metis (mono_tags, lifting) Suc_pred funpow_simp_l unat_gt_0)
  done

lemma parents_not_in_cycles_start_spc:
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          are_cycles'' s iCS' cse  \<and>
          iCS = abs_ICycles' s iCS' \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          v < ivertex_cnt iG \<and>
          (\<forall>i\<le>iN v. iP (((\<lambda>v. snd ((iedges iG) (iP v))) ^^ unat i) v) < iedge_cnt iG)) \<rbrace>
   parents_not_in_cycles_start' g cse p n v
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         parents_not_in_cycles_start_inv iG iCS iP v (unat (iN v))) \<rbrace>!"   
  (is "\<lbrace> ?pre  \<rbrace> ?prog \<lbrace> (\<lambda>_ s. P s) And (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> ?inv (unat ?numv)) \<rbrace>!" )
  unfolding parents_not_in_cycles_start'_def
  apply wpsimp
      apply (subst whileLoopE_add_inv [where 
              M="\<lambda>((i, u), s). ?numv - i" and
              I="\<lambda>(i, u) s. ?pre s \<and> 
                            i \<le> ?numv \<and> 
                            u = ((\<lambda>v. snd (iedges iG (iP v)))^^ (unat i)) v \<and>
                            ?inv (unat i)" ])
      apply wpsimp
          apply (rename_tac u'' r i' u' s i ba u)
          apply (rule_tac P1="(\<lambda>s.
                       ?pre s \<and>
                       i + 1 \<le> ?numv \<and>
                       i < ?numv \<and>
                       i = i' \<and> u = snd (iedges iG (iP u')) \<and> 
                       u = ((\<lambda>v. snd (iedges iG (iP v)))^^ (unat (i + 1))) v \<and>  
                       ?inv (unat i))"
                      and iCS1 ="iCS" and iCS'1="iCS'"
              in validNF_post_imp[OF _ vertex_not_in_cycles_start_spc])
          apply clarsimp 
          apply (rename_tac i r s) 
          apply (rule conjI; clarsimp) 
           apply (frule unat_le_mono)
           apply (frule parents_not_in_cycles_start_inv_le, simp) 
           apply (subst(asm) unat_Suc2, fastforce)+  
           apply (simp only:parents_not_in_cycles_start_inv_step, simp) 
          apply (rule conjI)   
           apply (metis Suc_eq_plus1 less_is_non_zero_p1 
                  word_overflow_unat parents_not_in_cycles_start_inv_stepD)
          apply (simp add: unat_minus_plus1_less word_less_nat_alt)
          apply(fastforce dest!: arrlist_nth_valid simp: is_numm_def uint_nat word_less_def) 
         apply wp+
       apply clarsimp
       apply (rename_tac i s)
       apply(subgoal_tac "unat (i + 1) = unat i + 1", simp)
        apply (clarsimp simp: is_graph_valid_graph)
        apply (rule conjI, simp add:is_numm_arrlist_heap inc_le) 
        apply (rule conjI, simp add: is_numm_arrlist_heap)
        apply (rule conjI, 
               force dest!:parent_head_in_verts is_graph_head_arrlist_eq 
                     simp: is_pedge_arrlist_eq)
        apply (rule conjI)
         apply (rule is_graph_valid_edge, simp)
         apply (force dest!:parent_head_in_verts is_graph_head_arrlist_eq 
                     simp: is_pedge_arrlist_eq)
        apply (fast intro: is_pedge_valid dest: parent_head_in_verts)
       apply (fastforce simp:less_le_trans)
      apply clarsimp
      apply (case_tac "a=iN v"; simp add:is_numm_arrlist_heap)
     apply wp
    apply (rule_tac P1="(\<lambda>s. ?pre s \<and> u=v)" and iCS1 ="iCS" and iCS'1="iCS'"
           in validNF_post_imp[OF _ vertex_not_in_cycles_start_spc])
    apply (fastforce simp: parents_not_in_cycles_start_inv_def intro: is_numm_valid)
   apply wp
   apply clarsimp
   done 

definition int_neg_cyc_inv :: 
  "IGraph \<Rightarrow> IENInt \<Rightarrow>ICycle_Set \<Rightarrow> IPEdge \<Rightarrow> IEInt \<Rightarrow> IVertex \<Rightarrow> bool" 
where
  "int_neg_cyc_inv G d CS P n k = 
    (\<forall>i< k. is_inf_d d i < 0 \<longrightarrow>  
            \<not> parents_not_in_cycles_start_inv G CS P i (unat (n i)))"

lemma int_neg_cyc_inv_step :
  "k < max_word \<Longrightarrow> 
   int_neg_cyc_inv G d CS P n (k + 1) = 
    (int_neg_cyc_inv G d CS P n k \<and> 
    (is_inf_d d k < 0 \<longrightarrow>  
      \<not> parents_not_in_cycles_start_inv G CS P k (unat (n k))))"
by (fastforce simp: int_neg_cyc_inv_def less_x_plus_1 not_less_iff_gr_or_eq)

lemma int_neg_cyc_spc:
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          are_cycles'' s iCS' cse  \<and>
          iCS = abs_ICycles' s iCS' \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          (\<forall>v \<le>ivertex_cnt iG.  \<forall>i\<le>iN v. 
             iP (((\<lambda>v. snd ((iedges iG) (iP v))) ^^ unat i) v) < iedge_cnt iG)) \<rbrace>
   int_neg_cyc' g d cse p n
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         int_neg_cyc_inv iG iD iCS iP iN (ivertex_cnt iG)) \<rbrace>!"   
(is 
  "\<lbrace> ?pre  \<rbrace> 
   ?prog
   \<lbrace> (\<lambda>_ s. P s) And (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
        ?inv (?verts:: 32 word)) \<rbrace>!" )
  unfolding int_neg_cyc'_def
  apply wpsimp
    apply (subst whileLoopE_add_inv [where 
            M="\<lambda>(i, s).  ?verts -  i" and
            I="\<lambda>i s. ?pre s \<and>  i \<le> ?verts \<and> ?inv i"])
    apply wp
       apply clarsimp

       apply (rule_tac P1="(\<lambda>s.
                       ?pre s \<and>
                       i < ?verts \<and>
                       is_inf_d iD  i < 0\<and>
                       ?inv i)"
                      and iCS1 ="iCS" and iCS'1="iCS'" and iN1=iN and iP1=iP and iG1=iG
              in validNF_post_imp[OF _ parents_not_in_cycles_start_spc])
       apply clarsimp
       apply (rule conjI; rule impI)
        apply (fastforce simp: int_neg_cyc_inv_def) 
       apply (rule conjI, fastforce intro: inc_le) 
       apply (rule conjI, fastforce simp: int_neg_cyc_inv_def intro: le_step)
       apply (simp add: is_graph_valid_graph unat_minus_plus1_less word_less_nat_alt)
      apply wp+
     apply clarsimp
     apply (rule conjI; clarsimp)
      apply (fastforce dest: is_dist_arrlist_is_inf is_dist_valid simp: is_graph_def)
     apply (rule conjI, fastforce intro!: inc_le simp: is_graph_def) 
     apply (rule conjI)
      apply (rule int_neg_cyc_inv_step[THEN iffD2])
       apply (metis max_word_max not_le not_less_iff_gr_or_eq)
      apply (simp add: is_graph_def is_dist_arrlist_is_inf)
     apply (simp add: is_graph_def unat_minus_plus1_less word_less_nat_alt is_dist_valid)
    apply (clarsimp simp: is_graph_def)
   apply wp
  apply (clarsimp simp: int_neg_cyc_inv_def is_graph_valid_graph)
  done


(**to be updated to step3 *)
(*


lemma shortest_paths_locale_step3_eq_maths:
  "\<And>G s c n p d pred.
    shortest_paths_locale_step3_inv G s c n p d pred
    =
    shortest_paths_locale_step3_pred
    (abs_IGraph G) s (abs_ICost c) (abs_INat n)
    (abs_IPedge p) (abs_IDist d) (abs_IPedge pred)"
  sorry
definition shortest_paths_locale_step2_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> ICost \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> IENInt \<Rightarrow> IPEdge \<Rightarrow> bool" where
  "shortest_paths_locale_step2_inv G sc c n p d pred  \<equiv>
   shortest_paths_locale_step1_inv G sc n p d \<and>
   basic_just_sp_inv G d c sc n pred \<and>
   source_val_inv G sc d n (ivertex_cnt G)\<and>
   no_edge_Vm_Vf_inv G d (iedge_cnt G)"

lemma shortest_paths_locale_step2_spc_intermediate:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_cost s iG iC c \<and>
          is_pedge s iG iP p \<and>
          is_pedge s iG iPred pred)\<rbrace>
   shortest_paths_locale_step2' g sc c n pred d p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
        shortest_paths_locale_step2_inv iG sc iC iN iP iD iPred)\<rbrace>!"
  apply (clarsimp simp: shortest_paths_locale_step2'_def shortest_paths_locale_step2_inv_def)
  apply wp
      apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_cost s iG iC c \<and>
          is_pedge s iG iP p \<and>
          is_pedge s iG iPred pred \<and>
          shortest_paths_locale_step1_inv iG sc iN iP iD \<and> 
          basic_just_sp_inv iG iD iC sc iN iPred \<and>
          source_val_inv iG sc iD iN (fst iG))" 
      in validNF_post_imp[OF _ no_edge_Vm_Vf_spc'])
      apply fastforce  
     apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_cost s iG iC c \<and>
          is_pedge s iG iP p \<and>
          is_pedge s iG iPred pred \<and>
          shortest_paths_locale_step1_inv iG sc iN iP iD \<and> 
          basic_just_sp_inv iG iD iC sc iN iPred)" 
      in validNF_post_imp[OF _ source_val_spc'])
     apply (unfold basic_just_sp_inv_def, fastforce simp: wf_inv_is_wf_digraph)[1]
    apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_cost s iG iC c \<and>
          is_pedge s iG iP p \<and>
          is_pedge s iG iPred pred \<and>
          shortest_paths_locale_step1_inv iG sc iN iP iD)" 
      in validNF_post_imp[OF _ check_basic_just_sp_spc_intermediate])
    apply (unfold shortest_paths_locale_step1_inv_def s_assms_inv_def, fastforce simp: wf_inv_is_wf_digraph)[1]
   apply (rule_tac P1=" P and 
    (\<lambda>s.  is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_cost s iG iC c \<and>
          is_numm s iG iN n \<and>
          is_pedge s iG iP p \<and>
          is_pedge s iG iPred pred)" 
      in validNF_post_imp[OF _ shortest_paths_locale_step1_spc_intermediate])
   apply (clarsimp, unfold shortest_paths_locale_step1_inv_def s_assms_inv_def, fast) 
  apply blast
  done 

lemma abs_INat_to_abs_INum:
    "shortest_paths_locale_step1
    (abs_IGraph G) s (abs_INat n)
    (abs_IPedge pred) (abs_IDist d) \<Longrightarrow> (shortest_paths_locale_step1.enum (abs_INat n) (abs_IDist d)) = (abs_INum n d)"
  using shortest_paths_locale_step1.enum_def[where
      ?G="(abs_IGraph G)" and ?s=s and ?num="(abs_INat n)" and
      ?parent_edge="(abs_IPedge pred)" and ?dist="(abs_IDist d)"]
  unfolding abs_INum_def abs_IDist_def abs_INat_def
  by auto

lemma shortest_paths_locale_step2_eq_maths:
  "\<And>G s c n p d pred.
    shortest_paths_locale_step2_inv G s c n p d pred
    =
    shortest_paths_locale_step2_pred
    (abs_IGraph G) s (abs_ICost c) (abs_INat n)
    (abs_IPedge p) (abs_IDist d) (abs_IPedge pred)"
proof -
  fix G c s n p d pred
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?ac = "abs_ICost c"
  let ?an = "abs_INat n"
  let ?ap = "abs_IPedge p"
  show "?thesis G s c n p d pred"
    unfolding  shortest_paths_locale_step2_inv_def 
      shortest_paths_locale_step2_pred_def 
      shortest_paths_locale_step2_pred_axioms_def
    by (metis (no_types, hide_lams) atLeastLessThan_iff no_edge_Vm_Vf_inv_eq_maths abs_INat_to_abs_INum 
      basic_just_sp_eq_maths shortest_paths_locale_step1_inv_eq_maths source_val_inv_eq_maths verts_absI 
      shortest_paths_locale_step1.s_assms(1))
qed

lemma shortest_paths_locale_step2_spc:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_dist s iG iD d \<and>
          is_numm s iG iN n \<and>
          is_cost s iG iC c \<and>
          is_pedge s iG iP p \<and>
          is_pedge s iG iPred pred)\<rbrace>
   shortest_paths_locale_step2' g sc c n pred d p
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
        shortest_paths_locale_step2_pred
    (abs_IGraph iG) sc (abs_ICost iC) (abs_INat iN)
    (abs_IPedge iP) (abs_IDist iD) (abs_IPedge iPred))\<rbrace>!"
     using validNF_post_imp[OF _ shortest_paths_locale_step2_spc_intermediate] 
        shortest_paths_locale_step2_eq_maths 
     by simp
*)

end

end
