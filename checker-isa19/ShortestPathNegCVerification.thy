(* uses Isabelle2019 and autocorres version 1.6 *)
theory ShortestPathNegCVerification
  imports
  "HOL-Library.Option_ord"
  "Library/Autocorres_Misc"
  "ShortestPath/ShortestPathNeg"
begin

install_C_file "shortest_path_neg_checker.c"

autocorres [unsigned_word_abs=awalktwo cas cyc_in_graph] "shortest_path_neg_checker.c"

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
(*
abbreviation icycles_num ::
  "ICycle_Set \<Rightarrow> 32 word"
where
  "icycles_num CS \<equiv> fst CS"

abbreviation icycles :: "ICycle_Set \<Rightarrow> ICycle list"
where
  "icycles CS \<equiv> snd CS"
       
abbreviation icycles'_num ::
  "ICycle_Set' \<Rightarrow> 32 word"
where
  "icycles'_num CS \<equiv> fst CS"

abbreviation icycles' :: "ICycle_Set' \<Rightarrow> ICycle' list"
where
  "icycles' CS \<equiv> snd CS"
*)

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

(*
fun mk_icycle_list :: 
  "ICycle_Set \<Rightarrow> ICycle list"
where 
  "mk_icycle_list CS = mk_list' (unat (icycles_num CS)) (icycles CS)"
*)
(*
fun mk_icycle_list ::
  "ICycle_Set \<Rightarrow> ICycle list"
where
  "mk_icycle_list CS = icycles CS"
*)
(*
fun mk_icycle'_list :: 
  "ICycle_Set' \<Rightarrow> ICycle' list"
where 
  "mk_icycle'_list CS = mk_list' (unat (icycles'_num CS)) (icycles' CS)"
*)

(*
fun mk_icycle'_list ::
"ICycle_Set' \<Rightarrow> ICycle' list"
where
"mk_icycle'_list CS = icycles' CS"
*)
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
  by (metis (no_types) ab_semigroup_add_class.add_ac(1) right_minus_eq measure_unat
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

(*
definition 
  from_icycle'_to_icycle_list ::
  "'a lifted_globals_scheme \<Rightarrow> ICycle'\<Rightarrow> ICycle \<Rightarrow> bool"
where
   "from_icycle'_to_icycle_list h iC' iC \<equiv>
    icycle_start iC = icycle'_start iC' \<and> 
    icycle_length iC = icycle'_length iC' \<and>
    is_path h iC (icycle'_path iC')"

definition is_cycle 
where
  "is_cycle h iC p \<equiv>
    is_valid_Cycle_C h p \<and> 
    icycle_start iC = start_C (heap_Cycle_C h p) \<and> 
    unat (icycle_length iC) = length (icycle_path iC) \<and>
    icycle_length iC = length_C (heap_Cycle_C h p) \<and>
    is_path h iC (path_C (heap_Cycle_C h p))"
*)

definition 
  is_cycle :: "'a lifted_globals_scheme \<Rightarrow> ICycle \<Rightarrow> Cycle_C ptr \<Rightarrow> bool"
where
  "is_cycle h iC p \<equiv>
    is_valid_Cycle_C h p \<and> 
    icycle_start iC = start_C (heap_Cycle_C h p) \<and> 
    length (icycle_path iC) = unat (length_C (heap_Cycle_C h p)) \<and>
    is_path h (icycle_path iC) (path_C (heap_Cycle_C h p))"
(*
definition final_is_cycle
where
  "final_is_cycle h iC' p \<equiv>
    is_valid_Cycle_C h p \<and>
    icycle'_start iC' = start_C (heap_Cycle_C h p) \<and>
    icycle'_length iC' = length_C (heap_Cycle_C h p) \<and>
    is_path h (abs_ICycle' h iC') (path_C (heap_Cycle_C h p))"
*)

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

(*
definition are_cycles
where
  "are_cycles h iCS p \<equiv>
    is_valid_Cycle_set_C h p \<and>
    icycles'_num iCS' = no_cycles_C (heap_Cycle_set_C h p) \<and> 
    arrlist (heap_Cycle_C h) (is_valid_Cycle_C h)
       (map to_cycle (icycles' iCS'))  (cyc_obj_C (heap_Cycle_set_C h p))"
*)
(*give  array_addrs*)

(*
definition is_cycle'
where
  "is_cycle' h iC p \<equiv>
    is_valid_Cycle_C h p \<and> 
    icycle'_start iC = start_C (heap_Cycle_C h p) \<and> 
    icycle'_length iC = length_C (heap_Cycle_C h p) \<and>
    icycle'_path iC = (path_C (heap_Cycle_C h p))"
 
definition is_cycle_set
where
  "is_cycle_set h iS p iC \<equiv>
    is_valid_Cycle_set_C h p \<and> 
    icycles_num iS = no_cycles_C (heap_Cycle_set_C h p) \<and> 
    arrlist (heap_Cycle_C h) (is_valid_Cycle_C h)
      ( (mk_icycle'_list iS)) (cyc_obj_C (heap_Cycle_set_C h p))"

*)

(*
function from  iCycle to Cycle_C

Operator:  arrlist (heap_Cycle_C h) (is_valid_Cycle_C h) ::
  Cycle_C list \<Rightarrow> Cycle_C ptr \<Rightarrow> bool
Operand:   mk_icycle_list iS :: (32 word \<times> 32 word \<times> (32 word \<Rightarrow> 32 word)) list

    icycles iS = is_cycle h (abs_) (cyc_obj_C (heap_Cycle_set_C h p))"
*)
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

lemma word_less_arith_simp[simp]:
  "\<lbrakk> x \<noteq> 0; (x :: 32 word) < l \<rbrakk> \<Longrightarrow> (x - 1) < l"
  by (simp add: less_1_simp)
  

(* Try structure for locale 3 **)
(*
if(shortest_paths_locale_step2(g, s, c, num, pred, dist, parent_edge) == 0) return 0;
    if(C_se(g, cse, c, dist) == 0) return 0;
    if(int_neg_cyc(g, s, dist, cse, c, parent_edge, num) == 0) return 0;
*)


(****)




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
     apply ((rule conjI)+, rule impI, clarsimp, rule_tac x = "ee" in exI, clarsimp, simp add: tail_heap)
       apply (rule impI, (rule conjI)+, rule impI, clarsimp, rule_tac x = "ee" in exI, clarsimp, simp add: head_heap)
        apply (rule impI, rule conjI, rule conjI, clarsimp, rule conjI)
           apply (metis inc_le not_le head_heap tail_heap word_le_less_eq) 
          apply (metis inc_le)
         apply (metis unat_minus_plus1_less)
        apply (force intro: unat_minus_plus1_less)
       apply (fast intro: unat_minus_plus1_less)
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (clarsimp simp: if_bool_eq_conj)+
   apply wp
  apply force
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
     apply (clarsimp simp del: Word_Lemmas.sint_0)
     apply (rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold trian_inv_def is_dist_def is_graph_def)[1] 
       apply (clarsimp simp del: Word_Lemmas.sint_0, rule_tac x=ee in exI, clarsimp simp del: Word_Lemmas.sint_0)
       apply (metis Word.sint_0 int_unat not_le is_inf_d_heap s_C_pte t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph)
      apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
         apply (unfold trian_inv_def is_dist_def is_cost_def is_graph_def)[1] 
         apply (clarsimp simp del: Word_Lemmas.sint_0, rule_tac x=ee in exI, clarsimp simp del: Word_Lemmas.sint_0)
         apply (rule conjI, metis Word.sint_0 is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
         apply (rule impI, rule conjI, metis (no_types, hide_lams) Word.sint_0 int_unat is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph)
         apply (subst arrlist_heap[where iL=iC], blast, blast, subst tail_heap, blast, blast, subst head_heap, blast, blast)
         apply (subst val_d_heap, blast, metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
         apply (subst val_d_heap, blast, metis s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
         apply (simp add: uint_nat)
        apply (rule conjI, rule impI, rule conjI)
          apply (unfold is_dist_def is_numm_def is_pedge_def is_cost_def is_graph_def)[1] 
          apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
           apply (subgoal_tac "ee < (max_word::32 word)") 
            apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
            apply (clarsimp simp del: Word_Lemmas.sint_0)
            apply (rule conjI, rule impI, rule conjI)
              apply (subst head_heap, blast, simp, subst is_inf_d_heap, blast,
                     metis (no_types, hide_lams) not_le t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat, simp)
             apply (rule impI, subst arrlist_heap[where iL=iC], blast, fast)
             apply (subst head_heap, blast, fast, subst tail_heap, blast, fast)
             apply (subst val_d_heap, blast, metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
             apply (subst val_d_heap, blast, metis s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
             apply (simp add: uint_nat)
            apply (rule impI, subst head_heap, blast, blast, subst is_inf_d_heap, blast, metis t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
            apply (metis is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
           apply (metis max_word_max not_le word_le_less_eq)
          apply (metis inc_le)
         apply (rule conjI, unfold is_graph_def, metis inc_le)[1]
         apply (rule conjI, metis unat_minus_plus1_less)
         apply (rule conjI)
          apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule conjI, unfold is_dist_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (metis wellformed_iGraph word_less_nat_alt)
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (rule conjI, blast intro: signed_overflow)
        apply (rule conjI, blast intro: signed_underflow)
        apply (rule conjI, unfold is_cost_def is_graph_def is_dist_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (metis wellformed_iGraph word_less_nat_alt)
       apply (rule conjI, rule impI, rule conjI)
         apply (unfold is_dist_def is_numm_def is_pedge_def is_cost_def is_graph_def)[1] 
         apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
          apply (subgoal_tac "ee < (max_word::32 word)") 
           apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
           apply (clarsimp simp del: Word_Lemmas.sint_0)
           apply (metis (no_types, hide_lams) Word_Lemmas.sint_0 int_unat less_le not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph)
          apply (metis max_word_max not_le word_le_less_eq)
         apply (metis inc_le)
        apply (rule conjI, unfold is_graph_def, metis inc_le)[1]
        apply (rule conjI, metis unat_minus_plus1_less)
        apply (rule conjI)
         apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule conjI, unfold is_dist_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (metis wellformed_iGraph word_less_nat_alt)
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply (unfold is_graph_def is_dist_def, rule conjI)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (metis wellformed_iGraph word_less_nat_alt)
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (unfold is_graph_def is_dist_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (metis wellformed_iGraph word_less_nat_alt)
     apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
        apply (unfold trian_inv_def is_graph_def is_dist_def)[1]
        apply (clarsimp simp del: Word_Lemmas.sint_0, rule_tac x=ee in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (subst (asm) (4) tail_heap, fast, fast, subst (asm) (4) head_heap, fast, fast)
        apply (subst (asm) (7) is_inf_d_heap, blast, metis head_heap wellformed_iGraph)
        apply (subst (asm) (6) is_inf_d_heap, blast, metis tail_heap wellformed_iGraph)
        apply linarith
       apply (rule conjI, rule impI, rule conjI)
         apply (unfold is_dist_def is_numm_def is_pedge_def is_cost_def is_graph_def)[1] 
         apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
          apply (subgoal_tac "ee < (max_word::32 word)") 
           apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
           apply (clarsimp simp del: Word_Lemmas.sint_0)
           apply (metis (no_types, hide_lams) less_le not_le is_inf_d_heap t_C_pte two_comp_to_edge_arrlist_heap 
                  wellformed_iGraph uint_nat)
          apply (metis max_word_max not_le word_le_less_eq)
         apply (metis inc_le)
        apply (rule conjI, unfold is_graph_def, metis inc_le)[1]
        apply (rule conjI, metis unat_minus_plus1_less)
        apply (clarsimp simp: if_bool_eq_conj)+
       apply (unfold is_graph_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply (metis wellformed_iGraph word_less_nat_alt)
      apply (rule conjI, rule impI, rule conjI)
        apply (unfold is_dist_def is_numm_def is_pedge_def is_cost_def is_graph_def)[1] 
        apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
         apply (subgoal_tac "ee < (max_word::32 word)") 
          apply (drule trian_inv_step[where d=iD and G=iG and c=iC])
          apply (clarsimp simp del: Word_Lemmas.sint_0)
          apply (metis Word_Lemmas.sint_0 int_unat is_inf_d_heap s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph)
         apply (metis max_word_max not_le word_le_less_eq)
        apply (metis inc_le)
       apply (rule conjI, unfold is_graph_def, metis inc_le)[1]
       apply (rule conjI, metis shortest_path_neg_checker.unat_minus_plus1_less)
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule conjI, unfold is_graph_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply (metis wellformed_iGraph word_less_nat_alt)
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (rule conjI, unfold is_graph_def is_dist_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (metis wellformed_iGraph word_less_nat_alt)
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis is_graph_def word_le_less_eq)
   apply wp
  apply (unfold is_graph_def trian_inv_def, force)
  done

definition just_inv :: 
  "IGraph \<Rightarrow> IENInt \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> 32 word \<Rightarrow> bool" where
  "just_inv G d c s n p k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> is_inf_d d v = 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        is_inf_d d (fst (iedges G e)) = 0 \<and> 
        val_d d v = val_d d (fst (iedges G e)) + sint (c e) \<and>
        cast_long (n v) = cast_long (n (fst (iedges G e))) + 1)"

lemma just_inv_step:
  assumes v_less_max: "v < (max_word::32 word)"
  shows "just_inv G d c s n p (v + 1) \<longleftrightarrow> just_inv G d c s n p v
    \<and> (v \<noteq> s \<and> is_inf_d d v = 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and> 
        v = snd (iedges G e) \<and>
        is_inf_d d (fst (iedges G e)) = 0 \<and>
        val_d d v = val_d d (fst (iedges G e)) + sint (c e) \<and>
        cast_long (n v) = cast_long (n (fst (iedges G e))) + 1))"
  unfolding just_inv_def apply safe
  by (metis less_x_plus_1 max_word_max not_le v_less_max)+
                  
  
lemma just_inv_le:
  assumes leq: "j \<le> i" 
  assumes just_i: "just_inv G d c s n p i"
  shows "just_inv G d c s n p j"
  using assms 
  by (induct j) (auto simp add: just_inv_def)

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
     apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
        apply (unfold just_inv_def is_graph_def is_pedge_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
        apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (rule conjI, subst is_inf_d_heap, blast, fast, fastforce)
        apply (clarsimp, subst (asm) (13) arrlist_heap[where iL=iP], blast, blast, simp add: int_unat sint_ucast)
       apply (rule impI, rule conjI, rule impI, rule conjI, blast)
        apply (unfold just_inv_def is_graph_def is_pedge_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
        apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (rule conjI, subst is_inf_d_heap, blast, fast, fastforce)
        apply (clarsimp, subst (asm) (12) arrlist_heap[where iL=iP], blast, blast, simp add: int_unat sint_ucast)
       apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
         apply (unfold just_inv_def is_graph_def is_pedge_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
         apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
         apply (rule conjI, subst is_inf_d_heap, blast, fast, fastforce)
         apply (clarsimp, subst (asm) (11) arrlist_heap[where iL=iP], blast, blast)
         apply (subst (asm) (2) head_heap, blast, simp add: uint_nat, simp add: uint_nat)
        apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
          apply (unfold just_inv_def is_graph_def is_pedge_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
          apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
          apply (rule conjI, subst is_inf_d_heap, blast, fast, fastforce)
          apply (clarsimp simp del: Word_Lemmas.sint_0, subst (asm) (10) arrlist_heap[where iL=iP], blast, blast)
          apply (subst (asm) (5) tail_heap, blast, simp add: uint_nat)
          apply (subst (asm) (3) is_inf_d_heap, fast, metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
          apply (simp add: uint_nat)
         apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
           apply (unfold just_inv_def is_graph_def is_pedge_def is_dist_def is_cost_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
           apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
           apply (rule conjI, subst is_inf_d_heap, blast, fast, fastforce)
           apply (clarsimp simp del: Word_Lemmas.sint_0, subst (asm) (9) arrlist_heap[where iL=iP], blast, blast)
           apply (subst (asm) (2) arrlist_heap[where iL=iC], blast, simp add: uint_nat)
           apply (subst (asm) (8) arrlist_heap[where iL=iP], blast, blast)
           apply (subst (asm) (4) tail_heap, blast, simp add: uint_nat)
           apply (subst (asm) (4) val_d_heap, fast, metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
           apply (subst (asm) (3) val_d_heap, fast, fast, simp add: uint_nat)
          apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
            apply (unfold just_inv_def is_graph_def is_pedge_def is_dist_def is_numm_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
            apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
            apply (rule conjI, subst is_inf_d_heap, blast, fast, fastforce)
            apply (clarsimp, subst (asm) (14) arrlist_heap[where iL=iP], blast, blast)
            apply (subst (asm) (6) tail_heap, blast, simp add: uint_nat)
            apply (subst (asm) (4) arrlist_heap[where iL=iN], fast, metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
            apply (subst (asm) (3) arrlist_heap[where iL=iN], fast, fast, simp add: uint_nat)
           apply (rule conjI, rule impI, clarsimp)
            apply (rule conjI)
             apply (subgoal_tac " vv + 1 \<le> fst iG")
              apply (subgoal_tac "vv < (max_word::32 word)")
               apply (drule just_inv_step[where G=iG and d=iD and c=iC and s=sc and n=iN and p=iP])
               apply (clarsimp simp del: Word_Lemmas.sint_0)+
               apply (unfold is_graph_def is_dist_def is_numm_def is_cost_def is_pedge_def)[1]
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, simp add: sint_ucast uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, simp add: uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst head_heap, force, simp add: uint_nat, simp add: uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat, subst is_inf_d_heap,
                      simp, simp add: uint_nat, metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add: uint_nat)
               apply (rule conjI, subst arrlist_heap[where iL=iP], simp, fast, subst arrlist_heap[where iL=iP], simp, fast,
                      subst arrlist_heap[where iL=iC], simp, simp add: uint_nat, subst tail_heap, force, simp add: uint_nat,
                      subst val_d_heap, simp, fast, subst val_d_heap, simp, simp add: uint_nat,
                      metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add: uint_nat)
               apply (subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                      subst arrlist_heap[where iL=iN], simp, fast, subst arrlist_heap[where iL=iN], simp, simp add: uint_nat, 
                      metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add: uint_nat)
              apply (metis max_word_max not_le word_le_less_eq)
             apply (metis inc_le is_graph_def)
            apply (rule conjI, metis inc_le is_graph_def)
            apply (rule conjI, metis is_graph_def unat_minus_plus1_less)
            apply (unfold is_graph_def)[1]
            apply (clarsimp simp: if_bool_eq_conj)+
           apply (unfold is_graph_def is_dist_def is_pedge_def is_numm_def is_cost_def)[1]
           apply (rule conjI)
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply (rule conjI)
            apply (clarsimp simp: if_bool_eq_conj)+
            apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
            apply (metis not_le wellformed_iGraph word_less_nat_alt)
            apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (rule conjI, unfold is_graph_def is_dist_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (rule conjI, blast intro: signed_overflow)
          apply (rule conjI, blast intro: signed_underflow)
          apply (rule conjI)
           apply (unfold is_graph_def is_cost_def is_pedge_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (rule conjI)
           apply (unfold is_graph_def is_dist_def is_pedge_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply (metis not_le wellformed_iGraph word_less_nat_alt)
          apply (rule conjI)
           apply (unfold is_graph_def is_pedge_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule conjI)
           apply (unfold is_graph_def is_dist_def is_pedge_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply (metis not_le wellformed_iGraph word_less_nat_alt)
          apply (rule conjI)
           apply (unfold is_graph_def is_pedge_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (unfold is_graph_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule conjI)
         apply (unfold is_graph_def is_pedge_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
        apply (unfold is_graph_def)[1]
        apply (clarsimp simp: if_bool_eq_conj)+
       apply (unfold is_graph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule conjI, rule impI, rule conjI)
        apply (subgoal_tac " vv + 1 \<le> fst iG")
         apply (subgoal_tac "vv < (max_word::32 word)")
          apply (drule just_inv_step[where G=iG and d=iD and c=iC and s=sc and n=iN and p=iP])
          apply (clarsimp simp del: Word_Lemmas.sint_0)
          apply (unfold is_graph_def is_dist_def)[1]
          apply (subst (asm) is_inf_d_heap, force, fastforce, simp)
         apply (metis max_word_max not_le word_le_less_eq)
        apply (metis inc_le is_graph_def)
       apply (rule conjI, metis inc_le is_graph_def)
       apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
       apply (unfold is_graph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (unfold is_graph_def is_dist_def is_pedge_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule conjI)
      apply (subgoal_tac " sc + 1 \<le> fst iG")
       apply (subgoal_tac "sc < (max_word::32 word)")
        apply (drule just_inv_step[where G=iG and d=iD and c=iC and s=sc and n=iN and p=iP])
        apply clarsimp
       apply (metis max_word_max not_le word_le_less_eq)
      apply (metis inc_le is_graph_def)
     apply (rule conjI, metis inc_le is_graph_def)
     apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
     apply (rule conjI, force simp add: is_graph_def)
     apply (unfold is_graph_def is_pedge_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis is_graph_def word_le_less_eq)
   apply wp
  apply (unfold just_inv_def is_graph_def)[1]
  apply auto
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

lemma wf_inv_is_wf_digraph:
   "is_wellformed_inv G (iedge_cnt G) \<longleftrightarrow> wf_digraph (abs_IGraph G)"
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
    (\<exists>i. abs_INum n d v = enat i) \<longrightarrow>
    (\<exists> e. (abs_IPedge p v) = Some e \<and>
     e < (fst (snd G)) \<and>
     v = snd (snd (snd G) e) \<and>
     abs_IDist d v =
       abs_IDist d (fst (snd (snd G) e)) + ereal (abs_ICost c e) \<and>
     abs_INum n d v = 
       abs_INum n d (fst (snd (snd G) e)) + enat (Suc 0)))"
  apply (simp add: just_inv_def)
  apply (rule iffI; clarsimp; erule_tac x=v in allE)
   apply (rule_tac x="p v" in exI; clarsimp simp: abs_IPedge_def)
   apply (case_tac "snd(d v) = 0"; clarsimp simp: not_le word_msb_sint abs_INum_def)
   apply (rule conjI)
    apply (simp add: add_ucast_no_overflow_unat abs_IDist_def abs_ICost_def abs_IPedge_def)
   apply (metis add.right_neutral add_Suc_right long_ucast word_add_cast_up_no_overflow unat_eq_1(2))
  apply (clarsimp simp add: abs_IPedge_def)
   apply (subgoal_tac "\<exists>i. abs_INum n d v = enat i"; simp add: abs_INum_def) 
  apply (case_tac "msb (p v)"; 
      clarsimp simp: not_le word_msb_sint 
      abs_INum_def abs_IDist_def abs_ICost_def)  
  apply (case_tac "n (fst (snd (snd G) (p v))) = 0") 
   apply (case_tac "snd (d v) = 0"; 
      case_tac "snd (d (fst (snd (snd G) (p v)))) = 0"; 
      clarsimp simp: add_ucast_no_overflow_unat)
   apply (simp add: unat_eq_1(2))
  apply (metis add.commute of_nat_Suc ucast_nat_def)
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
  apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, fast)
    apply (rule impI, rule conjI, rule impI, rule impI, rule impI, rule disjI1)
     apply (unfold is_graph_def is_dist_def)[1]
     apply (subst Word_Lemmas.sint_0[symmetric], subst is_inf_d_heap, simp, argo, subst val_d_heap, simp, argo, simp)
    apply (unfold is_graph_def is_dist_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, blast)
    apply (rule impI, rule conjI, rule impI, rule impI, rule disjI2)
     apply (unfold just_inv_def is_graph_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
     apply (rule_tac x=sc in exI, clarsimp simp del: Word_Lemmas.sint_0)
     apply (metis not_le ENInt_isInf_C_pte two_comp_arrlist_heap)
    apply (unfold is_graph_def is_dist_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply (rule impI, rule conjI, (rule impI)+, rule disjI2)
    apply (unfold just_inv_def is_graph_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
   apply (rule impI, rule conjI, unfold is_graph_def is_dist_def)[1]
    apply (subst is_inf_d_heap, simp, argo, simp add: uint_nat)
    apply (subst Word_Lemmas.sint_0[symmetric], subst is_inf_d_heap, simp, presburger, simp add: uint_nat)
   apply (rule conjI, metis wf_inv_is_wf_digraph)
    apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply (rule impI, rule conjI, rule impI, rule conjI, (rule impI)+, rule disjI1)
     apply (unfold is_graph_def is_dist_def)[1]
    apply (subst Word_Lemmas.sint_0[symmetric], subst is_inf_d_heap, simp, argo, subst val_d_heap, simp, argo, simp)
   apply (rule impI, rule conjI, unfold is_graph_def is_dist_def)[1]
    apply (subst is_inf_d_heap, simp, argo, simp add: uint_nat)
   apply (rule conjI, rule impI, subst val_d_heap, simp, argo, simp add: uint_nat)
  apply (rule conjI, metis wf_inv_is_wf_digraph)
    apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, argo)
   apply (rule impI, rule conjI, rule impI, rule impI, rule disjI2)
     apply (unfold just_inv_def is_graph_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
     apply (rule_tac x=sc in exI, clarsimp simp del: Word_Lemmas.sint_0)
    apply (metis not_le ENInt_isInf_C_pte two_comp_arrlist_heap)
  apply (unfold is_graph_def is_dist_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply (rule impI, rule conjI, rule impI, meson)
  apply (rule impI, rule conjI, unfold is_graph_def is_dist_def)[1]
   apply (subst is_inf_d_heap, simp, argo, simp add: uint_nat)
  apply (rule conjI, subst Word_Lemmas.sint_0[symmetric], subst is_inf_d_heap, simp, argo, simp add: uint_nat)
  apply (rule conjI, metis wf_inv_is_wf_digraph)
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
    (abs_ICost c) s (abs_INum n d) (abs_IPedge p) 
    "
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?ac = "abs_ICost c"
  let ?an = "abs_INum n d"  
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

lemma basic_just_sp_eq_maths:
  "\<And>G d c s n p. 
    (s < ivertex_cnt G \<and>
    basic_just_sp_inv G d c s n p)
    =
    basic_just_sp_pred 
    (abs_IGraph G) (abs_IDist d) 
    (abs_ICost c) s (abs_INum n d) (abs_IPedge p) 
    "
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?ac = "abs_ICost c"
  let ?an = "abs_INum n d"  
  let ?ap = "abs_IPedge p"
  show "?thesis G d c s n p"
    unfolding basic_just_sp_inv_def
    using basic_just_sp_eq_invariants_imp 
    by blast
qed

definition s_assms_inv :: "IGraph \<Rightarrow> IVertex \<Rightarrow> IENInt \<Rightarrow> IPEdge \<Rightarrow> IEInt \<Rightarrow> bool" where
  "s_assms_inv G sc d p n \<equiv> 
      sc < ivertex_cnt G \<and>
      is_inf_d d sc \<le> 0 \<and>
      sint (p sc) < 0 \<and>
      n sc = 0"

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
  apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
       apply (clarsimp, subst (asm) arrlist_heap[where iL=iN], fast, blast, metis uint_nat)
      apply (unfold s_assms_inv_def is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule conjI, rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p uint sc)" in notE)
      apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p int (unat sc))" in notE)
     apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p int (unat sc)))" in notE)
    apply (unfold s_assms_inv_def is_graph_def is_pedge_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_less_nat_alt)
   apply (rule impI, rule conjI, rule impI)
    apply (rule ccontr, erule_tac P="is_valid_w32 s (n +\<^sub>p uint sc)" in notE)
    apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_less_nat_alt)
   apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (n +\<^sub>p uint sc)" in notE)
   apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply (metis not_le word_less_nat_alt)
  apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_graph_def is_pedge_def, clarsimp)[1]
       apply (subst (asm) arrlist_heap[where iL=iP], blast, force, metis int_unat sint_ucast)
      apply (unfold s_assms_inv_def is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p uint sc)" in notE)
     apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (metis not_le word_less_nat_alt)
    apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint sc))" in notE)
    apply (unfold s_assms_inv_def is_graph_def is_pedge_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_less_nat_alt)
   apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_dist_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
       apply (metis int_unat not_le ENInt_isInf_C_pte two_comp_arrlist_heap)
      apply (unfold s_assms_inv_def is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p (uint sc))" in notE)
     apply (unfold s_assms_inv_def is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (metis not_le word_less_nat_alt)
    apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold s_assms_inv_def is_graph_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
       apply (force intro: not_le)
      apply (unfold s_assms_inv_def is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule conjI, rule impI)
      apply (unfold s_assms_inv_def is_graph_def is_pedge_def is_numm_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule conjI, force)
      apply (rule conjI, unfold is_graph_def is_dist_def, subst is_inf_d_heap, force, simp, fastforce)
      apply (rule conjI, subst arrlist_heap[where iL=iP], fast, simp, metis uint_nat sint_ucast)
      apply (subst arrlist_heap[where iL=iN], fast, simp, metis uint_nat)
     apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule ccontr, erule_tac P="is_valid_ENInt_C s (d +\<^sub>p uint sc)" in notE)
    apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
    apply (clarsimp simp: if_bool_eq_conj)+
    apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis not_le word_less_nat_alt)
   apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (PTR_COERCE(32 signed word \<rightarrow> 32 word) (p +\<^sub>p uint sc))" in notE)
   apply (unfold s_assms_inv_def is_graph_def is_pedge_def)[1]
   apply (clarsimp simp: if_bool_eq_conj)+
   apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
   apply (metis not_le word_less_nat_alt)
  apply (rule impI, rule ccontr, erule_tac P="is_valid_w32 s (n +\<^sub>p uint sc)" in notE)
  apply (unfold s_assms_inv_def is_graph_def is_numm_def)[1]
  apply (clarsimp simp: if_bool_eq_conj)+
  apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
  apply (metis not_le word_less_nat_alt)
  done

definition parent_num_assms_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> IENInt \<Rightarrow> IPEdge \<Rightarrow> IEInt  \<Rightarrow> 32 word \<Rightarrow> bool" where
  "parent_num_assms_inv G s d p n k \<equiv>
    \<forall>v < k. v \<noteq> s \<and> is_inf_d d v \<le> 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        is_inf_d d (fst (iedges G e)) \<le> 0 \<and>
        cast_long (n v) = cast_long (n (fst (iedges G e))) + 1)"

lemma parent_num_assms_inv_step:
  assumes v_less_max: "v < (max_word::32 word)"
  shows "parent_num_assms_inv G s d p n (v + 1) \<longleftrightarrow> parent_num_assms_inv G s d p n v
    \<and> (v \<noteq> s \<and> is_inf_d d v \<le> 0 \<longrightarrow> 
      sint (p v) \<ge> 0 \<and>
      (\<exists> e. e = p v \<and> e < iedge_cnt G \<and>
        v = snd (iedges G e) \<and>
        is_inf_d d (fst (iedges G e)) \<le> 0 \<and>
          cast_long (n v) = cast_long (n (fst (iedges G e))) + 1))"
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
        apply (clarsimp, subst (asm) (9) arrlist_heap[where iL=iP], fast, fast, simp add: uint_nat sint_ucast)
       apply (rule impI, rule conjI, rule impI, rule conjI, blast)
        apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
        apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
        apply (clarsimp, subst (asm) (8) arrlist_heap[where iL=iP], fast, fast, simp add: uint_nat sint_ucast)
       apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
         apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
         apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
         apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
         apply (clarsimp, subst (asm) (2) head_heap, blast, blast)
         apply (subst (asm) (7) arrlist_heap[where iL=iP], fast, fast, simp add: uint_nat sint_ucast)
        apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
          apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
          apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
          apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
          apply (clarsimp, subst (asm) (6) arrlist_heap[where iL=iP], blast, fast)
          apply (subst (asm) (3) tail_heap, blast, simp add: uint_nat) 
          apply (subst (asm) (3) is_inf_d_heap, blast, metis not_le tail_heap wellformed_iGraph uint_nat, simp add: uint_nat)
         apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, blast)
           apply (unfold parent_num_assms_inv_def is_graph_def is_dist_def is_numm_def is_pedge_def, clarsimp simp del: Word_Lemmas.sint_0)[1]
           apply (rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
           apply (rule conjI, subst is_inf_d_heap, fast, fast, blast)
           apply (clarsimp, subst (asm) (10) arrlist_heap[where iL=iP], blast, fast, subst (asm) (4) tail_heap, blast, simp add: uint_nat)
           apply (subst (asm) (4) arrlist_heap[where iL=iN], fast, metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph uint_nat)
           apply (subst (asm) (3) arrlist_heap[where iL=iN], fast, fast, simp add: uint_nat)
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
              apply (subst arrlist_heap[where iL=iP], simp, fast, subst tail_heap, force, simp add: uint_nat,
                     subst arrlist_heap[where iL=iN], simp, fast, subst arrlist_heap[where iL=iN], simp, simp add: uint_nat,
                     metis not_le s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, simp add: uint_nat)
             apply (metis max_word_max not_le word_le_less_eq)
            apply (metis inc_le is_graph_def)
           apply (rule conjI, metis inc_le is_graph_def)
           apply (rule conjI, metis is_graph_def unat_minus_plus1_less)
           apply (unfold parent_num_assms_inv_def is_graph_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule conjI, unfold parent_num_assms_inv_def is_graph_def is_numm_def is_pedge_def)[1]
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (rule conjI)
           apply (clarsimp simp: if_bool_eq_conj)+
           apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
           apply (metis not_le wellformed_iGraph word_less_nat_alt)
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (rule conjI, unfold parent_num_assms_inv_def is_graph_def is_dist_def is_pedge_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
          apply (metis not_le wellformed_iGraph word_less_nat_alt)
         apply (rule conjI, unfold parent_num_assms_inv_def is_graph_def is_numm_def is_pedge_def)[1]
          apply (clarsimp simp: if_bool_eq_conj)+
          apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
         apply (clarsimp simp: if_bool_eq_conj)+
        apply (rule conjI, unfold parent_num_assms_inv_def is_graph_def is_numm_def is_pedge_def)[1]
         apply (clarsimp simp: if_bool_eq_conj)+
         apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (unfold is_graph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule conjI, rule impI, rule conjI)
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

lemma parent_num_assms_inv_eq_math: 
  "parent_num_assms_inv G s d p n (ivertex_cnt G) \<longleftrightarrow> 
    (\<forall>v<fst G. v \<noteq> s \<longrightarrow>
    (\<exists>i. abs_IDist d v \<noteq> \<infinity>) \<longrightarrow>
    (\<exists> e. (abs_IPedge p v) = Some e \<and>
     e < (fst (snd G)) \<and>
     v = snd (snd (snd G) e) \<and>
     abs_IDist d (fst (snd (snd G) e)) \<noteq> \<infinity> \<and>
     abs_INat n v = 
     abs_INat n (fst (snd (snd G) e)) + enat (Suc 0)))"
  apply (simp add: parent_num_assms_inv_def)
  apply (rule iffI; clarsimp; erule_tac x=v in allE)
   apply (rule_tac x= "p v" in exI, rule conjI, clarsimp simp: abs_IPedge_def, metis abs_IDist_def infinity_ereal_def 
      not_le word_msb_sint)
   apply (clarsimp simp: not_le word_msb_sint abs_INat_def) 
   apply (rule conjI, metis abs_IDist_def infinity_ereal_def not_le)
   apply (metis (mono_tags, hide_lams) abs_IDist_def PInfty_neq_ereal(1) add.right_neutral add_Suc_right ereal.distinct(5) 
      infinity_ereal_def not_le long_ucast word_add_cast_up_no_overflow unat_eq_1(2))
  apply ((safe)[1], (fastforce simp add: abs_IDist_def)+, unfold abs_IGraph_def abs_IDist_def abs_INat_def abs_IPedge_def, simp_all)
     apply (simp add: word_msb_sint)+
   apply (metis (mono_tags, hide_lams) add.right_neutral add_Suc_right long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_unat.Rep_inject)+
  done

lemma s_assms_eq_math:
  "s_assms_inv G sc d p n  \<longleftrightarrow> 
   (sc \<in> verts (abs_IGraph G) \<and>
    abs_IDist d sc \<noteq> \<infinity> \<and>
    abs_IPedge p sc = None \<and>
    abs_INat n sc = 0)"
  apply safe
      apply (unfold s_assms_inv_def abs_IGraph_def, clarsimp)[1]
     apply (unfold s_assms_inv_def abs_IDist_def, clarsimp)[1]
    apply (unfold s_assms_inv_def abs_IDist_def, clarsimp)[1]
  using word_msb_sint apply blast
   apply (unfold s_assms_inv_def abs_INat_def, clarsimp)[1]
  apply (unfold s_assms_inv_def abs_IGraph_def abs_IDist_def abs_INat_def abs_IPedge_def, clarsimp)
   apply (simp add: unat_eq_zero word_msb_sint zero_enat_def)+
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

lemma shortest_paths_locale_step1_inv_eq_maths:
  "\<And>G d s n p. 
    shortest_paths_locale_step1_inv G s n p d
    =
    shortest_paths_locale_step1
    (abs_IGraph G) s (abs_INat n)
    (abs_IPedge p) (abs_IDist d)
    "
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  let ?ad = "abs_IDist d"
  let ?an = "abs_INat n"  
  let ?ap = "abs_IPedge p"
  show "?thesis G d s n p"
    unfolding 
      shortest_paths_locale_step1_def
      shortest_paths_locale_step1_inv_def
    apply (auto simp: wf_inv_is_fin_digraph[where ?G=G]
        s_assms_eq_math[where ?G=G and ?sc=s and ?d=d and ?p=p and ?n=n]
        parent_num_assms_inv_eq_math[where ?G=G and ?s=s and ?d=d and ?p=p and ?n=n])
     apply (unfold parent_num_assms_inv_def abs_IPedge_def abs_INat_def abs_IDist_def)[1]
     apply clarsimp
        apply (metis (mono_tags, hide_lams) Word_Lemmas.sint_0 add.right_neutral add_Suc_right 
        less_le not_le long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_msb_sint)
       apply (metis (mono_tags, hide_lams) Word_Lemmas.sint_0 add.right_neutral add_Suc_right less_le 
        not_le long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_msb_sint)
      apply (metis (mono_tags, hide_lams) Word_Lemmas.sint_0 add.right_neutral add_Suc_right 
        less_le not_le long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_msb_sint)
     apply (metis (mono_tags, hide_lams) Word_Lemmas.sint_0 add.right_neutral add_Suc_right 
        less_le not_le long_ucast word_add_cast_up_no_overflow unat_eq_1(2) word_msb_sint)
    apply (unfold parent_num_assms_inv_def abs_IPedge_def abs_INat_def abs_IDist_def)[1]
    apply clarsimp
     apply safe[1]
         apply (metis not_le word_msb_sint)
        apply (metis not_le)
       apply (metis not_le)
      apply (metis not_le not_less_iff_gr_or_eq)
     apply (subgoal_tac "\<forall>n. n + unat (1::64 word) = Suc n")
      apply (subgoal_tac "\<forall>w. unat (UCAST(32 \<rightarrow> 64) (w::32 word) + (1::64 word)) = Suc (unat (UCAST(32 \<rightarrow> 64) w::64 word))")
       apply (subgoal_tac "Suc (unat (UCAST(32 \<rightarrow> 64) (n (fst (snd (snd G) (p v))))::64 word)) = unat (UCAST(32 \<rightarrow> 64) (n v)::64 word)")
        apply (metis (no_types) word_unat.Rep_inject)
       apply (metis (no_types) not_le long_ucast)
      apply (metis (full_types) long_ucast word_add_cast_up_no_overflow unat_eq_1(2))
     apply simp
    apply safe
        apply (metis not_le word_msb_sint)
       apply (metis not_le)
      apply (metis not_le)
     apply (metis not_le not_less_iff_gr_or_eq)
    apply (metis (mono_tags, hide_lams) add.right_neutral add_Suc_right not_le long_ucast word_add_cast_up_no_overflow 
        unat_eq_1(2) word_unat.Rep_inverse)
    done
qed

definition source_val_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> IENInt \<Rightarrow> IEInt \<Rightarrow> 32 word \<Rightarrow> bool" where
  "source_val_inv G s d n k \<equiv>
    (\<exists>v < k. is_inf_d d v = 0) \<longrightarrow>
       (is_inf_d d s = 0 \<and>
        val_d d s = 0)"

lemma source_val_inv_step:
  assumes v_less_max: "v < (max_word::32 word)"
  shows "source_val_inv G s d n (v + 1) \<longleftrightarrow> 
         (source_val_inv G s d n v \<and> is_inf_d d s = 0 \<and> val_d d s = 0) \<or>
         (source_val_inv G s d n v \<and> is_inf_d d v \<noteq> 0)"
  unfolding source_val_inv_def
  by (metis less_irrefl less_x_plus_1 v_less_max)
  

lemma source_val_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          sc < ivertex_cnt iG \<and> 
          is_dist s iG iD d \<and>
          is_numm s iG iN n)\<rbrace>
   source_val' g sc d n
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> source_val_inv iG sc iD iN (ivertex_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: source_val'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(vv, s). unat (ivertex_cnt iG - vv)" and
        I="\<lambda>vv s. P s \<and> source_val_inv iG sc iD iN vv \<and>
                   vv \<le> ivertex_cnt iG \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   sc < ivertex_cnt iG \<and> 
                   is_dist s iG iD d \<and>
                   is_numm s iG iN n"])
  apply (simp add: skipE_def)
  apply wp
     apply (subst if_bool_eq_conj)+
     apply (clarsimp simp del: Word_Lemmas.sint_0)
     apply (rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold source_val_inv_def is_graph_def is_dist_def)[1]
       apply (clarsimp simp del: Word_Lemmas.sint_0)
       apply (rule, rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
        apply (subst is_inf_d_heap, blast, force, simp)
       apply (rule impI, subst val_d_heap, blast, fast)
       apply (metis Word_Lemmas.sint_0 int_unat ENInt_isInf_C_pte two_comp_arrlist_heap)
      apply (rule conjI, rule impI, rule conjI, rule impI)
        apply (unfold source_val_inv_def is_graph_def is_dist_def)[1]
        apply (clarsimp simp del: Word_Lemmas.sint_0, rule, rule_tac x=vv in exI, clarsimp simp del: Word_Lemmas.sint_0)
         apply (subst is_inf_d_heap, blast, force, simp)
        apply (rule impI, subst val_d_heap, blast, blast, fastforce)
       apply (rule conjI, rule impI)
        apply (unfold source_val_inv_def is_graph_def is_dist_def)[1]
        apply (rule, rule conjI, subst is_inf_d_heap, force, argo, simp)
        apply (subst val_d_heap, force, argo, simp)
       apply (unfold is_graph_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
       apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (unfold is_graph_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
     apply (rule conjI, rule impI, rule conjI)
       apply (subgoal_tac " vv + 1 \<le> fst iG")
        apply (subgoal_tac "vv < (max_word::32 word)")
         apply (drule source_val_inv_step[where G=iG and s=sc and d=iD and n=iN])
         apply (clarsimp simp del: Word_Lemmas.sint_0)+
         apply (unfold is_graph_def is_dist_def is_cost_def)[1]
         apply (subst (asm) (2) is_inf_d_heap, simp, fast, simp add: uint_nat)
        apply (metis max_word_max not_le word_le_less_eq)
       apply (metis inc_le is_graph_def)
      apply (rule conjI, metis inc_le is_graph_def)
      apply (rule conjI, metis is_graph_def unat_minus_plus1_less)
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (unfold is_graph_def is_dist_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (metis shortest_path_neg_checker.is_graph_def word_le_less_eq)
   apply wp
  apply (unfold source_val_inv_def is_graph_def, force)
  done

definition no_edge_Vm_Vf_inv :: "IGraph \<Rightarrow> IENInt \<Rightarrow> 32 word \<Rightarrow> bool" where
  "no_edge_Vm_Vf_inv G d m \<equiv> 
    \<forall>i < m. is_inf_d d (fst (iedges G i)) < 0 \<longrightarrow> is_inf_d d (snd (iedges G i)) \<noteq> 0"

lemma no_edge_Vm_Vf_inv_step:
  assumes i_less_max: "i < (max_word::32 word)"
  shows "no_edge_Vm_Vf_inv G d (i + 1) \<longleftrightarrow> no_edge_Vm_Vf_inv G d i \<and>
  (is_inf_d d (fst (iedges G i)) < 0 \<longrightarrow> is_inf_d d (snd (iedges G i)) \<noteq> 0)"
  unfolding no_edge_Vm_Vf_inv_def
  by (metis i_less_max less_x_plus_1 max_word_max not_le)+

lemma no_edge_Vm_Vf_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_dist s iG iD d)\<rbrace>
   no_edge_Vm_Vf' g d
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> no_edge_Vm_Vf_inv iG iD (iedge_cnt iG)) \<rbrace>!"
  apply (clarsimp simp: no_edge_Vm_Vf'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(ee, s). unat (iedge_cnt iG - ee)" and
        I="\<lambda>ee s. P s \<and> no_edge_Vm_Vf_inv iG iD ee \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   is_dist s iG iD d"])
  apply (simp add: skipE_def)
  apply wp
     apply (subst if_bool_eq_conj)+
     apply (clarsimp simp del: Word_Lemmas.sint_0)
     apply (rule conjI, rule impI, rule conjI, rule impI)
       apply (unfold no_edge_Vm_Vf_inv_def is_graph_def is_dist_def)[1]
       apply (clarsimp simp del: Word_Lemmas.sint_0, rule_tac x=ee in exI, clarsimp simp del: Word_Lemmas.sint_0)
       apply (rule conjI, subst tail_heap, blast, blast, subst is_inf_d_heap, blast, 
              metis int_unat s_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, fast)
       apply (subst head_heap, blast, blast, subst is_inf_d_heap, blast, 
              metis int_unat t_C_pte two_comp_to_edge_arrlist_heap wellformed_iGraph, force)
      apply (rule conjI, rule impI, rule conjI)
        apply (unfold is_graph_def is_dist_def)[1]
        apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
         apply (subgoal_tac "ee < (max_word::32 word)")
          apply (drule no_edge_Vm_Vf_inv_step[where G=iG and d=iD])
          apply (clarsimp simp del: Word_Lemmas.sint_0)
          apply (metis (no_types, hide_lams) Word_Lemmas.sint_0 ENInt_isInf_C_pte head_heap 
                 two_comp_arrlist_heap wellformed_iGraph uint_nat)
         apply (metis max_word_max not_le word_le_less_eq)
        apply (metis inc_le)
       apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
       apply (unfold is_graph_def)[1]
       apply (clarsimp simp: if_bool_eq_conj)+
      apply (unfold is_graph_def is_dist_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (metis wellformed_iGraph word_less_nat_alt)
     apply (rule conjI, rule impI, rule conjI)
       apply (unfold is_graph_def is_dist_def)[1]
       apply (subgoal_tac " ee + 1 \<le> fst (snd iG)")
        apply (subgoal_tac "ee < (max_word::32 word)")
         apply (drule no_edge_Vm_Vf_inv_step[where G=iG and d=iD])
         apply (clarsimp simp del: Word_Lemmas.sint_0)
         apply (metis is_inf_d_heap tail_heap wellformed_iGraph)
        apply (metis max_word_max not_le word_le_less_eq)
       apply (metis inc_le)
      apply (rule conjI, simp add: is_graph_def unat_minus_plus1_less)
      apply (unfold is_graph_def)[1]
      apply (clarsimp simp: if_bool_eq_conj)+
     apply (unfold is_graph_def is_dist_def)[1]
     apply (clarsimp simp: if_bool_eq_conj)+
     apply (rule conjI)
      apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
      apply (metis wellformed_iGraph word_less_nat_alt)
     apply (rule arrlist_nth, (simp add: uint_nat unat_mono )+)
    apply (simp add: no_edge_Vm_Vf_inv_def is_graph_def)
   apply wp
  apply (unfold no_edge_Vm_Vf_inv_def is_graph_def, fastforce)
  done

lemma source_val_inv_eq_maths:
  "source_val_inv G s d n (ivertex_cnt G) \<longleftrightarrow>
   (\<exists> v \<in> verts (abs_IGraph G). abs_INum n d v \<noteq> \<infinity>) \<longrightarrow> abs_IDist d s = 0"
  unfolding source_val_inv_def abs_INum_def abs_IDist_def by fastforce

lemma no_edge_Vm_Vf_inv_eq_maths:
  "no_edge_Vm_Vf_inv G d (iedge_cnt G) \<longleftrightarrow>
  (\<forall>e \<in> arcs (abs_IGraph G). 
    abs_IDist d (tail (abs_IGraph G) e) = -\<infinity> \<longrightarrow> (\<forall>r. abs_IDist d (head (abs_IGraph G) e) \<noteq> ereal r))"
  unfolding no_edge_Vm_Vf_inv_def abs_IDist_def abs_IGraph_def by auto

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
(*
definition awalk_inv ::
  "IGraph \<Rightarrow> ICycle \<Rightarrow> nat \<Rightarrow> bool"
where
"awalk_inv G C k \<equiv>
    icycle_start C < ivertex_cnt G \<and>
    (length (icycle_path C) \<noteq> 0 \<longrightarrow> 
       icycle_start C = snd (iedges G (last (icycle_path C)))) \<and>
    (\<forall>i < k. 
       icycle_path C ! i < iedge_cnt G \<and>
       icycle_path C ! (Suc i) < iedge_cnt G \<and>
       fst (iedges G (icycle_path C ! i)) =
       snd (iedges G (icycle_path C ! (Suc i))))"

lemma awalk_inv_step:
  assumes i_less_max: "k < unat (max_word::32 word)"
  assumes "icycle_path iY \<noteq> []"
  shows "awalk_inv iG iY (k + 1) \<longleftrightarrow> awalk_inv iG iY k \<and>
       icycle_path iY ! k < iedge_cnt iG \<and>
       icycle_path iY ! (Suc k) < iedge_cnt iG \<and>
       fst (iedges iG (icycle_path iY ! k)) =
       snd (iedges iG (icycle_path iY ! (Suc k)))"
  unfolding awalk_inv_def
  using less_antisym Suc_eq_plus1 less_Suc_eq
  by metis

lemma list_quant_set: "((P (hd xs)) \<and> (\<forall>i < length xs - 1. P (xs ! (i - 1)) \<and> P (xs ! i))) = (\<forall> x \<in> set xs. P x)"
  sledgehammer
  by (metis in_set_conv_nth)
*)

definition awalk_edge_inv ::
  "IGraph \<Rightarrow> ICycle \<Rightarrow> nat \<Rightarrow> bool"
where
  "awalk_edge_inv G C k \<equiv>
      \<forall> i < k. icycle_path C ! i < iedge_cnt G"

lemma awalk_edge_inv_step:
  "awalk_edge_inv G C (Suc k) \<longleftrightarrow> 
   awalk_edge_inv G C k \<and>  icycle_path C ! k < iedge_cnt G"
  unfolding awalk_edge_inv_def 
  by (rule iffI; clarsimp; rename_tac i;case_tac "i=k"; simp)


lemma awalk_edge_inv_le:
  assumes leq: "j \<le> i" 
  assumes cas_i: "awalk_edge_inv G C i"
  shows "awalk_edge_inv G C j"
  using assms 
  by (induct j) (auto simp add: awalk_edge_inv_def)

definition awalk_cas_inv ::
  "IGraph \<Rightarrow> ICycle \<Rightarrow> nat \<Rightarrow> bool"
where
  "awalk_cas_inv G C k \<equiv> 
    (length (icycle_path C) \<noteq> 0 \<longrightarrow>
      pre_digraph.cas (abs_IGraph G) 
                      (icycle_start C) 
                      (take k (icycle_path C)) 
                      (snd (iedges G (last (take k (icycle_path C))))) \<and>
      ((k = length (icycle_path C) \<and> k \<noteq> 0) \<longrightarrow> snd (iedges G (last (icycle_path C))) = icycle_start C))"


definition cas_inv ::
  "IGraph \<Rightarrow> IPath \<Rightarrow> nat \<Rightarrow> bool"
where
  "cas_inv G P k  \<equiv> 
    length P \<noteq> 0 \<longrightarrow>
       (\<forall>i<k-1. 
         snd (iedges G (P! i)) = 
         fst (iedges G (P! (i+1))))"

definition cas_inv' ::
   "IGraph \<Rightarrow> IVertex \<Rightarrow> IPath \<Rightarrow> IVertex \<Rightarrow> nat \<Rightarrow> bool"
where
  "cas_inv' G u P v k  \<equiv> 
    ((length P = 0 \<longrightarrow> u=v) \<and>
     (length P \<noteq> 0 \<longrightarrow>
      fst (iedges G (hd P)) = u \<and>
      snd (iedges G (last P)) = v \<and>
       cas_inv G P k))"

abbreviation cas_cyc_inv ::
  "IGraph \<Rightarrow> ICycle \<Rightarrow> nat \<Rightarrow> bool"
where
  "cas_cyc_inv G C k  \<equiv> 
   (cas_inv' G (icycle_start C) (icycle_path C) (icycle_start C) k)"

lemma cas_inv_step:
  assumes "k \<le> length P"
  shows "cas_inv G P (k + 1) \<longleftrightarrow> 
          cas_inv G P k
          \<and> (k > 0 \<longrightarrow> (snd (iedges G (P ! (k-1))) = 
                      fst (iedges G (P ! k))))"
  using assms 
  unfolding cas_inv_def  
  by (case_tac P; safe; clarsimp) 
     (case_tac "i = k -1"; simp) 

lemma cas_inv_le:
  assumes leq: "j \<le> i" 
  assumes cas_i: "cas_inv G P i"
  shows "cas_inv G P j"
  using assms 
  by (induct j) (auto simp add: cas_inv_def)

lemma cas_inv_ConsD:
  "\<lbrakk>cas_inv G (e # P) k'; k' = k + 1; k \<le> length P\<rbrakk> \<Longrightarrow>
          (cas_inv G P k
          \<and> (k > 0 \<longrightarrow> (snd (iedges G e)) = 
                      fst (iedges G (hd P))))"
  by (case_tac P; clarsimp simp add: cas_inv_def)
     (metis (no_types, hide_lams) Suc_le_eq Suc_pred diff_le_self 
      linorder_neqE_nat not_le not_less_zero nth_Cons_0 nth_Cons_Suc)

lemma cas_inv_Cons:
  assumes "k \<le> length P"
  assumes "k' = k + 1"
  shows "cas_inv G (e # P) k' =
          (cas_inv G P k
          \<and> (k > 0 \<longrightarrow> (snd (iedges G e)) = 
                      fst (iedges G (hd P))))"
  apply (rule iffI)
  apply (fastforce dest: cas_inv_ConsD simp: assms)
  using assms 
  unfolding cas_inv_def
  apply (case_tac P; clarsimp; case_tac i; clarsimp) 
  done

lemma cas_inv'_NilD:
  "\<lbrakk>cas_inv' G u [] v k; k=0 \<rbrakk> \<Longrightarrow> u=v"
  unfolding cas_inv'_def by simp

lemma cas_inv'_Nil:
  "cas_inv' G u [] v 0 =  (u=v)"
  unfolding cas_inv'_def by simp

lemma cas_inv'_ConsD:
  "\<lbrakk>cas_inv' G u (e # P) v k'; k'=k+1; k \<le> length P\<rbrakk> \<Longrightarrow>
      fst (iedges G e) = u \<and>
      snd (iedges G (last (e# P))) = v \<and>
      cas_inv G P k \<and> 
      (k > 0 \<longrightarrow> snd (iedges G e) = fst (iedges G (hd P)))"
  by (clarsimp simp: cas_inv'_def, simp add: cas_inv_def)
     (fastforce dest: cas_inv_ConsD)
 
lemma cas_inv'_Cons:
 "\<lbrakk>k'=k+1; k \<le> length P\<rbrakk> \<Longrightarrow>
     cas_inv' G u (e # P) v k' =
      (fst (iedges G e) = u \<and>
      snd (iedges G (last (e# P))) = v \<and>
      cas_inv G P k \<and> 
      (k > 0 \<longrightarrow> snd (iedges G e) = fst (iedges G (hd P))))"
  unfolding cas_inv'_def
  by (subst cas_inv_Cons[where k=k]; simp)

lemma cas_cyc_inv_stepD:
  assumes "cas_cyc_inv G C k"
  assumes "k \<le> length (icycle_path C)"
  assumes "k > 0 \<Longrightarrow> (snd (iedges G ((icycle_path C)! (k-1))) = 
                      fst (iedges G ((icycle_path C)! k)))"
  shows "cas_cyc_inv G C (k + 1)"
  using assms cas_inv_step 
  unfolding cas_inv'_def 
  by auto     

lemma cas_cyc_inv_step:
  assumes "k \<le> length (icycle_path C)"
  shows "cas_cyc_inv G C (k + 1) = 
          (cas_cyc_inv G C k
          \<and> (k > 0 \<longrightarrow> (snd (iedges G ((icycle_path C)! (k-1))) = 
                      fst (iedges G ((icycle_path C)! k)))))"
  unfolding  cas_inv'_def 
  using assms cas_inv_step 
  by auto        
  
lemma cas_cyc_inv_le:
  assumes awalk_i: "cas_cyc_inv G C i"
  assumes leq: "j \<le> i" 
  shows "cas_cyc_inv G C j"
  using assms 
  by (induct j) (auto simp add: cas_inv'_def cas_inv_def)
 
definition awalk_spc ::
  "IGraph \<Rightarrow> ICycle \<Rightarrow> bool"
where
  "awalk_spc G C \<equiv>
      icycle_start C < ivertex_cnt G \<and>
      awalk_edge_inv G C (length (icycle_path C)) \<and>
      awalk_cas_inv G C (length (icycle_path C))"


definition awalk_spc' ::
  "IGraph \<Rightarrow> ICycle \<Rightarrow> bool"
where
  "awalk_spc' G C \<equiv>
      icycle_start C < ivertex_cnt G \<and>
      awalk_edge_inv G C (length (icycle_path C)) \<and>
      cas_cyc_inv G C (length (icycle_path C))"

lemma last_cas_elem[simp]: 
  "p \<noteq> [] \<Longrightarrow> pre_digraph.cas G u p u \<Longrightarrow> u = head G (last p)"
  by (metis append_butlast_last_id pre_digraph.cas.simps pre_digraph.cas_append_iff)

lemma awalk_spc_eq_math:
  "awalk_spc iG iY \<longleftrightarrow> pre_digraph.awalk (abs_IGraph iG) 
                        (icycle_start iY) 
                        (icycle_path iY) 
                        (icycle_start iY)"
  apply (unfold awalk_spc_def pre_digraph.awalk_def)
  apply (rule iffI)
    (* spc to math *)
   apply safe[1]
     apply fastforce
    apply (metis atLeastLessThan_iff in_set_conv_nth awalk_edge_inv_def edges_absI word_zero_le)
   apply (clarsimp simp add: awalk_edge_inv_def)
   apply (case_tac "snd iY \<noteq> []")
  apply (fastforce simp: awalk_cas_inv_def)[1]
   apply (simp add: pre_digraph.cas.simps(1))
  (* math to spc*)
  apply safe
    apply simp
   apply (metis (no_types, hide_lams) atLeastLessThan_iff nth_mem awalk_edge_inv_def edges_absI subsetD)
  apply (metis (mono_tags, hide_lams) le_refl length_0_conv awalk_cas_inv_def last_cas_elem target_absI take_all)
  done

lemma cas_inv'_impl_cas:
  "cas_inv' G u P v (length P) \<Longrightarrow> pre_digraph.cas (abs_IGraph G) u P v"
  by (induct P arbitrary: u,
      simp add: cas_inv'_def pre_digraph.cas.simps(1))
     (fastforce dest: cas_inv_ConsD simp: cas_inv'_def pre_digraph.cas_simp)

lemma cas_impl_cas_inv':
  "pre_digraph.cas (abs_IGraph G) u P v \<Longrightarrow> cas_inv' G u P v (length P)"
  by (induct P arbitrary: u, simp add: cas_inv'_def pre_digraph.cas.simps(1))
     (clarsimp simp: cas_inv'_Cons pre_digraph.cas_simp,
         force simp: cas_inv'_def cas_inv_def)

lemma cas_inv'_eq_cas: 
  "cas_inv' G u P v (length P) = pre_digraph.cas (abs_IGraph G) u P v"
  by (fastforce intro: cas_inv'_impl_cas cas_impl_cas_inv')

lemma awalk_spc'_eq_awalk:
  "awalk_spc' iG iY \<longleftrightarrow> pre_digraph.awalk (abs_IGraph iG) 
                        (icycle_start iY) 
                        (icycle_path iY) 
                        (icycle_start iY)"
  unfolding awalk_spc'_def awalk_edge_inv_def pre_digraph.awalk_def
  by (simp add: cas_inv'_eq_cas) 
     (metis (no_types, hide_lams) atLeastLessThan_iff  
            subset_code(1) word_zero_le in_set_conv_nth)

lemma drop_impl_conj_leftI: "\<lbrakk>Q; P \<longrightarrow> R;  P' \<longrightarrow> R'\<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q \<and> R) \<and> (P' \<longrightarrow> Q \<and> R')"
  by simp

lemma drop_impl_conj_rightI: "\<lbrakk>P \<longrightarrow> Q;  P' \<longrightarrow> Q'; R\<rbrakk> \<Longrightarrow> (P \<longrightarrow> Q \<and> R) \<and> (P' \<longrightarrow> Q' \<and> R)"
  by simp

lemma cyc_in_graph_spc:
  "\<lbrace> P and 
     (\<lambda>s. is_graph s iG g \<and>
          is_cycle s iY y)\<rbrace>
   cyc_in_graph' g y
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         icycle_start iY < ivertex_cnt iG \<and>
          awalk_edge_inv iG iY (length (icycle_path iY))) \<rbrace>!"
  apply (simp add: cyc_in_graph'_def )
  apply wpsimp
     apply (subst whileLoopE_add_inv [where 
                   M="\<lambda>(r, s). length (icycle_path iY) - r" and
                   I="\<lambda>r s. P s \<and> 
                            is_graph s iG g \<and> 
                            is_cycle s iY y \<and> icycle_start iY < ivertex_cnt iG \<and>
                            awalk_edge_inv iG iY r \<and>
                            r \<le> length (icycle_path iY)"])
     apply wpsimp
      apply (rule conjI; rule impI) 
       apply (fastforce dest: unat_mono simp: not_le is_cycle_def is_graph_def awalk_edge_inv_def)
      apply (clarsimp simp: awalk_edge_inv_step word_less_nat_alt is_cycle_def is_graph_def)
      apply (rule conjI, simp)  
      apply (metis INT_MIN_MAX_lemmas(15) le_trans not_le not_less_eq_eq)
     apply (metis dual_order.order_iff_strict is_cycle_def)
    apply wp+
  by (clarsimp simp: is_cycle_def is_graph_def awalk_edge_inv_def word_less_nat_alt)

lemma arrlistD : 
  assumes "arrlist h v xs p"
  shows "\<forall>i. i\<ge>0  \<longrightarrow> i <int (length xs) \<longrightarrow> v (p +\<^sub>p i) \<and> (xs ! nat i = h (p +\<^sub>p i))"
  using assms by clarsimp

lemma cas_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_cycle s iY y \<and>
          icycle_start iY < ivertex_cnt iG \<and>
          awalk_edge_inv iG iY (length (icycle_path iY)))\<rbrace>
   cas' g y
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         cas_cyc_inv iG iY (length (icycle_path iY))) \<rbrace>!"
  apply (simp add: cas'_def skipE_def)
  apply (wpsimp simp: validNF_conj_prop)
           apply (subst whileLoopE_add_inv [where 
                    M="\<lambda>(r, s). length (icycle_path iY) - Suc r" and
                    I="\<lambda>r s. P s \<and> 
                              wf_digraph (abs_IGraph iG) \<and> is_graph s iG g \<and> 
                              is_cycle s iY y \<and> icycle_start iY < ivertex_cnt iG \<and>
                              awalk_edge_inv iG iY (length (icycle_path iY)) \<and>
                              cas_cyc_inv iG iY (r+1) \<and>
                              length (icycle_path iY) \<ge> 1 \<and>
                              r \<le> length (icycle_path iY) - 1"])
           apply (wpsimp simp: validNF_conj_prop) defer
            apply (fastforce intro: cas_cyc_inv_le simp: is_cycle_def)
           apply wp+
   apply clarsimp
   apply (case_tac "length (icycle_path iY)") 
    apply (clarsimp simp: is_cycle_def  cas_inv'_def)
   apply (clarsimp simp: is_graph_def is_cycle_def awalk_edge_inv_def)
   apply (frule arrlist_nth_valid[where i=0, simplified], fastforce) 
   apply (frule head_heap[where e="icycle_path iY !(length (icycle_path iY) - 1)"])
     apply simp
    apply (frule arrlistD)
    apply (erule_tac x="uint (icycle_path iY ! 0)" in all_dupE)
    apply (erule impE, simp add: word_less_nat_alt)
    apply (erule_tac x="uint (icycle_path iY ! nat (int (length (icycle_path iY) - 1)))" in allE)
    apply (erule impE, simp add: word_less_nat_alt uint_nat,
           erule impE, simp,
           erule impE, simp add: uint_nat word_less_nat_alt)
    apply (frule arrlist_cycle_path_heap[where i=0], simp) 
   apply (rule conjI; clarsimp simp: cas_inv'_def cas_inv_def)
    apply (metis One_nat_def int_minus last_conv_nth list.size(3) nat.distinct(1) nat_int of_nat_1)
   apply (rule conjI; clarsimp)  
    apply (metis hd_conv_nth list.size(3) nat.distinct(1)  tail_heap zero_less_Suc)
   apply (metis (no_types, hide_lams) One_nat_def hd_conv_nth int_minus last_conv_nth 
                list.size(3) nat.distinct(1) nat_int of_nat_1 s_C_pte two_comp_arrlist_heap 
                uint_nat zero_less_Suc)
  apply (clarsimp simp: awalk_edge_inv_def is_graph_def is_cycle_def)
  apply (subst conj_assoc[symmetric, where P="cas_inv' _ _ _ _ _"])
  apply (frule_tac e="  (snd iY ! r)" in head_heap, simp)
  apply (frule_tac e="(snd iY ! (r+1))" in tail_heap, simp) 
  apply (frule arrlistD)
  apply (erule_tac x="uint (icycle_path iY ! r)" in all_dupE)
  apply (erule impE, simp add: word_less_nat_alt)
  apply (erule impE, simp add:  int_unat) 
   apply (meson Suc_less_SucD diff_less_Suc less_trans_Suc word_less_def)
  apply (erule_tac x="uint ((icycle_path iY ! Suc r))" in allE)
  apply (erule impE, simp add: word_less_nat_alt)+
   apply (metis Suc_eq_plus1 int_unat less_diff_conv nat_1 nat_int of_nat_1 of_nat_less_iff)
  apply (rule drop_impl_conj_rightI, clarsimp)
    apply (clarsimp simp: cas_inv'_def cas_inv_def)
    apply (erule_tac x=r in allE, simp)
    apply (case_tac r; simp) 
    apply (metis (no_types, hide_lams) add.commute add_2_eq_Suc' nat_int.Rep_inverse of_nat_add of_nat_numeral)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: cas_inv'_def cas_inv_def)
    apply  (case_tac "i=r"; clarsimp) 
  apply (metis nat_int.Rep_inverse of_nat_Suc)
  apply (fastforce intro: diff_less_mono2)
  apply (rule conjI; clarsimp)
  apply (metis (no_types, hide_lams) INT_MIN_MAX_lemmas(12) diff_commute diff_is_0_eq' diff_less_mono not_less0 not_less_eq_eq zero_diff)
  apply (metis nat_int of_nat_Suc)
  done




(*is_valid_Edge_C s (arcs_C (heap_Graph_C s g) +\<^sub>p uint (heap_w32 s (path_C (heap_Cycle_C s y))))*)
  


  
lemma awalk_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          is_cycle s iY y)\<rbrace>
   awalktwo' g y
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         awalk_spc' iG iY)\<rbrace>!"
  apply (simp add: awalktwo'_def skipE_def)
  apply wpsimp
               apply (subst whileLoopE_add_inv [where 
                        M="\<lambda>(r, s). length (icycle_path iY) - Suc r" and
                        I="\<lambda>r s. P s \<and> icycle_start iY < ivertex_cnt iG \<and>
                   awalk_edge_inv iG iY (length (icycle_path iY)) \<and> 
                   awalk_inv' iG iY (r+1) \<and>
                   r \<le> (length (icycle_path iY)) - 1 \<and> 
                   wf_digraph (abs_IGraph iG) \<and> is_graph s iG g \<and> is_cycle s iY y"])
               apply (wpsimp; clarsimp?) defer
                apply (fastforce intro: awalktwo_inv_le simp: awalktwo_spc_def is_cycle_def)  
              apply wp+
apply (subst whileLoopE_add_inv [where 
                        M="\<lambda>(r, s). length (icycle_path iY) - r" and
                        I="\<lambda>r s. P s \<and> icycle_start iY < ivertex_cnt iG \<and>
                   awalk_edge_inv iG iY r \<and> 
awalktwo_inv iG iY (r+1)\<and>
                   r \<le> (length (icycle_path iY)) \<and> 
                   wf_digraph (abs_IGraph iG) \<and> is_graph s iG g \<and> is_cycle s iY y"])
             apply (wpsimp; clarsimp simp: is_cycle_def is_graph_def)
  unfolding is_cycle_def is_graph_def apply clarsimp
  apply (rule conjI; clarsimp)

   
              

  
               apply (subgoal_tac "r = length (icycle_path iY) \<or> r = length (icycle_path iY) - 1")
                apply (case_tac "length (icycle_path iY)";
                       clarsimp simp: cas_inv'_Nil is_cycle_def)
                apply (erule disjE; clarsimp simp add: is_cycle_def)
                apply (case_tac "icycle_path iY", simp add: awalktwo_inv_def cas_inv'_Nil) 
                apply (drule awalktwo_inv_le; simp)
                 apply clarsimp
  
  apply (subst 
  oops
                apply (case_tac "snd iY", simp)

apply (case_tac "r = length (snd iY) - 1"; clarsimp simp add: is_cycle_def)
  apply (rule awalktwo_inv_le, simp)
  
               apply ( subst cas_inv'_Cons, simp, simp, clarsimp simp add: is_cycle_def)

  apply clarsimp
  
  thm awalktwo_inv_step[where k=""]
  apply (drule )
               apply (case_tac "r =  length (snd iY)"; case_tac "r = length (snd iY) - 1"; simp)
  using awalktwo_inv_step[where k = "length (snd iY) - 1" and C = iY, simplified ]
                apply simp 
apply (case_tac "r =  unat (length_C (heap_Cycle_C s y)) - 1 ")  prefer 2 try0
  apply simp
               apply simp
  using awalktwo_inv_step
               apply (rule awalktwo_inv_le, simp) 
  
  apply ()
               apply (rule conjI)
  try0
         apply (unfold is_graph_def awalktwo_inv_def is_cycle_def , clarsimp)[1] 
               apply (simp_all)
               prefer 2
  apply clarsimp
  apply blast


  thm tail_heap
 
                 (* apply (metis Suc_diff_1 Suc_lessD Suc_less_eq nat_1 nat_int 
neq0_conv not_less0 of_nat_1 of_nat_Suc head_heap tail_heap zero_less_diff)*)

  oops
                             

 
  apply (simp add: skipE_def)
  apply wpsimp
        apply (subst whileLoopE_add_inv [where 
        M="\<lambda>((u, z), s). (length (icycle_path iY)) - unat z" and
        I="\<lambda>(u, z) s.  P s \<and> awalk_spc iG iY (length (icycle_path iY)) \<and>
                   awalk_cas_inv iG iY (unat z) \<and> 
                   unat z \<le> (length (icycle_path iY)) \<and>
                   u = (case (unat z) of 0 \<Rightarrow> icycle_start iY | 
                                  _ \<Rightarrow> snd (iedges iG (icycle_path iY ! unat (z - 1)))) \<and>
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   is_cycle s iY y"])
        apply (simp add: skipE_def)
        apply wpsimp


sorry
        apply (subst if_bool_eq_conj)+ 
              
         apply (unfold is_graph_def awalk_inv_def is_cycle_def, clarsimp)[1] 
  apply safe
                                   apply (metis (full_types) int_unat arrlist_cycle_path_heap word_gt_a_gt_0 word_less_nat_alt word_not_le)
                                  apply (unfold is_graph_def awalk_inv_def is_cycle_def, clarsimp)[1]
                                  apply (subgoal_tac "0 < length_C (heap_Cycle_C s y)", clarsimp)
                                   apply (erule_tac x=yy in allE, clarsimp)
                                   apply (subst (asm) (4) arrlist_cycle_path_heap, blast, metis not_le word_le_nat_alt)
                                   apply (subst (asm) (3) arrlist_cycle_path_heap, blast, metis less_1_simp word_less_nat_alt)
                                   apply (subst (asm) (2) head_heap, blast, metis less_1_simp not_le arrlist_cycle_path_heap word_le_nat_alt)
                                   apply (subst (asm) tail_heap, blast, metis not_le arrlist_cycle_path_heap word_le_nat_alt)
                                   apply (simp add: uint_nat)
                                  apply (blast intro: word_gt_a_gt_0)
                                 apply (unfold is_graph_def awalk_inv_def is_cycle_def, clarsimp)[1]
                                 apply (metis add.commute add_diff_cancel_left' less_1_simp)


 


  sorry

definition awalk_cost_neg_inv ::
  "ICost \<Rightarrow> ICycle \<Rightarrow> nat \<Rightarrow> int"
where
  "awalk_cost_neg_inv iC iY ee \<equiv> 
      sum_list (map (sint \<circ> iC) (take ee (icycle_path iY)))"

lemma sum_list_step:
  assumes "i < length xs" 
  assumes "xs \<noteq> []"
  shows "sum_list (take (i + 1) xs) = sum_list (take i xs) + xs ! i"
proof -
  have "\<forall>n. n + 1 = Suc n"
    by simp
  then show ?thesis
    by (metis (no_types) add.right_neutral assms(1) sum_list.Cons sum_list.Nil sum_list_append take_Suc_conv_app_nth)
qed

lemma sum_list_step_sint:
  assumes "i < length xs" 
  assumes "xs \<noteq> []"
  shows "sum_list (map sint (take (i + 1) xs)) = sum_list (map sint (take i xs)) + sint (xs ! i)"
proof -
  have "sum_list (take i (map sint xs)) + sint (xs ! i) = sum_list (take (i + 1) (map sint xs))"
    by (metis (no_types) add.commute assms(1) gen_length_code(1) gen_length_def length_map not_add_less1 nth_map sum_list_step)
  then show ?thesis
    by (simp add: take_map)
qed

lemma awalk_cost_neg_inv_step:
  assumes "is_cycle s iY y"
    and   "i  < (length (icycle_path iY))"
    and   "icycle_path iY \<noteq> []"
  shows "awalk_cost_neg_inv iC iY (i + 1) = awalk_cost_neg_inv iC iY i +
  sint (map iC (icycle_path iY) ! i)"
  unfolding awalk_cost_neg_inv_def is_cycle_def
  using  assms
  apply (subgoal_tac "sum_list (map sint (take (i + 1) 
          (map iC (icycle_path iY)))) =
        sum_list (map sint (take i (map iC (icycle_path iY)))) + 
         sint (map iC (icycle_path iY) ! i)")
  apply (simp add: take_map)
  apply (metis (no_types, lifting) 
        Nil_is_map_conv add.commute length_map sum_list_step_sint)
  done

corollary awalk_cost_neg_inv_step2:
  assumes "is_cycle s iY y"
    and "i < length (icycle_path iY)"
    and "icycle_path iY \<noteq> []"
  shows "awalk_cost_neg_inv iC iY (i + 1) = awalk_cost_neg_inv iC iY i +
  sint (iC (icycle_path iY ! i))"
  unfolding awalk_cost_neg_inv_def
  using assms awalk_cost_neg_inv_def awalk_cost_neg_inv_step
  by (metis (no_types, hide_lams) One_nat_def add_Suc_right nth_map
              gen_length_code(1) gen_length_def list.size(3))

lemma awalk_cost_neg_spc':
  "ovalid (\<lambda> s. 
   awalk_edge_inv iG iY (length (icycle_path iY)) \<and>
   wf_digraph (abs_IGraph iG) \<and>
   is_graph s iG g \<and>
   is_cost s iG iC c \<and>
   is_cycle s iY y) (awalk_cost_neg' c y) (\<lambda>r s. r = 
   awalk_cost_neg_inv iC iY (length (icycle_path iY)))"
  apply (unfold awalk_cost_neg_inv_def awalk_cost_neg'_def)[1]
  apply (subst owhile_add_inv [where 
         M="\<lambda> (ee, total) s. (length (icycle_path iY) - unat ee)" and
         I="\<lambda> (ee, total) s. 
              length (icycle_path iY) \<le> unat (max_word::32 word) \<and>
              awalk_edge_inv iG iY (length (icycle_path iY)) \<and>
              wf_digraph (abs_IGraph iG) \<and>
              is_graph s iG g \<and>
              is_cost s iG iC c \<and>
              is_cycle s iY y \<and>
              total = awalk_cost_neg_inv iC iY (unat ee)"])
  apply wpsimp
    apply (frule_tac i="unat a" in 
      awalk_cost_neg_inv_step2[where iC=iC and iY="iY"]) 
      apply (fastforce intro: unat_mono simp: is_cycle_def)
     apply (metis add.right_neutral list.size(3) not_add_less2 is_cycle_def word_less_nat_alt)
    apply (subgoal_tac "a < (max_word :: 32 word)")
     apply (subst (asm) word_nat_simp[symmetric], fast)
     apply (clarsimp simp add: awalk_cost_neg_inv_def is_cycle_def is_cost_def awalk_edge_inv_def)
     apply (subst (asm) arrlist_cycle_path_heap, blast, fastforce simp add: word_less_nat_alt)
     apply (subst (asm) arrlist_heap[where iL=iC], fast, metis arrlist_cycle_path_heap word_less_nat_alt)
     apply (simp add: uint_nat)
     apply (subst arrlist_cycle_path_heap, blast, fastforce simp add: word_less_nat_alt)
     apply (subst arrlist_heap[where iL=iC], fast, metis arrlist_cycle_path_heap word_less_nat_alt)
     apply clarsimp
    apply (insert less_linear max_word_not_less, blast)
   apply wpsimp
   apply (clarsimp simp add: awalk_cost_neg_inv_def is_cycle_def)
   apply (insert word_le_nat_alt word_le_not_less, fastforce)
  apply wpsimp
  apply (clarsimp simp add: is_cycle_def awalk_cost_neg_inv_def)
  done

lemma int_real_add_simp: "foldr (+) (map (real_of_int \<circ> sint) xs) 0 = 
                          real_of_int (foldr (+) (map sint xs) 0)"
  by (induct xs) simp+

lemma acc_list_simp: "real_of_int (awalk_cost_neg_inv iC iY (length (icycle_path iY))) = 
       sum_list (map (real_of_int \<circ> sint \<circ> iC) (icycle_path iY))"
  unfolding awalk_cost_neg_inv_def
  using int_real_add_simp
  by (metis (no_types, hide_lams) le_refl map_map sum_list.eq_foldr take_all)

lemma awalk_cost_eq_math:
  assumes "wf_digraph (abs_IGraph iG)"
  shows "real_of_int (awalk_cost_neg_inv iC iY (length (icycle_path iY))) = wf_digraph.awalk_cost (abs_ICost iC) (icycle_path iY)"
  apply (insert assms)
  apply (simp add: acc_list_simp)
  apply (unfold awalk_cost_neg_inv_def wf_digraph.awalk_cost_def abs_ICost_def)
  using acc_list_simp
  by (metis comp_apply)

definition C_se_inv :: 
  "IGraph \<Rightarrow> ICycle_Set \<Rightarrow> ICost \<Rightarrow>  IENInt \<Rightarrow> 32 word \<Rightarrow> bool" 
where
  (*FIXME*)
  "C_se_inv G cse c d k \<equiv>
   \<forall>i < k.  is_inf_d d (icycle_start (icycles cse ! unat i)) \<le> 0 \<and> 
   awalk_inv G (icycles cse ! unat i) (icycle_length (icycles cse ! unat i)) \<and>
   awalk_cost_neg_inv c (icycles cse ! unat i) (icycle_length (icycles cse ! unat i)) < 0"

lemma C_se_spc':
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
          are_cycles' s iY' cse  \<and>
          is_cost s iG iC c \<and>
          is_dist s iG iD d )\<rbrace>
   C_se' g cse c d 
   \<lbrace> (\<lambda>_ s. P s) And 
     (\<lambda>rr s. rr \<noteq> 0  \<longleftrightarrow> 
         C_se_inv iG (abs_ICycles' s iY') iC iD (icycles'_num iY'))\<rbrace>!"
  apply (clarsimp simp: C_se'_def)
  apply (subst whileLoopE_add_inv [where 
        M="\<lambda>(cc, s). unat (icycles'_num iY' - cc)" and
        I="\<lambda>cc s. P s \<and> C_se_inv iG (abs_ICycles' s iY') iC iD cc \<and> 
                   cc \<le> icycles'_num iY' \<and> 
                   wf_digraph (abs_IGraph iG) \<and>
                   is_graph s iG g \<and>
                   are_cycles' s iY' cse  \<and>
                   is_cost s iG iC c \<and>
                   is_dist s iG iD d "])
  apply (simp add: skipE_def)
  apply wp 
     
  sorry                     


lemma shortest_paths_locale_step3_eq_maths:
  "\<And>G s c n p d pred.
    shortest_paths_locale_step3_inv G s c n p d pred
    =
    shortest_paths_locale_step3_pred
    (abs_IGraph G) s (abs_ICost c) (abs_INat n)
    (abs_IPedge p) (abs_IDist d) (abs_IPedge pred)"
  sorry

lemma shortest_paths_locale_step3_spc:
  "\<lbrace> P and 
     (\<lambda>s. wf_digraph (abs_IGraph iG) \<and>
          is_graph s iG g \<and>
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
  sorry



definition int_neg_cyc_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> IENInt \<Rightarrow> ICycle_Set' \<Rightarrow> ICost \<Rightarrow> IPEdge \<Rightarrow> 
   IEInt \<Rightarrow> 32 word \<Rightarrow>  bool" 
where
  (*FIXME*)
  "int_neg_cyc_inv G sc d cse c p n k \<equiv>
   True"

definition shortest_paths_locale_step3_inv :: 
  "IGraph \<Rightarrow> IVertex \<Rightarrow> ICost \<Rightarrow> IEInt \<Rightarrow> IPEdge \<Rightarrow> 
   IENInt \<Rightarrow> IPEdge \<Rightarrow> ICycle_Set' \<Rightarrow> bool" 
where
  (*add shortest_paths_locale_step2_inv G sc c n p d pred*)
  "shortest_paths_locale_step3_inv G sc c n p d pred cse \<equiv>
   C_se_inv G cse c d (icycles'_num cse) \<and>
   int_neg_cyc_inv G sc d cse c p n (ivertex_cnt G)"


end

end
