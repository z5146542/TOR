theory a3
  imports "autocorres-1.4/autocorres/AutoCorres" 
begin

(* To run this file you need the AutoCorres tool used
   in the lecture.

  1. Download AutoCorres from 
       \url{http://www.cse.unsw.edu.au/~cs4161/autocorres-1.4.tar.gz}

  2. Unpack the .tar.gz file, which will create the directory autocorres-1.4
       tar -xzf autocorres-1.4.tar.gz

  3. Build the AutoCorres heap
     L4V_ARCH=X64 isabelle build -v -b -d autocorres-1.4 AutoCorres

  4. Load this file using the AutoCorres heap
     L4V_ARCH=X64 isabelle jedit -d autocorres-1.4 -l AutoCorres a3.thy

*)

section "Question 1: Regular Expression Matching"

(* Negation is too hard with this one, so we add Null and One instead *)
datatype regexp =
   Null
 | One
 | Atom char
 | Alt regexp regexp
 | Conc regexp regexp (infixl "\<cdot>"  60)
 | Star regexp

(* Same definitions for regular languages as in the lecture, but with Null and One *)
inductive_set star :: "string set \<Rightarrow> string set" for L
  where
  star_empty[simp,intro!]: "[] \<in> star L"
| star_app[elim]: "\<lbrakk> u \<in> L; v \<in> star L \<rbrakk> \<Longrightarrow> u@v \<in> star L"

definition conc :: "string set \<Rightarrow> string set \<Rightarrow> string set"
  where
  "conc A B \<equiv> {xs@ys |xs ys. xs \<in> A \<and> ys \<in> B}"

primrec lang :: "regexp \<Rightarrow> string set"
  where
  "lang Null = {}"
| "lang One = {[]}"
| "lang (Atom c) = {[c]}"
| "lang (Alt e1 e2) = lang e1 \<union> lang e2"
| "lang (Conc e1 e2) = conc (lang e1) (lang e2)"
| "lang (Star e) = star (lang e)"


(* For examples/testing. *)
primrec string :: "char list \<Rightarrow> regexp"
  where
  "string []     = One"
| "string (x#xs) = Atom x \<cdot> string xs"

(* Automatically coerce type "char list" into "regexp" using the function "string" *)
declare [[coercion string]]
(* Enable automatic type coercion *)
declare [[coercion_enabled]]
(* Can now write: *)
term "Star ''abc''"


(* This definition is taken from
   https://www.schoolofhaskell.com/school/to-infinity-and-beyond/pick-of-the-week/a-regular-expression-matcher
*)
function matches :: "regexp \<Rightarrow> string \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "matches Null         cs k = False"
| "matches One          cs k = k cs"
| "matches (Atom c)     cs k = (cs \<noteq> [] \<and> c = hd cs \<and> k (tl cs))"
| "matches (Alt r1 r2)  cs k = (matches r1 cs k \<or> matches r2 cs k)"
| "matches (Conc r1 r2) cs k =  matches r1 cs (\<lambda>cs'. matches r2 cs' k)"
| "matches (Star r)     cs k = (k cs \<or> matches r cs (\<lambda>cs'. if cs' \<noteq> cs
                                                           then matches (Star r) cs' k
                                                           else False))"
  by pat_completeness auto

(* Either change the cs' = cs condition to something more obviously terminating so that
   property "matches_correct" below still holds (easier) or prove termination of the
   version above directly (harder). *)
termination matches
  sorry (* TODO *)

value "matches ''xy'' ''xy'' (op = [])"
value "matches ''xyz'' ''xy'' (op = [])"
value "matches (Star ''xy'') ''xyxy'' (op = [])"

lemma concD[dest!]:
  "xs \<in> conc A B \<Longrightarrow> \<exists>as bs. as \<in> A \<and> bs \<in> B \<and> xs = as@bs"
  by (auto simp: conc_def)

lemma star_cases:
  "xs \<in> star A \<Longrightarrow> xs = [] \<or> (\<exists>u v. xs = u@v \<and> u \<in> A \<and> v \<in> star A \<and> u \<noteq> [])"
  oops (* TODO *)

lemma matches_correct:
  "matches r cs (op = []) = (cs \<in> lang r)"
  oops (* TODO *)

(*-------------------------------------------------*)
section "Question 2: Binary Search"

(* Hints: 
    - remember to try the @{text arith} proof method for arithmetic goals on
      integers or natural numbers. 
    - use find_theorems to find Isabelle library theorems about existing concepts.
    - the lemma @{thm sorted_equals_nth_mono} might be useful
    - you are allowed to use sledgehammer and other automation
    - if you can't prove one of the lemmas below, you can still assume it in the rest of the proof
    - the function @{const int} converts an Isabelle nat to an int
    - the function @{const nat} converts an Isabelle int to a nat
*)

thm sorted_equals_nth_mono
term int
term nat

install_C_file "binsearch.c"

autocorres [unsigned_word_abs=binary_search] "binsearch.c"

(*******************************************************************************)

context binsearch
begin

(* The monadic definition that autocorres produces for the C code: *)
thm binary_search'_def

(* Abbreviation for signed machine integers *)
type_synonym s_int = "32 signed word"

(* The heap only stores unsigned machine integers;
   they have the same representation as signed ones and can be converted to each other *)
type_synonym u_int = "32 word"

(*******************************************************************************)

(* A few lemmas to help improve automation: *)

(* Pointer arithmetic on pointers to signed and unsigned words is the same *)
lemma ptr_coerce_add_signed_unsigned [simp]:
  "(ptr_coerce ((a :: s_int ptr) +\<^sub>p x) :: u_int ptr) = ptr_coerce a +\<^sub>p x"
  by (cases a) (simp add: ptr_add_def)

(* Pointer arithmetic distributivity law *)
lemma ptr_add_add [simp]:
  "p +\<^sub>p (x + y) = p +\<^sub>p x +\<^sub>p y"
  by (simp add: ptr_add_def distrib_left mult.commute)

(* C division is the same as Isabelle division for non-negative numbers: *)
lemma sdiv [simp]:
  "0 \<le> a \<Longrightarrow> a sdiv 2 = a div (2::int)"
  by (auto simp: sdiv_int_def sgn_if)

(* Some useful facts about INT_MIN and INT_MAX to improve automation: *)
lemma INT_MIN_neg [simp]:
  "INT_MIN < 0"
  by (simp add: INT_MIN_def)
lemma INT_MAX_gr [simp]:
  "- 1 < INT_MAX" "-1 \<le> INT_MAX" "1 \<le> INT_MAX"
  by (auto simp add: INT_MAX_def)

(*******************************************************************************)

(* This function enumerates the addresses of the entries of an signed int array: *)
fun array_addrs :: "s_int ptr \<Rightarrow> nat \<Rightarrow> s_int ptr list" where
  "array_addrs p 0 = []" |
  "array_addrs p (Suc len) = p # array_addrs (p +\<^sub>p 1) len"

text \<open> Prove the following lemma: \<close>
lemma length_array_addrs [simp]:
  "length (array_addrs a len) = len"
  (* TODO *)
  apply (induct len arbitrary: a)
  apply auto
  done

text \<open> Prove the following lemma: \<close>
lemma array_addrs_nth [simp]:
  "\<lbrakk> 0 \<le> x; nat x < len \<rbrakk> \<Longrightarrow> array_addrs a len ! nat x = a +\<^sub>p x"
  (* TODO *)
  apply (induct len arbitrary: a x)
   apply simp+
  apply (case_tac "x = 0")
   apply simp+
  apply (subgoal_tac "\<exists>y. x = 1 + y \<and> 0 \<le> y")
   (* sledgehammer *)
   apply (metis (mono_tags, hide_lams) Suc_less_eq Suc_nat_eq_nat_zadd1 binsearch.ptr_add_add diff_Suc_Suc diff_zero)
  apply (metis le0 less_handy_casesE nat_0_iff nat_code(2) nat_int nat_le_iff nonneg_int_cases of_nat_Suc)
  done

(*******************************************************************************)
text \<open> fill in the array_list definition \<close>
definition array_list :: "(u_int ptr \<Rightarrow> u_int) \<Rightarrow> s_int ptr \<Rightarrow> int \<Rightarrow> int list" where
  "array_list h p len = map (uint o h o ptr_coerce) (array_addrs p (nat len))"

thm array_list_def

(*******************************************************************************)
text \<open> Prove the following lemma: \<close>

lemma ptr_array:
  "\<lbrakk> 0 \<le> x; x < len \<rbrakk> \<Longrightarrow>
   uint (heap_w32 s (ptr_coerce (a :: s_int ptr) +\<^sub>p x)) = array_list (heap_w32 s) a len ! nat x"
  apply (simp add: array_list_def)
  done

(*******************************************************************************)
text \<open> fill in the valid_array definition. It might make sense to do this in two parts and look
   at the invariant and proof obligations first. \<close>

definition valid_array1 :: "(u_int ptr \<Rightarrow> bool) \<Rightarrow> s_int ptr \<Rightarrow> int \<Rightarrow> bool" where
  "valid_array1 vld p len = 
  (\<forall>p' \<in> ptr_coerce ` set (array_addrs p (nat len)). vld p' )"

definition valid_array2 :: "(u_int ptr \<Rightarrow> bool) \<Rightarrow> (u_int ptr \<Rightarrow> u_int) \<Rightarrow> s_int ptr \<Rightarrow> int \<Rightarrow> bool" where
  "valid_array2 vld h p len = 
  (\<forall>p' \<in> ptr_coerce ` set (array_addrs p (nat len)).  unat (h p') \<le> nat INT_MAX)"

definition valid_array :: "(u_int ptr \<Rightarrow> bool) \<Rightarrow> (u_int ptr \<Rightarrow> u_int) \<Rightarrow> s_int ptr \<Rightarrow> int \<Rightarrow> bool" where
  "valid_array vld h p len = (valid_array1 vld p len \<and> valid_array2 vld h p len)"

(*******************************************************************************)


text \<open> Prove the following lemma: \<close>
lemma key_lt:
  "\<lbrakk> key < xs ! nat mid;  mid - 1 < x; sorted xs; 0 \<le> mid; x < int (length xs) \<rbrakk> 
  \<Longrightarrow> key < xs ! nat x"
  apply (simp add: sorted_equals_nth_mono) thm sorted_equals_nth_mono
  apply (case_tac "mid = x")
   apply (simp)
  apply (erule_tac x = "nat x" in allE)
  apply (rule impE) 
    apply (simp+)
  apply (erule_tac x = "nat mid" in allE)
  apply (erule impE) 
   apply (arith+)
  apply fastforce
  done

text \<open> Prove the following lemma: \<close>
lemma key_gt:
  "\<lbrakk> xs ! nat mid < key; 0 \<le> x; x \<le> mid; sorted xs; mid < int (length xs) \<rbrakk>
  \<Longrightarrow> xs ! nat x < key"
  apply (simp add: sorted_equals_nth_mono)
  apply (case_tac "mid = x")
   apply (simp)
  apply (erule_tac x = "nat mid" in allE)
  apply (rule impE) 
    apply (simp+)
  apply (erule_tac x = "nat x" in allE)
  apply (erule impE) 
   apply (arith+)
   apply fastforce
  done

(*******************************************************************************)

text \<open> extra lemmas needed \<close>

lemma length_array_list [simp]:
  "length (array_list h a len) = nat len"
  unfolding array_list_def by simp

lemma array_addrs:
  "\<lbrakk> 0 \<le> x; nat x < len \<rbrakk> \<Longrightarrow> p +\<^sub>p x \<in> set (array_addrs p len)"
  by (force simp add: set_conv_nth)

lemma valid_arrayD:
  "\<lbrakk> valid_array vld h p len; 0 \<le> x; x < len \<rbrakk> 
  \<Longrightarrow> vld (ptr_coerce p +\<^sub>p x) \<and> unat (h (ptr_coerce p +\<^sub>p x)) \<le> nat INT_MAX"
  unfolding valid_array_def valid_array1_def valid_array2_def
  apply clarsimp
  apply (drule bspec)
   apply (fastforce intro: array_addrs)
  apply (drule bspec)
   apply (fastforce intro: array_addrs)
  apply simp
  done

(*******************************************************************************)

lemma binary_search_correct:
  notes ptr_array [where len=len, simp]
  shows
  "\<lbrace>\<lambda>s. sorted (array_list (heap_w32 s) a len) \<and>
        valid_array (is_valid_w32 s) (heap_w32 s) a len \<and> 
        0 \<le> len \<and> len + len -2 \<le> INT_MAX \<rbrace>
   binary_search' a len key
   \<lbrace> \<lambda>r s. (r < 0 \<longrightarrow> key \<notin> set (array_list (heap_w32 s) a len)) \<and>
           (0 \<le> r \<longrightarrow> r < len \<and> (array_list (heap_w32 s) a len ! nat r) = key)\<rbrace>!"
  unfolding binary_search'_def
  apply(subst whileLoopE_add_inv[where
               I="\<lambda>(high,low) s. valid_array (is_valid_w32 s) (heap_w32 s) a len \<and>
                                 sorted (array_list (heap_w32 s) a len) \<and>
                                 0 \<le> low \<and> low \<le> len \<and> high < len \<and> len + len -2 \<le> INT_MAX \<and>
                                 (\<forall>x. 0 \<le> x \<longrightarrow> x < low \<longrightarrow> array_list (heap_w32 s) a len ! nat x < key) \<and>
                                 (\<forall>x. high < x \<longrightarrow> x < len \<longrightarrow> array_list (heap_w32 s) a len ! nat x > key)" and 
               M="\<lambda>((high,low),_). nat (high + 1 - low)"])
  apply (simp add:INT_MAX_def INT_MIN_def)
  apply wp
      prefer 3
      apply wp
     prefer 3
     apply wp
    prefer 3
    apply wp
    apply clarsimp
   apply clarsimp
   apply (rename_tac high low s)
   apply (drule_tac x="(low + high) div 2"
          in valid_arrayD [unfolded INT_MAX_def], simp+)
   apply (intro conjI impI; clarsimp?; arith?)
    apply (erule (2) key_lt, simp+)
   apply (erule (3) key_gt, simp)
  apply clarsimp
  apply (rename_tac high low s)
  apply (clarsimp simp: not_le set_conv_nth)
  apply (drule_tac x="int i" in spec)
  apply (drule_tac x="int i" in spec)
  apply clarsimp
  apply arith
  done

end


end