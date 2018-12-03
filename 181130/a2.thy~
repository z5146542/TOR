theory a2
  (* Download the file RegExp.thy and put it in the same directory as this one: *)
  imports RegExp
begin

section "Question 1: Higher-Order Logic"

lemma hol_a: "\<not>(\<forall>x. P x) \<longleftrightarrow> (\<exists>x. \<not>P x)"
  (*TODO*)
  apply (rule iffI)
   apply (rule classical)
   apply (erule notE)
   apply (rule allI)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule_tac x = "x" in exI)
   apply assumption
  apply (rule notI)
  apply (erule exE)
  apply (erule notE)
  apply (erule_tac x = "x" in allE)
  apply assumption
  done

lemma hol_b: "(\<forall>x. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x. Q x))"
  (*TODO*)
  apply (rule iffI)
   apply (rule impI)
   apply (rule allI)
   apply (erule_tac x = "x" in allE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule_tac x = "x" in allE)
  apply assumption
  oops

  find_theorems "(_ \<or> _)"

lemma hol_c: "\<forall>x. \<not>f x \<longrightarrow> f (g x) \<Longrightarrow> \<forall>x. f x \<or> f (g x)"
  (*TODO*)
  apply (rule allI)
  apply (erule_tac x = "x" in allE)
  apply (rule classical)
  apply (erule impE)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma hol_d: "\<lbrakk>\<forall>x. \<not>f x \<longrightarrow> f (g x); \<exists>x. f x\<rbrakk> \<Longrightarrow> \<exists>x. f x \<and> f (g (g x))"
  (*TODO*)
  apply (erule exE)
  apply (case_tac "f (g (g x))")
   apply (rule_tac x = "x" in exI)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule_tac x = "g x" in exI)
  apply (rule conjI)
   apply (drule hol_c)
   apply (erule_tac x = "g x" in allE)
   apply (erule disjE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule_tac x = "g (g x)" in allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma hol_e: "(\<forall>x. Q x = P x) \<and> ((\<exists>x. P x) \<longrightarrow> H) \<and> (\<exists>x. Q x) \<longrightarrow> H"
  (*TODO*)
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (drule iffD1)
   apply assumption
  apply (erule impE)
   apply (rule_tac x = "x" in exI)
   apply assumption
  apply assumption
  done

lemma hol_f: "(\<forall>Q. (\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> Q) \<longrightarrow> (\<exists>x. P x)"
  (*TODO*)
  apply (rule impI)
  apply (erule_tac x = "\<exists>x . P x" in allE)
  apply (erule impE)
   prefer 2
   apply assumption
  apply (rule allI)
  apply (rule impI)
  apply (rule_tac x = "x" in exI)
  apply assumption
  done


(*---------------------------------------------------------*) 
section "Question 2: Strings and Regular Expressions"

(* An example string with newline characters *)
definition
  test_str :: string
  where
  "test_str = 
''some
test
abc hello
text''"

definition
  new_line :: char
  where
  "new_line = CHR ''\<newline>''"


(*----------------*)
(* Question 2 (a) *)
primrec
  glue :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list"
  where
  "glue a [] = []" |
  "glue a (xs # xss) = (if xss = [] then xs else xs @ a # glue a xss)"

(* test on some examples *)

value "glue (Suc 0) [[0, 0], [2, 2], [0]]"
value "glue (Suc 0) [[0, 0], [2, 2], [0], []]"
value "glue (Suc 0) [[],[]]"


(* Define and test on some examples:
  chop :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list"
*)

primrec
  chop' :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where
  "chop' ys a [] = [ys]" |
  "chop' ys a (x # xs) = (if x = a then ys # (chop' [] a xs) else chop' (ys @ [x]) a xs)"

definition "chop = chop' []"

(*----------------*)
(* Question 2 (b) *)
primrec
  num_of :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
  where
  "num_of a [] = 0" |
  "num_of a (x # xs ) = (if a = x then Suc (num_of a xs) else num_of a xs)"

lemma length_glue:
  "length (glue a xss) = sum_list (map length xss) + length xss - 1"
  (*TODO*)
  apply (induct xss)
  apply auto
  done

lemma length_chop' [simp]:
  "length (chop' ys x xs) = num_of x xs + 1"
  apply (induct xs arbitrary: ys)
  apply auto
  done

lemma length_chop:
  "length (chop x xs) = num_of x xs + 1"
  (*TODO*)
  apply (unfold chop_def)
  apply (simp add: chop_def)
  done



(*----------------*)
(* Question 2 (c) *)
lemma chop'_set:
  "\<lbrakk> ls \<in> set (chop' ys a xs); a \<notin> set ys \<rbrakk> \<Longrightarrow> a \<notin> set ls"
  apply (induct xs arbitrary: ys ls)
  apply (auto split: if_split_asm)
  sorry

lemma chop_sep:
  "ls \<in> set (chop a xs) \<Longrightarrow> a \<notin> set ls"
  (*TODO*)
  apply (simp add: chop'_set chop_def)
  oops

lemma chop'_neq_Nil[simp]:
  "chop' ys a xs \<noteq> []"
  by (induct xs arbitrary: ys) auto

lemma glue_chop'[simp]:
  "glue a (chop' ys a xs) = ys @ xs"
  by (induct xs arbitrary: ys) auto


lemma glue_chop:
  "glue a (chop a xs) = xs"
  (*TODO*)
   apply (simp add: chop_def)
  done



(*----------------*)
(* Question 2 (d) *)

(* TODO: define
  any_of :: "regexp list \<Rightarrow> regexp"
*)

definition
  any_of :: "regexp list \<Rightarrow> regexp"
  where
  "any_of xs = fold Alt xs null"

lemma lang_fold_Alt[simp]:
  "lang (fold Alt rs r) = \<Union> (lang ` set rs) \<union> lang r"
  apply (induct rs arbitrary: r)
   apply auto
  done

lemma lang_any_of[simp]:
  "lang (any_of rs) = \<Union> (lang ` set rs)"
  (* TODO *)
  apply (simp add: any_of_def)
  done

primrec
  repeat :: "word set \<Rightarrow> nat \<Rightarrow> word set"
  where
  "repeat A 0 = {[]}"
| "repeat A (Suc n) = conc A (repeat A n)"

lemma concI[elim]:
  "\<lbrakk> as \<in> A; bs \<in> B \<rbrakk> \<Longrightarrow> as @ bs \<in> conc A B"
  apply (auto simp: conc_def)
  done

lemma concD[dest!]:
  "xs \<in> conc A B \<Longrightarrow> \<exists>as bs. as \<in> A \<and> bs \<in> B \<and> xs = as @ bs"
  apply (auto simp: conc_def)
  done

lemma repeat_0[simp,intro!]:
  "[] \<in> repeat A 0"
  apply simp
  done

lemma repeat_Suc[elim]:
  "\<lbrakk> as \<in> A; xs \<in> repeat A n \<rbrakk> \<Longrightarrow> as @ xs \<in> repeat A (Suc n)"
  apply auto
  done

lemma star_repeat_Ex:
  "as \<in> star A \<Longrightarrow> \<exists>n. as \<in> repeat A n"
  apply (erule star.induct)
    apply auto
  done

lemma repeat_n_star:
  "as \<in> repeat A n \<Longrightarrow> as \<in> star A"
  apply (induct n arbitrary: as) 
    apply auto
  done

lemma star_repeat:
  "star A = (\<Union>n. repeat A n)"
  apply auto
  apply (auto simp: star_repeat_Ex repeat_n_star)
  done

(*----------------*)
(* Question 2 (e) *)
definition
  matches :: "regexp \<Rightarrow> string \<Rightarrow> bool"
  where
  "matches r w \<equiv> w \<in> lang r"

definition
  matches_sub :: "regexp \<Rightarrow> string \<Rightarrow> bool"
  where
  "matches_sub r = matches TODO"

primrec
  string :: "string \<Rightarrow> regexp"
  where
  "string [] = TODO"

primrec
  is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "is_prefix [] ys = TODO"

primrec
  is_substring :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "is_substring xs [] = TODO"

(* TODO: test on some examples *)


lemma matches_sub:
  "matches_sub r xs = (\<exists>xs' ys zs. xs = ys @ xs' @ zs \<and> matches r xs')"
  (* TODO *)
  oops

lemma matches_string[simp]:
  "matches (string xs) ys = (ys = xs)"
  (* TODO *)
  oops

lemma is_substring:
  "is_substring xs ys = (\<exists>bs cs. ys = bs @ xs @ cs)"
  (* TODO *)
  oops

lemma matches_substring:
  "matches_sub (string xs) l = is_substring xs l"
  (* TODO *)
  oops


(*----------------*)
(* Question 2 (f) *)
primrec
  rlen :: "regexp \<Rightarrow> nat option"
  where
  "rlen (Atom a) = TODO"

lemma rlen_string[simp]:
  "rlen (string xs) = Some (length xs)"
  (* TODO *)
  oops

lemma rlen_lang:
  "rlen r = Some n \<Longrightarrow> \<forall>xs \<in> lang r. length xs = n"
  (* TODO *)
  oops



(*---------------------------------------------------------*)
section "Question 3: Normal Forms"

(*----------------*)
(* Question 3 (a) *)
fun
  find_pat :: "'a list \<Rightarrow> 'a list"
  where
  (* TODO *)

value "find_pat ''cababc''"

lemma hd_find_pat[simp]:
  "hd (find_pat xs) = hd xs"
  (* TODO *)
  oops

lemma last_find_pat[simp]:
  "last (find_pat xs) = last xs"
  (* TODO *)
  oops

lemma find_pat_neq:
  "(find_pat xs \<noteq> xs) = (\<exists>as bs x y. xs = as @ x # y # x # bs)"
  (* TODO *)
  oops

lemma find_pat_eq:
  "(find_pat xs = xs) = (\<forall>as bs x y. xs \<noteq> as @ x # y # x # bs)"
  by (metis find_pat_neq)


(*----------------*)
(* Question 3 (b) *)

lemma find_pat_neq_Cons:
  "find_pat xs \<noteq> xs \<Longrightarrow> find_pat (x#xs) \<noteq> x#xs"
  oops (* helper *)

lemma find_pat_eq_Cons:
  "find_pat (x#xs) = x#xs \<Longrightarrow> find_pat xs = xs"
  oops (* helper *)

lemma find_pat_Cons_find_pat:
  "find_pat (x#find_pat xs) = find_pat (find_pat (x#xs))"
  (* TODO *)
  oops

lemma find_pat_app_find_pat:
  "find_pat (find_pat xs @ [x]) = find_pat (find_pat (xs @ [x]))"
  (* TODO *)
  oops

lemma find_pat_appendD:
  "find_pat (xs @ ys) = xs @ ys \<Longrightarrow> find_pat xs = xs"
  oops (* helper *)

lemma find_pat_eq_rev:
  "find_pat xs = xs \<Longrightarrow> find_pat (rev xs) = rev xs"
  (* TODO *)
  oops

lemma find_pat_rev:
  "find_pat xs = xs \<Longrightarrow> find_pat (rev xs @ [x]) = rev (find_pat (x # xs))"
  (* TODO *)
  oops


(*----------------*)
(* Question 3 (c) *)
fun
  nf :: "'a list \<Rightarrow> 'a list"
  where
  "nf xs = (if find_pat xs = xs then xs else nf (find_pat xs))"
  (* Extract a lemma that helps Isabelle to prove termination here. Make it [simp]. *)
  sorry


(* This means simp will not automatically unfold nf. Use "subst nf.simps" to unfold manually. *)
declare nf.simps[simp del]

value "nf ''cabacacb''"


lemma nf_singles[simp]:
  "nf [] = []"
  "nf [x] = [x]"
  "nf [x,y] = [x,y]"
  by (auto simp: nf.simps)

lemma nf_find_pat:
  "nf (find_pat xs) = nf xs"
  (* TODO *)
  oops

lemma nf_fp:
  "find_pat (nf xs) = nf xs"
  (* TODO *)
  oops

lemma nf_nf:
  "nf (nf xs) = nf xs"
  (* TODO *)
  oops

lemma hd_nf:
  "hd (nf xs) = hd xs"
  (* TODO *)
  oops

lemma last_nf:
  "last (nf xs) = last xs"
  (* TODO *)
  oops


(*----------------*)
(* Question 3 (d) *)


lemma find_pat_nf_Cons:
  "find_pat xs = xs \<Longrightarrow> nf (x#xs) = find_pat (x#xs)"
  oops (* helper *)

lemma nf_find_pat_Cons:
  "find_pat xs \<noteq> xs \<Longrightarrow> nf (x # find_pat xs) = nf (x # xs)"
  oops (* helper *)

lemma nf_Cons_nf:
  "nf (x#nf xs) = nf (x#xs)"
  (* TODO *)
  oops

lemma nf_hd_dist:
  "nf (x#xs) = find_pat (x#nf xs)"
  (* TODO *)
  oops

lemma nf_last_dist:
  "nf (xs @ [x]) = find_pat (nf xs @ [x])"
  (* TODO *)
  oops

lemma find_pat_rev_Cons:
  "rev (find_pat (x#nf xs)) = find_pat (rev (x#nf xs))"
  oops (* helper *)

lemma nf_rev:
  "nf (rev xs) = rev (nf xs)"
  (* TODO *)
  oops

end