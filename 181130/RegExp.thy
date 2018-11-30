theory RegExp
  imports Main
begin

(* --------------------------------------------- *)
(* Defining the data type of regular expressions *)

datatype regexp =
   Atom char
 | Alt regexp regexp
 | Conc regexp regexp (infixl "\<cdot>"  60)
 | Star regexp
 | Neg regexp

(* Some expressions: *)

term "Neg (Atom a \<cdot> Atom b)"
term "Star (Neg (Atom (CHR ''a''))) \<cdot> Atom (CHR ''b'')"

(* Match everything: *)
definition
  "Univ = Alt (Neg undefined) undefined"

(* Match nothing: *)
definition
  "null = Neg Univ"

(* Match only the empty string: *)
definition
  "epsilon = Star null"


(* --------------------------------------------- *)
(* Defining the language of a regular expression *)

type_synonym word = "char list"

inductive_set star for L
  where
  star_empty[simp,intro!]: "[] \<in> star L"
| star_app[elim]: "\<lbrakk> u \<in> L; v \<in> star L \<rbrakk> \<Longrightarrow> u@v \<in> star L"

definition conc :: "word set \<Rightarrow> word set \<Rightarrow> word set"
  where
  "conc A B \<equiv> { xs@ys |xs ys. xs \<in> A \<and> ys \<in> B}"

primrec
  lang :: "regexp \<Rightarrow> word set"
  where
  "lang (Atom c) = {[c]}"
| "lang (Alt e1 e2) = lang e1 \<union> lang e2"
| "lang (Conc e1 e2) = conc (lang e1) (lang e2)"
| "lang (Star e) = star (lang e)"
| "lang (Neg e) = -lang e"


lemma lang_all[simp]:
  "lang Univ = UNIV"
  by (simp add: Univ_def)

lemma lang_null[simp]:
  "lang null = {}"
  by (simp add: null_def)

lemma star_empty[simp]:
  "star {} = {[]}"
  by (auto elim: star.induct)

lemma lang_epsilon[simp]:
  "lang epsilon = {[]}"
  by (simp add: epsilon_def)

lemma Alt_null:
  "lang (Alt x null) = lang x"
  by simp

(*-----------------------------------------------------*)
(* Defining the reverse of a regular expression *)

primrec
  rrev :: "regexp \<Rightarrow> regexp"
  where
  "rrev (Atom c) = Atom c"
| "rrev (Alt e1 e2) = Alt (rrev e1) (rrev e2)"
| "rrev (Conc e1 e2) = Conc (rrev e2) (rrev e1)"
| "rrev (Star e) = Star (rrev e)"
| "rrev (Neg e) = Neg (rrev e)"



(*-----------------------------------------------------*)
(* Correctness proof *)

lemma star_one[intro]:
  "xs \<in> L \<Longrightarrow> xs \<in> star L"
  by (drule star_app[where v="[]"]; simp)

lemma star_app2[elim]:
  "\<lbrakk> xs \<in> star L; ys \<in> L \<rbrakk> \<Longrightarrow> xs @ ys \<in> star L"
  by (erule star.induct) auto

lemma star_rev1:
  "xs \<in> star (rev ` L) \<Longrightarrow> xs \<in> rev ` star L"
  apply (induct rule: star.induct; clarsimp)
  apply (rename_tac xs ys)
  apply (rule_tac x="ys@xs" in image_eqI, simp)
  apply fastforce
  done

lemma star_rev2:
  "xs \<in> star L \<Longrightarrow> rev xs \<in> star (rev ` L)"
  by (induct rule: star.induct) auto

lemma star_rev[simp]:
  "star (rev ` L) = rev ` star L"
  by (auto simp: star_rev1 star_rev2)

lemma conc_rev[simp]:
  "conc (rev ` L2) (rev ` L1) = rev ` conc L1 L2"
  apply (simp add: conc_def)
  apply (rule equalityI)
   apply clarsimp
   apply (rename_tac xs ys)
   apply (rule_tac x="ys@xs" in image_eqI, auto)[1]
  apply fastforce
  done

lemma neg_rev[simp]:
  "- rev ` L = rev ` (-L)"
  apply (rule bij_image_Compl_eq[symmetric])
  apply (rule bijI, simp)
  apply (rule_tac f=rev in surjI)
  apply simp
  done

lemma "lang (rrev e) = rev ` (lang e)"
  by (induct e; fastforce)

end