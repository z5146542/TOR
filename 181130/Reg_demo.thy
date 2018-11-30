theory Reg_demo
  imports Main
begin

datatype regexp =
    Atom char
  | Star regexp
  | Alt regexp regexp
  | Conc regexp regexp (infixl "\<cdot>" 60)
  | Neg regexp

term "''abc''"
term "char_of_nat 13"

term UNIV

definition
  "Univ = Alt undefined (Neg undefined)"

definition
  "null = Neg Univ"

definition
  "epsilon = Star null"

primrec
  rrev :: "regexp \<Rightarrow> regexp"
where
  "rrev (Atom c) = Atom c"
| "rrev (Star r) = Star (rrev r)"
| "rrev (Conc r1 r2) = Conc (rrev r2) (rrev r1)"
| "rrev (Alt r1 r2) = Alt (rrev r1) (rrev r2)"
| "rrev (Neg r) = Neg (rrev r)"

type_synonym word = "char list"

definition
  conc :: "word set \<Rightarrow> word set \<Rightarrow> word set"
where
  "conc A B = { as @ bs |as bs. as \<in> A \<and> bs \<in> B }"

inductive_set
  star :: "word set \<Rightarrow> word set" for R
where
  star_empty[simp, intro!]: "[] \<in> star R"
| star_app[elim]: "\<lbrakk> xs \<in> R; ys \<in> star R \<rbrakk> \<Longrightarrow> xs @ ys \<in> star R"


primrec
  lang :: "regexp \<Rightarrow> word set"
where
  "lang (Atom c) = {[c]}"
| "lang (Alt r1 r2) = lang r1 \<union> lang r2"
| "lang (Neg r) = -lang r"
| "lang (Conc r1 r2) = conc (lang r1) (lang r2)"
| "lang (Star r) = star (lang r)"

(*
  repeatn :: nat \<Rightarrow> regexp \<Rightarrow> regexp

  star = \<Union>n. lang (repeatn n r) 
*)

lemma lang_Univ[simp]:
  "lang Univ = UNIV"
  by (simp add: Univ_def)

lemma lang_null[simp]:
  "lang null = {}"
  by (simp add: null_def)

lemma star_empty[simp]:
  "star {} = {[]}"
  by (auto elim: star.cases)

lemma lang_epsilon[simp]:
  "lang epsilon = {[]}"
  by (simp add: epsilon_def)

lemma
  "lang (Alt r1 r2) = lang (Alt r2 r1)"
  by auto

lemma rev_complement[simp]:
  "- rev ` A = rev ` (- A)"
  apply (rule bij_image_Compl_eq[symmetric])
  apply (rule bijI)
   apply (rule injI)
   apply simp
  apply (rule surjI[where f=rev])
  apply simp
  done

lemma conc_rev[simp]:
  "conc (rev ` B) (rev ` A) = rev ` conc A B"
  by (fastforce simp: conc_def image_iff)

lemma star_app2[elim]:
  "\<lbrakk> a \<in> A; as \<in> star A \<rbrakk> \<Longrightarrow> as @ a \<in> star A"
  apply (erule star.induct)
   apply simp
   apply (drule star_app[where ys="[]"])
    apply simp
   apply simp
  apply auto
  done

lemma star_rev1:
  "as \<in> star (rev ` A) \<Longrightarrow> as \<in> rev ` star A"
  apply (erule star.induct)
   apply simp
  apply clarsimp
  apply (rename_tac a as)
  apply (clarsimp simp: image_iff)
  apply (rule_tac x="as @ a" in bexI)
   apply simp
  apply auto
  done

lemma rev2[simp]:
  "as \<in> star A \<Longrightarrow> rev as \<in> star (rev ` A)"
  apply (erule star.induct)
   apply simp
  apply (clarsimp simp: image_iff)
  apply (rule star_app2)
  apply auto
  done

lemma star_rev[simp]:
  "star (rev ` A) = rev ` star A"
  by (auto simp: star_rev1)   

lemma "lang (rrev r) = rev ` lang r"
  by (induct r) auto

end