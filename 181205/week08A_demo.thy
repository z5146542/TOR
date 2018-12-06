theory week08A_demo
  imports Main
begin


-- "Syntax and State Space"

type_synonym
  vname   = string
type_synonym
  state = "vname \<Rightarrow> nat"

type_synonym
  aexp  = "state \<Rightarrow> nat"
type_synonym  
  bexp  = "state \<Rightarrow> bool"

datatype
  com = SKIP                    
      | Assign vname aexp       ("_ :== _ " [60,60] 60)
      | Semi   com com          ("_;; _"  [50, 51] 50)
      | Cond   bexp com com     ("IF _ THEN _ ELSE _"  [0,0,59] 60)
      | While  bexp com         ("WHILE _ DO _ OD"  [0,45] 60)


-- "Example Program"

definition
  A :: vname where
  "A \<equiv> ''A''"

definition
  B :: vname  where
  "B \<equiv> ''B''"

lemma [simp]: "A \<noteq> B" by (simp add: A_def B_def)
lemma [simp]: "B \<noteq> A" by (simp add: A_def B_def)

definition
  factorial :: com where
  "factorial \<equiv>  B :== (\<lambda>s. 1);;
                WHILE (\<lambda>s. s A \<noteq> 0) DO
                   B :== (\<lambda>s. s B * s A);;
                   A :== (\<lambda>s. s A - 1)
                OD"

-- "Execution"

inductive 
  eval :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" ("_/ \<Rightarrow> _" [60,60] 61)
where
  Skip [intro!,simp]:    
  "(SKIP, s) \<Rightarrow> s"
|
  Assign [intro!,simp]: 
  "(x :== a, s) \<Rightarrow> s (x := a s)"
|
  Semi [intro!]:
  "\<lbrakk> (c\<^sub>1,s) \<Rightarrow> s''; (c\<^sub>2,s'') \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> s'"
|
  IfTrue: 
  "\<lbrakk> b s; (c\<^sub>1,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> s'"
|
  IfFalse: 
  "\<lbrakk> \<not>b s; (c\<^sub>2,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> s'"
|
  WhileFalse: 
  "\<not>b s \<Longrightarrow> (WHILE b DO c OD, s) \<Rightarrow> s"
|
  WhileTrue:  
  "\<lbrakk>b s; (c,s) \<Rightarrow> s''; (WHILE b DO c OD, s'') \<Rightarrow> s'\<rbrakk> \<Longrightarrow> (WHILE b DO c OD, s) \<Rightarrow> s'"


(* Isabelle provides eval.induct which allows the 
   elimination of terms cs \<Rightarrow> t.
   In practice, we will have cs as a tuple (c,s).
   To avoid to manually have to split cs every time,
   we can use split_format as below to define an induction
   rule that will work on terms of the form (c, s) \<Rightarrow> t.*)

thm eval.induct
lemmas eval_induct = eval.induct [split_format (complete)]
thm eval_induct


(* In practice, it is also useful to have elimination rules
   for precisely when e.g. c=SKIP, or c= c1;;c2, etc.
   (If c=SKIP, eval_induct has many useless cases).
   The command inductive_cases allows exactly this.*)

inductive_cases
  skip [elim!]:   "(SKIP, s) \<Rightarrow> s'" and
  assign [elim!]: "(x :== a, s) \<Rightarrow> s'" and
  semi [elim!]:   "(c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> s'" and
  "if" [elim!]:   "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> s'" and
  while:          "(WHILE b DO c OD, s) \<Rightarrow> s'"

thm skip assign semi "if" while

lemma skip_eq [simp]: "(SKIP, s) \<Rightarrow> s' = (s' = s)" by blast
lemma assign_eq [simp]: "(x :== a, s) \<Rightarrow> s' = (s' = s (x := a s))"  by blast



-- ---------------------------------------------------------------------
-- "Example Proof"

primrec
  fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
 |"fac (Suc n) = (Suc n) * fac n"

(* Need to relate the final state of B to values of A and B *at each iteration* 
   of the loop *)
lemma factorial_partial_correct_helper:
  "(prog, s) \<Rightarrow> s' \<Longrightarrow> 
    prog = WHILE \<lambda>s. 0 < s A DO B :== (\<lambda>s. s B * s A) ;; A :== (\<lambda>s. s A - Suc 0)  OD \<Longrightarrow> 
    s' B = s B * fac (s A)"
  using [[simp_trace]]
  (*TODO*)
  apply (induct rule: eval_induct)
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply simp
  apply simp
  apply (case_tac "s A")
   apply simp
  apply clarsimp
  apply (simp add: distrib_left distrib_right)
  done

lemma factorial_partial_correct:
  "(factorial, s) \<Rightarrow> s' \<Longrightarrow> s' B = fac (s A)"
  (*TODO*)
  apply (unfold factorial_def)
  apply clarsimp
  apply (simp add: factorial_partial_correct_helper)
  done

-- ---------------------------------------------------------------------

type_synonym assn = "state => bool"

definition
  hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile> {P} c {Q} \<equiv> \<forall>s s'. P s \<longrightarrow> (c,s) \<Rightarrow> s' \<longrightarrow> Q s'"


inductive 
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
  h_skip: 
  "\<turnstile> {P} SKIP {P}"
|
  h_assign:  
  "\<turnstile> {\<lambda>s. P (s(x:= a s))} x:==a {P}"
|
  h_semi: 
  "\<lbrakk> \<turnstile> {P} c\<^sub>1 {R}; \<turnstile> {R} c\<^sub>2 {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P} c\<^sub>1;;c\<^sub>2 {Q}"
|
  h_if: 
  "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> b s} c\<^sub>1 {Q}; \<turnstile> {\<lambda>s. P s \<and> \<not>b s} c\<^sub>2 {Q} \<rbrakk> \<Longrightarrow>
  \<turnstile> {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"
|
  h_while: 
  "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> b s} c {P}; \<forall>s. P s \<and> \<not>b s \<longrightarrow> Q s \<rbrakk> \<Longrightarrow>
  \<turnstile> {P} WHILE b DO c OD {Q}"
|
  conseq: 
  "\<lbrakk> \<forall>s. P s \<longrightarrow> P' s; \<turnstile> {P'} c {Q'}; \<forall>s. Q' s \<longrightarrow> Q s \<rbrakk> \<Longrightarrow>
  \<turnstile> {P} c {Q}"

print_theorems

-- "Soundness Proof"
 
(* When a while loop is fully executed to a state s', 
   then the loop condition is false in s' (otherwise there
   would have been another iteration). Moreover, if the loop
   satisfies an invariant P, then P is true when the loop exits. *)
lemma while_final:
  "\<lbrakk>(prog, s) \<Rightarrow> s';  \<forall>s. P s \<and> b s \<longrightarrow> (\<forall>s'. (c, s) \<Rightarrow> s' \<longrightarrow> P s');  P s;
    prog = WHILE b DO c OD\<rbrakk>  \<Longrightarrow> P s' \<and> \<not> b s'"
  (*TODO*)
  by (induct rule: eval_induct; auto)
   
(* To show that a postcondition Q holds after a While loop,
   we need to find a predicate P that is an invariant of the loop
   (i.e. preserved by the loop body at each iteration) and
   is "enough" to prove the postcondition when the proof exits.*)
lemma while_sound:
  "\<lbrakk>\<Turnstile> {\<lambda>a. P a \<and> b a} c {P}; \<forall>s. P s \<and> \<not> b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow> 
  \<Turnstile> {P} WHILE b DO c OD {Q}"
  (*TODO*)
  apply (simp add: hoare_valid_def)
  apply clarsimp
  apply (drule (2) while_final, simp)
  apply simp
  done

theorem hoare_sound:
  "\<turnstile> {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
  (*TODO*)
  apply (induct rule: hoare.induct)
       apply (fastforce simp: hoare_valid_def)+
   apply (erule (1) while_sound)
  apply (fastforce simp: hoare_valid_def)+
  done

-- --------------------------------------------------------------------------------------
-- "derived rules"

lemma h_ass:
  "(\<And>s. P s \<Longrightarrow> Q (s(x := a s))) \<Longrightarrow> \<turnstile> {P} x :== a {Q}"
  apply(rule_tac Q'=Q in conseq)
  prefer 2
  apply(rule h_assign)
  apply(blast)+
  done
 


-- "example proof"

lemma "\<turnstile> {\<lambda>s. True} x :== (\<lambda>s. 2) {\<lambda>s. s x = 2}"
  apply(rule h_ass)
  apply simp
  done

lemma 
  "\<turnstile> {\<lambda>s. s A = n} factorial {\<lambda>s. s B = fac n}"
  apply(unfold factorial_def)
  apply(rule h_semi)
   prefer 2
   apply(rule_tac P="\<lambda>s. s B * fac (s A) = fac n" in h_while)
    apply(rule h_semi)
     prefer 2
     apply(rule h_assign)
    apply(rule h_ass)
    apply clarsimp
    apply(case_tac "s A", simp)
    apply clarsimp
    apply (simp add: add_mult_distrib2 comm_semiring_class.distrib)
   apply clarsimp
  apply(rule h_ass)
  apply clarsimp
  done
  
end
