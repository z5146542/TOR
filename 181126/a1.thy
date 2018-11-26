theory a1
imports Main
begin

section "Question 1: Types"

text {* submit as part of a .txt or .pdf file *}

section "Question 2: Lambda-Calculus"

text {* submit as part of a .txt or .pdf file *}

section "Question 3: Higher Order Unification"

text {* submit as part of a .txt or .pdf file *}

section "Question 4: Propositional Logic"

lemma prop_a:
  "A \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (rule disjI1)
  apply assumption
  done

lemma prop_b:
  "A \<and> B \<longrightarrow> A"
  apply (rule impI)
  apply (erule conjE)
  apply assumption
  done

lemma prop_c:
  "(P \<or> P) = P"
  apply (rule iffI)
   apply (erule disjE)
    apply assumption
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma prop_d:
  "\<not>\<not>P \<longrightarrow> P"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma prop_e:
  "P \<longrightarrow> \<not>\<not>P"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

lemma prop_f:
  "\<not>\<not>\<not>P \<longrightarrow> \<not>P"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done
  

lemma prop_g:
  "(A \<and> B \<longrightarrow> C) = (A \<longrightarrow> B \<longrightarrow> C)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule impI)
   apply(erule impE)
    apply(rule conjI)
     apply assumption
    apply assumption
   apply assumption
  apply (rule impI)
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma prop_h:
  "(x = False) = (\<not> x)"
  apply (rule iffI)
   apply (rule ccontr)
  apply 
  done

lemma prop_i:
  "(P \<longrightarrow> Q) = (\<not> (P \<and> \<not> Q))"
  oops

lemma prop_j:
  "(P \<or> \<not> P) \<longrightarrow> (\<not>\<not> P \<longrightarrow> P)"
  oops

lemma prop_k:
  "(P \<or> (Q \<and> R)) \<longrightarrow> ((P \<or> Q) \<and> (P \<or> R))"
  oops

text {*
Which of the above statements are provable only in a classical logic?
*}

end