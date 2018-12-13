theory test
  imports Main
begin

lemma notnoteq: "\<not>\<not>A \<Longrightarrow> A"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma "\<not>(A \<or> B) \<longrightarrow> \<not>A \<and> \<not>B"
  apply (rule impI)
  apply (rule conjI)
  apply (rule classical)
   apply (erule notE)
   apply (rule disjI1)
   apply (simp add: notnoteq)
  apply (rule classical)
  apply (erule notE)
  apply (simp add: notnoteq)
  done

end