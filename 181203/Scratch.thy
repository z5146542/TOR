theory Scratch
  imports Main
begin
lemma a:
  assumes "A"
  assumes "B"
  shows "A \<and> B \<Longrightarrow> True"
  using [[simp_trace]]
  apply auto
  done
end