theory week04B_demo imports Main begin

-- ------------------------------------------------------------------

text {* implicit backtracking *}
lemma "\<lbrakk>P \<and> Q; R \<and> S\<rbrakk> \<Longrightarrow> S"
  (* doesn't work -- picks the wrong assumption 
  apply(erule conjE)
  apply assumption  *)
  -- "apply(erule conjE, assumption)"
  apply(erule_tac Q = "S" in conjE)
  apply assumption
  done

text {* do (n) assumption steps *}
lemma "\<lbrakk>P \<and> Q\<rbrakk> \<Longrightarrow> P"
  apply(erule (1) conjE)
  done

text {* 'by' does extra assumption steps implicitly *}
lemma "\<lbrakk>P \<and> Q\<rbrakk> \<Longrightarrow> P"
  by(erule conjE)

text {* more automation *}

-- "clarsimp: repeated clarify and simp"
lemma "ys = []  \<Longrightarrow> \<forall>xs. xs @ ys = []"
  apply clarsimp
  oops

-- "auto: simplification, classical reasoning, more"
lemma "(\<exists>u::nat. x=y+u) \<longrightarrow> a*(b+c)+y \<le> x + a*b+a*c" thm add_mult_distrib2
  apply (auto simp add: add_mult_distrib2)
  done

-- "limit auto (and any other tactic) to first [n] goals"
lemma "(True \<and> True)"
  apply(rule conjI)
   apply(simp+)[1]
  apply(rule TrueI)
  done

-- "also try: fastforce and force"


print_simpset


text {* simplification with assumptions, more control: *}

lemma "\<forall>x. f x = g x \<and> g x = f x \<Longrightarrow> f [] = f [] @ []"
  -- "would diverge:"
  (* 
  apply(simp)
  *)
  apply(simp (no_asm_use))
  done

-- ------------------------------------------------------

-- "let expressions"

lemma "let a = f x in g a = x"
  apply (simp add: Let_def)
  oops

thm Let_def

term "let a = f x in g a"
term "(let a = f x in g (a + a)) = (Let (f x) (\<lambda>a. g (a + a)))"
-- ------------------------------------------------------

-- "splitting case: manually"

lemma "(case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> x) = x"
  apply (simp only: split: nat.splits)
  apply simp
  done

-- "splitting if: automatic in conclusion"

lemma "\<lbrakk> P; Q \<rbrakk> \<Longrightarrow> (if x then A else B) = z"
  apply simp
  oops


thm if_splits 
thm if_split_asm

lemma "\<lbrakk> (if x then A else B) = z; Q \<rbrakk> \<Longrightarrow> P" 
   apply(simp split: if_splits) (*
   apply (simp split: if_split_asm)*)
  oops

lemma " ((if x then A else B) =z) \<longrightarrow> (z=A\<or>z=B)" 
  apply simp
done

thm conj_cong

lemma "A \<and> (A \<longrightarrow> B)"
  apply (simp cong: conj_cong)
  oops

thm if_cong

lemma "\<lbrakk> (if x then x \<longrightarrow> z else B) = z; Q \<rbrakk> \<Longrightarrow> P"
  apply (simp cong: if_cong)
  oops

thm add_ac
thm mult_ac

lemmas all_ac = add_ac mult_ac
print_theorems

lemma
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<odot>" 70)
  assumes A: "\<And>x y z. (x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  assumes C: "\<And>x y. x \<odot> y = y \<odot> x"
  assumes AC: "\<And>x y z. x \<odot> (y \<odot> z) = y \<odot> (x \<odot> z)"
  shows "(z \<odot> x) \<odot> (y \<odot> v) = something"
  apply (simp only: C)
  apply (simp only: A C)
  apply (simp only: AC)
  oops
  
text {* when all else fails: tracing the simplifier

typing
  declare [[simp_trace]]        turns tracing on,
  declare [[simp_trace=false]]  turns tracing off
(within a proof, write 'using' rather than 'declare')
*}

declare [[simp_trace]]
lemma "A \<and> (A \<longrightarrow> B)"
  apply (simp cong: conj_cong)
  oops
declare [[simp_trace=false]]

-- "single stepping: subst"

thm add.commute
thm add.assoc
declare add.assoc [simp]

lemma "a + b = x + ((y::nat) + z)"
thm add.assoc[symmetric]
  apply (simp add: add.assoc [symmetric] del: add.assoc)
thm add.commute
  apply (subst add.commute [where a=x]) 
  oops


end