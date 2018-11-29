theory week06A_demo imports Main begin

-- -----------------------------------------------------------------------

-- {* a recursive data type: *}
datatype ('a,'b) tree = Tip | Node "('a,'b) tree" 'b "('a,'b) tree"

term Tip
term Node

print_theorems

-- {* distinctness of constructors automatic: *}
lemma "Tip ~= Node l x r" by simp

-- {* case syntax, case distinction manual *}
lemma "(1::nat) \<le> (case t of Tip \<Rightarrow> 1 | Node l x r \<Rightarrow> x+1)"
  apply(case_tac t)
  apply auto
  done

-- {* partial cases and dummy patterns: *}
term "case t of Node _ b _ => b" 

-- {* partial case maps to 'undefined': *}
lemma "(case Tip of Node _ _ _ => 0) = undefined" by simp

-- {* nested case and default pattern: *}
term "case t of Node (Node _ _ _) x Tip => 0 | _ => 1"


-- {* inifinitely branching: *}
datatype 'a inftree = Tp | Nd 'a "nat \<Rightarrow> 'a inftree"

-- {* mutually recursive *} 
datatype 
  ty = Integer | Real | RefT ref
  and
  ref = Class | Array ty







-- -----------------------------------------------------------------  

-- {* primitive recursion *}

primrec
  app :: "'a list => 'a list => 'a list"
where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"

print_theorems

primrec
  rv :: "'a list => 'a list"
where
  "rv [] = []" |
  "rv (x#xs) = app (rv xs) [x]"


-- {* on trees *}
primrec
  mirror :: "('a,'b) tree => ('a,'b) tree"
where
  "mirror Tip = Tip" |
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"

print_theorems


-- {* mutual recursion *}
primrec
  has_int :: "ty \<Rightarrow> bool" and
  has_int_ref :: "ref \<Rightarrow> bool"
where
  "has_int Integer       = True" |
  "has_int Real          = False" |
  "has_int (RefT T)      = has_int_ref T" |

  "has_int_ref Class     = False" |
  "has_int_ref (Array T) = has_int T"



-- ------------------------------------------------------------------

-- {* structural induction *}

-- {* discovering lemmas needed to prove a theorem *}

term app

lemma rv_Nil: "app xs Nil = xs"
  apply (induction xs)
   apply simp
  apply simp
  done

lemma app_assoc: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induct xs)
   apply auto
  done

lemma rv_app: "rv (app xs ys) = app (rv ys) (rv xs)"
  apply (induction xs)
   apply simp
   apply (simp add:rv_Nil)
  apply simp
  apply (simp add:app_assoc)
  done

theorem rv_rv: "rv (rv xs) = xs"
  apply (induction xs)
   apply simp
  apply simp
  apply (simp add: rv_app)
  done




-- {* induction heuristics *}

primrec
  itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_cons: "app (app xs (Cons a Nil)) ys = app xs (Cons a ys)"
  apply (induction xs)
   apply auto
  done

lemma itrev_app: "\<forall>ys. itrev xs ys = app (rv xs) ys"
  apply (induction xs)
   apply simp+
  apply clarsimp
  apply (simp only: itrev_cons)
  done

lemma "itrev xs [] = rv xs"
  apply (induct xs)
   apply simp+
  apply (simp add: itrev_app)
  done

lemma de_morgans_law: "\<not>(A \<or> B) \<longrightarrow> \<not>A \<and> \<not>B"
  using [[simp_trace]]
  apply (rule impI)
  apply (rule conjI)
   apply (rule classical)
   apply (erule notE)
  apply (rule disjI1)
   apply (rule classical)
   apply (erule notE)
   apply assumption
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done



-- ------------------------------------------------------------------

primrec
  lsum :: "nat list \<Rightarrow> nat"
where
  "lsum [] = 0" |
  "lsum (x#xs) = x + lsum xs"


lemma 
  "2 * lsum [0 ..< Suc n] = n * (n + 1)"

  apply (induction n)
  apply simp
  apply simp
  apply ()
  oops

lemma 
  "lsum (replicate n a) = n * a"
  oops


-- {* tail recursive version: *}

primrec
  lsumT :: "nat list \<Rightarrow> nat \<Rightarrow> nat" 
where
  "lsumT [] s = ?" 

lemma lsum_correct:
  "lsumT xs 0 = lsum xs"
  oops

end