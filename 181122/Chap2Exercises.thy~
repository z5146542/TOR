theory Chap2Exercises
  imports Main
begin

-- "declare [[names_short]]"

text "Exercise 2.1"

(* Following produces 3 *)
value "1 + (2::nat)"

(* Following produces 3 *)
value "1 + (2::int)"

(* Following produces 0 *)
value "1 - (2::nat)"

(* Following produces -1 *)
value "1 - (2::int)"

text "Exercise 2.2"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)"

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"

value "double 3"

lemma add_associative [simp]: "add x (Suc y) = add (Suc x) y"
  apply (induction x)
   apply (auto)
  done

lemma add_identity: "add x 0 = add 0 x"
  apply (induction x)
   apply (auto)
  done

lemma add_commutative: "add y x = add x y"
  apply (induction x)
   apply (auto)
  apply (simp add:add_identity)
  done

lemma double_is_addition: "add x x = double x"
  apply (induction x)
   apply (auto)
  done

text "Exercise 2.3"

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count a Nil = 0" |
  "count a (Cons x xs) = (if x = a then add 1 (count a xs) else add 0 (count a xs))"

value "count a [b, c, a]"

lemma identical_elements_le: "count y xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

end