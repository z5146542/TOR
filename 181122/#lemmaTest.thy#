theory lemmaTest
  imports Main
begin

datatype boolean = True | False
fun conj :: "boolean \<Rightarrow> boolean \<Rightarrow> boolean" where
  "conj True True = True" |
  "conj _ _ = False"

fun disj :: "boolean \<Rightarrow> boolean \<Rightarrow> boolean" where
  "disj False False = False" |
  "disj _ _ = True"

value "disj True False"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"

lemma add_02: "add m 0 = m"
  apply (induction m)
  apply (auto)
  done

datatype 'a array = Nil | Cons 'a "'a array"

fun append :: "'a array \<Rightarrow> 'a array \<Rightarrow> 'a array" where 
  "append Nil ys = ys" |
  "append (Cons x xs) ys = Cons x (append xs ys)"

fun reverse :: "'a array \<Rightarrow> 'a array" where
  "reverse Nil = Nil" |
  "reverse (Cons x xs) = append (reverse xs) (Cons x Nil)"

value "reverse(Cons True (Cons False Nil))"

lemma append_Nil2 [simp]: "append xs Nil = xs"
  apply (induction xs)
  apply (auto)
  done

lemma append_association [simp]: "append (append xs ys) zs = append xs (append ys zs)"
  apply (induction xs)
  apply (auto)
  done

lemma reverse_append [simp]: "reverse(append xs ys) = append (reverse ys) (reverse xs)"
  apply (induction xs)
  apply (auto)
  done

lemma reverse_reverse [simp]: "reverse(reverse xs) = xs"
  apply (induction xs)
  apply (auto)
  done

value "1+(3::nat)"
value "1+(3::int)"
value "1-(3::nat)"
value "1-(3::int)"

end