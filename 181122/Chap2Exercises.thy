theory Chap2Exercises
  imports Main 
begin

declare [[names_short]]

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

lemma add_swap: "add x 0 = add 0 x"
  apply (induction x)
   apply (auto)
  done

lemma add_commutative: "add y x = add x y"
  apply (induction x)
   apply (auto)
  apply (simp add:add_swap)
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

text "Exercise 2.4"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil y = [y]" |
  "snoc (Cons x xs) y = Cons x (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil" |
  "reverse (Cons x xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = Cons x (reverse xs)"
  apply (induction xs)
   apply (auto)
  done

lemma reverse_reverse: "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto)
  done

text "Exercise 2.5"

fun sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0" |
  "sum (Suc n) = Suc n + sum n"

lemma simple_sum: "sum n = n * (n + 1) div 2"
  apply (induction n)
   apply (auto)
  done

text "Exercise 2.6"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = Nil" |
  "contents (Node l a r) = Cons a (append (contents l) (contents r))"

fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0" |
  "treesum (Node l a r) = a + treesum l + treesum r"

fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum Nil = 0" |
  "listsum (Cons x xs) = x + listsum xs"

lemma sum_of_two_lists [simp]: "listsum x + listsum y = listsum (append x y)"
  apply (induction x)
   apply (auto)
  done

lemma sum_is_same: "treesum t = listsum (contents t)"
  apply (induction t)
  apply (auto)
  done

text "Exercise 2.7"

datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Leaf a) = Leaf a" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Leaf a) = Cons a Nil" |
  "pre_order (Node l a r) = Cons a (append (pre_order l) (pre_order r))"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Leaf a) = Cons a Nil" |
  "post_order (Node l a r) = append (append (post_order l) (post_order r)) (Cons a Nil)"

lemma pre_reverse_post: "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply (auto)
  done

text "Exercise 2.8"

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a Nil = Nil" |
  "intersperse a (Cons b Nil) = Cons b Nil" |
  "intersperse a (Cons b xs) = Cons b (Cons a (intersperse a xs))"

value "intersperse a [b, c, d]"

lemma map: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply (auto)
  done

text "Exercise 2.9"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd n 0 = n" |
  "itadd n (Suc m) = itadd (Suc n) m"

lemma add_identity [simp]: "add n 0 = n"
  apply (induction n)
  apply (auto)
  done

lemma add_it_rec_equiv: "itadd n m = add n m"
  apply (induction m arbitrary: n)
   apply (auto)
  done

text "Exercise 2.10"

datatype tree0 = last | node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes last = 1" |
  "nodes (node n1 n2) = 1 + nodes n1 + nodes n2"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (node t t)"

theorem explosion_size: "nodes (explode n t) = 2 ^ n * nodes t + 2 ^ n - 1"
  apply (induction n arbitrary: t)
   apply (auto simp add:algebra_simps)
  done

text "Exercise 2.11"

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval (Var) x = x" |
  "eval (Const c) x = c" |
  "eval (Add a b) x = (eval a) x + (eval b) x" |
  "eval (Mult a b) x = (eval a) x * (eval b) x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp Nil x = 0" |
  "evalp (Cons a list) x = a + x * evalp list x"  

end