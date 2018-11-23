theory three
  imports Main
begin


text "the leaf of the tree is just referred to as Tip; acts like Nil in nat and list"
text "All nodes that are not a leaf are defined a structure of two subtrees and the element itself"
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma double_mirror: "mirror (mirror t) = t"
  apply (induction t)
   apply (auto)
  done

fun is_element :: "'a tree \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_element Tip x = False" |
  "is_element (Node l a r) x = (if a = x then True else (is_element l x \<or> is_element r x))"

definition sq :: "nat \<Rightarrow> nat" where
  "sq n = n * n"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev Nil ys = ys" |
  "itrev (Cons x xs) ys = itrev xs (Cons x ys)"

lemma equiv_rev: "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply (auto)
  done

end