theory week08B_demo 
imports "~~/src/HOL/Hoare/HeapSyntax" 
begin


primrec
  fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
| "fac (Suc n) = (Suc n) * fac n"


lemma "VARS B { True } B := x { B = x }"
  apply vcg
  done
  
lemma 
  " VARS (x::nat) y r 
    {True} 
    IF x>y THEN r:=x ELSE r:=y FI
    {r \<ge> x \<and> r \<ge>y \<and> (r=x \<or> r=y)}"
  apply vcg
  apply simp
  done
  
lemma
  "VARS (A::int) B 
   { A = 0 \<and> B = 0 }
    WHILE A \<noteq> a
    INV { B = A * b } DO
      B := B + b; 
      A := A + 1
    OD
    {B = a * b }"
  apply vcg 
    apply simp
   apply clarsimp
   apply (simp add: semiring_normalization_rules(2))
  apply simp
  done
  
lemma factorial_sound:
  "VARS A B
  { A = n}
  B := 1;
  WHILE A \<noteq> 0 INV { fac n = B * fac A } DO
    B := B * A;
    A := A - 1
  OD
  { B = fac n }"
  apply (vcg; clarsimp)
  apply (case_tac A; simp)
  done



-- ----------------------------------------------------------------------------------

-- "Arrays"

(* define a program that looks for a key in an array *)
(*think about the loop invariant *)

lemma
 "VARS I L 
 { True }
  I := 0;
  WHILE I < length L \<and> L!I \<noteq> key 
  INV { I \<le> length L \<and> (\<forall>j < I. L!j \<noteq> key)} DO
    I := I+1 
  OD
  { (I < length L \<longrightarrow> L!I = key) \<and> (I=length L \<longrightarrow> key \<notin> set L)}"
  apply (vcg)
    apply clarsimp
   apply clarsimp
   apply (case_tac "I = j"; simp?)
   apply (metis linorder_neqE_nat not_less_eq)
  apply clarsimp
  apply (clarsimp simp: in_set_conv_nth)
  apply auto
  done


-- "Pointers"
thm List_def Path.simps

(* "List nxt p Ps" represents a linked list, starting
    at pointer p, with 'nxt' being the function to find
    the next pointer, and Ps the list of all the content
    of the linked list *)

(* define a function that takes X, p and nxt function,
   assuming that X is in the set of the linked list,
   then it returns the pointer to that element *)

(* think about its loop invariant *)


lemma "VARS nxt p
  { List nxt p Ps \<and> X \<in> set Ps }
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X  INV { \<exists>xs. Path nxt p xs (Ref X) }
  DO p := p^.nxt OD
  { p = Ref X }"
  apply vcg
    apply (clarsimp simp: List_def)
    apply (clarsimp simp: in_set_conv_decomp)
    apply auto
  done



(* define a function that "splices" 2 disjoint linked lists together *)

(* think about its loop invariant *)

lemma "VARS tl p q pp qq
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps}
  pp := p;
  WHILE q \<noteq> Null
  INV { TODO }
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  {List tl p (splice Ps Qs)}"
  sorry

end