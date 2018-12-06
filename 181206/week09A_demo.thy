theory week09A_demo
imports "~~/src/HOL/Hoare/HeapSyntax" 
begin


lemma
  "VARS (A::int) B 
   { a \<ge> 0 \<and> b \<ge> 0 }
    A:=0;
    B:=0;
    WHILE A \<noteq> a
    INV { B = A * b } DO
      B := B + b; 
      A := A + 1
    OD
    {B = a * b }"
  (*TODO*)
  apply vcg
    apply auto
  apply (simp add: semiring_normalization_rules(2))
  done


lemma
  "VARS (A::int) B 
   { a \<ge> 0 \<and> b \<ge> 0 }
    A:=0;
    B:=0;
    WHILE A < a
    INV { B = A * b \<and> A \<le> a } DO
      B := B + b; 
      A := A + 1
    OD
    {B = a * b }"
  (* TODO *)
  apply vcg
    apply auto
  apply (simp add:semiring_normalization_rules(2))
  done
  

lemma
  "VARS (A::nat) (B::int) 
   { b \<ge> 0 }
    A:=a;
    B:=1;
    WHILE A \<noteq> 0
    INV { B = (b^(a-A)) \<and> A \<le> a } DO
      B := B * b; 
      A := A - 1
    OD
    {B = (b^a) }"
  (* TODO *)
  apply vcg
    apply auto
  apply (simp add: Suc_diff_le)
  done


lemma
  "VARS (X::int list) (Y::int list)
   { True }
    X:=x;
    Y:=[];
    WHILE X \<noteq> []
    INV { (rev X)@Y = rev x } DO
      Y := (hd X # Y);
      X := tl X
    OD
    {Y = rev x }"
  (* TODO *)
  apply vcg
    apply simp
   apply (metis (no_types, lifting) append.left_neutral append_eq_append_conv2 list.collapse rev.simps(2) rev_append rev_rev_ident)
  apply (erule conjE)
  apply simp
  done


lemma
  "VARS (A::int) (B::nat) (C::int)
   { a \<ge> 0 }
    A:=a;
    B:=b;
    C:=1;
    WHILE B \<noteq> 0
    INV { a^b = C*A^B} DO
      WHILE ((B mod 2) = 0) 
      INV {a^b = C*A^B} DO
        A:=A*A;
        B:=B div 2
      OD;
      C := C * A; 
      B := B - 1
    OD
    {C = (a^b) }"
  (* TODO *)
  apply vcg
      apply simp
     apply simp
    apply (metis (no_types, lifting) mod_eq_0_iff nonzero_mult_div_cancel_left power2_eq_square power_mult zero_not_eq_two)
   apply (metis Divides.mod_less mult.assoc power_eq_if zero_less_numeral)
  apply simp
  done




-- "Pointers"
thm List_def Path.simps

(* "List nxt p Ps" represents a linked list, starting
    at pointer p, with 'nxt' being the function to find
    the next pointer, and Ps the list of all the content
    of the linked list *)

(* define a function that takes X, p and nxt function,
   assuming that X in the set of the linked list,
   then it returns the pointer to that element *)

(* think about its loop invariant *)

lemma
 "VARS nxt p
  { List nxt p Ps \<and> X \<in> set Ps }
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV { \<exists>Ps. List nxt p Ps \<and> X \<in> set Ps }
  DO p := p^.nxt OD
  { p = Ref X }"
  (* TODO *)
  apply vcg
    apply auto
  done

lemma
 "VARS nxt p
  { List nxt p Ps \<and> X \<in> set Ps }
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV { \<exists>Ps. Path nxt p Ps (Ref X) }
  DO p := p^.nxt OD
  {  p = Ref X }"
  (* TODO *)
  apply vcg
    apply auto
  apply (metis List_app List_def Path.simps(2) split_list_first)
  done



(* define a function that "splices" 2 disjoint linked lists together *)

(* think about its loop invariant *)

lemma "VARS tl p q pp qq
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps}
  pp := p;
  WHILE q \<noteq> Null
  INV {\<exists>as bs qs.
    distinct as \<and> Path tl p as pp \<and> List tl pp bs \<and> List tl q qs \<and>
    set bs \<inter> set qs = {} \<and> set as \<inter> (set bs \<union> set qs) = {} \<and>
    size qs \<le> size bs \<and> splice Ps Qs = as @ splice bs qs}
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  {List tl p (splice Ps Qs)}"
  (* todo*)
  apply vcg
    apply (metis Path.simps(1) append.simps(1) card.empty card_distinct inf_bot_left list.set(1) list.size(3))
  apply clarsimp+
  sorry


end