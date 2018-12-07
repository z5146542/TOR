theory week09B_demo_gcd
imports WhileLoopRule GCD
begin


definition gcd' :: "nat \<Rightarrow> nat \<Rightarrow> ('s,nat) nondet_monad" where
  "gcd' a b \<equiv>
   do {
     (a, b) \<leftarrow> whileLoop (\<lambda>(a, b) b. 0 < a)
                          (\<lambda>(a, b). return (b mod a, a))
                          (a, b);
      return b
   }"

lemma prod_case_valid:
  "\<lbrace>P\<rbrace> f (fst x) (snd x) \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> case x of (a,b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>"
  apply (auto split: prod.splits)
  done

lemma gcd'_correct: 
  "\<lbrace>\<lambda>_. True\<rbrace> gcd' a b \<lbrace>\<lambda>r s. r = gcd a b\<rbrace>"
  apply (unfold gcd'_def)
  thm whileLoop_wp
  apply (rule bind_wp)
  apply (rule prod_case_valid)
  apply (rule return_wp)
  apply (rule hoare_weaken_pre)
   apply (rule_tac I="\<lambda>(x,y) s. gcd x y = gcd a b " in whileLoop_wp)
    apply clarsimp
  apply (rule hoare_weaken_pre)
     apply (rule return_wp)
    apply clarsimp
    apply (metis gcd.commute gcd_red_nat)
   apply clarsimp
  apply clarsimp
  done

end