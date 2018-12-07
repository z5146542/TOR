theory week09B_demo_monad
imports "~~/src/HOL/Library/Monad_Syntax"
begin

text {* The nondeterministic state monad with failure *}

type_synonym ('s,'a) nondet_monad = "'s \<Rightarrow> (('a \<times> 's) set \<times> bool)"

definition
  return :: "'a \<Rightarrow> ('s,'a) nondet_monad"
where
  "return x \<equiv> \<lambda>s. ({(x,s)},False)"

definition
  bind :: "('s,'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> ('s,'b) nondet_monad) \<Rightarrow> ('s,'b) nondet_monad"
where
  "bind a b \<equiv> \<lambda>s. ({(r'',s''). \<exists> (r',s') \<in> fst (a s). (r'',s'') \<in> fst (b r' s')},
                     snd (a s) \<or> (\<exists>(r', s') \<in> fst (a s). snd (b r' s')))" 

(* Use standard monad syntax for our new "bind" *)
adhoc_overloading
  Monad_Syntax.bind bind 

(* Always use do-notation *)
translations
  "CONST bind_do" == "CONST Monad_Syntax.bind"  

  
lemma
  "return x >>= f = f x"
  apply(unfold bind_def return_def)
  apply simp
  done

lemma
  "m >>= return = m"
  apply(rule ext)
  apply(simp add: bind_def return_def)
  apply(rule prod_eqI)
  apply auto
  done
 
lemma
  "(a >>= b) >>= c = (a >>= (\<lambda>s. b s >>= c) :: ('s,'a) nondet_monad)"
  apply(rule ext)
  apply(fastforce simp: bind_def split: prod.splits)
  done

definition
  get :: "('s,'s) nondet_monad"
where
  "get \<equiv> \<lambda>s. ({(s,s)},False)"

definition
  put :: "'s \<Rightarrow> ('s,unit) nondet_monad"
where
  "put s \<equiv> \<lambda>_. ({((),s)},False)"

definition
  gets :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s,'a) nondet_monad"
where
  "gets f \<equiv> get >>= (\<lambda>s. return (f s))"

definition
  modify :: "('s \<Rightarrow> 's) \<Rightarrow> ('s,unit) nondet_monad"
where
  "modify f \<equiv> get >>= (\<lambda>s. put (f s))"

definition
  fail :: "('s,'a) nondet_monad"
where
  "fail \<equiv> \<lambda>_. ({},True)"

definition
  assert :: "bool \<Rightarrow> ('s,unit) nondet_monad"
where
  "assert P \<equiv> if P then return () else fail"

definition
  guard :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,unit) nondet_monad"
where
  "guard P \<equiv> get >>= (\<lambda>s. assert (P s))"

definition
  select :: "'a set \<Rightarrow> ('s,'a) nondet_monad"
where
  "select A \<equiv> \<lambda>s. ((A \<times> {s}),False)"

definition 
  alternative :: "('s,'a) nondet_monad \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('s,'a) nondet_monad"
  (infixl "OR" 20)
where
  "alternative a b \<equiv> (\<lambda>s. (fst (a s) \<union> (fst (b s)),snd (a s) \<or> snd (b s)))"


  

text {* 
  We use an abstract type for pointers. 
  Later we talk more about how to faithfully model pointers.
*}
typedecl ptr

record state =
  hp :: "ptr \<Rightarrow> int"
  pvalid :: "ptr \<Rightarrow> bool"

definition
  func :: "ptr \<Rightarrow> (state,unit) nondet_monad"
where
  "func p \<equiv> do {
     y \<leftarrow> guard (\<lambda>s. pvalid s p);
     x \<leftarrow> gets (\<lambda>s. hp s p);
     if x < 10 then
       modify (hp_update (\<lambda>h. (h(p := x + 1))))
     else
       return ()
   }" 

  
  

inductive_set
  whileLoop_results :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) nondet_monad) \<Rightarrow> ((('r \<times> 's) option) \<times> (('r \<times> 's) option)) set"
  for C B
where
    "\<lbrakk> \<not> C r s \<rbrakk> \<Longrightarrow> (Some (r, s), Some (r, s)) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; snd (B r s) \<rbrakk> \<Longrightarrow> (Some (r, s), None) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (r', s') \<in> fst (B r s); (Some (r', s'), z) \<in> whileLoop_results C B  \<rbrakk>
       \<Longrightarrow> (Some (r, s), z) \<in> whileLoop_results C B"

inductive_cases whileLoop_results_cases_valid: "(Some x, Some y) \<in> whileLoop_results C B"
inductive_cases whileLoop_results_cases_fail: "(Some x, None) \<in> whileLoop_results C B"
inductive_simps whileLoop_results_simps: "(Some x, y) \<in> whileLoop_results C B"
inductive_simps whileLoop_results_simps_valid: "(Some x, Some y) \<in> whileLoop_results C B"
inductive_simps whileLoop_results_simps_start_fail [simp]: "(None, x) \<in> whileLoop_results C B"

inductive
  whileLoop_terminates :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) nondet_monad) \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
  for C B
where
    "\<not> C r s \<Longrightarrow> whileLoop_terminates C B r s"
  | "\<lbrakk> C r s; \<forall>(r', s') \<in> fst (B r s). whileLoop_terminates C B r' s' \<rbrakk>
        \<Longrightarrow> whileLoop_terminates C B r s"

inductive_cases whileLoop_terminates_cases: "whileLoop_terminates C B r s"
inductive_simps whileLoop_terminates_simps: "whileLoop_terminates C B r s"

definition
  "whileLoop C B \<equiv> (\<lambda>r s.
     ({(r',s'). (Some (r, s), Some (r', s')) \<in> whileLoop_results C B},
        (Some (r, s), None) \<in> whileLoop_results C B \<or> (\<not> whileLoop_terminates C B r s)))"

notation (output)
  whileLoop  ("(whileLoop (_)//  (_))" [1000, 1000] 1000)

consts 
  ptrAdd :: "ptr \<Rightarrow> nat \<Rightarrow> ptr"

term "whileLoop (\<lambda>p s. hp s p = 0) (\<lambda>p. return (ptrAdd p 1)) p"

definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> fst (f s). Q r s')"


lemma return_wp:
  "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>"
  by(simp add: valid_def return_def)

lemma get_wp:
  "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>"
  by(simp add: valid_def get_def)

lemma gets_wp:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>"
  apply(simp add:valid_def split_def gets_def return_def get_def bind_def)
  done

lemma modify_wp:
  "\<lbrace>\<lambda>s. P () (f s)\<rbrace> modify f \<lbrace>P\<rbrace>"
  apply(simp add:valid_def split_def modify_def get_def put_def bind_def)
  done

lemma put_wp:
  "\<lbrace>\<lambda>s. P () x\<rbrace> put x \<lbrace>P\<rbrace>"
  apply(simp add:valid_def put_def)
  done

lemma hoare_weaken_pre:
  "\<lbrakk>\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  apply(auto simp: valid_def)
  done
  
lemma fail_wp:  "\<lbrace>\<lambda>_. True\<rbrace> fail \<lbrace>Q\<rbrace>"
  apply(simp add: fail_def valid_def)
  done

lemma if_wp:
 "\<lbrakk> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>"
  by simp

(* do this proof using wp rules above *)
lemma assert_wp: "\<lbrace>\<lambda>s. P \<longrightarrow> Q () s\<rbrace> assert P \<lbrace>Q\<rbrace>"
  apply(unfold assert_def)
  apply (rule hoare_weaken_pre)
   apply (rule if_wp)
    apply (rule return_wp)
   apply (rule fail_wp)
  apply simp
  done
  
lemma bind_wp:
  "\<lbrakk> \<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>; \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do { x \<leftarrow> f; g x } \<lbrace>C\<rbrace>"
  apply(force simp: valid_def bind_def split: prod.splits)
  done

lemma select_wp: "\<lbrace>\<lambda>s. \<forall>x \<in> S. Q x s\<rbrace> select S \<lbrace>Q\<rbrace>"
  by (simp add: select_def valid_def)

lemma guard_wp:
  "\<lbrace>\<lambda>s. P s \<longrightarrow> Q () s\<rbrace> guard P \<lbrace>Q\<rbrace>"
  apply (unfold guard_def)
  apply (rule bind_wp)
   apply (rule assert_wp)
  apply (rule get_wp)
  done
  

lemma func_lemma:
  "\<lbrace>\<lambda>s. hp s p \<ge> 10 \<and> Q () s\<rbrace> func p \<lbrace>Q\<rbrace>"
  apply (unfold func_def)
  apply (rule bind_wp)+
    apply (rule if_wp)
     apply (rule modify_wp)
    apply (rule return_wp)
   apply (rule gets_wp)
  apply (rule hoare_weaken_pre)
   apply (rule guard_wp)
  apply simp
  done

end