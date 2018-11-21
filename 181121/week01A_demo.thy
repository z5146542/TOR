(* A simple comment *)

theory week01A_demo imports Main
begin

text {* This is also a comment but it generates nice \LaTeX-text! *}

text {*
 Note that free variables (eg @{term x}), 
 bound variables (eg @{term "\<lambda>n. n"}) and
 constants (eg @{term Suc}) are displayed differently.
*}

text {* To display more types inside terms: *}
declare [[show_types]]
term "Suc x = Succ y"

text {* To switch off again: *}
declare [[show_types=false]]
term "Suc x = Succ y"


text {* 0 and + are overloaded: *}

prop "n + n = 0"
prop "(n::nat) + n = 0"
prop "(n::int) + n = 0"
prop "n + n = Suc m"

text{* A bound variable: *}
term "\<lambda>x. x v"
term "\<lambda>x. Suc x < y"
prop "map (\<lambda>n. Suc n + 1) [0, 1] = [2, 3]"


text {* Terms must be type correct! *}
text {* term "Suc n = True" *}


text {* Displaying theorems, schematic variables *}

thm conjI
text {* Schematic variables have question marks and can be instantiated: *}
thm conjI [where ?Q = "x"]
thm impI
thm disjE


text {*
  You can use \texttt{term}, \texttt{prop} and \texttt{thm} in \LaTeX
  sections, too!  The lemma conjI is: @{thm conjI}. Nicer version, 
  without schematic variables: @{thm conjI [no_vars]}.
*}

thm conjI [no_vars]

text {* Finding theorems *}

text {* Searching for constants/functions: *}
find_theorems "map"

text {* A list of search criteria finds thms that match all of them: *}
find_theorems "map" "zip"

text {* To search for patterns, use underscore: *}
find_theorems "_ + _ = _ - _"
find_theorems "_ + _" "_ < _" "Suc"

text {* Searching for theorem names: *}
find_theorems name: "conj"

text {* They can all be combined, theorem names include the theory name: *}
find_theorems "_ \<and> _" name: "HOL." -name: "conj"

text {* Stating theorems and a first proof *}

lemma "A \<longrightarrow> A"
  -- "a single line comment"
  -- "note the goals window" 
  apply (rule impI)  
  apply assumption
  done

text {* 
  A proof is a list of {\tt apply} statements, terminated by {\tt done}.

  {\tt apply} takes a proof method as argument (assumption, rule,
  etc.). It needs parentheses when the method consists of more than
  one word.  
*}


text {* Isabelle doesn't care if you call it lemma, theorem or corollary *}

theorem "A \<longrightarrow> A" 
  apply (rule impI)
  apply assumption
  done

corollary "A \<longrightarrow> A" 
  apply (rule impI)
  apply assumption
  done
  
text {* You can give it a name, too *}

lemma mylemma: "A \<longrightarrow> A" by (rule impI)


text {* Abandoning a proof *}

lemma "P = NP"
  -- "this is too hard"
  oops

text {* Isabelle forgets the lemma and you cannot use it later *}

text {* Faking a proof *}

lemma "P \<noteq> NP"
  -- "have an idea, will show this later"
  sorry

text {* 
  {\tt sorry} only works interactively (and in {\em quick-and-dirty-mode}), 
  and Isabelle keeps track of what you have faked.
*}


text {* Proof styles *}

-- "automatic"
theorem Cantor: "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)" by best

-- "exploring, but unstructured"
theorem Cantor': "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)" 
  apply (rule_tac x = "{x. x \<notin> f x}" in exI)
  apply (rule notI) 
  apply clarsimp
  apply blast
  done    

-- "structured, explaining"
theorem Cantor'': "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume yin: "y \<in> ?S"
      hence "y \<notin> f y" by simp
      hence "y \<notin> ?S"  by(simp add:fy)
      thus False using yin by contradiction
    next
      assume yout: "y \<notin> ?S"
      hence "y \<in> f y" by simp
      hence "y \<in> ?S"  by(simp add:fy)
      thus False using yout by contradiction
    qed
  qed
qed


end