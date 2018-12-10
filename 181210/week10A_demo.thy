theory week10A_demo
imports
  "autocorres-1.4/autocorres/AutoCorres"
  GCD
begin

text {*
  To run this demo you must have the AutoCorres tool.
  This demo was tested with the AutoCorres tarball from the COMP4161 website.

  You can download AutoCorres from 
  \url{http://www.cse.unsw.edu.au/~cs4161/autocorres-1.4.tar.gz}

  The following instructions assume you downloaded autocorres-1.4.tar.gz

  1. Unpack the .tar.gz file, which will create the directory autocorres-1.4
  
     tar -xzf autocorres-1.4.tar.gz

  2. To test that it builds with your Isabelle version, build the AutoCorres heap

     L4V_ARCH=X64 isabelle build -v -b -d autocorres-1.4 AutoCorres
OR:
     L4V_ARCH=ARM isabelle build -v -b -d autocorres-1.4 AutoCorres

     (depending whether you want 32-bit or 64-bit words)

  3. Load this demo theory using the AutoCorres heap

     L4V_ARCH=X64 isabelle jedit -d autocorres-1.4 -l AutoCorres week10A_demo.thy
OR:
     L4V_ARCH=ARM isabelle jedit -d autocorres-1.4 -l AutoCorres week10A_demo.thy

    (needs to be the same as the one used to build the heap in 2.)

  To parse the C file you need to have 'cpp' installed. On Linux you
  will probably already have gcc. On Mac OS, you may need to download
  the Command Line Tools. You can do this via Xcode if you have it installed.
  Or you can download standalone packages with command 
    xcode-select --install 
  in a terminal window.

  Make sure the demo C file simple.c is in the same directory as this .thy file
*}

text {*
  Parse in the C file; give each function a deeply embedded semantics in
  the SIMPL language.
*}
install_C_file "simple.c"

text {*
  Use AutoCorres to give each function a (monadic) shallow embedding that
  is designed to be more easily reasoned about.
  (The ts_force_nondet option below forces AutoCorres not to type strengthen
   the gcd function. Try removing it to see type strengthening in action.
   You might also like to experiment with forcing other levels of type
   strengthening for max by adding ts_force monad=max  where monad is
   one of pure, gets, option, nondet.)
*}
autocorres [unsigned_word_abs=gcd max except, ts_force nondet=gcd] "simple.c"
text {*
   Enter the environment in which all of the C parser and AutoCorres output is placed
*}
context simple begin

text {* 
  View the AutoCorres semantics of the max function
*}
thm max'_def

text {*
  This is its original semantics in SIMPL
*}
thm max_body_def

text {*
  The state type of the monad that AutoCorres produces is called @{typ lifted_globals}.

  It is a record containing a set of heaps, one for each pointer 
  type used in the program. Ours uses only unsigned *, i.e. 32-bit word pointers.
*}
term heap_w32
term heap_w32_update

text {*
  This is the AutoCorres semantics of the func function. Observe that it
  is very similar to the hand-written example from the last lecture.
*}
thm func'_def

text {*
  The automated tactic "wp" does automatic rule application of the monadic
  weakest precondition style rules we saw last lecture.
*}
lemma func'_partial_wp: 
  "\<lbrace>\<lambda>s. heap_w32 s p \<ge> 10 \<and> Q () s\<rbrace> func' p \<lbrace>Q\<rbrace>"
  apply(unfold func'_def)
  apply(rule hoare_weaken_pre)
   apply wp
  apply auto
  done

text {*
  AutoCorres gives the gcd function a semantics in the nondeterministic
  state monad with failure (from last lecture). Observe that the guard to
  check for the absence of division by zero in the SIMPL is absent from the
  state monad version, because AutoCorres can prove it isn't needed due to the
  loop condition.
*}
thm gcd'_def gcd_body_def

text {*
  AutoCorres also proves that its (monadic) abstractions of each function
  correspond to their semantics in SIMPL. In this sense AutoCorres is a
  self-certifying tool, and doesn't need to be trusted.
*}
thm gcd'_ac_corres max'_ac_corres func'_ac_corres

lemma gcd'_correct:
  "\<lbrace>\<lambda>_. True\<rbrace> gcd' a b \<lbrace>\<lambda>r s. r = gcd a b\<rbrace>"
  apply(unfold gcd'_def)
  apply(rule hoare_weaken_pre)
   apply wp
   apply(rule whileLoop_wp[where I="\<lambda>(x,y) _. gcd x y = gcd a b"])
    apply clarsimp
    apply wp
    apply clarsimp (*sledgehammer*)
    apply (metis gcd.commute gcd_red_nat)
   apply clarsimp (*sledgehammer*)
  using gr_zeroI apply fastforce
   apply clarsimp
  done

lemma gcd'_correct2:
  "\<lbrace>\<lambda>_. True\<rbrace> gcd' a b \<lbrace>\<lambda>r s. r = gcd a b\<rbrace>"
  apply (unfold gcd'_def)
  apply (rule hoare_weaken_pre)
  (*sledgehammer*)
   apply (metis (no_types, lifting) hoare_chain simple.gcd'_correct simple.gcd'_def)
  apply simp
  done

text {*
  AutoCorres loops can be annotated with invariants which will be used by
  the wp ruleset when doing automated proofs. You annotate a rule by
  using the @{thm whileLoop_add_inv} substitution rule.
*}
lemma gcd'_le:
  "\<lbrace>\<lambda>_. True\<rbrace> gcd' a b \<lbrace>\<lambda>r s. r \<le> max a b\<rbrace>"
  apply(unfold gcd'_def)
  apply(subst whileLoop_add_inv[where I="\<lambda>(x,y) _. max x y \<le> max a b"])
  apply wp 
    apply clarsimp
    using dual_order.trans mod_le_divisor apply blast
   apply clarsimp
  apply clarsimp
  done





thm unlessE_def
text {*
  A helper lemma about @{term unlessE}.
*}
lemma validE_unlessE[wp]:
  "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. if P then Q () s else P' s\<rbrace> unlessE P f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  apply(clarsimp simp: unlessE_def)
  apply wp
  done


text {*
  wp tends to handle most reasoning about exceptions over AutoCorres output
*}
lemma except'_result:
  "\<lbrace>\<lambda>_. True\<rbrace> except' u \<lbrace>\<lambda>r _. r \<ge> 6 \<and> r \<le> 8\<rbrace>"
  apply(unfold except'_def)
  apply(subst whileLoopE_add_inv[where I="\<lambda>(ret, u) _. u < 9"])
  apply wp
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply wp
  done


text {*
  Some more helper lemmas.
*}
lemma no_fail_returnOk [simp]:
  "no_fail P (returnOk v)"
  apply(auto simp: no_fail_def)
  done

lemma validNF_unlessE[wp]:
  "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>! \<Longrightarrow>
   \<lbrace>\<lambda>s. if P then Q () s else P' s\<rbrace> unlessE P f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>!"
  apply(clarsimp simp: validE_NF_def unlessE_def | wp )+
  done
thm valid_def validNF_def no_fail_def

text {*
  This lemma proves additionally that the @{term except'} function never
  fails --- i.e. it proves \emph{total correctness}, and guarantees the
  side-conditions on the soundness of the AutoCorres-produced abstraction of
  the C code.
*}
lemma except'_result_nf:
  "\<lbrace>\<lambda>_. True\<rbrace> except' u \<lbrace>\<lambda>r _. r \<ge> 6 \<and> r \<le> 8\<rbrace>!"
  apply(unfold except'_def)
  apply(subst whileLoopE_add_inv[where I="\<lambda>(ret,u) _. u \<le> 8" and M="\<lambda>((ret,u),_). (9::nat) - u"])
  apply (wp | clarsimp)+
    apply(simp add: UINT_MAX_def, arith)
   apply clarsimp
  apply wp
  apply clarsimp
  done

end (* context simple *)

end