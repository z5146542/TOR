theory WhileLoopRule
  imports week09B_demo_monad
begin
  
text {*
 While Loop rules follow
*}
  
  
subsection "Basic induction helper lemmas"
  
lemma whileLoop_results_induct_lemma1:
  "\<lbrakk> (a, b) \<in> whileLoop_results C B; b = Some (x, y) \<rbrakk> \<Longrightarrow> \<not> C x y"
  apply (induct rule: whileLoop_results.induct, auto)
  done
    
lemma whileLoop_results_induct_lemma1':
  "\<lbrakk> (a, b) \<in> whileLoop_results C B; a \<noteq> b \<rbrakk> \<Longrightarrow> \<exists>x. a = Some x \<and> C (fst x) (snd x)"
  apply (induct rule: whileLoop_results.induct, auto)
  done
    
lemma whileLoop_results_induct_lemma2 [consumes 1]:
  "\<lbrakk> (a, b) \<in> whileLoop_results C B;
     a = Some (x :: 'a \<times> 'b); b = Some y;
     P x; \<And>s t. \<lbrakk> P s; t \<in> fst (B (fst s) (snd s)); C (fst s) (snd s) \<rbrakk> \<Longrightarrow> P t \<rbrakk> \<Longrightarrow> P y"
  apply (induct arbitrary: x y rule: whileLoop_results.induct)
    apply simp
   apply simp
  apply fastforce
  done
    
lemma whileLoop_results_induct_lemma3 [consumes 1]:
  assumes result: "(Some (r, s), Some (r', s')) \<in> whileLoop_results C B"
    and inv_start: "I r s"
    and inv_step: "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' s'"
  shows "I r' s'"
  apply (rule whileLoop_results_induct_lemma2 [where P="case_prod I" and y="(r', s')" and x="(r, s)",
        simplified split_def, simplified])
      apply (rule result)
     apply simp
    apply simp
   apply fact
  apply (erule (1) inv_step)
  apply clarsimp
  done
    
lemma whileLoop_cond_fail:
  "\<lbrakk> \<not> C x s \<rbrakk> \<Longrightarrow> (whileLoop C B x s) = (return x s)"
  apply (auto simp: return_def whileLoop_def
             intro: whileLoop_results.intros whileLoop_terminates.intros
             elim!: whileLoop_results.cases)
  done
    
definition
  condition :: "('s \<Rightarrow> bool)
      \<Rightarrow> ('s, 'r) nondet_monad
      \<Rightarrow> ('s, 'r) nondet_monad
      \<Rightarrow> ('s, 'r) nondet_monad"
  where
    "condition P L R \<equiv> \<lambda>s. if (P s) then (L s) else (R s)"
    
notation (output)
  condition  ("(condition (_)//  (_)//  (_))" [1000,1000,1000] 1000)
  
lemma monad_state_eqI [intro]:
  "\<lbrakk> \<And>r t. (r, t) \<in> fst (A s) \<Longrightarrow> (r, t) \<in> fst (B s');
     \<And>r t. (r, t) \<in> fst (B s') \<Longrightarrow> (r, t) \<in> fst (A s);
     snd (A s) = snd (B s') \<rbrakk>
  \<Longrightarrow> (A :: ('s, 'a) nondet_monad) s = B s'"
  apply (fastforce intro!: set_eqI prod_eqI)
  done
    
lemma whileLoop_unroll:
  "(whileLoop C B r) =  ((condition (C r) (B r >>= (whileLoop C B)) (return r)))"
  (is "?LHS r = ?RHS r")
proof -
  have cond_fail: "\<And>r s. \<not> C r s \<Longrightarrow> ?LHS r s = ?RHS r s"
    apply (subst whileLoop_cond_fail, simp)
    apply (clarsimp simp: condition_def bind_def return_def)
    done
      
  have cond_pass: "\<And>r s. C r s \<Longrightarrow> whileLoop C B r s = (B r >>= (whileLoop C B)) s"
    apply (rule monad_state_eqI)
      apply (clarsimp simp: whileLoop_def bind_def split_def)
      apply (subst (asm) whileLoop_results_simps_valid)
      apply fastforce
     apply (clarsimp simp: whileLoop_def bind_def split_def)
     apply (subst whileLoop_results.simps)
     apply fastforce
    apply (clarsimp simp: whileLoop_def bind_def split_def)
    apply (subst whileLoop_results.simps)
    apply (subst whileLoop_terminates.simps)
    apply fastforce
    done
      
  show ?thesis
    apply (rule ext)
    apply (metis cond_fail cond_pass condition_def)
    done
qed
  
subsection "Inductive reasoning about whileLoop results"
  
lemma in_whileLoop_induct [consumes 1]:
  assumes in_whileLoop: "(r', s') \<in> fst (whileLoop C B r s)"
    and init_I: "\<And> r s. \<not> C r s \<Longrightarrow> I r s r s"
    and step:
    "\<And>r s r' s' r'' s''.
        \<lbrakk> C r s; (r', s') \<in> fst (B r s);
          (r'', s'') \<in> fst (whileLoop C B r' s');
           I r' s' r'' s'' \<rbrakk> \<Longrightarrow> I r s r'' s''"
  shows "I r s r' s'"
proof cases
  assume "C r s"
    
  {
    obtain a where a_def: "a = Some (r, s)"
      by blast
    obtain b where b_def: "b = Some (r', s')"
      by blast
        
    have "\<lbrakk> (a, b) \<in> whileLoop_results C B; \<exists>x. a = Some x;  \<exists>x. b = Some x \<rbrakk>
        \<Longrightarrow> I (fst (the a)) (snd (the a)) (fst (the b)) (snd (the b))"
      apply (induct rule: whileLoop_results.induct)
        apply (auto simp: init_I whileLoop_def intro: step)
      done
        
    hence "(Some (r, s), Some (r', s')) \<in> whileLoop_results C B
                 \<Longrightarrow> I r s r' s'"
      by (clarsimp simp: a_def b_def)
  }
    
  thus ?thesis
    using in_whileLoop
    by (clarsimp simp: whileLoop_def)
next
  assume "\<not> C r s"
    
  hence "r' = r \<and> s' = s"
    using in_whileLoop
    by (subst (asm) whileLoop_unroll,
        clarsimp simp: condition_def return_def)
      
  thus ?thesis
    by (metis init_I `\<not> C r s`)
qed
  
lemma snd_whileLoop_induct [consumes 1]:
  assumes induct: "snd (whileLoop C B r s)"
    and terminates: "\<not> whileLoop_terminates C B r s \<Longrightarrow> I r s"
    and init: "\<And> r s. \<lbrakk> snd (B r s); C r s \<rbrakk> \<Longrightarrow> I r s"
    and step: "\<And>r s r' s' r'' s''.
        \<lbrakk> C r s; (r', s') \<in> fst (B r s);
           snd (whileLoop C B r' s');
           I r' s' \<rbrakk> \<Longrightarrow> I r s"
  shows "I r s"
  apply (insert init induct)
  apply atomize
  apply (unfold whileLoop_def)
  apply clarsimp
  apply (erule disjE)
   apply (erule rev_mp)
   apply (induct "Some (r, s)" "None :: ('a \<times> 'b) option" arbitrary: r s rule: whileLoop_results.induct)
    apply clarsimp
   apply clarsimp
   apply (erule (1) step)
    apply (clarsimp simp: whileLoop_def)
   apply clarsimp
  apply (metis terminates)
  done
    
    
subsection "Direct reasoning about whileLoop components"
  
lemma fst_whileLoop_cond_false:
  assumes loop_result: "(r', s') \<in> fst (whileLoop C B r s)"
  shows "\<not> C r' s'"
  using loop_result
  by (rule in_whileLoop_induct, auto)
    
lemma use_valid: "\<lbrakk>(r, s') \<in> fst (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; P s \<rbrakk> \<Longrightarrow> Q r s'"
  apply (simp add: valid_def)
  apply blast
  done
    
lemma valid_whileLoop:
  assumes first_step: "\<And>s. P r s \<Longrightarrow> I r s"
    and inv_step: "\<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>"
    and final_step: "\<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s"
  shows "\<lbrace> P r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
proof -
  {
    fix r' s' s
    assume inv: "I r s"
    assume step: "(r', s') \<in> fst (whileLoop C B r s)"
      
    have "I r' s'"
      using step inv
      apply (induct rule: in_whileLoop_induct)
      apply simp
      apply (drule use_valid, rule inv_step, auto)
      done
  }
    
  thus ?thesis
    apply (clarsimp simp: valid_def)
    apply (drule first_step)
    apply (rule final_step, simp)
    apply (metis fst_whileLoop_cond_false)
    done
qed
  
lemma whileLoop_wp:
  "\<lbrakk> \<And>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>;
     \<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s \<rbrakk> \<Longrightarrow>
  \<lbrace> I r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
  by (rule valid_whileLoop)
    
    
end