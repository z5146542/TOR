theory ShortestPathCounterExampleLEDA
  imports
  "ShortestPathLEDA"
begin

section 
  \<open> Proof that shortest path LEDA axioms are deficient for checking shortest path\<close>



(*
Stuck proving that if pred s = Some e then s \<in> U−.
*)

lemma (in basic_sp) s_in_Um:
  "pred s = Some e  \<Longrightarrow> s \<in> U_minus"
  unfolding U_minus_def s_in_verts
  oops

(*
The Us do not form a partition on vertices. 
Therefore we cannot infer Uf  \<union> U− = Vf  \<union> V−.

In fact, the LEDA conditions (axioms in our locale) 
are not sufficient for a correct checker. Below is 
a counter-example.
——————
Counterexample: 
Graph:  v —> s
c (v,s) = 1
pred s = (v,s) and    pred v = nil
dist s = 17    and    dist v = 17

P = {(v,s)}
U+ = {v}
Uf = U− = {}
——
(1) v is not reachable 
and is in U+
(2) All P-cycles \<dots>
vacuously true
(3) nothing in U- 
 vacuously true
(4) nothing in Uf
vacuously true
(5) nothing in Uf
vacuously true
——
Here the Us do not form a partition, yet all conditions are satisfied.

*)

abbreviation 
  ce_graph :: "(bool, bool \<times> bool) pre_digraph"
where
  "ce_graph \<equiv>
   \<lparr>verts = {False,True::bool}, 
    arcs = {(True, False)}, 
    tail = fst, 
    head = snd \<rparr>"

abbreviation 
  ce_source :: "bool"
where
  "ce_source \<equiv> False"

abbreviation 
  ce_cost :: "(bool \<times> bool) \<Rightarrow> real"
where
  "ce_cost \<equiv> \<lambda> x. 1"

abbreviation 
  ce_dist :: "bool \<Rightarrow> ereal"
where
  "ce_dist \<equiv> \<lambda> x. 17"

abbreviation 
  ce_pred :: "bool \<Rightarrow> (bool \<times> bool) option" 
where
  "ce_pred \<equiv> (\<lambda>x. if x then None else Some (True,False))"

interpretation ce_wf_digraph: 
   wf_digraph ce_graph  
  by unfold_locales simp_all 

interpretation ce_fin_digraph: 
   fin_digraph ce_graph 
  by unfold_locales simp_all 

interpretation ce_basic_sp: 
  basic_sp 
    ce_graph (*G*)
    ce_cost (*c*)
    ce_source (*s*)
    ce_dist (*dist*)
    ce_pred (*pred*)
  by unfold_locales simp_all 

interpretation ce_sp_plus: 
  sp_plus 
    ce_graph (*G*)
    ce_cost (*c*)
    ce_source (*s*)
    ce_dist (*dist*)
    ce_pred (*pred*)
  unfolding sp_plus_def sp_plus_axioms_def  
  apply (simp add: ce_basic_sp.basic_sp_axioms)
  unfolding ce_basic_sp.U_plus_def 
  by (subst ce_wf_digraph.reachable_conv') 
     (force simp: arcs_ends_def arc_to_ends_def 
            elim: converse_rtranclE)+

interpretation ce_sp_inf: 
  sp_inf
    ce_graph (*G*)
    ce_cost (*c*)
    ce_source (*s*)
    ce_dist (*dist*)
    ce_pred (*pred*)
  unfolding sp_inf_def sp_inf_axioms_def
  apply (clarsimp simp: ce_sp_plus.sp_plus_axioms)
  apply (rule conjI) 
   unfolding pre_digraph.cycle_def pre_digraph.awalk_def 
   apply clarsimp
   apply (smt  insertI1 insert_commute list.simps(15) 
              pre_digraph.simps(3) pre_digraph.simps(4) prod.sel(1) prod.sel(2) 
              singletonD subset_eq ce_wf_digraph.cas.elims)
  using ce_basic_sp.U_finite_def  
  apply simp
  done
   
interpretation counterexample: 
  sp_trian
    ce_graph (*G*)
    ce_cost (*c*)
    ce_source (*s*)
    ce_dist (*dist*)
    ce_pred (*pred*)
  unfolding sp_trian_def sp_trian_axioms_def  
  using ce_sp_inf.sp_inf_axioms 
  by simp

(* LEDA axioms: counter example  *)
interpretation counterexample: 
  sp_trian_just 
    ce_graph (*G*)
    ce_cost (*c*)
    ce_source (*s*)
    ce_dist (*dist*)
    ce_pred (*pred*)
  unfolding sp_trian_just_def sp_trian_just_axioms_def  
  using counterexample.sp_trian_axioms
  by (simp add: ce_basic_sp.U_finite_def)


lemma ce_mu_True: "ce_wf_digraph.\<mu> ce_cost ce_source True = \<infinity>"
  using ce_sp_plus.pred_some_mu by auto

lemma (in sp_trian_just) ce_dist_not_shortest_path:
  "\<exists>v. (v \<in> verts ce_graph \<and> 
        ce_dist v  \<noteq> ce_wf_digraph.\<mu> ce_cost ce_source v)"
  by (rule_tac x=True in exI) (simp add: ce_mu_True)
