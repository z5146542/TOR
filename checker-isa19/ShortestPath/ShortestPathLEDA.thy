theory ShortestPathLEDA
  imports
  "../Graph_Theory/Graph_Theory"
begin

section \<open>Shortest Path (with non-negative edge costs)\<close>
text\<open>The following theory is used in the verification of a certifying algorithm's checker for shortest path. For more information see \cite{FrameworkVerificationofCertifyingComputations}.\<close>

(* Formalism based on the LEDA book, Section 7.5.2 on Graph Algorithms *)
locale basic_sp = 
  fin_digraph +
  fixes c :: "'b \<Rightarrow> real"
  fixes s :: "'a"
  fixes dist :: "'a \<Rightarrow> ereal"
  fixes pred :: "'a \<Rightarrow> 'b option"
  assumes s_in_verts: "s \<in> verts G"

(* Let P = {pred[v] ; pred[v] \<noteq> nil} be the set of edges defined by the pred-array *)

(* differs from LEDA definition: (is this necessary?)
   limits set to edges (pred v) that are in G such that v is also in G *)
definition (in basic_sp) pred_edges :: "'b set" where 
 "pred_edges = { e\<in> arcs G. \<exists> v \<in> verts G.  pred v = Some e }"
               
lemma (in basic_sp) finite_pred_edge: 
  "finite pred_edges" 
  by (simp add: pred_edges_def)
(*
U+ = {v;v \<noteq> s \<and> pred[v]=nil},
U f = \<emptyset>, if pred[s]\<noteq> nil,
Uf = {v; v is reachable from s by a P-path}, if pred[s]=nil,
U− = {v ; v lies on a P-cycle or is reachable from a P-cycle by a P-path}.
*)

(* U+ differs from LEDA in that it adds that v is in G *)
definition (in basic_sp) U_plus :: "'a set" where
  "U_plus = {v \<in> verts G. v \<noteq> s \<and> pred v = None}"  

definition (in basic_sp) U_finite :: "'a set" where
  "U_finite = (if (pred s = None) then 
                  {v. \<exists> p. apath s p v \<and> set p \<subseteq> pred_edges} else {})"  

definition (in basic_sp) U_minus :: "'a set" where
  "U_minus = {v. \<exists> cyc. cycle cyc \<and> 
                  set cyc \<subseteq> pred_edges \<and>
                  (v\<in> set (awalk_verts v cyc) \<or> 
                    (\<exists>u p. u \<in> set (awalk_verts v cyc) \<and> 
                           apath u p v \<and> set p \<subseteq> pred_edges)) }"

(*
definition (in basic_sp) pred_edges :: "'b set" where 
 "pred_edges = { e. \<exists> v.  pred v = Some e }"
     

definition (in basic_sp) U_plus :: "'a set" where
  "U_plus = {v. v \<noteq> s \<and> pred v = None}"  

definition (in basic_sp) U_finite :: "'a set" where
  "U_finite = (if (pred s = None) then 
                  {v. \<exists> p. apath s p v \<and> set p \<subseteq> pred_edges} else {})"  

definition (in basic_sp) U_minus :: "'a set" where
  "U_minus = {v. \<exists> cyc. cycle cyc \<and> 
                  set cyc \<subseteq> pred_edges \<and>
                  (v\<in> set (awalk_verts v cyc) \<or> 
                    (\<exists>u p. u \<in> set (awalk_verts v cyc) \<and> 
                           apath u p v \<and> set p \<subseteq> pred_edges)) }"
*)

locale sp_plus =
  basic_sp +
(* (1) v\<in>U+ iff v is not reachable from s in G. *)
  assumes reach_plus:
    "\<And>v. (v \<in> U_plus) = (\<not> (s \<rightarrow>\<^sup>* v))"

locale sp_inf = 
  sp_plus +
(* (2) All P-cycles have negative cost.
   (3) There is no edge(v,w)\<in>E with v\<in>U− and w\<in>Uf.
*)
  assumes pred_cyc_neg:
  "\<And> cyc. \<lbrakk>cycle cyc; set cyc \<subseteq> pred_edges\<rbrakk> \<Longrightarrow>
             awalk_cost c cyc < 0"
  assumes no_pedge_Um_Uf: 
    "\<And>e. \<lbrakk>e \<in> arcs G; (tail G e)\<in> U_minus\<rbrakk> \<Longrightarrow> 
      (head G e)\<notin> U_finite"


locale sp_trian =
  sp_inf +
(*(4) Forall e=(v,w)\<in>E:ifv\<in>Uf and w\<in>Uf then dist[v]+c[e] \<ge> dist[w].*)
  assumes trian:
    "\<And>e. \<lbrakk>e \<in> arcs G; 
          head G e \<in> U_finite; 
          tail G e \<in> U_finite\<rbrakk> \<Longrightarrow>
      dist (head G e) \<le> dist (tail G e) + c e"

locale sp_trian_just = 
  sp_trian +
(* (5) For all v \<in> U f : 
   if v = s then dist[v] = 0 and 
   if v \<noteq> s 
   then dist[v] = dist[u] +
   c[pred[v]] where u is the source of pred[v].*)
(* deviating from LEDA definition 
   in just assumption: 
   adding through an edge in pred (pred v = Some e). *)
  assumes source_dist_0: 
        "s \<in> U_finite \<Longrightarrow> dist s = 0"
  assumes just:
    "\<And>v. \<lbrakk>v \<in> U_finite; v\<noteq> s\<rbrakk> \<Longrightarrow>
      \<exists> e \<in> arcs G. 
        pred v = Some e \<and> 
        v = head G e \<and>
        dist v = dist (tail G e) + c e"
  
lemma tail_value_helper:
  assumes "hd p = last p"
  assumes "distinct p"
  assumes "p \<noteq> []"
  shows "p = [hd p]"
  by (metis assms distinct.simps(2) list.sel(1) neq_Nil_conv last_ConsR last_in_set)

(*
   V− = {v\<in>V;\<mu>(v)=−\<infinity>},
   Vf = {v\<in>V;−\<infinity><\<mu>(v)<+\<infinity>},and 
   V+ = {v\<in>V;\<mu>(v)=+\<infinity>}.
*)

definition (in basic_sp) V_minus :: "'a set" where
  "V_minus = {v\<in>verts G. \<mu> c s v= -\<infinity> }"

definition (in basic_sp) V_finite :: "'a set" where
  "V_finite = {v\<in>verts G. \<exists>r. \<mu> c s v= ereal r }"

definition (in basic_sp) V_plus :: "'a set" where
  "V_plus = {v\<in>verts G. \<mu> c s v= \<infinity> }"

lemma (in basic_sp) V_partition: 
  "verts G = (V_minus \<union> V_finite \<union> V_plus) \<and>
   disjnt V_plus V_minus \<and>
   disjnt V_plus V_finite \<and>
   disjnt V_minus V_finite" 
  unfolding V_minus_def V_finite_def V_plus_def disjnt_def
  by (auto intro: real_of_ereal.cases) 

lemma (in basic_sp) Us_in_verts: 
  "U_minus \<union> U_finite \<union> U_plus \<subseteq> verts G"
proof (rule subsetI)
  fix v
  assume v_in_Us: "v \<in> U_minus \<union> U_finite \<union> U_plus"
  then have v_in_a_U: "v \<in> U_minus \<or> v \<in> U_finite \<or> v \<in> U_plus" by simp
  moreover 
  { 
    assume  "v \<in> U_minus" 
    then have "v \<in> verts G" 
      unfolding U_minus_def cycle_def awalk_def pred_edges_def apath_def
      by clarsimp (metis (no_types, hide_lams) awalk_verts_in_verts 
          awalk_verts_ne_eq awlast_in_verts awlast_if_cas)
  }
  moreover 
  { 
    assume  "v \<in> U_finite" 
    then have "v \<in> verts G" 
      unfolding U_finite_def 
      by (case_tac "pred s") (fastforce dest: awalkI_apath)+ 
  }
  ultimately show "v \<in> verts G" unfolding U_plus_def by blast
qed


lemma (in sp_plus) Up_Vp_eq:
  shows "U_plus = V_plus"
  using reach_plus \<mu>_reach_conv  shortest_path_inf 
  unfolding  V_plus_def U_plus_def by auto

lemma (in sp_plus) pred_some_mu:
  "\<lbrakk>v \<in> verts G; v \<noteq> s \<rbrakk> \<Longrightarrow> 
      (\<exists>e. pred v = Some e) = (\<mu> c s v < \<infinity>)"
  using reach_plus \<mu>_reach_conv U_plus_def 
  by (simp cong: Collect_cong) (metis not_Some_eq)

lemma (in fin_digraph) mu_le_zero: 
  "v \<in> verts G \<Longrightarrow> \<mu> f v v \<le> ereal 0" 
  by (metis awalk_cost_Nil zero_ereal_def awalk_Nil_iff min_cost_le_walk_cost)

lemma (in basic_sp) s_in_Uf:
  "pred s = None \<Longrightarrow> s \<in> U_finite"
  using apath_Nil_iff s_in_verts
  by (fastforce simp: U_finite_def)

context sp_trian_just
begin

thm U_finite_def
thm V_finite_def
thm just

function pwalk :: "'a \<Rightarrow> 'b list" 
where
  "pwalk v = 
    (if (v = s \<or> dist v = \<infinity> \<or>  v \<notin> verts G)
      then [] 
      else pwalk (tail G (the (pred v))) @ [the (pred v)]
    )" 
  by simp+
termination (in sp_trian_just) 
  using just  
  by (relation "measure num", simp, fastforce)  

fun 
  num :: "'a \<Rightarrow> nat"
  where 
  "num v = (if (v \<in> U_finite \<and> v \<noteq> s) then 
               
               {v. \<exists>p. apath s p v \<and> set p \<subseteq> pred_edges} else 0)"
end

lemma (in sp_trian_just) just_pred:
  "\<And>v. \<lbrakk>v \<in> U_finite; v \<noteq> s\<rbrakk> \<Longrightarrow>
    \<exists> (k :: 'a \<Rightarrow> nat). 
      \<exists> e \<in> arcs G. 
        v = head G e \<and>
        dist v = dist (tail G e) + c e  \<and>
        (c e = 0 \<longrightarrow> k (tail G e) < k v)" 
  apply (frule just; clarsimp)
  unfolding U_finite_def
  apply (case_tac "pred s"; clarsimp)
  apply (rule_tac x="\<lambda>v. if (c e = 0 \<and> v = head G e ) 
         then 1" in exI)
  apply (rule_tac x=e in bexI)
   apply simp
   apply (rule impI)

  oops
end
