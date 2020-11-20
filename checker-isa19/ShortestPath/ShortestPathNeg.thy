theory ShortestPathNeg

(*
  This theory uses the graph library and  
  several lemmas that were proven in the 
  shortest path theory
*)
imports ShortestPath

begin
section \<open>Shortest Path (with general edge costs)\<close>

locale shortest_paths_general_cost_source = 
  basic_just_sp_pred +
  assumes source_num: "num s = 0"
  assumes source_val: "(\<exists>v \<in> verts G. enum v \<noteq> \<infinity>) \<Longrightarrow> dist s = 0"
  (*can we prove this and just assume dist s \<noteq> \<infinity> like in old version? *)
  

lemma (in basic_sp) noPedge:                       
  "\<And>e. e\<in>arcs G \<Longrightarrow> 
    dist (tail G e) \<noteq> \<infinity> \<Longrightarrow> dist (head G e) \<noteq> \<infinity>"
  by (case_tac "dist (head G e)") (fastforce dest: trian)+
 
function (in shortest_paths_general_cost_source) pwalk :: "'a \<Rightarrow> 'b list" 
where
  "pwalk v = 
    (if (v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G)
      then [] 
      else pwalk (tail G (the (pred v))) @ [the (pred v)]
    )"
by auto 
termination (in shortest_paths_general_cost_source) 
  using just  
  by (relation "measure num", simp, fastforce)  

lemma (in shortest_paths_general_cost_source) pwalk_simps:
  "v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G \<Longrightarrow> pwalk v = []"
  "v \<noteq> s \<Longrightarrow> dist v \<noteq> \<infinity> \<Longrightarrow> v \<in> verts G \<Longrightarrow> 
    pwalk v = pwalk (tail G (the (pred v))) @ [the (pred v)]" 
by auto

definition (in shortest_paths_general_cost_source) pwalk_verts :: "'a  \<Rightarrow> 'a set" where 
  "pwalk_verts v = {u. u \<in> set (awalk_verts s (pwalk v))}" 

locale shortest_paths_general_cost =
  shortest_paths_general_cost_source +
  fixes C :: "('a \<times>('b awalk)) set"
  assumes no_edge_Vm_Vf: 
    "\<And>e. e \<in> arcs G \<Longrightarrow> dist (tail G e) = - \<infinity> \<Longrightarrow> 
         \<forall> r. dist (head G e) \<noteq> ereal r"
  assumes C_se: 
    "C \<subseteq> {(u, p). dist u \<noteq> \<infinity> \<and> awalk u p u \<and> awalk_cost c p < 0}"
  assumes int_neg_cyc: 
    "\<And>v. v \<in> verts G \<Longrightarrow> dist v = -\<infinity> \<Longrightarrow> 
      (fst ` C) \<inter> pwalk_verts v  \<noteq> {}"

lemma (in shortest_paths_general_cost_source) num_s_is_min:
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "dist v \<noteq> \<infinity>"
  shows "num v > 0"
     using just[OF assms] by fastforce

lemma (in shortest_paths_general_cost_source) path_from_root_Vr_ex:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "dist v \<noteq> \<infinity>"
  shows  "\<exists>e. s \<rightarrow>\<^sup>* tail G e \<and>
          e \<in> arcs G \<and> head G e = v \<and> dist (tail G e) \<noteq> \<infinity> \<and>
          pred v = Some e \<and> num v = num (tail G e) + 1"
using assms
proof(induct "num v - 1" arbitrary : v)
case 0
   obtain e where ee:
    "e \<in> arcs G" "v = head G e" "dist (tail G e) \<noteq> \<infinity>" 
    "pred v = Some e" "num v = num (tail G e) + 1"
    using just[OF 0(2-4)] `dist v \<noteq> \<infinity>`
    by force 
  have "tail G e = s" 
    using num_s_is_min[OF tail_in_verts [OF ee(1)] _ ee(3)] 
    ee(5) 0(1) by auto
  then show ?case using ee by auto
next
case (Suc n')
  then obtain e where ee:
    "e \<in> arcs G" "v = head G e" "dist (tail G e) \<noteq> \<infinity>" 
    "pred v = Some e" "num v = num (tail G e) + 1"
    using just[OF Suc(3-5)] by force 
  then have ss: "tail G e \<noteq> s"
    using num_s_is_min tail_in_verts
    Suc(2) source_num by force 
  have nst: "n' = num (tail G e) - 1"
    using ee(5) Suc(2) by presburger
  obtain e' where reach: "s \<rightarrow>\<^sup>* tail G e'" and
    e': "e' \<in> arcs G" "head G e' = tail G e" "dist (tail G e') \<noteq> \<infinity>"
    using Suc(1)[OF nst tail_in_verts[OF ee(1)] ss ee(3)] by blast
  then have "s \<rightarrow>\<^sup>* tail G e"
    by (metis arc_implies_awalk reachable_awalk reachable_trans)
  then show ?case using e' ee by auto
qed

lemma (in shortest_paths_general_cost_source) path_from_root_Vr:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "s \<rightarrow>\<^sup>* v"
proof(cases "v = s")
case True thus ?thesis using assms by simp
next
case False
  obtain e where "s \<rightarrow>\<^sup>* tail G e" "e \<in> arcs G" "head G e = v"
      using path_from_root_Vr_ex[OF assms(1) False assms(2)] by blast
  then have "s \<rightarrow>\<^sup>* tail G e" and "tail G e \<rightarrow> v"
    by (auto intro: in_arcs_imp_in_arcs_ends)
  then show ?thesis by (rule reachable_adj_trans)
qed

lemma (in shortest_paths_general_cost_source) \<mu>_V_less_inf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "\<mu> c s v \<noteq> \<infinity>"
  using assms path_from_root_Vr \<mu>_reach_conv by force

lemma (in shortest_paths_general_cost) num_not0:
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "enum v \<noteq> \<infinity>"
  shows "num v \<noteq> 0"
     using just[OF assms(1,2)] assms unfolding enum_def by fastforce 

lemma (in shortest_paths_general_cost) dist_Vf_\<mu>:
  fixes v :: 'a
  assumes vG: "v \<in> verts G"
  assumes "\<exists>r. dist v = ereal r"
  shows "dist v = \<mu> c s v"
proof -
  have ds: "dist s =  0" 
    using assms source_val unfolding enum_def by force
  have ews:"awalk s [] s" 
     unfolding awalk_def using s_in_G by simp
  have mu: "\<mu> c s s = ereal 0" 
    using min_cost_le_walk_cost[OF ews, where c=c] 
    awalk_cost_Nil ds  dist_le_\<mu>[OF s_in_G] zero_ereal_def
    by simp
  thus ?thesis 
    using ds assms dist_le_\<mu>[OF vG] 
    dist_ge_\<mu>[OF vG _ mu ds num_not0]      
    unfolding enum_def 
    by force 
qed

lemma (in shortest_paths_general_cost_source) pwalk_awalk:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "awalk s (pwalk v) v" 
proof (cases "v=s")
case True
  thus ?thesis 
    using assms pwalk.simps[where v=v] 
    awalk_Nil_iff by presburger 
next
case False
  from assms show ?thesis 
  proof (induct rule: pwalk.induct)
    fix v 
    let ?e = "the (pred v)"
    let ?u = "tail G ?e"
    assume ewu: "\<not> (v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G) \<Longrightarrow> 
                 ?u \<in> verts G \<Longrightarrow> dist ?u \<noteq> \<infinity> \<Longrightarrow> 
                 awalk s (pwalk ?u) ?u"
    assume vG: "v \<in> verts G" 
    assume dv: "dist v \<noteq> \<infinity>"
    thus "awalk s (pwalk v) v "
    proof (cases "v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G")
    case True
      thus ?thesis 
        using pwalk.simps vG dv 
        awalk_Nil_iff by fastforce
    next
    case False
      obtain e  where ee:
        "e \<in>arcs G" 
        "pred v = Some e" 
        "v = head G e" 
        "dist (tail G e) \<noteq> \<infinity>" 
        using just False by force
      hence "awalk s (pwalk ?u) ?u"
        using ewu[OF False] tail_in_verts by simp
      hence "awalk s (pwalk (tail G e) @ [e]) v"
        using ee(1-3) vG
        by (auto simp: awalk_simps simp del: pwalk.simps)
      also have "pwalk (tail G e) @ [e] = pwalk v"
        using False ee(2) unfolding pwalk.simps[where v=v] by auto
      finally show ?thesis .
    qed
  qed
qed

lemma (in shortest_paths_general_cost) \<mu>_ninf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v = - \<infinity>"
  shows "\<mu> c s v = - \<infinity>"
proof -
  have "awalk s (pwalk v) v"
    using pwalk_awalk assms by force
moreover
  obtain w where ww: "w \<in> fst ` C \<inter> pwalk_verts v"
    using int_neg_cyc[OF assms] by blast
  then obtain q where 
     "awalk w q w" 
     "awalk_cost c q < 0"
     using C_se by auto
moreover 
  have "w \<in> set (awalk_verts s (pwalk v))"
    using ww unfolding pwalk_verts_def by fast
ultimately
  show ?thesis using  neg_cycle_imp_inf_\<mu> by force
qed

lemma (in shortest_paths_general_cost) correct_shortest_path:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
proof(cases "dist v")
show " \<And>r. dist v = ereal r \<Longrightarrow> dist v = \<mu> c s v"
  using dist_Vf_\<mu>[OF assms] by simp 
next
show "dist v = \<infinity> \<Longrightarrow> dist v = \<mu> c s v"
  using \<mu>_V_less_inf[OF assms] 
  dist_le_\<mu>[OF assms] by simp
next
show "dist v = -\<infinity> \<Longrightarrow> dist v = \<mu> c s v"
  using \<mu>_ninf[OF assms] by simp
qed

end

