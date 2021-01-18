theory ShortestPathLEDAExt
  imports
  ShortestPathLEDA
begin

(*
  This extra condition is not in LEDA but it is needed.
  See  example in ShortestPathCounterExampleLEDA 

  (6) if pred s \<noteq> nil then s \<in> U− 
*)
locale sp_axioms = 
  sp_trian_just + 
  assumes s_in_Um:
  "pred s \<noteq> None \<Longrightarrow> s \<in> U_minus"

lemma (in sp_axioms) s_in_Um:
  "pred s = Some e  \<Longrightarrow> s \<in> U_minus"
  using s_in_Um 
  by simp 

lemma (in sp_axioms) Us_in_verts:
  "verts G \<subseteq> U_minus \<union> U_finite \<union> U_plus"
proof (rule subsetI)
  fix v
  assume vG: "v \<in> verts G"
  show  "v \<in> U_minus \<union> U_finite \<union> U_plus"
  proof (cases "v = s")
    case True
    then show ?thesis 
      by (case_tac "pred s"; simp add: s_in_Uf s_in_Um) 
  next
    case False
      then show ?thesis using vG
  qed 


  }
  then have v_in_a_U: "v \<in> U_minus \<or> v \<in> U_finite \<or> v \<in> U_plus" sorry
  moreover 
  { 
    assume  "v\<in>U_minus" 
    then have "v \<in> verts G" 
      unfolding U_minus_def cycle_def awalk_def pred_edges_def apath_def
      by clarsimp (metis (no_types, hide_lams) awalk_verts_in_verts 
          awalk_verts_ne_eq awlast_in_verts awlast_if_cas)
  }
  moreover 
  { 
    assume  "v\<in>U_finite" 
    then have "v \<in> verts G" 
      unfolding U_finite_def 
      by (case_tac "pred s") (fastforce dest: awalkI_apath)+ 
  }
  ultimately show "v\<in> verts G" unfolding U_plus_def by blast
qed
  proof (rule subsetI)
  apply (rename_tac v)
  apply (case_tac "v = s")
   apply  
  apply ()

  oops



lemma (in sp_plus) Umf_not_\<mu>_inf:
  "U_minus \<union> U_finite = {v \<in> verts G. \<mu> c s v < \<infinity>}"
  unfolding Un_def
  apply (subst Collect_cong[where Q="\<lambda>v. v \<in> verts G \<and> \<mu> c s v < \<infinity>"])
  prefer 2 
   apply simp 
  apply (rename_tac v)
  
  apply (case_tac "v = s")
   apply (subgoal_tac "(s \<in> U_minus \<or> s \<in> U_finite)") 
    apply simp
    using s_in_verts
    apply (fastforce dest: mu_le_zero[where v=s and f=c])
   apply (case_tac "pred s")
    apply (fastforce dest: s_in_Uf)
  apply (rule disjI1)
    oops

lemma (in sp_plus) Umf_Vmf_eq:
  "U_minus \<union> U_finite = V_minus \<union> V_finite" 
  unfolding V_minus_def V_finite_def
  apply (subst conjunct1[OF V_partition])+
  using reach_plus \<mu>_reach_conv  shortest_path_inf V_partition Up_Vp_eq Us_in_verts
  oops

  
lemma (in sp_plus) U_minus_U_finite_eq_V_minus_V_finite:
  fixes v :: 'a
  shows "(U_finite \<union> U_minus) = V_finite \<union> V_minus"
proof - 

  oops


(*
lemma (in basic_sp) dist_le_cost:
  fixes v :: 'a
  fixes p :: "'b list" 
  assumes "awalk s p v"
  shows "dist v \<le> awalk_cost c p"
  using assms
  proof (induct "length p" arbitrary: p v)
  case 0
    hence "s = v" by auto
    thus ?case using 0(1) general_source_val
      by (metis awalk_cost_Nil length_0_conv zero_ereal_def)
  next
  case (Suc n)
    then obtain p' e where p'e: "p = p' @ [e]"
      by (cases p rule: rev_cases) auto
    then obtain u where ewu: "awalk s p' u \<and> awalk u [e] v" 
      using awalk_append_iff Suc(3) by simp
    then have du: "dist u \<le> ereal (awalk_cost c p')"
      using Suc p'e by simp
    from ewu have ust: "u = tail G e" and vta: "v = head G e"
      by auto
    then have "dist v \<le> dist u + c e"
      using ewu du ust trian[where e=e] by force
    with du have "dist v \<le> ereal (awalk_cost c p') + c e"
      by (metis add_right_mono order_trans)
    thus "dist v \<le> awalk_cost c p" 
      using awalk_cost_append p'e by simp
  qed

lemma (in fin_digraph) witness_path:
  assumes "\<mu> c s v = ereal r"
  shows "\<exists> p. apath s p v \<and> \<mu> c s v = awalk_cost c p"
proof -
  have sv: "s \<rightarrow>\<^sup>* v" 
    using shortest_path_inf[of s v c] assms by fastforce
  { 
    fix p assume "awalk s p v"
    then have no_neg_cyc: 
    "\<not> (\<exists>w q. awalk w q w \<and> w \<in> set (awalk_verts s p) \<and> awalk_cost c q < 0)"
      using neg_cycle_imp_inf_\<mu> assms by force
  }
  thus ?thesis using no_neg_cyc_reach_imp_path[OF sv] by presburger
qed

lemma (in basic_sp) dist_le_\<mu>:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v \<le> \<mu> c s v" 
proof (rule ccontr)
  assume nt: "\<not> ?thesis"
  show False
  proof (cases "\<mu> c s v")
    show "\<And>r. \<mu> c s v = ereal r \<Longrightarrow> False"
    proof -
      fix r assume r_asm: "\<mu> c s v = ereal r"
      hence sv: "s \<rightarrow>\<^sup>* v"
        using shortest_path_inf[where u=s and v=v and f=c] by auto
      obtain p where 
        "awalk s p v" 
        "\<mu> c s v = awalk_cost c p"
        using witness_path[OF r_asm] unfolding apath_def by force 
      thus False using nt dist_le_cost by simp
    qed
  next
    show "\<mu> c s v = \<infinity> \<Longrightarrow> False" using nt by simp
  next
    show "\<mu> c s v = - \<infinity> \<Longrightarrow> False" using dist_le_cost
    proof -
      assume asm: "\<mu> c s v = - \<infinity>"
      let ?C = "(\<lambda>x. ereal (awalk_cost c x)) ` {p. awalk s p v}"
      have "\<exists>x\<in> ?C. x < dist v"
        using nt unfolding \<mu>_def not_le INF_less_iff by simp
      then obtain p where  
        "awalk s p v" 
        "awalk_cost c p < dist v" 
        by force
      thus False using dist_le_cost by force
    qed
  qed
qed

lemma (in basic_just_sp) dist_ge_\<mu>:
  fixes v :: 'a
  assumes "v \<in> verts G"
 (* assumes "enum v \<noteq> \<infinity>"*)
  assumes "v \<noteq> s"
  shows "dist v \<ge> \<mu> c s v"
proof -
  obtain n where "n = num v" using assms(2) by force
  thus ?thesis using assms
  proof(induct n arbitrary: v) 
    case 0 thus ?case 
    proof (cases "v=s")
      obtain e where e_assms:
        "e \<in> arcs G" 
        "v = head G e"
        "dist v = dist (tail G e) + ereal (c e)" 
        "num v = num (tail G e) + 1" 
        using just[OF Suc(3) False]Suc(4) enum_def by metis
  next
  case (Suc n)
    thus ?case 
    proof (cases "v=s") 
    case False
      obtain e where e_assms:
        "e \<in> arcs G" 
        "v = head G e"
        "dist v = dist (tail G e) + ereal (c e)" 
        "num v = num (tail G e) + 1" 
        using just[OF Suc(3) False]Suc(4) enum_def by metis
      then have nsinf:"enum (tail G e) \<noteq> \<infinity>" 
        using assms
        using Suc.prems(3) enum_def by auto
      then have ns:"n = num (tail G e)" 
        using e_assms(4) Suc(2) enum_def 
        by auto
      have  ds: "dist (tail G e) = \<mu> c s (tail G e)" 
        using Suc(1)[OF ns tail_in_verts[OF e_assms(1)] nsinf] 
        Suc(5-7) dist_le_\<mu>[OF tail_in_verts[OF e_assms(1)]]
        by simp
      have dmuc:"dist v \<ge> \<mu> c s (tail G e) + ereal (c e)"
        using e_assms(3) ds  by auto
      thus ?thesis
      proof (cases "dist v = \<infinity>")
      case False
        have "arc_to_ends G e = (tail G e, v)" 
          unfolding arc_to_ends_def
          by (simp add: e_assms(2))
        obtain r where  \<mu>r: "\<mu> c s (tail G e) = ereal r"
           using ds enum_def nsinf
           by (cases "\<mu> c s (tail G e)", auto)
        obtain p where 
          "awalk s p (tail G e)" and
          \<mu>s: "\<mu> c s (tail G e) = ereal (awalk_cost c p)"
          using witness_path[OF \<mu>r] unfolding apath_def 
          by blast
        then have pe: "awalk s (p @ [e]) v" 
          using e_assms(1,2) by (auto simp: awalk_simps)
        hence muc:"\<mu> c s v \<le> \<mu> c s (tail G e) + ereal (c e)" 
        using \<mu>s min_cost_le_walk_cost[OF pe] by simp 
        thus  "dist v \<ge> \<mu> c s v"  using dmuc by simp
      qed simp
    qed (simp add: Suc(6,7))
  qed
qed

lemma (in shortest_path_pos_cost) tail_value_check: 
  fixes u :: 'a
  assumes "s \<in> verts G"
  shows "\<mu> c s s = ereal 0"
proof -
  have *: "awalk s [] s" using assms unfolding awalk_def by simp
  hence "\<mu> c s s \<le> ereal 0" using min_cost_le_walk_cost[OF *] by simp
  moreover
  have "(\<And>p. awalk s p s \<Longrightarrow> ereal(awalk_cost c p) \<ge> ereal 0)"
   using pos_cost pos_cost_pos_awalk_cost by auto
  hence "\<mu> c s s \<ge> ereal 0" 
    unfolding \<mu>_def by (blast intro: INF_greatest)
  ultimately
  show ?thesis by simp
qed

lemma (in shortest_path_pos_cost) num_not0:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "enum v \<noteq> \<infinity>"
  shows "num v \<noteq> 0"
proof -
  obtain ku where "num v = ku + 1" 
    using assms just enum_def by metis
  thus ?thesis  by (induct ku) auto
qed

lemma (in shortest_path_pos_cost) dist_ne_ninf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v \<noteq> -\<infinity>"
proof (cases "enum v = \<infinity>")
case False 
  obtain n where "n = num v"
    using False by force
  thus ?thesis using assms False
  proof(induct n arbitrary: v) 
  case 0 thus ?case 
    using num_not0 tail_val  by (cases "v=s", auto) 
  next
  case (Suc n)
    thus ?case 
    proof (cases "v=s") 
    case True 
      thus ?thesis using tail_val by simp
    next
    case False
      obtain e where e_assms:
        "e \<in> arcs G"
        "dist v = dist (tail G e) + ereal (c e)" 
        "num v = num (tail G e) + 1" 
        using just[OF Suc(3) False] Suc(4) enum_def 
        by metis
      then have nsinf:"enum (tail G e) \<noteq> \<infinity>" 
        using Suc(4) enum_def 
        by auto
      then have ns:"n = num (tail G e)" 
        using e_assms(3) Suc(2) by force
      have "dist (tail G e ) \<noteq> - \<infinity>" 
        by (rule Suc(1) [OF ns tail_in_verts[OF e_assms(1)] nsinf])
      thus ?thesis using e_assms(2) by simp
    qed
  qed
next
case True 
  thus ?thesis using assms no_neg_dist by simp 
qed

theorem (in shortest_path_pos_cost) correct_shortest_path:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
  using  dist_le_\<mu>[OF assms(1)]
    dist_ge_\<mu>[OF assms(1) _ 
   tail_value_check[OF s_in_G] tail_val] 
   dist_ne_ninf[OF assms(1)] 
   num_not0 enum_def by fastforce

corollary (in shortest_path_pos_cost_pred) correct_shortest_path_pred:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
  using correct_shortest_path assms by simp
*)
