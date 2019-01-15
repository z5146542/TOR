(* uses Isabelle2017 and autocorres version 1.0 *)
theory shortest_path_neg
  imports 
  "checker-verification/Library/Autocorres_Misc"
  "checker-verification/Witness_Property/Connected_Components"
begin
(* Parse the input file. *)

install_C_file "shortest_path_neg.c"

autocorres "shortest_path_neg.c"

context shortest_path_neg begin

subsection {* Definitions *}
(* non-negative cost *)
thm "is_wellformed_body_def"
thm "trian_body_def"
thm "just_body_def"
thm "no_path_body_def"
thm "pos_cost_body_def"
thm "check_basic_just_sp_body_def"
thm "check_sp_body_def"

thm "is_wellformed'_def"
thm "trian'_def"
thm "just'_def"
thm "no_path'_def"
thm "pos_cost'_def"
thm "check_basic_just_sp'_def"
thm "check_sp'_def"

(* general cost *)

thm "s_assums_body_def"
thm "parent_num_assms_body_def"
thm "no_p_edge_body_def"
thm "source_val_body_def"
thm "no_edge_Vm_Vf_body_def"
thm "awalk_body_def"
thm "awalk_cost_body_def"
thm "C_se_body_def"
thm "int_neg_cyc_body_def"
thm "shortest_paths_locale_step1_body_def"
thm "shortest_paths_locale_step2_body_def"
thm "shortest_paths_locale_step3_body_def"

thm "s_assums'_def"
thm "parent_num_assms'_def"
thm "no_p_edge'_def"
thm "source_val'_def"
thm "no_edge_Vm_Vf'_def"
thm "awalk'_def"
thm "awalk_cost'_def"
thm "C_se'_def"
thm "int_neg_cyc'_def"
thm "shortest_paths_locale_step1'_def"
thm "shortest_paths_locale_step2'_def"
thm "shortest_paths_locale_step3'_def"

subsection {* Implementations *}

(*Implementation Graph Types*)

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> 32 word"
type_synonym INum = "IVertex \<Rightarrow> 32 word"
type_synonym IDist = "IVertex \<Rightarrow> 32 word"
type_synonym IGraph = "32 word \<times> 32 word \<times> (IEdge_Id \<Rightarrow> IEdge)"

end

end