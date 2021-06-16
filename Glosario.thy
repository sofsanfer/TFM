(*<*) 
theory Glosario
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*)

(* chapter \<open>Glosario de reglas\<close> *)

text \<open>\comentario{Modificar las páginas donde se encuentran.}
  
  \comentario{Añadir las nuevas reglas usadas.}

  \comentario{Modificar y unificar secciones.}\<close>

text \<open>En este glosario se recoge la lista de los lemas y reglas usadas
  indicando la página del \href{https://acortar.link/BytjC}{libro de HOL} 
  donde se encuentran.\<close>

section \<open>La base de lógica de primer orden (1)\<close>

text \<open>En Isabelle corresponde a la teoría 
  \href{https://acortar.link/qTQCQ}{HOL.thy}\<close>

text \<open>
  \begin{itemize}
    \item (p.35) @{thm[mode=Rule] impI[no_vars]} 
      \hfill (@{text impI})
    \item (p.35) @{thm[mode=Rule] mp[no_vars]} 
      \hfill (@{text mp})
    \item (p.35) @{thm[mode=Rule] Let_def[no_vars]} 
      \hfill (@{text Let_def})
    \item (p.36) @{thm[mode=Rule] forw_subst[no_vars]} 
      \hfill (@{text forw_subst})
    \item (p.36) @{thm[mode=Rule] back_subst[no_vars]} 
      \hfill (@{text back_subst})
    \item (p.36) @{thm[mode=Rule] iffD1[no_vars]} 
      \hfill (@{text iffD1})
    \item (p.37) @{thm[mode=Rule] allE[no_vars]} 
      \hfill (@{text allE})
    \item (p.38) @{thm[mode=Rule] notE[no_vars]} 
      \hfill (@{text notE})
    \item (p.38) @{thm[mode=Rule] contrapos_nn[no_vars]} 
      \hfill (@{text contrapos_nn})
    \item (p.39) @{thm[mode=Rule] disjE[no_vars]} 
      \hfill (@{text disjE})
    \item (p.39) @{thm[mode=Rule] iffI[no_vars]} 
      \hfill (@{text iffI})
    \item (p.40) @{thm[mode=Rule] allI[no_vars]} 
      \hfill (@{text allI})
    \item (p.40) @{thm[mode=Rule] exI[no_vars]} 
      \hfill (@{text exI})
    \item (p.40) @{thm[mode=Rule] exE[no_vars]} 
      \hfill (@{text exE})
    \item (p.40) @{thm[mode=Rule] conjI[no_vars]} 
      \hfill (@{text conjI})
    \item (p.40) @{thm[mode=Rule] conjunct1[no_vars]} 
      \hfill (@{text conjunct1})
    \item (p.40) @{thm[mode=Rule] conjunct2[no_vars]} 
      \hfill (@{text conjunct2})
    \item (p.41) @{thm[mode=Rule] disjI1[no_vars]} 
      \hfill (@{text disjI1})
    \item (p.41) @{thm[mode=Rule] disjI2[no_vars]} 
      \hfill (@{text disjI2})
    \item (p.41) @{thm[mode=Rule] ccontr[no_vars]} 
      \hfill (@{text ccontr})
    \item (p.41) @{thm[mode=Rule] notnotD[no_vars]} 
      \hfill (@{text notnotD})
    \item (p.49) @{thm[mode=Rule] simp_thms[no_vars]} 
      \hfill (@{text simp_thms})
    \item (p.49) @{thm[mode=Rule] not_not[no_vars]} 
      \hfill (@{text not_not})
    \item (p.50) @{thm[mode=Rule] disj_absorb[no_vars]} 
      \hfill (@{text disj_absorb})
    \item (p.50) @{thm[mode=Rule] conj_absorb[no_vars]} 
      \hfill (@{text conj_absorb})
    \item (p.50) @{thm[mode=Rule] conj_assoc[no_vars]} 
      \hfill (@{text conj_assoc})
    \item (p.50) @{thm[mode=Rule] disj_assoc[no_vars]} 
      \hfill (@{text disj_assoc})
    \item (p.51) @{thm[mode=Rule] de_Morgan_disj[no_vars]} 
      \hfill (@{text de_Morgan_disj})
    \item (p.51) @{thm[mode=Rule] de_Morgan_conj[no_vars]} 
      \hfill (@{text de_Morgan_conj})
    \item (p.51) @{thm[mode=Rule] not_imp[no_vars]} 
      \hfill (@{text not_imp})
    \item (p.51) @{thm[mode=Rule] disj_imp[no_vars]} 
      \hfill (@{text disj_imp})
    \item (p.52) @{thm[mode=Rule] if_True[no_vars]} 
      \hfill (@{text if_True})
    \item (p.52) @{thm[mode=Rule] if_False[no_vars]} 
      \hfill (@{text if_False})
  \end{itemize}\<close>

section \<open>Grupos, también combinados con órdenes (5)\<close>

text \<open>Los siguientes resultados pertenecen a la teoría de 
  grupos \href{https://bit.ly/3fwjIPe}{Groups.thy}.\<close>

section \<open>Retículos abstractos (6)\<close>

text \<open>Los resultados expuestos a continuación pertenecen a la teoría de 
  retículos \href{https://bit.ly/2N4lbjn}{Lattices.thy}.\<close>

section \<open>Teoría de conjuntos (6)\<close>

text \<open>Los siguientes resultados corresponden a la teoría de conjuntos 
  \href{https://acortar.link/adxMr}{Set.thy}.\<close>

text \<open>
  \begin{itemize}
    \item (p.158) @{thm[mode=Rule] mem_Collect_eq[no_vars]} 
      \hfill (@{text mem_Collect_eq})
    \item (p.159) @{thm[mode=Rule] CollectI[no_vars]} 
      \hfill (@{text CollectI})
    \item (p.159) @{thm[mode=Rule] CollectD[no_vars]} 
      \hfill (@{text CollectD})
    \item (p.165) @{thm[mode=Rule] ballI[no_vars]} 
      \hfill (@{text ballI})
    \item (p.165) @{thm[mode=Rule] bspec[no_vars]} 
      \hfill (@{text bspec})
    \item (p.165) @{thm[mode=Rule] bexI[no_vars]} 
      \hfill (@{text bexI})
    \item (p.166) @{thm[mode=Rule] bexE[no_vars]} 
      \hfill (@{text bexE})
    \item (p.167) @{thm[mode=Rule] subsetI[no_vars]} 
      \hfill (@{text subsetI})
    \item (p.167) @{thm[mode=Rule] rev_subsetD[no_vars]} 
      \hfill (@{text rev_subsetD})
    \item (p.167) @{thm[mode=Rule] subsetCE[no_vars]} 
      \hfill (@{text subsetCE})
    \item (p.167) @{thm[mode=Rule] contra_subsetD[no_vars]} 
      \hfill (@{text contra_subsetD})
    \item (p.167) @{thm[mode=Rule] subset_refl[no_vars]} 
      \hfill (@{text subset_refl})
    \item (p.168) @{thm[mode=Rule] subset_trans[no_vars]} 
      \hfill (@{text subset_trans})
    \item (p.168) @{thm[mode=Rule] equalityD2[no_vars]} 
      \hfill (@{text equalityD2})
    \item (p.169) @{thm[mode=Rule] empty_subsetI[no_vars]} 
      \hfill (@{text empty_subsetI})
    \item (p.169) @{thm[mode=Rule] UNIV_def[no_vars]} 
      \hfill (@{text UNIV_def})
    \item (p.169) @{thm[mode=Rule] UNIV_I[no_vars]} 
      \hfill (@{text UNIV_I})
    \item (p.169) @{thm[mode=Rule] bex_UNIV[no_vars]} 
      \hfill (@{text bex_UNIV})
    \item (p.171) @{thm[mode=Rule] Un_iff[no_vars]} 
      \hfill (@{text Un_iff})
    \item (p.171) @{thm[mode=Rule] UnI1[no_vars]} 
      \hfill (@{text UnI1})
    \item (p.171) @{thm[mode=Rule] UnI2[no_vars]} 
      \hfill (@{text UnI2})
    \item (p.172) @{thm[mode=Rule] Diff_iff[no_vars]} 
      \hfill (@{text Diff_iff})
    \item (p.172) @{thm[mode=Rule] insert_iff[no_vars]} 
      \hfill (@{text insert_iff})
    \item (p.172) @{thm[mode=Rule] insertI1[no_vars]} 
      \hfill (@{text insertI1})
    \item (p.173) @{thm[mode=Rule] singletonI[no_vars]} 
      \hfill (@{text singletonI})
    \item (p.174) @{thm[mode=Rule]singleton_conv[no_vars]} 
      \hfill (@{text singleton_conv})
    \item (p.175) @{thm[mode=Rule] imageI[no_vars]} 
      \hfill (@{text imageI})
    \item (p.175) @{thm[mode=Rule] image_Un[no_vars]} 
      \hfill (@{text image_Un})
    \item (p.176) @{thm[mode=Rule] image_empty[no_vars]} 
      \hfill (@{text image_empty})
    \item (p.176) @{thm[mode=Rule] image_insert[no_vars]} 
      \hfill (@{text image_insert})
    \item (p.176) @{thm[mode=Rule] image_Collect[no_vars]} 
      \hfill (@{text image_Collect})
    \item (p.178) @{thm[mode=Rule] psubset_eq[no_vars]} 
      \hfill (@{text psubset_eq})
    \item (p.179) @{thm[mode=Rule] psubset_imp_ex_mem[no_vars]} 
      \hfill (@{text psubset_imp_ex_mem})
    \item (p.179) @{thm[mode=Rule] subset_insertI[no_vars]} 
      \hfill (@{text subset_insertI})
    \item (p.179) @{thm[mode=Rule] subset_insertI2[no_vars]} 
      \hfill (@{text subset_insertI2})
    \item (p.179) @{thm[mode=Rule] Un_upper1[no_vars]} 
      \hfill (@{text Un_upper1})
    \item (p.179) @{thm[mode=Rule] Un_upper2[no_vars]} 
      \hfill (@{text Un_upper2})
    \item (p.179) @{thm[mode=Rule] Un_least[no_vars]} 
      \hfill (@{text Un_least})
    \item (p.180) @{thm[mode=Rule] Diff_subset_conv[no_vars]} 
      \hfill (@{text Diff_subset_conv})
    \item (p.180) @{thm[mode=Rule] Collect_const[no_vars]} 
      \hfill (@{text Collect_const})
    \item (p.180) @{thm[mode=Rule] Collect_disj_eq[no_vars]} 
      \hfill (@{text Collect_disj_eq})
    \item (p.181) @{thm[mode=Rule] insert_is_Un[no_vars]} 
      \hfill (@{text insert_is_Un})
    \item (p.181) @{thm[mode=Rule] insert_absorb[no_vars]} 
      \hfill (@{text insert_absorb})
    \item (p.181) @{thm[mode=Rule] insert_absorb2[no_vars]} 
      \hfill (@{text insert_absorb2})
    \item (p.181) @{thm[mode=Rule] insert_commute[no_vars]} 
      \hfill (@{text insert_commute})
    \item (p.181) @{thm[mode=Rule] insert_subset[no_vars]} 
      \hfill (@{text insert_subset})
    \item (p.183) @{thm[mode=Rule] Un_commute[no_vars]} 
      \hfill (@{text Un_commute})
    \item (p.183) @{thm[mode=Rule] Un_left_commute[no_vars]} 
      \hfill (@{text Un_left_commute})
    \item (p.183) @{thm[mode=Rule] Un_assoc[no_vars]} 
      \hfill (@{text Un_assoc})
    \item (p.184) @{thm[mode=Rule] Un_subset_iff[no_vars]} 
      \hfill (@{text Un_subset_iff})
    \item (p.187) @{thm[mode=Rule] insert_Diff_single[no_vars]} 
      \hfill (@{text insert_Diff_single})
    \item (p.187) @{thm[mode=Rule] insert_Diff[no_vars]} 
      \hfill (@{text insert_Diff})
    \item (p.187) @{thm[mode=Rule] Un_Diff_cancel[no_vars]} 
      \hfill (@{text Un_Diff_cancel})
    \item (p.189) @{thm[mode=Rule] bex_simps[no_vars]} 
      \hfill (@{text bex_simps})
    \item (p.190) @{thm[mode=Rule] insert_mono[no_vars]} 
      \hfill (@{text insert_mono})
    \item (p.190) @{thm[mode=Rule] in_mono[no_vars]} 
      \hfill (@{text in_mono})
    \item (p.197) @{thm[mode=Rule] set_mp[no_vars]} 
      \hfill (@{text set_mp})
  \end{itemize}\<close>

section \<open>Nociones sobre funciones (9)\<close>

text \<open>En Isabelle, la teoría de funciones se corresponde con 
  \href{https://bit.ly/2VBe1Im}{Fun.thy}.\<close>


section \<open>Retículos completos (10)\<close>

text \<open>En Isabelle corresponde a la teoría 
  \href{https://bit.ly/2Y5wxKA}{Complete-Lattices.thy}.\<close>

section \<open>Conjuntos finitos (18)\<close>

text \<open>A continuación se muestran resultados relativos a la teoría 
  \href{https://bit.ly/3bEIScG}{Finite-Set.thy}.\<close>

text \<open>
  \begin{itemize}
    \item (p.419) @{thm[mode=Rule] finite[no_vars]} 
      \hfill (@{text finite})
  \end{itemize}\<close>

text\<open>  
  \begin{itemize}
    \item (p.423) @{thm[mode=Rule] finite_insert[no_vars]} 
      \hfill (@{text finite_insert})
  \end{itemize}\<close>

section \<open>Composición de functores (33)\<close>

text \<open>En esta sección se muestran resultados pertenecientes a la
  teoría de composición de functores naturales acotados de Isabelle 
  \href{https://bit.ly/2zGl9v6}{BNFComposition.thy}.\<close>


(*<*)
end
(*>*) 
