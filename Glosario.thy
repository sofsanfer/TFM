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
  indicando la página del \href{https://bit.ly/2KvG2ej}{libro de HOL} 
  donde se encuentran.\<close>

section \<open>La base de lógica de primer orden (2)\<close>

text \<open>En Isabelle corresponde a la teoría 
  \href{https://bit.ly/3bGva9s}{HOL.thy}\<close>

text \<open>
  \begin{itemize}
    \item (p.36) @{thm[mode=Rule] impI[no_vars]} 
      \hfill (@{text impI})
    \item (p.36) @{thm[mode=Rule] mp[no_vars]} 
      \hfill (@{text mp})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.38) @{thm[mode=Rule] iffD1[no_vars]} 
      \hfill (@{text iffD1})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.38) @{thm[mode=Rule] allE[no_vars]} 
      \hfill (@{text allE})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.39) @{thm[mode=Rule] notE[no_vars]} 
      \hfill (@{text notE})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.40) @{thm[mode=Rule] disjE[no_vars]} 
      \hfill (@{text disjE})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.40) @{thm[mode=Rule] iffI[no_vars]} 
      \hfill (@{text iffI})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.41) @{thm[mode=Rule] allI[no_vars]} 
      \hfill (@{text allI})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.41) @{thm[mode=Rule] exI[no_vars]} 
      \hfill (@{text exI})
    \item (p.41) @{thm[mode=Rule] exE[no_vars]} 
      \hfill (@{text exE})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.41) @{thm[mode=Rule] conjI[no_vars]} 
      \hfill (@{text conjI})
    \item (p.41) @{thm[mode=Rule] conjunct1[no_vars]} 
      \hfill (@{text conjunct1})
    \item (p.41) @{thm[mode=Rule] conjunct2[no_vars]} 
      \hfill (@{text conjunct2})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.42) @{thm[mode=Rule] disjI1[no_vars]} 
      \hfill (@{text disjI1})
    \item (p.42) @{thm[mode=Rule] disjI2[no_vars]} 
      \hfill (@{text disjI2})
  \end{itemize}\<close>

section \<open>Grupos, también combinados con órdenes (5)\<close>

text \<open>Los siguientes resultados pertenecen a la teoría de 
  grupos \href{https://bit.ly/3fwjIPe}{Groups.thy}.\<close>

section \<open>Retículos abstractos (6)\<close>

text \<open>Los resultados expuestos a continuación pertenecen a la teoría de 
  retículos \href{https://bit.ly/2N4lbjn}{Lattices.thy}.\<close>

section \<open>Teoría de conjuntos para lógica de orden superior (7)\<close>

text \<open>Los siguientes resultados corresponden a la teoría de conjuntos 
  \href{https://bit.ly/3ePFv4B}{Set.thy}.\<close>

text \<open>
  \begin{itemize}
    \item (p.163) @{thm[mode=Rule] ballI[no_vars]} 
      \hfill (@{text ballI})
    \item (p.163) @{thm[mode=Rule] bspec[no_vars]} 
      \hfill (@{text bspec})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.165) @{thm[mode=Rule] rev_subsetD[no_vars]} 
      \hfill (@{text rev_subsetD})
    \item (p.166) @{thm[mode=Rule] subset_refl[no_vars]} 
      \hfill (@{text subset_refl})
    \item (p.166) @{thm[mode=Rule] subset_trans[no_vars]} 
      \hfill (@{text subset_trans})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.167) @{thm[mode=Rule] empty_subsetI[no_vars]} 
      \hfill (@{text empty_subsetI})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.169) @{thm[mode=Rule] Un_iff[no_vars]} 
      \hfill (@{text Un_iff})
    \item (p.169) @{thm[mode=Rule] UnI1[no_vars]} 
      \hfill (@{text UnI1})
    \item (p.170) @{thm[mode=Rule] UnI2[no_vars]} 
      \hfill (@{text UnI2})
  \end{itemize}\<close>

text\<open>
  \begin{itemize}
    \item (p.172) @{thm[mode=Rule] singletonI[no_vars]} 
      \hfill (@{text singletonI})
  \end{itemize}
\<close>

text\<open>
  \begin{itemize}
    \item (p.173) @{thm[mode=Rule] image_Un[no_vars]} 
      \hfill (@{text image_Un})
    \item (p.174) @{thm[mode=Rule] image_empty[no_vars]} 
      \hfill (@{text image_empty})
    \item (p.174) @{thm[mode=Rule] image_insert[no_vars]} 
      \hfill (@{text image_insert})
  \end{itemize}
\<close>

text \<open>
  \begin{itemize}
    \item (p.177) @{thm[mode=Rule] Un_upper1[no_vars]} 
      \hfill (@{text Un_upper1})
    \item (p.177) @{thm[mode=Rule] Un_upper2[no_vars]} 
      \hfill (@{text Un_upper2})
  \end{itemize}\<close>

text \<open>
  \begin{itemize}
    \item (p.179) @{thm[mode=Rule] insert_is_Un[no_vars]} 
      \hfill (@{text insert_is_Un})
    \item (p.187) @{thm[mode=Rule] bex_simps[no_vars]} 
      \hfill (@{text bex_simps})
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

section \<open>El tipo de datos de la listas finitas (66)\<close>

text \<open>En esta sección se muestran resultados sobre listas finitas 
  dentro de la teoría de listas de Isabelle 
  \href{https://bit.ly/3bCNxvX}{List.thy}.\<close>


(*<*)
end
(*>*) 
