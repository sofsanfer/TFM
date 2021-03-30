(*<*) 
theory Consistencia
  imports 
    Sintaxis
    Semantica
    Hintikka
begin
(*>*)

section\<open>Consistencia\<close>

subsection \<open>Condición de consistencia proposicional\<close>

text \<open>En esta sección probaremos la consistencia de la lógica proposicional
  demostrando el \<open>teorema de existencia de modelos\<close>. Para ello, definiremos 
  inicialmente una condición de consistencia proposicional para una colección 
  de conjuntos de fórmulas proposicionales. De este modo, cualquier conjunto de
  fórmulas proposicionales perteneciente a una colección que verifique dicha
  condición será satisfacible por el \<open>teorema de existencia de modelos\<close>.\<close>

text \<open>
  \begin{definicion}
    Sea \<open>C\<close> una colección de conjuntos de fórmulas proposicionales. Decimos que
    \<open>C\<close> verifica la \<open>condición de consistencia proposicional\<close> si, para todo
    conjunto \<open>S\<close> perteneciente a la colección, se verifica:
    \begin{enumerate}
      \item \<open>\<bottom> \<notin> S\<close>.
      \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
        simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
      \item Si \<open>F \<and> G \<in> S\<close>, entonces el conjunto \<open>{F,G} \<union> S\<close> pertenece a la colección.
      \item Si \<open>F \<or> G \<in> S\<close>, entonces o bien el conjunto \<open>{F} \<union> S\<close> pertenece a la
        colección, o bien el conjunto \<open>{G} \<union> S\<close> pertenece a la colección.
      \item Si \<open>F \<rightarrow> G \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> F} \<union> S\<close> pertenece a la
        colección, o bien el conjunto \<open>{G} \<union> S\<close> pertenece a la colección.
      \item Si \<open>\<not>(\<not> F) \<in> S\<close>, entonces el conjunto \<open>{F} \<union> S\<close> pertenece a la colección.
      \item Si \<open>\<not>(F \<and> G) \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> F} \<union> S\<close> pertenece a la
        colección, o bien el conjunto \<open>{\<not> G} \<union> S\<close> pertenece a la colección.
      \item Si \<open>\<not>(F \<or> G) \<in> S\<close>, entonces el conjunto \<open>{\<not> F, \<not> G} \<union> S\<close> pertenece a la 
        colección. 
      \item Si \<open>\<not>(F \<rightarrow> G) \<in> S\<close>, entonces el conjunto \<open>{F, \<not> G} \<union> S\<close> pertenece a la
        colección. 
    \end{enumerate}
  \end{definicion}

  Veamos, a continuación, su formalización en Isabelle mediante el tipo \<open>definition\<close>.\<close>

definition "pcp C \<equiv> (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> {F,G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> {F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> {\<^bold>\<not>F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> {F} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> {\<^bold>\<not> F} \<union> S \<in> C \<or> {\<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> {\<^bold>\<not> F, \<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> {F,\<^bold>\<not> G} \<union> S \<in> C))"

text \<open>Observando la definición anterior, se prueba fácilmente que la colección trivial
  formada por el conjunto vacío de fórmulas verifica la condición de consistencia 
  proposicional.\<close>

lemma "pcp {{}}"
  unfolding pcp_def by simp

text \<open>Del mismo modo, aplicando la definición, se demuestra que los siguientes ejemplos
  de colecciones de conjuntos de fórmulas proposicionales verifican igualmente la 
  condición.\<close>

lemma "pcp {{Atom 0}}"
  unfolding pcp_def by simp

lemma "pcp {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))},
  {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1)),  Atom 1}}" 
  unfolding pcp_def by auto

text \<open>En contraposición, podemos ilustrar un caso de colección que no verifique la 
  condición con la siguiente colección obtenida al modificar el último ejemplo. De
  esta manera, aunque la colección verifique correctamente la quinta condición de la
  definición, no cumplirá la sexta.\<close>

lemma "\<not> pcp {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))}}" 
  unfolding pcp_def by auto

text \<open>Seguidamente presentaremos dos lemas auxiliares derivados de la definición anterior
  que facilitarán las posteriores demostraciones realizadas en Isabelle/HOL. Estos dos 
  lemas indican que la verificación de la conjunción de las nueve condiciones de la 
  definición para cualquier conjunto perteneciente a la colección es una condición 
  necesaria y suficiente para que la colección verifique la condición de consistencia 
  proposicional.\<close>

lemma auxEq1:
  assumes "\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> {F,G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> {F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> {\<^bold>\<not>F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> {F} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> {\<^bold>\<not> F} \<union> S \<in> C \<or> {\<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> {\<^bold>\<not> F, \<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> {F,\<^bold>\<not> G} \<union> S \<in> C)"
  shows "pcp C"
proof -
  have "pcp C = (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> {F,G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> {F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> {\<^bold>\<not>F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> {F} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> {\<^bold>\<not> F} \<union> S \<in> C \<or> {\<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> {\<^bold>\<not> F, \<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> {F,\<^bold>\<not> G} \<union> S \<in> C))" 
    using pcp_def by (simp only: atomize_eq)
  thus "pcp C"
    using assms by (rule iffD2)
qed

lemma auxEq2:
  assumes "pcp C"
          "S \<in> C"
  shows "\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> {F,G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> {F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> {\<^bold>\<not>F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> {F} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> {\<^bold>\<not> F} \<union> S \<in> C \<or> {\<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> {\<^bold>\<not> F, \<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> {F,\<^bold>\<not> G} \<union> S \<in> C)"
proof -
  have "pcp C = (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> {F,G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> {F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> {\<^bold>\<not>F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> {F} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> {\<^bold>\<not> F} \<union> S \<in> C \<or> {\<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> {\<^bold>\<not> F, \<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> {F,\<^bold>\<not> G} \<union> S \<in> C))" 
    using pcp_def by (simp only: atomize_eq)
  then have "\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> {F,G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> {F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> {\<^bold>\<not>F} \<union> S \<in> C \<or> {G} \<union> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> {F} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> {\<^bold>\<not> F} \<union> S \<in> C \<or> {\<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> {\<^bold>\<not> F, \<^bold>\<not> G} \<union> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> {F,\<^bold>\<not> G} \<union> S \<in> C)"
    using assms(1) by (rule iffD1)
  thus ?thesis 
    using assms(2) by (rule bspec)
qed

subsection \<open>Notación uniforme: fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>\<close>

text \<open>En esta subsección vamos a introducir una notación uniforme inicialmente 
  desarrollada por \<open>R. M. Smullyan\<close> (añadir referencia bibliográfica). La finalidad
  de dicha notación es reducir el número de casos a considerar sobre la estructura de 
  las fórmulas al clasificar estas en dos categorías, facilitando las demostraciones
  y métodos empleados en adelante.

  \comentario{Añadir referencia bibliográfica.}

  De este modo, las fórmulas proposicionales pueden ser de dos tipos: aquellas que 
  actúan de manera \<open>conjuntiva\<close> (las fórmulas \<open>\<alpha>\<close>) y las que actúan de manera 
  disyuntiva (las fórmulas \<open>\<beta>\<close>). Para cada fórmula \<open>\<alpha>\<close>, o \<open>\<beta>\<close> respectivamente, se definen 
  dos componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, o \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> respectivamente. 

  \begin{definicion}
    Las fórmulas de tipo \<open>\<alpha>\<close> (\<open>fórmulas conjuntivas\<close>) y sus correspondientes componentes
    \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se definen inductivamente, dadas \<open>F\<close> y \<open>G\<close> fórmulas cualesquiera, como sigue:
    \begin{enumerate}
      \item \<open>F \<and> G\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>G\<close>.
      \item \<open>\<not>(F \<or> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(F \<longrightarrow> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(\<not> F)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>F\<close>.
    \end{enumerate} 
  \end{definicion}

  Como se trata de una definición inductiva, su formalización en Isabelle emplea el tipo
  \<open>inductive\<close>.\<close>

inductive Con :: "'a formula => 'a formula => 'a formula => bool" where
"Con (And F G) F G" |
"Con (Not (Or F G)) (Not F) (Not G)" |
"Con (Not (Imp F G)) F (Not G)" |
"Con (Not (Not F)) F F"

text \<open>De este modo, el uso del tipo \<open>inductive\<close> proporciona la formalización de cada
  una de las reglas de introducción que conforman la definición inductiva de manera 
  simultánea.

  \begin{itemize}
    \item[] @{thm[mode=Rule] Con.intros[no_vars]} 
      \hfill (@{text Con.intros})
  \end{itemize}

  Finalmente, definamos las fórmulas disyuntivas.

  \begin{definicion}
    Las fórmulas de tipo \<open>\<beta>\<close> (\<open>fórmulas disyuntivas\<close>) y sus correspondientes componentes
    \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se definen inductivamente, dadas \<open>F\<close> y \<open>G\<close> fórmulas cualesquiera, como sigue:
    \begin{enumerate}
      \item \<open>F \<or> G\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>F\<close> y \<open>G\<close>.
      \item \<open>F \<longrightarrow> G\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>G\<close>.
      \item \<open>\<not>(F \<and> G)\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(\<not> F)\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>F\<close> y \<open>F\<close>.
    \end{enumerate} 
  \end{definicion}

  Su formalización en Isabelle emplea análogamente el tipo \<open>inductive\<close>, como se muestra
  a continuación.\<close>

inductive Dis :: "'a formula => 'a formula => 'a formula => bool" where
"Dis (Or F G) F G" |
"Dis (Imp F G) (Not F) G" |
"Dis (Not (And F G)) (Not F) (Not G)" |
"Dis (Not (Not F)) F F"

text \<open>Del mismo modo, se formalizan en Isabelle las reglas de introducción de la definición
  anterior como sigue.

  \begin{itemize}
    \item[] @{thm[mode=Rule] Dis.intros[no_vars]} 
      \hfill (@{text Dis.intros})
  \end{itemize}

  Observando las definiciones dadas de las fórmulas \<open>\<alpha>\<close> y \<open>\<beta>\<close>, podemos trivialmente
  deducir el siguiente lema.

  \begin{lema}
    La doble negación de una fórmula cualquiera es una fórmula conjuntiva y disyuntiva
    simultáneamente.
  \end{lema}

  Su formalización y demostración detallada en Isabelle se muestran a continuación.\<close>

lemma notDisCon: "Con (Not (Not F)) F F" "Dis (Not (Not F)) F F" 
  by (simp only: Con.intros(4) Dis.intros(4))+

text \<open>\comentario{Voy por aquí en redacción}\<close>

text \<open>Ejemplos:
 \comentario{Redactar esto con enlace.}\<close>

lemma con_dis_simps:
  "Con a1 a2 a3 = (a1 = a2 \<^bold>\<and> a3 \<or> 
    (\<exists>F G. a1 = \<^bold>\<not> (F \<^bold>\<or> G) \<and> a2 = \<^bold>\<not> F \<and> a3 = \<^bold>\<not> G) \<or> 
    (\<exists>G. a1 = \<^bold>\<not> (a2 \<^bold>\<rightarrow> G) \<and> a3 = \<^bold>\<not> G) \<or> 
    a1 = \<^bold>\<not> (\<^bold>\<not> a2) \<and> a3 = a2)"
  "Dis a1 a2 a3 = (a1 = a2 \<^bold>\<or> a3 \<or> 
    (\<exists>F G. a1 = F \<^bold>\<rightarrow> G \<and> a2 = \<^bold>\<not> F \<and> a3 = G) \<or> 
    (\<exists>F G. a1 = \<^bold>\<not> (F \<^bold>\<and> G) \<and> a2 = \<^bold>\<not> F \<and> a3 = \<^bold>\<not> G) \<or> 
    a1 = \<^bold>\<not> (\<^bold>\<not> a2) \<and> a3 = a2)" 
  by (simp_all add: Con.simps Dis.simps)

text\<open>Veamos a continuación resultados que permiten caracterizar los conjuntos
  de Hintikka y la condición de consistencia proposicional empleando la 
  notación uniforme.

  \begin{lema}[Caracterización de los conjuntos de Hintikka mediante la
  notación uniforme]
    Dado un conjunto de fórmulas proposicionales \<open>S\<close>, son equivalentes:
    \begin{enumerate}
      \item \<open>S\<close> es un conjunto de Hintikka.
      \item Se verifican las condiciones siguientes.
      \begin{itemize}
        \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
        \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
        simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
        \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica 
        que si la fórmula pertenece al conjunto \<open>S\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> también.
        \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se verifica 
        que si la fórmula pertenece al conjunto \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> pertenece
        al conjunto o bien \<open>\<beta>\<^sub>2\<close> pertenece al conjunto.
      \end{itemize} 
    \end{enumerate}
  \end{lema}

  En Isabelle/HOL se formaliza del siguiente modo.\<close>

lemma "Hintikka S = (\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))" 
  oops

text \<open>Procedamos a la demostración del resultado.

\begin{demostracion}
Para probar la equivalencia, veamos cada una de las implicaciones por separado.

\textbf{\<open>1) \<Longrightarrow> 2)\<close>}
  Supongamos que \<open>S\<close> es un conjunto de Hintikka. Vamos a probar que, en efecto, se 
  verifican las condiciones del enunciado del lema.

  Por definición de conjunto de Hintikka, \<open>S\<close> verifica las siguientes condiciones:
  \begin{enumerate}
    \item \<open>\<bottom> \<notin> S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Si \<open>G \<and> H \<in> S\<close>, entonces \<open>G \<in> S\<close> y \<open>H \<in> S\<close>.
    \item Si \<open>G \<or> H \<in> S\<close>, entonces \<open>G \<in> S\<close> o \<open>H \<in> S\<close>.
    \item Si \<open>G \<rightarrow> H \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> o \<open>H \<in> S\<close>.
    \item Si \<open>\<not>(\<not> G) \<in> S\<close>, entonces \<open>G \<in> S\<close>.
    \item Si \<open>\<not>(G \<and> H) \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> o \<open>\<not> H \<in> S\<close>.
    \item Si \<open>\<not>(G \<or> H) \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> y \<open>\<not> H \<in> S\<close>. 
    \item Si \<open>\<not>(G \<rightarrow> H) \<in> S\<close>, entonces \<open>G \<in> S\<close> y \<open>\<not> H \<in> S\<close>. 
  \end{enumerate}  
  De este modo, el conjunto \<open>S\<close> cumple la primera y la segunda condición del
  enunciado del lema, que se corresponden con las dos primeras condiciones
  de la definición de conjunto de Hintikka. Veamos que, además, verifica las
  dos últimas condiciones del resultado.

  En primer lugar, probemos que para toda fórmula de tipo \<open>\<alpha>\<close> con 
  componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica que si la fórmula pertenece al conjunto 
  \<open>S\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> también. Para ello, supongamos que una fórmula 
  cualquiera de tipo \<open>\<alpha>\<close> pertence a \<open>S\<close>. Por definición de este tipo de
  fórmulas, tenemos que \<open>\<alpha>\<close> puede ser de la forma \<open>G \<and> H\<close>, \<open>\<not>(\<not> G)\<close>, \<open>\<not>(G \<or> H)\<close> 
  o \<open>\<not>(G \<longrightarrow> H)\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera. Probemos que, para cada
  tipo de fórmula \<open>\<alpha>\<close> perteneciente a \<open>S\<close>, sus componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> están en
  \<open>S\<close>.

  \begin{enumerate}
    \item[Fórmula del tipo \<open>G \<and> H\<close>:] Sus componentes conjuntivas son \<open>G\<close> y \<open>H\<close>. 
    Por la tercera condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>G \<and> H\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>H\<close> están ambas en el conjunto,
    lo que prueba este caso.
    \item[Fórmula del tipo \<open>\<not>(\<not> G)\<close>:] Sus componentes conjuntivas son ambas \<open>G\<close>.
    Por la sexta condición de la definición de conjunto de Hintikka, obtenemos que
    si \<open>\<not>(\<not> G)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> pertenece al conjunto, lo que prueba
    este caso.
    \item[Fórmula del tipo \<open>\<not>(G \<or> H)\<close>:] Sus componentes conjuntivas son \<open>\<not> G\<close> y \<open>\<not> H\<close>. 
    Por la octava condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>\<not>(G \<or> H)\<close> pertenece a \<open>S\<close>, entonces \<open>\<not> G\<close> y \<open>\<not> H\<close> están ambas en el conjunto,
    lo que prueba este caso.
    \item[Fórmula del tipo \<open>\<not>(G \<longrightarrow> H)\<close>:] Sus componentes conjuntivas son \<open>G\<close> y \<open>\<not> H\<close>. 
    Por la novena condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>\<not>(G \<longrightarrow> H)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>\<not> H\<close> están ambas en el conjunto,
    lo que prueba este caso.
  \end{enumerate}

  Finalmente, probemos que para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y 
  \<open>\<beta>\<^sub>2\<close> se verifica que si la fórmula pertenece al conjunto \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> 
  pertenece al conjunto o bien \<open>\<beta>\<^sub>2\<close> pertenece a conjunto. Para ello, supongamos que 
  una fórmula cualquiera de tipo \<open>\<beta>\<close> pertence a \<open>S\<close>. Por definición de este tipo de
  fórmulas, tenemos que \<open>\<beta>\<close> puede ser de la forma \<open>G \<or> H\<close>, \<open>G \<longrightarrow> H\<close>, \<open>\<not>(\<not> G)\<close> 
  o \<open>\<not>(G \<and> H)\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera. Probemos que, para cada
  tipo de fórmula \<open>\<beta>\<close> perteneciente a \<open>S\<close>, o bien su componente \<open>\<beta>\<^sub>1\<close> pertenece a \<open>S\<close> 
  o bien su componente \<open>\<beta>\<^sub>2\<close> pertenece a \<open>S\<close>.

  \begin{enumerate}
    \item[Fórmula del tipo \<open>G \<or> H\<close>:] Sus componentes disyuntivas son \<open>G\<close> y \<open>H\<close>. 
    Por la cuarta condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>G \<or> H\<close> pertenece a \<open>S\<close>, entonces o bien \<open>G\<close> está en \<open>S\<close> o bien \<open>H\<close> está
    en \<open>S\<close>, lo que prueba este caso.
    \item[Fórmula del tipo \<open>G \<longrightarrow> H\<close>:] Sus componentes disyuntivas son \<open>\<not> G\<close> y \<open>H\<close>.
    Por la quinta condición de la definición de conjunto de Hintikka, obtenemos que
    si \<open>G \<longrightarrow> H\<close> pertenece a \<open>S\<close>, entonces o bien \<open>\<not> G\<close> pertenece al conjunto o bien
    \<open>H\<close> pertenece al conjunto, lo que prueba este caso.
    \item[Fórmula del tipo \<open>\<not>(\<not> G)\<close>:] Sus componentes conjuntivas son ambas \<open>G\<close>.
    Por la sexta condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>\<not>(\<not> G)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> pertenece al conjunto. De este modo,
    por la regla de introducción a la disyunción, se prueba que o bien una de las 
    componentes está en el conjunto o bien lo está la otra pues, en este caso,
    coinciden.
    \item[Fórmula del tipo \<open>\<not>(G \<and> H)\<close>:] Sus componentes conjuntivas son \<open>\<not> G\<close> y \<open>\<not> H\<close>. 
    Por la séptima condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>\<not>(G \<and> H)\<close> pertenece a \<open>S\<close>, entonces o bien \<open>\<not> G\<close> pertenece al conjunto
    o bien \<open>\<not> H\<close> pertenece al conjunto, lo que prueba este caso.
  \end{enumerate}

\textbf{\<open>2) \<Longrightarrow> 1)\<close>}
  Supongamos que se verifican las condiciones del enunciado del lema:

  \begin{itemize}
    \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica 
    que si la fórmula pertenece al conjunto \<open>S\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> también.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se verifica 
    que si la fórmula pertenece al conjunto \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> pertenece
    al conjunto o bien \<open>\<beta>\<^sub>2\<close> pertenece al conjunto.
  \end{itemize}  

  Vamos a probar que \<open>S\<close> es un conjunto de Hintikka.

  Por la definición de conjunto de Hintikka, es suficiente probar las siguientes
  condiciones:

  \begin{enumerate}
    \item \<open>\<bottom> \<notin> S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Si \<open>G \<and> H \<in> S\<close>, entonces \<open>G \<in> S\<close> y \<open>H \<in> S\<close>.
    \item Si \<open>G \<or> H \<in> S\<close>, entonces \<open>G \<in> S\<close> o \<open>H \<in> S\<close>.
    \item Si \<open>G \<rightarrow> H \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> o \<open>H \<in> S\<close>.
    \item Si \<open>\<not>(\<not> G) \<in> S\<close>, entonces \<open>G \<in> S\<close>.
    \item Si \<open>\<not>(G \<and> H) \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> o \<open>\<not> H \<in> S\<close>.
    \item Si \<open>\<not>(G \<or> H) \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> y \<open>\<not> H \<in> S\<close>. 
    \item Si \<open>\<not>(G \<rightarrow> H) \<in> S\<close>, entonces \<open>G \<in> S\<close> y \<open>\<not> H \<in> S\<close>. 
  \end{enumerate} 

  En primer lugar se observa que, por hipótesis, se verifican las dos primeras
  condiciones de la definición de conjunto de Hintikka. Veamos que, en efecto, se
  cumplen las demás.

  \begin{enumerate}
    \item[\<open>3)\<close>] Supongamos que \<open>G \<and> H\<close> está en \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera.
    Por definición, \<open>G \<and> H\<close> es una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>G\<close> y \<open>H\<close>.
    Por lo tanto, por hipótesis se cumple que \<open>G\<close> y \<open>H\<close> están en \<open>S\<close>.
    \item[\<open>4)\<close>] Supongamos que \<open>G \<or> H\<close> está en \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera.
    Por definición, \<open>G \<or> H\<close> es una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>G\<close> y \<open>H\<close>.
    Por lo tanto, por hipótesis se cumple que o bien \<open>G\<close> está en \<open>S\<close> o bien \<open>H\<close> está 
    en \<open>S\<close>.
    \item[\<open>5)\<close>] Supongamos que \<open>G \<longrightarrow> H\<close> está en \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera.
    Por definición, \<open>G \<longrightarrow> H\<close> es una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<not> G\<close> y \<open>H\<close>.
    Por lo tanto, por hipótesis se cumple que o bien \<open>\<not> G\<close> está en \<open>S\<close> o bien \<open>H\<close> está 
    en \<open>S\<close>.
    \item[\<open>6)\<close>] Supongamos que \<open>\<not>(\<not> G)\<close> está en \<open>S\<close> para una fórmula \<open>G\<close> cualquiera.
    Por definición, \<open>\<not>(\<not> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son ambas \<open>G\<close>.
    Por lo tanto, por hipótesis se cumple que \<open>G\<close> está en \<open>S\<close>.
    \item[\<open>7)\<close>] Supongamos que \<open>\<not>(G \<and> H)\<close> está en \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera.
    Por definición, \<open>\<not>(G \<and> H)\<close> es una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<not> G\<close> y \<open>\<not> H\<close>.
    Por lo tanto, por hipótesis se cumple que o bien \<open>\<not> G\<close> está en \<open>S\<close> o bien \<open>\<not> H\<close> está 
    en \<open>S\<close>.
    \item[\<open>8)\<close>] Supongamos que \<open>\<not>(G \<or> H)\<close> está en \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera.
    Por definición, \<open>\<not>(G \<or> H)\<close> es una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<not> G\<close> y \<open>\<not> H\<close>.
    Por lo tanto, por hipótesis se cumple que \<open>\<not> G\<close> y \<open>\<not> H\<close> están en \<open>S\<close>.
    \item[\<open>9)\<close>] Supongamos que \<open>\<not>(G \<longrightarrow> H)\<close> está en \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera.
    Por definición, \<open>\<not>(G \<longrightarrow> H)\<close> es una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>G\<close> y \<open>\<not> H\<close>.
    Por lo tanto, por hipótesis se cumple que \<open>G\<close> y \<open>\<not> H\<close> están en \<open>S\<close>.
  \end{enumerate}

  Por tanto, queda probado el resultado.
\end{demostracion}

  Para probar de manera detallada el lema en Isabelle, vamos a demostrar inicialmenre 
  cada una de las implicaciones de la equivalencia por separado. 

  La primera implicación del lema se basa en dos lemas auxiliares. El primero de ellos 
  prueba que la tercera, sexta, octava y novena condición de la definición de conjunto de 
  Hintikka son suficientes para probar que para toda fórmula de tipo \<open>\<alpha>\<close> con componentes 
  \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica que si la fórmula pertenece al conjunto \<open>S\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y 
  \<open>\<alpha>\<^sub>2\<close> también. Su demostración detallada en Isabelle se muestra a continuación.\<close>

lemma Hintikka_alt1Con:
  assumes "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
  shows "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
proof (rule impI)
  assume "Con F G H"
  then have "F = G \<^bold>\<and> H \<or> 
    ((\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
    (\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G)"
    by (simp only: con_dis_simps(1))
  thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
  proof (rule disjE)
    assume "F = G \<^bold>\<and> H"
    have "\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      using assms by (rule conjunct1)
    thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      using \<open>F = G \<^bold>\<and> H\<close> by (iprover elim: allE)
  next 
    assume "(\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
    ((\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G)"
    thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S" 
    proof (rule disjE)
      assume E1:"\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1"
      obtain G1 H1 where A1:"F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1"
        using E1 by (iprover elim: exE)
      then have "F = \<^bold>\<not> (G1 \<^bold>\<or> H1)"
        by (rule conjunct1)
      have "G = \<^bold>\<not> G1"
        using A1 by (iprover elim: conjunct1)
      have "H = \<^bold>\<not> H1"
        using A1 by (iprover elim: conjunct1)
      have "\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
        using assms by (iprover elim: conjunct2 conjunct1)
      thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
        using \<open>F = \<^bold>\<not> (G1 \<^bold>\<or> H1)\<close> \<open>G = \<^bold>\<not> G1\<close> \<open>H = \<^bold>\<not> H1\<close> by (iprover elim: allE)
    next
      assume "(\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2) \<or> 
      F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
      thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S" 
      proof (rule disjE)
        assume E2:"\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2"
        obtain H2 where A2:"F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2"
          using E2 by (rule exE)
        have "F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2)"
          using A2 by (rule conjunct1)
        have "H = \<^bold>\<not> H2"
          using A2 by (rule conjunct2)
        have "\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using assms by (iprover elim: conjunct2 conjunct1)
        thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          using \<open>F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2)\<close> \<open>H = \<^bold>\<not> H2\<close> by (iprover elim: allE)
      next 
        assume "F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
        then have "F = \<^bold>\<not> (\<^bold>\<not> G)"
          by (rule conjunct1)
        have "H = G"
          using \<open>F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G\<close> by (rule conjunct2)
        have "\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
          using assms by (iprover elim: conjunct2 conjunct1)
        then have "\<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
          by (rule allE)
        then have "F \<in> S \<longrightarrow> G \<in> S"
          by (simp only: \<open>F = \<^bold>\<not> (\<^bold>\<not> G)\<close>) 
        then have "F \<in> S \<longrightarrow> G \<in> S \<and> G \<in> S"
          by (simp only: conj_absorb)
        thus "F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          by (simp only: \<open>H=G\<close>)
      qed
    qed
  qed
qed

text \<open>Por otro lado, el segundo lema auxiliar prueba que la cuarta, quinta, sexta
  y séptima condición de la definición de conjunto de Hintikka son suficientes para
  probar que para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se verifica 
  que si la fórmula pertenece al conjunto \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> pertenece al
  conjunto o bien \<open>\<beta>\<^sub>2\<close> pertenece al conjunto. Veamos su prueba detallada en 
  Isabelle/HOL.\<close>

lemma Hintikka_alt1Dis:
  assumes  "(\<forall> G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
  \<and> (\<forall> G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S)
  \<and> (\<forall> G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
  \<and> (\<forall> G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)"
  shows "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
proof (rule impI)
  assume "Dis F G H"
  then have "F = G \<^bold>\<or> H \<or> 
    (\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
    (\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G" 
    by (simp only: con_dis_simps(2))
  thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S" 
  proof (rule disjE)
    assume "F = G \<^bold>\<or> H"
    have "\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
      using assms by (rule conjunct1)
    thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S" 
      using \<open>F = G \<^bold>\<or> H\<close> by (iprover elim: allE)
  next
    assume "(\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
    (\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
    thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
    proof (rule disjE)
      assume E1:"\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1"
      obtain G1 H1 where A1:"F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1"
        using E1 by (iprover elim: exE)
      have "F = G1 \<^bold>\<rightarrow> H1"
        using A1 by (rule conjunct1)
      have "G = \<^bold>\<not> G1"
        using A1 by (iprover elim: conjunct1)
      have "H = H1"
        using A1 by (iprover elim: conjunct2 conjunct1)
      have "\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
        using assms by (iprover elim: conjunct2 conjunct1)
      thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
        using \<open>F = G1 \<^bold>\<rightarrow> H1\<close> \<open>G = \<^bold>\<not> G1\<close> \<open>H = H1\<close> by (iprover elim: allE)
    next
      assume "(\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2) \<or> 
      F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
      thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
      proof (rule disjE)
        assume E2:"\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2"
        obtain G2 H2 where A2:"F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2" 
          using E2 by (iprover elim: exE)
        have "F = \<^bold>\<not> (G2 \<^bold>\<and> H2)" 
          using A2 by (rule conjunct1)
        have "G = \<^bold>\<not> G2"
          using A2 by (iprover elim: conjunct2 conjunct1)
        have "H = \<^bold>\<not> H2"
          using A2 by (iprover elim: conjunct1)
        have "\<forall> G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using assms by (iprover elim: conjunct2 conjunct1)
        thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          using \<open>F = \<^bold>\<not>(G2 \<^bold>\<and> H2)\<close> \<open>G = \<^bold>\<not> G2\<close> \<open>H = \<^bold>\<not> H2\<close> by (iprover elim: allE)
      next
        assume "F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
        then have "F = \<^bold>\<not> (\<^bold>\<not> G)" 
          by (rule conjunct1)
        have "H = G"
          using \<open>F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G\<close> by (rule conjunct2)
        have "\<forall> G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
          using assms by (iprover elim: conjunct2 conjunct1)
        then have "\<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
          by (rule allE)
        then have "F \<in> S \<longrightarrow> G \<in> S"
          by (simp only: \<open>F = \<^bold>\<not> (\<^bold>\<not> G)\<close>)
        then have "F \<in> S \<longrightarrow> G \<in> S \<or> G \<in> S"
          by (simp only: disj_absorb)
        thus "F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
        by (simp only: \<open>H = G\<close>)
      qed
    qed
  qed
qed

text \<open>Finalmente, podemos demostrar detalladamente esta primera implicación de la
  equivalencia del lema en Isabelle.\<close>

lemma Hintikka_alt1:
  assumes "Hintikka S"
  shows "\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
proof -
  have Hk:"(\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S))"
    using assms by (rule auxEq)
  then have C1: "\<bottom> \<notin> S"
    by (rule conjunct1)
  have C2: "\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
    using Hk by (iprover elim: conjunct2 conjunct1)
  have C3: "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
  proof (rule allI)
    fix F
    show "\<forall>G H.  Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
    proof (rule allI)
      fix G 
      show "\<forall>H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      proof (rule allI)
        fix H
        have C31:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have C32:"\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have C33:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have C34:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)" 
          using C31 C32 C33 C34 by (iprover intro: conjI)
        thus "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          by (rule Hintikka_alt1Con)
      qed
    qed
  qed
  have C4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
  proof (rule allI)
    fix F
    show "\<forall>G H.  Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
    proof (rule allI)
      fix G 
      show "\<forall>H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
      proof (rule allI)
        fix H
        have C41:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have C42:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have C43:"\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have C44:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using Hk by (iprover elim: conjunct2 conjunct1)
        have "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
        \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)"
          using C41 C42 C43 C44 by (iprover intro: conjI)
        thus "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          by (rule Hintikka_alt1Dis)
      qed
    qed
  qed
  show "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    using C1 C2 C3 C4 by (iprover intro: conjI)
qed

text \<open>Por último, probamos la implicación contraria de forma detallada en Isabelle mediante
  el siguiente lema.\<close>

lemma Hintikka_alt2:
  assumes "\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S) 
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"  
  shows "Hintikka S"
proof -
  have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
    using assms by (iprover elim: conjunct2 conjunct1)
  have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
    using assms by (iprover elim: conjunct2 conjunct1)
  have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
  proof -
    have C1:"\<bottom> \<notin> S"
      using assms by (rule conjunct1)
    have C2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
      using assms by (iprover elim: conjunct2 conjunct1)
    have C3:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
    proof (rule allI)
      fix G
      show "\<forall>H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      proof (rule allI)
        fix H
        have "Con (G \<^bold>\<and> H) G H"
          by (simp only: Con.intros(1))
        have "Con (G \<^bold>\<and> H) G H \<longrightarrow> G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          using Con by (iprover elim: allE)
        thus "G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          using \<open>Con (G \<^bold>\<and> H) G H\<close> by (rule mp)
      qed
    qed
    have C4:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
    proof (rule allI)
      fix G
      show "\<forall>H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
      proof (rule allI)
        fix H
        have "Dis (G \<^bold>\<or> H) G H"
          by (simp only: Dis.intros(1))
        have "Dis (G \<^bold>\<or> H) G H \<longrightarrow> G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          using Dis by (iprover elim: allE)
        thus "G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          using \<open>Dis (G \<^bold>\<or> H) G H\<close> by (rule mp)
      qed
    qed
    have C5:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
    proof (rule allI)
      fix G
      show "\<forall>H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
      proof (rule allI)
        fix H
        have "Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not> G) H"
          by (simp only: Dis.intros(2))
        have "Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not> G) H \<longrightarrow> G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
          using Dis by (iprover elim: allE)
        thus "G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S" 
          using \<open>Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not> G) H\<close> by (rule mp)
      qed
    qed
    have C6:"\<forall>G. \<^bold>\<not>(\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
    proof (rule allI)
      fix G
      show "\<^bold>\<not>(\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S"
      proof (rule impI)
        assume "\<^bold>\<not> (\<^bold>\<not> G) \<in> S" 
        have "Con (\<^bold>\<not> (\<^bold>\<not> G)) G G"
          by (simp only: Con.intros(4))
        have "Con (\<^bold>\<not>(\<^bold>\<not> G)) G G \<longrightarrow> (\<^bold>\<not>(\<^bold>\<not> G)) \<in> S \<longrightarrow> G \<in> S \<and> G \<in> S"
          using Con by (iprover elim: allE)
        then have "(\<^bold>\<not>(\<^bold>\<not> G)) \<in> S \<longrightarrow> G \<in> S \<and> G \<in> S"
          using \<open>Con (\<^bold>\<not> (\<^bold>\<not> G)) G G\<close> by (rule mp)
        then have "G \<in> S \<and> G \<in> S"
          using \<open>\<^bold>\<not> (\<^bold>\<not> G) \<in> S\<close> by (rule mp)
        thus "G \<in> S"
          by (simp only: conj_absorb)
      qed
    qed
    have C7:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
    proof (rule allI)
      fix G
      show "\<forall>H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
      proof (rule allI)
        fix H
        have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)"
          by (simp only: Dis.intros(3))
        have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not> G) (\<^bold>\<not> H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using Dis by (iprover elim: allE)
        thus "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using \<open>Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)\<close> by (rule mp)
      qed
    qed
    have C8:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    proof (rule allI)
      fix G
      show "\<forall>H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
      proof (rule allI)
        fix H
        have "Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)"
          by (simp only: Con.intros(2))
        have "Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not> G) (\<^bold>\<not> H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using Con by (iprover elim: allE)
        thus "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using \<open>Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)\<close> by (rule mp)
      qed
    qed
    have C9:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    proof (rule allI)
      fix G
      show "\<forall>H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
      proof (rule allI)
        fix H
        have "Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not> H)"
          by (simp only: Con.intros(3))
        have "Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not> H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using Con by (iprover elim: allE)
        thus "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using \<open>Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not> H)\<close> by (rule mp)
      qed
    qed
    have A:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)"
      using C1 C2 C3 C4 C5 by (iprover intro: conjI)
    have B:"(\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
      using C6 C7 C8 C9 by (iprover intro: conjI)
    have "(\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S))
    \<and> ((\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S))"
      using A B by (rule conjI)
    thus "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)" 
      by (iprover intro: conj_assoc)
  qed
  thus "Hintikka S"
    unfolding Hintikka_def by this
qed

text \<open>En conclusión, el lema completo se demuestra detalladamente en Isabelle/HOL como sigue.\<close>

lemma "Hintikka S = (\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))"  
proof (rule iffI)
  assume "Hintikka S"
  thus "(\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))"
    by (rule Hintikka_alt1)
next
  assume "(\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))"
  thus "Hintikka S"
    by (rule Hintikka_alt2)
qed

text \<open>Del mismo modo, veamos su demostración automática.\<close>

lemma Hintikka_alt: "Hintikka S = (\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))"  
  apply(simp add: Hintikka_def con_dis_simps)
  apply(rule iffI)
   subgoal by blast
  subgoal by safe metis+
  done

text \<open>\comentario{Voy redactando por aqui.}\<close>

text\<open> Lema: caracterización de la propiedad de consistencia proposicional
 mediante las fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>.\<close>

text \<open>El lema \<open>pcp_alt1\<close> es el lema auxiliar para la primera implicación.\<close>

lemma pcp_alt1Con:
  assumes "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
  shows "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
proof -
  have C1:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    using assms by (rule conjunct1)
  have C2:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using assms by (iprover elim: conjunct2 conjunct1)
  have C3:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
    using assms by (iprover elim: conjunct2 conjunct1)
  have C4:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
    using assms by (iprover elim: conjunct2) 
  show "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  proof (rule allI)
    fix F
    show "\<forall>G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    proof (rule allI)
      fix G
      show "\<forall>H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
      proof (rule allI)
        fix H
        show "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        proof (rule impI)
          assume "Con F G H"
          then have "F = G \<^bold>\<and> H \<or> 
          ((\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
          (\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2) \<or> 
           F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G)"
            by (simp only: con_dis_simps(1))
          thus "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
          proof (rule disjE)
            assume "F = G \<^bold>\<and> H"
            show "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
              using C1 \<open>F = G \<^bold>\<and> H\<close> by (iprover elim: allE)
          next
            assume "(\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
          (\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2) \<or> 
           F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
            thus "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
            proof (rule disjE)
              assume E1:"\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1"
              obtain G1 H1 where A1:"F = \<^bold>\<not> (G1 \<^bold>\<or> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1"
                using E1 by (iprover elim: exE)
              have "F = \<^bold>\<not> (G1 \<^bold>\<or> H1)"
                using A1 by (rule conjunct1)
              have "G = \<^bold>\<not> G1"
                using A1 by (iprover elim: conjunct2 conjunct1)
              have "H = \<^bold>\<not> H1"
                using A1 by (iprover elim: conjunct2)
              show "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
                using C3 \<open>F = \<^bold>\<not> (G1 \<^bold>\<or> H1)\<close> \<open>G = \<^bold>\<not> G1\<close> \<open>H = \<^bold>\<not> H1\<close> by (iprover elim: allE)
            next
              assume "(\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2) \<or> 
              F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G" 
              thus "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
              proof (rule disjE)
                assume E2:"\<exists>H2. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2"
                obtain H2 where A2:"F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2) \<and> H = \<^bold>\<not> H2"
                  using E2 by (rule exE)
                have "F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2)"
                  using A2 by (rule conjunct1)
                have "H = \<^bold>\<not> H2"
                  using A2 by (rule conjunct2)
                show "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
                  using C4 \<open>F = \<^bold>\<not> (G \<^bold>\<rightarrow> H2)\<close> \<open>H = \<^bold>\<not> H2\<close> by (iprover elim: allE)
              next
                assume A3:"F = \<^bold>\<not>(\<^bold>\<not> G) \<and> H = G"
                then have "F = \<^bold>\<not>(\<^bold>\<not> G)"
                  by (rule conjunct1)
                have "H = G"
                  using A3 by (rule conjunct2)
                have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C"
                  using C2 \<open>F = \<^bold>\<not>(\<^bold>\<not> G)\<close> by (iprover elim: allE)
                then have "F \<in> S \<longrightarrow> {G,G} \<union> S \<in> C"
                  by (simp only: insert_absorb2)
                thus "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C" 
                  by (simp only: \<open>H = G\<close>)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma pcp_alt1Dis:
  assumes "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
  shows "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
proof -
  have C1:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using assms by (rule conjunct1)
  have C2:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using assms by (iprover elim: conjunct2 conjunct1)
  have C3:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using assms by (iprover elim: conjunct2 conjunct1)
  have C4:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
    using assms by (iprover elim: conjunct2) 
  show "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  proof (rule allI)
    fix F
    show "\<forall>G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    proof (rule allI)
      fix G
      show "\<forall>H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      proof (rule allI)
        fix H
        show "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        proof (rule impI)
          assume "Dis F G H"
          then have "F = G \<^bold>\<or> H \<or> 
          (\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
          (\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2) \<or> 
          F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G" 
            by (simp only: con_dis_simps(2))
          thus "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          proof (rule disjE)
            assume "F = G \<^bold>\<or> H"
            show "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
              using C1 \<open>F = G \<^bold>\<or> H\<close> by (iprover elim: allE)
          next
            assume "(\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
            (\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2) \<or> 
            F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
            thus "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
            proof (rule disjE)
              assume E1:"\<exists>G1 H1. F = (G1 \<^bold>\<rightarrow> H1) \<and> G = \<^bold>\<not> G1 \<and> H = H1"
              obtain G1 H1 where A1:" F = (G1 \<^bold>\<rightarrow> H1) \<and> G = \<^bold>\<not> G1 \<and> H = H1"
                using E1 by (iprover elim: exE)
              have "F = (G1 \<^bold>\<rightarrow> H1)"
                using A1 by (rule conjunct1)
              have "G = \<^bold>\<not> G1"
                using A1 by (iprover elim: conjunct2 conjunct1)
              have "H = H1"
                using A1 by (iprover elim: conjunct2)
              show "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
                using C2 \<open>F = (G1 \<^bold>\<rightarrow> H1)\<close> \<open>G = \<^bold>\<not> G1\<close> \<open>H = H1\<close> by (iprover elim: allE)
            next
              assume "(\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2) \<or> 
                        F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G" 
              thus "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
              proof (rule disjE)
                assume E2:"\<exists>G2 H2. F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2"
                obtain G2 H2 where A2:"F = \<^bold>\<not> (G2 \<^bold>\<and> H2) \<and> G = \<^bold>\<not> G2 \<and> H = \<^bold>\<not> H2"
                  using E2 by (iprover elim: exE)
                have "F = \<^bold>\<not> (G2 \<^bold>\<and> H2)"
                  using A2 by (rule conjunct1)
                have "G = \<^bold>\<not> G2"
                  using A2 by (iprover elim: conjunct2 conjunct1)
                have "H = \<^bold>\<not> H2"
                  using A2 by (iprover elim: conjunct2)
                show "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
                  using C4 \<open>F = \<^bold>\<not> (G2 \<^bold>\<and> H2)\<close> \<open>G = \<^bold>\<not> G2\<close> \<open>H = \<^bold>\<not> H2\<close> by (iprover elim: allE)
              next
                assume A3:"F = \<^bold>\<not>(\<^bold>\<not> G) \<and> H = G"
                then have "F = \<^bold>\<not>(\<^bold>\<not> G)"
                  by (rule conjunct1)
                have "H = G"
                  using A3 by (rule conjunct2)
                have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C"
                  using C3 \<open>F = \<^bold>\<not>(\<^bold>\<not> G)\<close> by (iprover elim: allE)
                then have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
                  by (simp only: disj_absorb)
                thus "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
                  by (simp only: \<open>H = G\<close>)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed 

lemma pcp_alt1: 
  assumes "pcp C"
  shows "\<forall>S \<in> C. \<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
proof (rule ballI)
  fix S
  assume "S \<in> C"
  have "(\<forall>S \<in> C.
  \<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C))"
    using assms by (simp only: pcp_def)
  then have pcpS:"\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
    using \<open>S \<in> C\<close> by (rule bspec)
  then have C1:"\<bottom> \<notin> S"
    by (rule conjunct1)
  have C2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C3:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C4:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C5:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C6:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C7:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C8:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2 conjunct1)
  have C9:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
    using pcpS by (iprover elim: conjunct2)
  have "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
    using C3 C6 C8 C9 by (iprover intro: conjI)
  then have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    by (rule pcp_alt1Con)
  have "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
    using C4 C5 C6 C7 by (iprover intro: conjI)
  then have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    by (rule pcp_alt1Dis)
  thus "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using C1 C2 Con Dis by (iprover intro: conjI)
qed

text \<open>El lema \<open>pcp_alt2\<close> es para la implicación contraria.\<close>

text \<open>Lemas auxiliares para \<open>pcp_alt2Con\<close> para las distintas conectivas (análogos)
  Idea: hacer estas demostraciones a mano resumidas en una sola demostración
  donde se considera la fórmula beta y sus componentes.\<close>

lemma pcp_alt2Con1:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<forall>H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  proof (rule allI)
    fix H
    show "G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    proof (rule impI)
      assume "G \<^bold>\<and> H \<in> S"
      then have "Con (G \<^bold>\<and> H) G H"
        by (simp only: Con.intros(1))
      let ?F="G \<^bold>\<and> H"
      have "Con ?F G H \<longrightarrow> ?F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        using assms by (iprover elim: allE)
      then have "?F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        using \<open>Con (G \<^bold>\<and> H) G H\<close> by (rule mp)
      thus "{G,H} \<union> S \<in> C"
        using \<open>(G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

lemma pcp_alt2Con2:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
  proof (rule impI)
    assume "\<^bold>\<not>(\<^bold>\<not>G) \<in> S"
    then have "Con (\<^bold>\<not>(\<^bold>\<not>G)) G G"
      by (simp only: Con.intros(4))
    let ?F="\<^bold>\<not>(\<^bold>\<not> G)"
    have "\<forall>G H. Con ?F G H \<longrightarrow> ?F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
      using assms by (rule allE)
    then have "\<forall>H. Con ?F G H \<longrightarrow> ?F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
      by (rule allE)
    then have "Con ?F G G \<longrightarrow> ?F \<in> S \<longrightarrow> {G,G} \<union> S \<in> C"
      by (rule allE)
    then have "?F \<in> S \<longrightarrow> {G,G} \<union> S \<in> C"
      using \<open>Con (\<^bold>\<not>(\<^bold>\<not>G)) G G\<close> by (rule mp)
    then have "{G,G} \<union> S \<in> C"
      using \<open>(\<^bold>\<not>(\<^bold>\<not>G)) \<in> S\<close> by (rule mp)
    thus "{G} \<union> S \<in> C"
      by (simp only: insert_absorb2)
  qed
qed

lemma pcp_alt2Con3:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<forall>H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
  proof (rule allI)
    fix H
    show "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
    proof (rule impI)
      assume "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S"
      then have "Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)"
        by (simp only: Con.intros(2))
      let ?F = "\<^bold>\<not>(G \<^bold>\<or> H)"
      have "Con ?F (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> ?F \<in> S \<longrightarrow> {\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
        using assms by (iprover elim: allE)
      then have "?F \<in> S \<longrightarrow> {\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)\<close> by (rule mp)
      thus "{\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>\<^bold>\<not>(G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

lemma pcp_alt2Con4:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<forall>H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
  proof (rule allI)
    fix H
    show "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
    proof (rule impI)
      assume "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S"
      then have "Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not>H)"
        by (simp only: Con.intros(3))
      let ?F = "\<^bold>\<not>(G \<^bold>\<rightarrow> H)"
      have "Con ?F G (\<^bold>\<not>H) \<longrightarrow> ?F \<in> S \<longrightarrow> {G,\<^bold>\<not>H} \<union> S \<in> C"
        using assms by (iprover elim: allE)
      then have "?F \<in> S \<longrightarrow> {G,\<^bold>\<not>H} \<union> S \<in> C"  
        using \<open>Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not>H)\<close> by (rule mp)
      thus "{G,\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

lemma pcp_alt2Con:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
proof -
  have 1:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    using assms by (rule pcp_alt2Con1)
  have 2:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using assms by (rule pcp_alt2Con2)
  have 3:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
    using assms by (rule pcp_alt2Con3)
  have 4:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
    using assms by (rule pcp_alt2Con4)
  show ?thesis
    using 1 2 3 4 by (iprover intro: conjI)
qed

text \<open>Lemas auxiliares para \<open>pcp_alt2Dis\<close> para las distintas conectivas (análogos)
  Idea: hacer estas demostraciones a mano resumidas en una sola demostración
  donde se considera la fórmula beta y sus componentes.\<close>

lemma pcp_alt2Dis1:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<forall>H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  proof (rule allI)
    fix H
    show "G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    proof (rule impI)
      assume "G \<^bold>\<or> H \<in> S"
      then have "Dis (G \<^bold>\<or> H) G H"
        by (simp only: Dis.intros(1))
      let ?F="G \<^bold>\<or> H"
      have "Dis ?F G H \<longrightarrow> ?F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using assms by (iprover elim: allE)
      then have "?F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using \<open>Dis (G \<^bold>\<or> H) G H\<close> by (rule mp)
      thus "{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using \<open>(G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

lemma pcp_alt2Dis2:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<forall>H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  proof (rule allI)
    fix H
    show "G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    proof (rule impI)
      assume "G \<^bold>\<rightarrow> H \<in> S"
      then have "Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not>G) H"
        by (simp only: Dis.intros(2))
      let ?F="G \<^bold>\<rightarrow> H" 
      have "Dis ?F (\<^bold>\<not>G) H \<longrightarrow> ?F \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using assms by (iprover elim: allE)
      then have "?F \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using \<open>Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not>G) H\<close> by (rule mp)
      thus "{\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using \<open>(G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

lemma pcp_alt2Dis3:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
  proof (rule impI)
    assume "\<^bold>\<not> (\<^bold>\<not>G) \<in> S"
    then have "Dis (\<^bold>\<not> (\<^bold>\<not>G)) G G"
      by (simp only: Dis.intros(4))
    let ?F="\<^bold>\<not> (\<^bold>\<not> G)" 
    have "\<forall>G H. Dis ?F G H \<longrightarrow> ?F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using assms by (rule allE)
    then have "\<forall>H. Dis ?F G H \<longrightarrow> ?F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      by (rule allE)
    then have "Dis ?F G G \<longrightarrow> ?F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
      by (rule allE)
    then have "?F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
      using \<open>Dis (\<^bold>\<not> (\<^bold>\<not>G)) G G\<close> by (rule mp)
    then have "{G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
      using \<open>(\<^bold>\<not> (\<^bold>\<not>G)) \<in> S\<close> by (rule mp)
    thus "{G} \<union> S \<in> C"
      by (simp only: disj_absorb)
  qed
qed

lemma pcp_alt2Dis4:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
proof (rule allI)
  fix G
  show "\<forall>H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
  proof (rule allI)
    fix H
    show "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
    proof (rule impI)
      assume "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S"
      then have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)"
        by (simp only: Dis.intros(3))
      have "\<forall>G H. Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        using assms by auto (*Pendiente*)
      then have "\<forall>H. Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        by (rule allE)
      then have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        by (rule allE)
      then have "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)\<close> by (rule mp)
      thus "{\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>\<^bold>\<not>(G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

text \<open>Lema \<open>pcp_alt2Dis\<close>\<close>

lemma pcp_alt2Dis:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
proof -
  have 1:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using assms by (rule pcp_alt2Dis1)
  have 2:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using assms by (rule pcp_alt2Dis2)
  have 3:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using assms by (rule pcp_alt2Dis3)
  have 4:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
    using assms by (rule pcp_alt2Dis4)
  show ?thesis
    using 1 2 3 4 by (iprover intro: conjI)
qed

lemma pcp_alt2: 
  assumes "\<forall>S \<in> C. \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
  shows "pcp C"
  unfolding pcp_def
proof (rule ballI)
  fix S
  assume "S \<in> C"
  have H:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms \<open>S \<in> C\<close> by (rule bspec)
  then have "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    by (iprover elim: conjunct1 conjunct2)
  then have C:"(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
    by (rule pcp_alt2Con)
  have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using H by (iprover elim: conjunct1 conjunct2)
  then have D:"(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
    by (rule pcp_alt2Dis)
  have 1:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
    using H by (iprover elim: conjunct1)
  have 2:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    using C by (iprover elim: conjunct1 conjunct2)
  have 3:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using D by (iprover elim: conjunct1 conjunct2)
  have 4:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using D by (iprover elim: conjunct1 conjunct2)
  have 5:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using C by (iprover elim: conjunct1 conjunct2)
  have 6:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
    using D by (iprover elim: conjunct1 conjunct2)
  have 7:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
    using C by (iprover elim: conjunct1 conjunct2)
  have 8:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
    using C by (iprover elim: conjunct1 conjunct2)
  show "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
    using 1 2 3 4 5 6 7 8 by blast (*Pendiente*)
qed
text \<open>\comentario{Pendientes}\<close>

lemma "pcp C = (\<forall>S \<in> C. \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))"
proof (rule iffI)
  assume "pcp C"
  thus "\<forall>S \<in> C. \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    by (rule pcp_alt1)
next
  assume "\<forall>S \<in> C. \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
  thus "pcp C"
    by (rule pcp_alt2)
qed

lemma pcp_alt: "pcp C = (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))"
  apply(simp add: pcp_def con_dis_simps)
  apply(rule iffI; unfold Ball_def; elim all_forward)
  by (auto simp add: insert_absorb split: formula.splits)

text\<open> Definición: C es cerrado bajo subconjunto.\<close>
definition "subset_closed C \<equiv> (\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C)"

text \<open> Definición: C tiene la propiedad de carácter finito.\<close>
definition "finite_character C \<equiv> 
            (\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C))"

text \<open> Lema: Si C verifica la propidad de consistencia proposicional, 
entonces tiene un subconjunto con la propiedad de consistencia
proposicional y cerrado bajo subconjunto.\<close>

lemma ex1_subset: "C \<subseteq> {s. \<exists>S\<in>C. s \<subseteq> S}"
proof (rule subsetI)
  fix s
  assume "s \<in> C"
  have "s \<subseteq> s"
    by (rule subset_refl)
  then have "\<exists>S\<in>C. s \<subseteq> S"
    using \<open>s \<in> C\<close> by (rule bexI)
  thus "s \<in> {s. \<exists>S\<in>C. s \<subseteq> S}"
    by simp (*Pendiente*)
qed

lemma ex1_pcp: 
  assumes "pcp C"
  shows "pcp {s. \<exists>S\<in>C. s \<subseteq> S}"
proof -
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  have C1: "C \<subseteq> ?E"
    by (rule ex1_subset)
  show "pcp ?E"
  proof (rule pcp_alt2)
    show "\<forall>S \<in> ?E. (\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E))"
    proof (rule ballI)
      fix S
      assume "S \<in> ?E"
      then have 1:"\<exists>S'\<in> C. S \<subseteq> S'"
        by (rule CollectD)  
      obtain S' where "S' \<in> C" "S \<subseteq> S'"
        using 1 by (rule bexE)
      have 2:"(\<forall>S \<in> C.
      \<bottom> \<notin> S
      \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))"
        using assms by (rule pcp_alt1)
      have 3:"\<bottom> \<notin> S'
      \<and> (\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C)"
        using \<open>S' \<in> C\<close> 2 by simp (*Pendiente*)
      then have "\<bottom> \<notin> S'"
        by (rule conjunct1)
      have S1:"\<bottom> \<notin> S"
        using \<open>S \<subseteq> S'\<close> \<open>\<bottom> \<notin> S'\<close> by (rule contra_subsetD)
      have 4:"(\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C)"
        using 3 by (rule conjunct2)
      then have 5:"\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
        by (rule conjunct1)
      have S2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
      proof (rule allI)
        fix k
        show "Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
        proof (rule impI)
          assume "Atom k \<in> S"
          have "Atom k \<in> S'"
            using \<open>S \<subseteq> S'\<close> \<open>Atom k \<in> S\<close> by (rule set_mp)
          show "\<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
          proof (rule impI)
            assume "\<^bold>\<not> (Atom k) \<in> S"
            have "\<^bold>\<not> (Atom k) \<in> S'"
              using \<open>S \<subseteq> S'\<close> \<open>\<^bold>\<not> (Atom k) \<in> S\<close> by (rule set_mp)
            have "Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
              using 5 by (rule allE)
            then have "\<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
              using \<open>Atom k \<in> S'\<close> by (rule mp)
            thus "False"
              using \<open>\<^bold>\<not> (Atom k) \<in> S'\<close> by (rule mp)
          qed
        qed
      qed
      have 6:"(\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C)"
        using 4 by (rule conjunct2)
      then have 7:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
        by (rule conjunct1)
      have S3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E"
      proof (rule allI)
        fix F
        show "\<forall>G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E"
        proof (rule allI)
          fix G
          show "\<forall>H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E"
          proof (rule allI)
            fix H
            show "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E"
            proof (rule impI)
              assume "Con F G H"
              show "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E"
              proof (rule impI)
                assume "F \<in> S"
                have "F \<in> S'"
                  using \<open>S \<subseteq> S'\<close> \<open>F \<in> S\<close> by (rule set_mp)
                have "Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
                  using 7 by (iprover elim: allE)
                then have "F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
                  using \<open>Con F G H\<close> by (rule mp)
                then have "{G,H} \<union> S' \<in> C"
                  using \<open>F \<in> S'\<close> by (rule mp)
                have "{G,H} \<union> S' \<in> ?E"
                  using C1 \<open>{G,H} \<union> S' \<in> C\<close> by (rule set_mp)
                have "S \<subseteq> insert H S'"
                  using \<open>S \<subseteq> S'\<close> by (rule subset_insertI2) 
                have "insert H S' = {H} \<union> S'"
                  by (rule insert_is_Un)
                then have "S \<subseteq> {H} \<union> S'"
                  using \<open>S \<subseteq> insert H S'\<close> by simp (*Pendiente*)
                have "S \<subseteq> insert G ({H} \<union> S')"
                  using \<open>S \<subseteq> {H} \<union> S'\<close> by (rule subset_insertI2)
                have "insert G ({H} \<union> S') = {G} \<union> ({H} \<union> S')"
                  by (rule insert_is_Un)
                then have "S \<subseteq> {G} \<union> ({H} \<union> S')"
                  using \<open>S \<subseteq> insert G ({H} \<union> S')\<close> by simp (*Pendiente*)
                then have "S \<subseteq> {G,H} \<union> S'"
                  by auto (*Pendiente*)
                then have "{G,H} \<union> S \<subseteq> {G,H} \<union> S'"
                  by simp (*Pendiente*)
                thus "{G,H} \<union> S \<in> ?E"
                  using \<open>{G, H} \<union> S' \<in> C\<close> by blast (*Pendiente*)
              qed
            qed
          qed
        qed
      qed
      have 8:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
        using 6 by (rule conjunct2)
      have S4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
      proof (rule allI)
        fix F
        show "\<forall>G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
        proof (rule allI)
          fix G
          show "\<forall>H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
          proof (rule allI)
            fix H
            show "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
            proof (rule impI)
              assume "Dis F G H"
              show "F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
              proof (rule impI)
                assume "F \<in> S"
                have "F \<in> S'"
                  using \<open>S \<subseteq> S'\<close> \<open>F \<in> S\<close> by (rule set_mp)
                have "Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
                  using 8 by (iprover elim: allE)
                then have "F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
                  using \<open>Dis F G H\<close> by (rule mp)
                then have 9:"{G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
                  using \<open>F \<in> S'\<close> by (rule mp)
                show "{G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
                  using 9
                proof (rule disjE)
                  assume "{G} \<union> S' \<in> C"
                  have "{G} \<union> S' \<in> ?E"
                    using C1 \<open>{G} \<union> S' \<in> C\<close> by (rule set_mp)
                  have "S \<subseteq> insert G S'"
                    using \<open>S \<subseteq> S'\<close> by (rule subset_insertI2)
                  have "insert G S' = {G} \<union> S'"
                    by (rule insert_is_Un)
                  then have "S \<subseteq> {G} \<union> S'"
                    using \<open>S \<subseteq> insert G S'\<close> by simp (*Pendiente*)
                  then have "{G} \<union> S \<subseteq> {G} \<union> S'"
                    by simp (*Pendiente*)
                  then have "{G} \<union> S \<in> ?E"
                    using \<open>{G} \<union> S' \<in> C\<close> by blast (*Pendiente*)
                  thus "{G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
                    by (rule disjI1)
                next
                  assume "{H} \<union> S' \<in> C"
                  have "{H} \<union> S' \<in> ?E"
                    using C1 \<open>{H} \<union> S' \<in> C\<close> by (rule set_mp)
                  have "S \<subseteq> insert H S'"
                    using \<open>S \<subseteq> S'\<close> by (rule subset_insertI2)
                  have "insert H S' = {H} \<union> S'"
                    by (rule insert_is_Un)
                  then have "S \<subseteq> {H} \<union> S'"
                    using \<open>S \<subseteq> insert H S'\<close> by simp (*Pendiente*)
                  then have "{H} \<union> S \<subseteq> {H} \<union> S'"
                    by simp (*Pendiente*)
                  then have "{H} \<union> S \<in> ?E"
                    using \<open>{H} \<union> S' \<in> C\<close> by blast (*Pendiente*)
                  thus "{G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
                    by (rule disjI2)
                qed
              qed
            qed
          qed
        qed
      qed
      show "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E)"
        using S1 S2 S3 S4 by (iprover intro: conjI)
    qed
  qed
qed

lemma ex1_subset_closed:
  assumes "pcp C"
  shows "subset_closed {s. \<exists>S\<in>C. s \<subseteq> S}"
  unfolding subset_closed_def
proof (rule ballI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  fix S
  assume "S \<in> ?E"
  thus "\<forall>s \<subseteq> S. s \<in> ?E"
    by auto (*Pendiente*)
qed

lemma ex1_detallada:
  assumes "pcp C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof -
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  have C1:"C \<subseteq> ?E"
    by (rule ex1_subset)
  have C2:"pcp ?E"
    using assms by (rule ex1_pcp)
  have C3:"subset_closed ?E"
    using assms by (rule ex1_subset_closed)
  have "C \<subseteq> ?E \<and> pcp ?E \<and> subset_closed ?E" 
    using C1 C2 C3 by (iprover intro: conjI)
  thus ?thesis
    by (rule exI)
qed

text \<open>\comentario{Pendientes}\<close>

lemma ex1: "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof(intro exI[of _ "{s . \<exists>S \<in> C. s \<subseteq> S}"] conjI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  show "C \<subseteq> ?E" by blast
  show "subset_closed ?E" unfolding subset_closed_def by blast
  assume C: \<open>pcp C\<close>
  show "pcp ?E" using C unfolding pcp_alt
    by (intro ballI conjI; simp; meson insertI1 rev_subsetD subset_insertI subset_insertI2)
qed

text\<open>Lema auxiliar similar a ballI para contención y propiedades.\<close>

lemma 
  assumes "(\<And>s. s \<subseteq> S \<Longrightarrow> P s)"
  shows "\<forall>s \<subseteq> S. P s" 
proof (rule allI)
  fix s
  show "s \<subseteq> S \<longrightarrow> P s"
  proof (rule impI)
    assume "s \<subseteq> S"
    thus "P s" 
      by (rule assms)
  qed
qed

lemma sallI: "(\<And>s. s \<subseteq> S \<Longrightarrow> P s) \<Longrightarrow> \<forall>s \<subseteq> S. P s"
  by simp

text\<open> Lema: Si C tiene la propiedad de carácter finito, entonces C es 
cerrado bajo subconjunto.\<close>

lemma ex2_detallada:
  assumes "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix s S
  assume  \<open>S \<in> C\<close> and \<open>s \<subseteq> S\<close>
  then have "t \<subseteq> s \<Longrightarrow> s \<subseteq> S \<Longrightarrow> t \<subseteq> S" for t 
    by (simp only: subset_trans)
  have "\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C)"
    using assms unfolding finite_character_def by this
  then have 1:"S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C)"
    by (rule allE)
  have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
    using \<open>S \<in> C\<close> 1 by (rule back_subst)
  then have "t \<subseteq> S \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t 
    using \<open>S \<in> C\<close> by blast (*Pendiente*)
  then have "t \<subseteq> s \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t 
    using \<open>s \<subseteq> S\<close> \<open>t \<subseteq> s \<Longrightarrow> s \<subseteq> S \<Longrightarrow> t \<subseteq> S\<close> by simp
  with assms show \<open>s \<in> C\<close> unfolding finite_character_def by blast
qed

text \<open>\comentario{Pendiente}\<close>

lemma ex2: 
  assumes fc: "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix s S
  assume e: \<open>S \<in> C\<close> and s: \<open>s \<subseteq> S\<close>
  hence *: "t \<subseteq> s \<Longrightarrow> t \<subseteq> S" for t by simp
  from fc have "t \<subseteq> S \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t 
    unfolding finite_character_def using e by blast
  hence "t \<subseteq> s \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t using * by simp
  with fc show \<open>s \<in> C\<close> unfolding finite_character_def by blast
qed

text\<open>Lema: Si C tiene la propiedad de consistencia proposicional y es 
cerrado bajo subconjunto, entonces tiene un subconjunto con la propiedad
de consistencia proposicional y de carácter finito.\<close>

lemma ex3_finite_character:
  assumes "subset_closed C"
        shows "finite_character (C \<union> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C})"
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  show "finite_character (C \<union> ?E)"
    unfolding finite_character_def
  proof (rule allI)
   fix S
   show "S \<in> C \<union> ?E \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<union> ?E)"
   proof (rule iffI)
     assume "S \<in> C \<union> ?E"
     show "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<union> ?E"
     proof (intro sallI)
       fix s 
       assume "s \<subseteq> S"
       show "finite s \<longrightarrow> s \<in> C \<union> ?E"
       proof (rule impI)
         assume "finite s"
         have "S \<in> C \<or> S \<in> ?E"
           using \<open>S \<in> C \<union> ?E\<close> by simp (*Pendiente*)
         thus "s \<in> C \<union> ?E"
         proof (rule disjE)
           assume "S \<in> C"
           have "\<forall>S \<in> C. \<forall>s \<subseteq> S. s \<in> C"
             using assms by (simp only: subset_closed_def)
           then have "\<forall>s \<subseteq> S. s \<in> C"
             using \<open>S \<in> C\<close> by blast (*Pendiente*)
           then have "s \<in> C"
             using \<open>s \<subseteq> S\<close> by blast (*Pendiente*)
           thus "s \<in> C \<union> ?E"
             by blast (*Pendiente*)
         next
           assume "S \<in> ?E"
           then have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
             by simp (*Pendiente*)
           then have "finite s \<longrightarrow> s \<in> C"
             using \<open>s \<subseteq> S\<close> by blast (*Pendiente*)
           then have "s \<in> C"
             using \<open>finite s\<close> by (rule mp)
           thus "s \<in> C \<union> ?E"
             by blast (*Pendiente*)
        qed
       qed
      qed
   next
     assume "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<union> ?E"
     then have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<or> s \<in> ?E"
       by simp (*Pendiente*)
     then have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<or> s \<in> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
       by simp (*Pendiente*)
     then have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
       by blast (*Pendiente*)
     then have "S \<in> ?E"
       by simp (*Pendiente*)
     thus "S \<in> C \<union> ?E"
       by simp (*Pendiente*)
   qed
 qed
qed

lemma ex3_pcp_CON:
  assumes "pcp C"
          "subset_closed C"
          "\<And>s. \<lbrakk>s\<subseteq>S; finite s\<rbrakk> \<Longrightarrow> s \<in> C"
          "Con F G H"
          "F \<in> S"
  shows "{G,H} \<union> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have 1:"\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have 2:"\<forall>s \<subseteq> S. finite s \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
  proof (rule sallI)
    fix s
    assume "s \<subseteq> S"
    show "finite s \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
    proof (rule impI)
      assume "finite s"
      show "F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
      proof (rule impI)
        assume "F \<in> s" 
        have "s \<in> C"
          using \<open>s \<subseteq> S\<close> \<open>finite s\<close> by (rule assms(3))
        have "\<forall>F G H. Con F G H \<longrightarrow> F \<in> s \<longrightarrow> {G, H} \<union> s \<in> C"
          using 1 \<open>s \<in> C\<close> by blast (*Pendiente*)
        then have "Con F G H \<longrightarrow> F \<in> s \<longrightarrow> {G, H} \<union> s \<in> C"
          by (iprover elim: allE)
        then have "F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
          using assms(4) by (rule mp)
        thus "{G, H} \<union> s \<in> C"
          using \<open>F \<in> s\<close> by (rule mp)
      qed
    qed
  qed
  have "{G,H} \<union> S \<in> ?E"
    unfolding mem_Collect_eq Un_iff
  proof (rule sallI)
    fix s
    assume H:"s \<subseteq> {G,H} \<union> S"
    show "finite s \<longrightarrow> s \<in> C"
    proof (rule impI)
      assume "finite s"
      have "insert F  (s - {G,H}) \<subseteq> S" 
        using assms(5) H by blast (*Pendiente*)
      then have "insert G  (insert H (insert F (s - {G,H}))) \<in> C"
        using 2 \<open>finite s\<close> by simp (*Pendiente*)
      then have "insert F (insert G (insert H  s)) \<in> C" 
        using insert_absorb by fastforce (*Pendiente*)
      thus "s \<in> C" 
        using assms(2) unfolding subset_closed_def by fast (*Pendiente*) 
    qed
  qed
  thus "{G, H} \<union> S \<in> C \<union> ?E" 
    by simp (*Pendiente*)
qed

text \<open>\comentario{No se como integrarlo como lema auxiliar en ex3pcp.}\<close>

lemma ex3_pcp_DIS:
  assumes "pcp C"
          "subset_closed C"
          "\<And>s. \<lbrakk>s\<subseteq>S; finite s\<rbrakk> \<Longrightarrow> s \<in> C"
          "Dis F G H"
          "F \<in> S"
  shows "insert G S \<in> (C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}) \<or> insert H S \<in> (C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C})"
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have 1:"\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have H1:"\<exists>I\<in>{G,H}. insert I s1 \<in> C \<and> insert I s2 \<in> C" 
        if "s1 \<subseteq> S" "finite s1" "F \<in> s1" 
          "s2 \<subseteq> S" "finite s2" "F \<in> s2" for s1 s2
  proof -
    let ?s = "s1 \<union> s2"
    have "?s \<subseteq> S" "finite ?s" 
      using that by simp_all (*Pendiente*)
    then have "?s \<in> C" 
      using assms(3) by simp (*Pendiente*)
    then have "F \<in> ?s" 
      using that by simp (*Pendiente*)
    have "\<bottom> \<notin> ?s
  \<and> (\<forall>k. Atom k \<in> ?s \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?s \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G,H} \<union> ?s \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C)"
      using 1 \<open>?s \<in> C\<close> by (rule bspec)
    then have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
      by (iprover elim: conjunct2)
    then have "Dis F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
      by (iprover elim: allE)
    then have "F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
      using assms(4) by (rule mp)
    then have "{G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
      using \<open>F \<in> ?s\<close> by (rule mp)
    then have "\<exists>I\<in>{G,H}. insert I ?s \<in> C" 
      by simp (*Pendiente*)
    thus "\<exists>I\<in>{G,H}. insert I s1 \<in> C \<and> insert I s2 \<in> C"
      by (meson assms(2)[unfolded subset_closed_def, THEN bspec] insert_mono sup.cobounded2 sup_ge1) (*Pendiente*)
  qed
  have H2:"\<lbrakk>s1 \<subseteq> S; finite s1; F \<in> s1; insert G s1 \<notin> C; s2 \<subseteq> S; finite s2; F \<in> s2; insert H s2 \<notin> C\<rbrakk> \<Longrightarrow> False" for s1 s2
    using H1 by blast (*Pendiente*)
  have "False" if "s1 \<subseteq> S" "finite s1" "insert G s1 \<notin> C" "s2 \<subseteq> S" "finite s2" "insert H s2 \<notin> C" for s1 s2
  proof -
    have *: "insert F  s1 \<subseteq> S" "finite (insert F  s1)" "F \<in> insert F s1" if  "s1 \<subseteq> S" "finite s1" for s1
      using that assms(5) by simp_all (*Pendiente*)
    have  "insert G (insert F s1) \<notin> C" "insert H (insert F s2) \<notin> C" 
      by (meson assms(2) insert_mono subset_closed_def subset_insertI that(3,6))+ (*Pendiente*)
    from H2[OF *[OF that(1-2)] this(1) *[OF that(4-5)] this(2)]
    show False . (*Pendiente*)
  qed
  then have "insert G S \<in> ?E \<or> insert H S \<in> ?E"
    unfolding mem_Collect_eq Un_iff
    by (metis (no_types, lifting) finite_Diff insert_Diff assms(3) subset_insert_iff) (*Pendiente*)
  then have "{G} \<union> S \<in> C \<union> ?E \<or> insert H S \<in> C \<union> ?E" 
    by blast (*Pendiente*)
  thus ?thesis
    by simp (*Pendiente*)
qed

text \<open>\comentario{No se como integrarlo como lema auxiliar en ex3pcp.}\<close>

lemma ex3_pcp:
  assumes "pcp C"
          "subset_closed C"
        shows "pcp (C \<union> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C})"
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have 1:"\<forall>S \<in> C.
  \<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have CON: "{G,H} \<union> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
             if H1:"\<And>s. \<lbrakk>s\<subseteq>S; finite s\<rbrakk> \<Longrightarrow> s \<in> C" and
    H2:"Con F G H" and H3:"F \<in> S" for F G H S 
  proof -
    have 2:"\<forall>s \<subseteq> S. finite s \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
    proof (rule sallI)
      fix s
      assume "s \<subseteq> S"
      show "finite s \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
      proof (rule impI)
        assume "finite s"
        show "F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
        proof (rule impI)
          assume "F \<in> s" 
          have "s \<in> C"
            using \<open>s \<subseteq> S\<close> \<open>finite s\<close> by (rule H1)
          have "\<forall>F G H. Con F G H \<longrightarrow> F \<in> s \<longrightarrow> {G, H} \<union> s \<in> C"
            using 1 \<open>s \<in> C\<close> by blast (*Pendiente*)
          then have "Con F G H \<longrightarrow> F \<in> s \<longrightarrow> {G, H} \<union> s \<in> C"
            by (iprover elim: allE)
          then have "F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
            using H2 by (rule mp)
          thus "{G, H} \<union> s \<in> C"
            using \<open>F \<in> s\<close> by (rule mp)
        qed
      qed
    qed
    have "{G,H} \<union> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff
    proof (rule sallI)
      fix s
      assume H:"s \<subseteq> {G,H} \<union> S"
      show "finite s \<longrightarrow> s \<in> C"
      proof (rule impI)
        assume "finite s"
        have "insert F  (s - {G,H}) \<subseteq> S" 
          using H3 H by blast (*Pendiente*)
        then have "insert G  (insert H (insert F (s - {G,H}))) \<in> C"
          using 2 \<open>finite s\<close> by simp (*Pendiente*)
        then have "insert F (insert G (insert H  s)) \<in> C" 
          using insert_absorb by fastforce (*Pendiente*)
        thus "s \<in> C" 
          using assms(2) unfolding subset_closed_def by fast (*Pendiente*) 
      qed
    qed
    thus "{G, H} \<union> S \<in> C \<union> ?E" 
      by simp (*Pendiente*)
  qed   
  have DIS: "{G} \<union> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> insert H S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
    if H4:"\<And>s. s\<subseteq>S \<Longrightarrow> finite s \<Longrightarrow> s \<in> C" and H5:"Dis F G H" and H6:"F \<in> S"
    for F G H S 
  proof -
    have l: "\<exists>I\<in>{G,H}. insert I s1 \<in> C \<and> insert I s2 \<in> C" 
        if "s1 \<subseteq> S" "finite s1" "F \<in> s1" 
          "s2 \<subseteq> S" "finite s2" "F \<in> s2" for s1 s2
    proof -
      let ?s = "s1 \<union> s2"
      have "?s \<subseteq> S" "finite ?s" 
        using that by simp_all (*Pendiente*)
      then have "?s \<in> C" 
        using H4 by simp (*Pendiente*)
      then have "F \<in> ?s" 
        using that by simp (*Pendiente*)
      have "\<bottom> \<notin> ?s
  \<and> (\<forall>k. Atom k \<in> ?s \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?s \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G,H} \<union> ?s \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C)"
        using 1 \<open>?s \<in> C\<close> by (rule bspec)
      then have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
        by (iprover elim: conjunct2)
      then have "Dis F G H \<longrightarrow> F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
        by (iprover elim: allE)
      then have "F \<in> ?s \<longrightarrow> {G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
        using H5 by (rule mp)
      then have "{G} \<union> ?s \<in> C \<or> {H} \<union> ?s \<in> C"
        using \<open>F \<in> ?s\<close> by (rule mp)
      then have "\<exists>I\<in>{G,H}. insert I ?s \<in> C" 
        by simp (*Pendiente*)
      thus "\<exists>I\<in>{G,H}. insert I s1 \<in> C \<and> insert I s2 \<in> C"
        by (meson assms(2)[unfolded subset_closed_def, THEN bspec] insert_mono sup.cobounded2 sup_ge1) (*Pendiente*)
    qed
    have H7:"\<lbrakk>s1 \<subseteq> S; finite s1; F \<in> s1; insert G s1 \<notin> C; s2 \<subseteq> S; finite s2; F \<in> s2; insert H s2 \<notin> C\<rbrakk> \<Longrightarrow> False" for s1 s2
      using l by blast (*Pendiente*)
    have "False" if "s1 \<subseteq> S" "finite s1" "insert G s1 \<notin> C" "s2 \<subseteq> S" "finite s2" "insert H s2 \<notin> C" for s1 s2
    proof -
      have *: "insert F  s1 \<subseteq> S" "finite (insert F  s1)" "F \<in> insert F s1" if  "s1 \<subseteq> S" "finite s1" for s1
        using that H6 by simp_all (*Pendiente*)
      have  "insert G (insert F s1) \<notin> C" "insert H (insert F s2) \<notin> C" 
        by (meson assms(2) insert_mono subset_closed_def subset_insertI that(3,6))+ (*Pendiente*)
      from H7[OF *[OF that(1-2)] this(1) *[OF that(4-5)] this(2)]
      show False . (*Pendiente*)
    qed
    then have "insert G S \<in> ?E \<or> insert H S \<in> ?E"
      unfolding mem_Collect_eq Un_iff
      by (metis (no_types, lifting) finite_Diff insert_Diff H4 subset_insert_iff) (*Pendiente*)
    then have "{G} \<union> S \<in> C \<union> ?E \<or> insert H S \<in> C \<union> ?E" 
      by blast (*Pendiente*)
    thus ?thesis
      by simp (*Pendiente*)
  qed
  have CON': "\<And>f2 g2 h2 F2 G2 S2. \<lbrakk>\<And>s. \<lbrakk>s \<in> C; h2 F2 G2 \<in> s\<rbrakk> \<Longrightarrow> f2 insert F2 s \<in> C \<or> g2 insert G2 s \<in> C; 
                                   \<forall>s\<subseteq>S2. finite s \<longrightarrow> s \<in> C; h2 F2 G2 \<in> S2; False\<rbrakk>
      \<Longrightarrow> f2 insert F2 S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> g2 insert G2 S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
  by fast (*Pendiente*)
  show "pcp (C \<union> ?E)" 
    unfolding pcp_alt
  proof (rule ballI)
    fix S
    assume "S \<in> C \<union> ?E"
    show "\<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E)"
      using \<open>S \<in> C \<union> ?E\<close>
    proof (rule UnE)
      assume "S \<in> C"
      have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
        using 1 \<open>S \<in> C\<close> by auto (*Pendiente*)
      thus "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E)"
        by blast (*Pendiente*)
    next
      assume "S \<in> ?E"
      then have E:"\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
        by simp (*Pendiente*)
      have "{} \<subseteq> S"
        by (rule empty_subsetI)
      have "finite {}"
        by (rule finite.emptyI)
      have "finite {} \<longrightarrow> {} \<in> C"
        using E \<open>{} \<subseteq> S\<close> by blast (*Pendiente*)
      then have "{} \<in> C"
        using \<open>finite {}\<close> by (rule mp)
      have "\<bottom> \<notin> {}
  \<and> (\<forall>k. Atom k \<in> {} \<longrightarrow> \<^bold>\<not> (Atom k) \<in> {} \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> {} \<longrightarrow> {G,H} \<union> {} \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> {} \<longrightarrow> {G} \<union> {} \<in> C \<or> {H} \<union> {} \<in> C)"
        using 1 \<open>{} \<in> C\<close> by auto (*Pendiente*)
    oops
    (*apply(intro ballI conjI; elim UnE; (unfold mem_Collect_eq)?)
           subgoal using C'' by blast
          subgoal using C'' by blast
         subgoal using C'' by (simp;fail)
        subgoal by (meson C'' empty_subsetI finite.emptyI finite_insert insert_subset subset_insertI)
       subgoal using C'' by simp
      subgoal using CON by simp
     subgoal using C'' by blast
    subgoal using DIS by simp
  done
qed*)

lemma ex3_detallada:
  assumes "pcp C"
          "subset_closed C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have C1:"C \<subseteq> C \<union> ?E" 
    by simp (*Pendiente*)
  have C2:"finite_character (C \<union> ?E)"
    using assms(2) by (rule ex3_finite_character)
  have C3:"pcp (C \<union> ?E)"
    oops

lemma ex3:
  assumes C: "pcp C"
  assumes S: "subset_closed C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof(intro exI[of _ "C \<union> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"] conjI)
  let ?E = " {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  show "C \<subseteq> C \<union> ?E" by blast
  from S show "finite_character (C \<union> ?E)" 
    unfolding finite_character_def subset_closed_def by blast
  note C'' = C[unfolded pcp_alt, THEN bspec]
  have CON: "{G,H} \<union> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
             if si: "\<And>s. \<lbrakk>s\<subseteq>S; finite s\<rbrakk> \<Longrightarrow> s \<in> C" and
    un: "Con F G H" and el: "F \<in> S" for F G H S 
  proof -
    have k: "\<forall>s \<subseteq> S. finite s \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
      using si un C'' by simp
    have "{G,H} \<union> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff 
    proof safe
      fix s
      assume "s \<subseteq> {G,H} \<union> S" and f: "finite s"
      hence "insert F  (s - {G,H}) \<subseteq> S" using el by blast
      with k f have "insert G  (insert H (insert F (s - {G,H}))) \<in> C" by simp
      hence "insert F (insert G (insert H  s)) \<in> C" using insert_absorb by fastforce
      thus "s \<in> C" using S unfolding subset_closed_def by fast  
    qed
    thus "{G, H} \<union> S \<in> C \<union> ?E" by simp
  qed
  have DIS: "{G}\<union> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> insert H S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
    if si: "\<And>s. s\<subseteq>S \<Longrightarrow> finite s \<Longrightarrow> s \<in> C" and un: "Dis F G H" and el: "F \<in> S"
    for F G H S 
  proof -
    have l: "\<exists>I\<in>{G, H}. insert I s1 \<in> C \<and> insert I s2 \<in> C" 
      if "s1 \<subseteq> S" "finite s1" "F \<in> s1" 
         "s2 \<subseteq> S" "finite s2" "F \<in> s2" for s1 s2
    proof -
      let ?s = "s1 \<union> s2"
      have "?s \<subseteq> S" "finite ?s" using that by simp_all 
      with si have "?s \<in> C" by simp
      moreover have "F \<in> ?s" using that by simp
      ultimately have "\<exists>I\<in>{G,H}. insert I ?s \<in> C"
        using C'' un by simp
      thus "\<exists>I\<in>{G,H}. insert I s1 \<in> C \<and> insert I s2 \<in> C"
        by (meson S[unfolded subset_closed_def, THEN bspec] insert_mono sup.cobounded2 sup_ge1)
    qed
    have m: "\<lbrakk>s1 \<subseteq> S; finite s1; F \<in> s1; insert G s1 \<notin> C; s2 \<subseteq> S; finite s2; F \<in> s2; insert H s2 \<notin> C\<rbrakk> \<Longrightarrow> False" for s1 s2
      using l by blast
    have "False" if "s1 \<subseteq> S" "finite s1" "insert G s1 \<notin> C" "s2 \<subseteq> S" "finite s2" "insert H s2 \<notin> C" for s1 s2
    proof -
      have *: "insert F  s1 \<subseteq> S" "finite (insert F  s1)" "F \<in> insert F s1" if  "s1 \<subseteq> S" "finite s1" for s1
        using that el by simp_all
      have  "insert G (insert F s1) \<notin> C" "insert H (insert F s2) \<notin> C" 
        by (meson S insert_mono subset_closed_def subset_insertI that(3,6))+
      from m[OF *[OF that(1-2)] this(1) *[OF that(4-5)] this(2)]
      show False .
    qed
    hence "insert G S \<in> ?E \<or> insert H S \<in> ?E"
      unfolding mem_Collect_eq Un_iff
      by (metis (no_types, lifting) finite_Diff insert_Diff si subset_insert_iff)
    thus "{G}\<union> S \<in> C \<union> ?E \<or> insert H S \<in> C \<union> ?E" by blast
  qed 
  have CON': "\<And>f2 g2 h2 F2 G2 S2. \<lbrakk>\<And>s. \<lbrakk>s \<in> C; h2 F2 G2 \<in> s\<rbrakk> \<Longrightarrow> f2 insert F2 s \<in> C \<or> g2 insert G2 s \<in> C; 
                                   \<forall>s\<subseteq>S2. finite s \<longrightarrow> s \<in> C; h2 F2 G2 \<in> S2; False\<rbrakk>
      \<Longrightarrow> f2 insert F2 S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> g2 insert G2 S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
    by fast
  show "pcp (C \<union> ?E)" unfolding pcp_alt
    apply(intro ballI conjI; elim UnE; (unfold mem_Collect_eq)?)
           subgoal using C'' by blast
          subgoal using C'' by blast
         subgoal using C'' by (simp;fail)
        subgoal by (meson C'' empty_subsetI finite.emptyI finite_insert insert_subset subset_insertI)
       subgoal using C'' by simp
      subgoal using CON by simp
     subgoal using C'' by blast
    subgoal using DIS by simp
  done
qed

text\<open> Definición: definición de una sucesión de conjuntos a partir de 
C y S: \<open>S_0, S_1,...,S_n,...\<close>\<close>

primrec pcp_seq where
"pcp_seq C S 0 = S" |
"pcp_seq C S (Suc n) = (let Sn = pcp_seq C S n; Sn1 = insert (from_nat n) Sn in
                        if Sn1 \<in> C then Sn1 else Sn)" 

text\<open>Lema: Si C tiene la propiedad de consistencia proposicional y S 
pertenece a C, todos los conjuntos de la sucesión están en C.\<close>

text \<open>He introducido una instancia en Sintaxis que señala que las fórmulas
  son contables si sus átomos lo son. En caso contrario hay interferencias
  entre los tipos.\<close>

lemma pcp_seq_in_detallada: 
  assumes "pcp C" 
          "S \<in> C"
        shows "pcp_seq C S n \<in> C"
proof (induction n)
  show "pcp_seq C S 0 \<in> C"
    by (simp only: pcp_seq.simps(1) \<open>S \<in> C\<close>)
next
  fix n
  assume HI:"pcp_seq C S n \<in> C"
  then have "(if (insert (from_nat n) (pcp_seq C S n) \<in> C) then (insert (from_nat n) (pcp_seq C S n))
        else (pcp_seq C S n)) \<in> C"
    by simp (*Pendiente*)
  then have "(let Sn = pcp_seq C S n; Sn1 = insert (from_nat n) Sn in
                        if Sn1 \<in> C then Sn1 else Sn) \<in> C"
    by (simp only: Let_def)
  thus "pcp_seq C S (Suc n) \<in> C"
    by (simp only: pcp_seq.simps(2))
qed

text \<open>\comentario{Entender y terminar.}\<close>

lemma pcp_seq_in: "pcp C \<Longrightarrow> S \<in> C \<Longrightarrow> pcp_seq C S n \<in> C"
proof(induction n)
  case (Suc n)  
  hence "pcp_seq C S n \<in> C" by simp
  thus ?case by (simp add: Let_def)
qed simp

text\<open>Lema: la sucesión es monónota.\<close>

lemma pcp_seq_mono_detallada: "n \<le> m \<Longrightarrow> pcp_seq C S n \<subseteq> pcp_seq C S m"
proof(induction m)
  assume "n \<le> 0" 
  then have "n = 0"
    by (simp only: canonically_ordered_monoid_add_class.le_zero_eq)
  thus "pcp_seq C S n \<subseteq> pcp_seq C S 0"
    by (simp only: subset_refl)
next
  fix m
  assume HI:"n \<le> m \<Longrightarrow> pcp_seq C S n \<subseteq> pcp_seq C S m"
  assume "n \<le> Suc m"
  then have "n \<le> m \<or> n = Suc m"
    by (simp only: le_Suc_eq)
  thus "pcp_seq C S n \<subseteq> pcp_seq C S (Suc m)"
  proof (rule disjE)
    assume "n \<le> m"
    have "pcp_seq C S n \<subseteq> pcp_seq C S m"
      using \<open>n \<le> m\<close> by (simp only: HI)
    then have "pcp_seq C S n \<subseteq> (if (insert (from_nat m) (pcp_seq C S m) \<in> C) then (insert (from_nat m) (pcp_seq C S m))
          else (pcp_seq C S m))"
      by auto (*Pendiente*)
    then have "pcp_seq C S n \<subseteq> (let Sn = pcp_seq C S m; Sn1 = insert (from_nat m) Sn in
                        if Sn1 \<in> C then Sn1 else Sn)"
      by (simp only: Let_def)
    thus "pcp_seq C S n \<subseteq> pcp_seq C S (Suc m)"
      by (simp only: pcp_seq.simps(2))
  next
    assume "n = Suc m"
    thus "pcp_seq C S n \<subseteq> pcp_seq C S (Suc m)"
      by (simp only: subset_refl)
  qed
qed

lemma pcp_seq_mono: "n \<le> m \<Longrightarrow> pcp_seq C S n \<subseteq> pcp_seq C S m"
proof(induction m)
  case (Suc m)
  thus ?case by(cases "n = Suc m"; simp add: Let_def; blast)
qed simp

lemma pcp_seq_UN_detallada: "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof(induct m)
  have "\<Union>{pcp_seq C S n|n. n \<le> 0} = \<Union>{pcp_seq C S n|n. n = 0}"
    by (simp only: canonically_ordered_monoid_add_class.le_zero_eq)
  also have "\<dots> = \<Union>{pcp_seq C S 0}"
    by simp
  also have "\<dots> = (pcp_seq C S 0) \<union> \<Union>{}"
    by (simp only: complete_lattice_class.Sup_insert)
  also have "\<dots> = (pcp_seq C S 0) \<union> {}"
    by (simp only: complete_lattice_class.Sup_empty)
  also have "\<dots> = pcp_seq C S 0"
    by (simp only: bounded_semilattice_sup_bot_class.sup_bot.right_neutral)
  finally show "\<Union>{pcp_seq C S n|n. n \<le> 0} = pcp_seq C S 0" 
    by this
next
  fix m
  assume HI:"\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
  have "0 \<le> Suc 0"
    by (simp only: canonically_ordered_monoid_add_class.zero_le)
  then have "0 + m \<le> Suc 0 + m"
    by (simp only: ordered_ab_semigroup_add_imp_le_class.add_le_cancel_right)
  then have "0 + m \<le> Suc (0 + m)"
    by (simp only: plus_nat.add_Suc)
  then have "m \<le> Suc m" 
    by (simp only: monoid_add_class.add_0_right)
  have 1:"pcp_seq C S m \<subseteq> pcp_seq C S (Suc m)"
    using \<open>m \<le> Suc m\<close> by (rule pcp_seq_mono)
  have "{pcp_seq C S n |n. n \<le> Suc m} = {pcp_seq C S n |n. (n \<le> m \<or> n = Suc m)}"
    by (simp only: le_Suc_eq)
  also have "\<dots> = insert (pcp_seq C S (Suc m)) {pcp_seq C S n |n. n \<le> m}"
    by blast (*Pendiente*)
  finally have 2:"{pcp_seq C S n |n. n \<le> Suc m} = 
          insert (pcp_seq C S (Suc m)) {pcp_seq C S n |n. n \<le> m}"
    by this
  have "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = \<Union>{pcp_seq C S n |n. n \<le> m} \<union> pcp_seq C S (Suc m)" 
    using 2 by auto
  also have "\<dots> = pcp_seq C S m \<union> pcp_seq C S (Suc m)"
    by (simp only: HI)
  also have "\<dots> = pcp_seq C S (Suc m)"
    using 1 by (simp only: subset_Un_eq)
  finally show "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = pcp_seq C S (Suc m)"
    by this
qed

lemma pcp_seq_UN: "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof(induction m)
  case (Suc m)
  have "{f n |n. n \<le> Suc m} = insert (f (Suc m)) {f n |n. n \<le> m}" 
    for f using le_Suc_eq by auto
  hence "{pcp_seq C S n |n. n \<le> Suc m} = 
          insert (pcp_seq C S (Suc m)) {pcp_seq C S n |n. n \<le> m}" .
  hence "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = 
         \<Union>{pcp_seq C S n |n. n \<le> m} \<union> pcp_seq C S (Suc m)" by auto
  thus ?case using Suc pcp_seq_mono by blast
qed simp

text\<open>
lemma \<open>wont_get_added:\<close>
\<open>"(F :: ('a :: countable) formula) \<notin> pcp_seq C S (Suc (to_nat F)) \<Longrightarrow> 
F \<notin> pcp_seq C S (Suc (to_nat F) + n)"\<close>
text\<open>We don't necessarily have @{term "n = to_nat (from_nat n)"}, so this doesn't hold.\<close>
\<close>

definition "pcp_lim C S \<equiv> \<Union>{pcp_seq C S n|n. True}"

lemma pcp_seq_sub_detallada: "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def
proof (induction n)
  have "pcp_seq C S 0 \<in> {pcp_seq C S 0}" 
    by (simp only: singletonI)
  thus "pcp_seq C S 0 \<subseteq> \<Union> {pcp_seq C S n|n. True}"
    by blast (*Pendiente*)
next
  fix n
  assume "pcp_seq C S n \<subseteq> \<Union>{pcp_seq C S n|n. True}"
  show "pcp_seq C S (Suc n) \<subseteq> \<Union>{pcp_seq C S n|n. True}"
    by blast (*Pendiente*)
qed

lemma pcp_seq_sub: "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def by(induction n; blast)

lemma pcp_lim_inserted_at_ex_detallada: 
  assumes "x \<in> pcp_lim C S"
  shows "\<exists>k. x \<in> pcp_seq C S k"
proof -
  have "x \<in> \<Union>{pcp_seq C S n|n. True}"
    using assms by (simp only: pcp_lim_def)
  thus "\<exists>k. x \<in> pcp_seq C S k" 
    by blast (*Pendiente*)
qed

lemma pcp_lim_inserted_at_ex: 
    "x \<in> pcp_lim C S \<Longrightarrow> \<exists>k. x \<in> pcp_seq C S k"
  unfolding pcp_lim_def by blast

lemma pcp_lim_in_detallada:
  assumes "pcp C"
          "S \<in> C"
          "subset_closed C"
          "finite_character C"
  shows "pcp_lim C S \<in> C" (is "?cl \<in> C")
proof -
  have "\<forall>n. pcp_seq C S n \<in> C" 
  proof (rule allI)
    fix n
    show "pcp_seq C S n \<in> C" 
      using assms(1) assms(2) by (rule pcp_seq_in)
  qed
  then have "\<forall>m. \<Union>{pcp_seq C S n|n. n \<le> m} \<in> C" 
    unfolding pcp_seq_UN by this
  have "\<forall>s \<subseteq> ?cl. finite s \<longrightarrow> s \<in> C" (*Pendiente*)
  proof safe
    fix s :: "'a formula set"
    have "pcp_seq C S (Suc (Max (to_nat ` s))) \<subseteq> pcp_lim C S" 
      using pcp_seq_sub by blast
    assume \<open>finite s\<close> \<open>s \<subseteq> pcp_lim C S\<close>
    hence "\<exists>k. s \<subseteq> pcp_seq C S k" 
    proof(induction s rule: finite_induct) 
      case (insert x s)
      hence "\<exists>k. s \<subseteq> pcp_seq C S k" by fast
      then guess k1 ..
      moreover obtain k2 where "x \<in> pcp_seq C S k2"
        by (meson pcp_lim_inserted_at_ex insert.prems insert_subset)
      ultimately have "insert x s \<subseteq> pcp_seq C S (max k1 k2)"
        by (meson pcp_seq_mono dual_order.trans insert_subset max.bounded_iff order_refl subsetCE)
      thus ?case by blast
    qed simp
    with pcp_seq_in[OF assms(1) assms(2)] assms(3)
    show "s \<in> C" 
      unfolding subset_closed_def by blast
  qed
  thus "?cl \<in> C" 
    using assms(4) unfolding finite_character_def by blast
qed

lemma pcp_lim_in:
  assumes c: "pcp C"
  and el: "S \<in> C"
  and sc: "subset_closed C"
  and fc: "finite_character C"
  shows "pcp_lim C S \<in> C" (is "?cl \<in> C")
proof -
  from pcp_seq_in[OF c el, THEN allI] have "\<forall>n. pcp_seq C S n \<in> C" .
  hence "\<forall>m. \<Union>{pcp_seq C S n|n. n \<le> m} \<in> C" unfolding pcp_seq_UN .
  
  have "\<forall>s \<subseteq> ?cl. finite s \<longrightarrow> s \<in> C"
  proof safe
    fix s :: "'a formula set"
    have "pcp_seq C S (Suc (Max (to_nat ` s))) \<subseteq> pcp_lim C S" 
      using pcp_seq_sub by blast
    assume \<open>finite s\<close> \<open>s \<subseteq> pcp_lim C S\<close>
    hence "\<exists>k. s \<subseteq> pcp_seq C S k" 
    proof(induction s rule: finite_induct) 
      case (insert x s)
      hence "\<exists>k. s \<subseteq> pcp_seq C S k" by fast
      then guess k1 ..
      moreover obtain k2 where "x \<in> pcp_seq C S k2"
        by (meson pcp_lim_inserted_at_ex insert.prems insert_subset)
      ultimately have "insert x s \<subseteq> pcp_seq C S (max k1 k2)"
        by (meson pcp_seq_mono dual_order.trans insert_subset max.bounded_iff order_refl subsetCE)
      thus ?case by blast
    qed simp
    with pcp_seq_in[OF c el] sc
    show "s \<in> C" unfolding subset_closed_def by blast
  qed
  thus "?cl \<in> C" using fc unfolding finite_character_def by blast
qed
  
lemma cl_max:
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  assumes el: "K \<in> C"
  assumes su: "pcp_lim C S \<subseteq> K"
  shows "pcp_lim C S = K" (is ?e)
proof (rule ccontr)
  assume \<open>\<not>?e\<close>
  with su have "pcp_lim C S \<subset> K" by simp
  then obtain F where e: "F \<in> K" and ne: "F \<notin> pcp_lim C S" by blast
  from ne have "F \<notin> pcp_seq C S (Suc (to_nat F))" using pcp_seq_sub by fast
  hence 1: "insert F (pcp_seq C S (to_nat F)) \<notin> C" by (simp add: Let_def split: if_splits)
  have "insert F (pcp_seq C S (to_nat F)) \<subseteq> K" using pcp_seq_sub e su by blast
  hence "insert F (pcp_seq C S (to_nat F)) \<in> C" using sc 
    unfolding subset_closed_def using el by blast
  with 1 show False ..
qed

lemma cl_max':
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  shows "insert F (pcp_lim C S) \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
    "insert F (insert G (pcp_lim C S)) \<in> C \<Longrightarrow> F \<in> pcp_lim C S \<and> G \<in> pcp_lim C S"
using cl_max[OF assms] by blast+

lemma pcp_lim_Hintikka:
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  assumes fc: "finite_character C"
  assumes el: "S \<in> C"
  shows "Hintikka (pcp_lim C S)"
proof -
  let ?cl = "pcp_lim C S"
  have "?cl \<in> C" using pcp_lim_in[OF c el sc fc] .
  from c[unfolded pcp_alt, THEN bspec, OF this]
  have d: "\<bottom> \<notin> ?cl"
    "Atom k \<in> ?cl \<Longrightarrow> \<^bold>\<not> (Atom k) \<in> ?cl \<Longrightarrow> False"
    "Con F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> insert G (insert H ?cl) \<in> C"
    "Dis F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> insert G ?cl \<in> C \<or> insert H ?cl \<in> C"
  for k F G H by force+
  have "Con F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
       "Dis F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
    for F G H
       by(auto dest: d(3-) cl_max'[OF c sc])
  with d(1,2) show ?thesis unfolding Hintikka_alt by fast
qed
  
theorem pcp_sat: \<comment> \<open>model existence theorem\<close>
  fixes S :: "'a :: countable formula set"
  assumes c: "pcp C"
  assumes el: "S \<in> C"
  shows "sat S"
proof -
  note [[show_types]]
  from c obtain Ce where 
      "C \<subseteq> Ce" "pcp Ce" "subset_closed Ce" "finite_character Ce" 
      using ex1[where 'a='a] ex2[where 'a='a] ex3[where 'a='a]
    by (meson dual_order.trans ex2)
  have "S \<in> Ce" using \<open>C \<subseteq> Ce\<close> el ..
  with pcp_lim_Hintikka \<open>pcp Ce\<close> \<open>subset_closed Ce\<close> \<open>finite_character Ce\<close>
  have  "Hintikka (pcp_lim Ce S)" .
  with Hintikkaslemma have "sat (pcp_lim Ce S)" .
  moreover have "S \<subseteq> pcp_lim Ce S" 
    using pcp_seq.simps(1) pcp_seq_sub by fast
  ultimately show ?thesis unfolding sat_def by fast
qed

(* This and Hintikka's lemma are the only two where we need semantics. 
   Still, I don't think it's meaningful to separate those two into 
   an extra theory. *)

(*<*)
end
(*>*) 
