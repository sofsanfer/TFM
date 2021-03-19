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

text \<open>\comentario{Voy por aquí en redacción.}\<close>

text \<open>Ejemplos:\<close>

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

text\<open> Lema: caracterización de los conjuntos de Hintikka mediante las 
fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>.\<close>

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
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)"
          using C31 C32 by (rule conjI)
        then have "((\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S))
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
          using C33 by (rule conjI)
        then have "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
          by blast (*Pendiente*) (*conj_assoc*)
        then have "((\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S))
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)" 
          using C34 by (rule conjI)
        then have "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)" 
          by blast (*Pendiente*) (*conj_assoc*)
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
        \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S)"
          using C41 C42 by (rule conjI)
        then have "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
        \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)"
          using C43 by blast (*Pendiente*)
        then have "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
        \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S)
        \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S)
        \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)"
          using C44 by blast (*Pendiente*)
        thus "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          by (rule Hintikka_alt1Dis)
      qed
    qed
  qed
  have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
    using C1 C2 by (rule conjI)
  then have "(\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False))
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)"
    using C3 by (rule conjI)
  then have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)"
    by simp (*Pendiente*)
  then have "(\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S))
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    using C4 by (rule conjI)
  thus "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    by simp (*Pendiente*)
qed

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
      have "Con (\<^bold>\<not>(\<^bold>\<not> G)) G G \<longrightarrow> (\<^bold>\<not>(\<^bold>\<not> G)) \<in> S \<longrightarrow> G \<in> S \<and> G \<in> S"
        using Con by blast (*Pendiente*)
      have "(\<^bold>\<not>(\<^bold>\<not> G)) \<in> S \<longrightarrow> G \<in> S \<and> G \<in> S"
        using Con.intros(4) \<open>Con (\<^bold>\<not> (\<^bold>\<not> G)) G G \<longrightarrow> \<^bold>\<not> (\<^bold>\<not> G) \<in> S \<longrightarrow> G \<in> S \<and> G \<in> S\<close> by blast 
              (*Pendiente*)
      thus "(\<^bold>\<not>(\<^bold>\<not> G)) \<in> S \<longrightarrow> G \<in> S"
        by (simp only: conj_absorb)
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
    have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
      using C1 C2 by (rule conjI)
    then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)" 
      using C3 by (iprover intro: conjI)
    then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
      using C4 by (iprover intro: conjI)
    then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)"
      using C5 by (iprover intro: conjI)
    then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)"
      using C6 by (iprover intro: conjI)
    then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)"
      using C7 by (iprover intro: conjI)
    then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
      using C8 by (iprover intro: conjI)
    thus "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> G \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
      using C9 by blast (*Pendiente*)
  qed
  thus "Hintikka S"
    unfolding Hintikka_def by this
qed

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

lemma Hintikka_alt: "Hintikka S = (\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))"  
  apply(simp add: Hintikka_def con_dis_simps)
  apply(rule iffI)
   subgoal by blast
  subgoal by safe metis+
done

text\<open> Lema: caracterización de la propiedad de consistencia proposicional
 mediante las fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>.\<close>

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
                thus "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
                  using \<open>H = G\<close> by simp (*Pendiente*)
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
    using C3 C6 C8 C9 by simp (*Pendiente*)
  then have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    by (rule pcp_alt1Con)
  have "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
    using C4 C5 C6 C7 by simp (*Pendiente*)
  then have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    by (rule pcp_alt1Dis)
  thus "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using C1 C2 Con Dis by simp (*Pendiente*)
qed

lemma pcp_alt2Con:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
proof -
  have 1:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
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
        have "\<forall>G H. Con (G \<^bold>\<and> H) G H \<longrightarrow> (G \<^bold>\<and> H) \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
          using assms by auto (*Pendiente*)
        then have "\<forall>H. Con (G \<^bold>\<and> H) G H \<longrightarrow> (G \<^bold>\<and> H) \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
          by (rule allE)
        then have "Con (G \<^bold>\<and> H) G H \<longrightarrow> (G \<^bold>\<and> H) \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
          by (rule allE)
        then have "(G \<^bold>\<and> H) \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
          using \<open>Con (G \<^bold>\<and> H) G H\<close> by (rule mp)
        thus "{G,H} \<union> S \<in> C"
          using \<open>(G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
      qed
    qed
  qed
  have 2:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
  proof (rule allI)
    fix G
    show "\<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    proof (rule impI)
      assume "\<^bold>\<not>(\<^bold>\<not>G) \<in> S"
      then have "Con (\<^bold>\<not>(\<^bold>\<not>G)) G G"
        by (simp only: Con.intros(4))
      have "\<forall>G H. Con (\<^bold>\<not>(\<^bold>\<not>G)) G H \<longrightarrow> (\<^bold>\<not>(\<^bold>\<not>G)) \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        using assms by auto (*Pendiente*)
      then have "\<forall>H. Con (\<^bold>\<not>(\<^bold>\<not>G)) G H \<longrightarrow> (\<^bold>\<not>(\<^bold>\<not>G)) \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        by (rule allE)
      then have "Con (\<^bold>\<not>(\<^bold>\<not>G)) G G \<longrightarrow> (\<^bold>\<not>(\<^bold>\<not>G)) \<in> S \<longrightarrow> {G,G} \<union> S \<in> C"
        by (rule allE)
      then have "(\<^bold>\<not>(\<^bold>\<not>G)) \<in> S \<longrightarrow> {G,G} \<union> S \<in> C"
        using \<open>Con (\<^bold>\<not>(\<^bold>\<not>G)) G G\<close> by (rule mp)
      then have "{G,G} \<union> S \<in> C"
        using \<open>(\<^bold>\<not>(\<^bold>\<not>G)) \<in> S\<close> by (rule mp)
      thus "{G} \<union> S \<in> C"
        by simp (*Pendiente*)
    qed
  qed
  have 3:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
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
        have "\<forall>G H. Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
          using assms by auto (*Pendiente*)
        then have "\<forall>H. Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
          by (rule allE)
        then have "Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
          by (rule allE)
        then have "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
          using \<open>Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)\<close> by (rule mp)
        thus "{\<^bold>\<not>G,\<^bold>\<not>H} \<union> S \<in> C"
          using \<open>\<^bold>\<not>(G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
      qed
    qed
  qed
  have 4:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
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
        have "\<forall>G H. Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not>H} \<union> S \<in> C"
          using assms by auto (*Pendiente*)
        then have "\<forall>H. Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not>H} \<union> S \<in> C"
          by (rule allE)
        then have "Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not>H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not>H} \<union> S \<in> C"
          by (rule allE)
        then have "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not>H} \<union> S \<in> C"  
          using \<open>Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not>H)\<close> by (rule mp)
        thus "{G,\<^bold>\<not>H} \<union> S \<in> C"
          using \<open>\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
      qed
    qed
  qed
  show ?thesis
    using 1 2 3 4 by auto (*Pendiente*)
qed

lemma pcp_alt2Dis:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
  \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
  \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
proof -
  have 1:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
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
        have "\<forall>G H. Dis (G \<^bold>\<or> H) G H \<longrightarrow> (G \<^bold>\<or> H) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          using assms by auto (*Pendiente*)
        then have "\<forall>H. Dis (G \<^bold>\<or> H) G H \<longrightarrow> (G \<^bold>\<or> H) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          by (rule allE)
        then have "Dis (G \<^bold>\<or> H) G H \<longrightarrow> (G \<^bold>\<or> H) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          by (rule allE)
        then have "(G \<^bold>\<or> H) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          using \<open>Dis (G \<^bold>\<or> H) G H\<close> by (rule mp)
        thus "{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          using \<open>(G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
      qed
    qed
  qed
  have 2:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
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
        have "\<forall>G H. Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not>G) H \<longrightarrow> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          using assms by auto (*Pendiente*)
        then have "\<forall>H. Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not>G) H \<longrightarrow> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          by (rule allE)
        then have "Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not>G) H \<longrightarrow> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          by (rule allE)
        then have "(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          using \<open>Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not>G) H\<close> by (rule mp)
        thus "{\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
          using \<open>(G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
      qed
    qed
  qed
  have 3:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
  proof (rule allI)
    fix G
    show "\<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    proof (rule impI)
      assume "\<^bold>\<not> (\<^bold>\<not>G) \<in> S"
      then have "Dis (\<^bold>\<not> (\<^bold>\<not>G)) G G"
        by (simp only: Dis.intros(4))
      have "\<forall>G H. Dis (\<^bold>\<not> (\<^bold>\<not>G)) G H \<longrightarrow> (\<^bold>\<not> (\<^bold>\<not>G)) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using assms by auto (*Pendiente*)
      then have "\<forall>H. Dis (\<^bold>\<not> (\<^bold>\<not>G)) G H \<longrightarrow> (\<^bold>\<not> (\<^bold>\<not>G)) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        by (rule allE)
      then have "Dis (\<^bold>\<not> (\<^bold>\<not>G)) G G \<longrightarrow> (\<^bold>\<not> (\<^bold>\<not>G)) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
        by (rule allE)
      then have "(\<^bold>\<not> (\<^bold>\<not>G)) \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
        using \<open>Dis (\<^bold>\<not> (\<^bold>\<not>G)) G G\<close> by (rule mp)
      then have "{G} \<union> S \<in> C \<or> {G} \<union> S \<in> C"
        using \<open>(\<^bold>\<not> (\<^bold>\<not>G)) \<in> S\<close> by (rule mp)
      thus "{G} \<union> S \<in> C"
        by (simp only: disj_absorb)
    qed
  qed
  have 4:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
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
  show ?thesis
    using 1 2 3 4 by auto (*Pendiente*)
qed

lemma pcp_alt2: 
  assumes "\<forall>S \<in> C. \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
  shows "pcp C"
proof -
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
  proof (rule ballI)
    fix S
    assume "S \<in> C"
    have H:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
      using assms \<open>S \<in> C\<close> by (rule bspec)
    then have "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
      by blast (*Pendiente*)
    then have C:"(\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
      by (rule pcp_alt2Con)
    have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using H by blast (*Pendiente*)
    then have D:"(\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)"
      by (rule pcp_alt2Dis)
    have 1:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
      using H by blast (*Pendiente*)
    have 2:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
      using C by blast (*Pendiente*)
    have 3:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using D by blast (*Pendiente*)
    have 4:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using D by blast (*Pendiente*)
    have 5:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
      using C by blast (*Pendiente*)
    have 6:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
      using D by blast (*Pendiente*)
    have 7:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
      using C by blast (*Pendiente*)
    have 8:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
      using C by blast (*Pendiente*)
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
  thus "pcp C" 
    by (rule auxEq1)
qed

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

lemma 
  assumes "pcp C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof -
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  have C1:"C \<subseteq> ?E"
  proof (rule subsetI)
    fix s
    assume "s \<in> C"
    have "s \<subseteq> s"
      by (rule subset_refl)
    then have "\<exists>S\<in>C. s \<subseteq> S"
      using \<open>s \<in> C\<close> by (rule bexI)
    thus "s \<in> ?E"
      by (rule CollectI)
  qed
  have C2:"pcp ?E"
  proof -
    have "(\<forall>S \<in> ?E.
    \<bottom> \<notin> S
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
      have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
        using S1 S2 by (rule conjI)
      then have "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E)"
        using S3 by simp (*Pendiente*)
      thus "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> ?E)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E)"
        using S4 by simp (*Pendiente*)
    qed
    thus "pcp ?E"
      by (rule pcp_alt2)
  qed
  have C3:"subset_closed ?E"
  proof -
    have "\<forall>S \<in> ?E. \<forall>s\<subseteq>S. s \<in> ?E"
    proof (rule ballI)
      fix S
      assume "S \<in> ?E"
      thus "\<forall>s\<subseteq>S. s \<in> ?E"
        by auto (*Pendiente*)
    qed
    thus "subset_closed ?E"
      unfolding subset_closed_def by this
  qed
  have "C \<subseteq> ?E \<and> pcp ?E \<and> subset_closed ?E" 
    using C1 C2 C3 by blast (*Pendiente*)
  thus ?thesis
    by (rule exI)
qed


lemma ex1: "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof(intro exI[of _ "{s . \<exists>S \<in> C. s \<subseteq> S}"] conjI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  show "C \<subseteq> ?E" by blast
  show "subset_closed ?E" unfolding subset_closed_def by blast
  assume C: \<open>pcp C\<close>
  show "pcp ?E" using C unfolding pcp_alt
    by (intro ballI conjI; simp; meson insertI1 rev_subsetD subset_insertI subset_insertI2)
qed

text\<open>Lema: \<close>

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
  by simp (*Pendiente*)

text\<open> Lema: Si C tiene la propiedad de carácter finito, entonces C es 
cerrado bajo subconjunto.\<close>

lemma
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

text \<open>\comentario{Pendiente.}\<close>

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

text \<open>\comentario{He demostrado de manera detallada hasta aquí.}\<close>

text\<open>Lema: Si C tiene la propiedad de consistencia proposicional y es 
cerrado bajo subconjunto, entonces tiene un subconjunto con la propiedad
de consistencia proposicional y de carácter finito.\<close>

lemma
  assumes C: "pcp C"
  assumes S: "subset_closed C"
  shows ex3: "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof(intro exI[of _ "C \<union> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"] conjI)
  let ?E = " {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  show "C \<subseteq> C \<union> ?E" by blast
  from S show "finite_character (C \<union> ?E)" 
    unfolding finite_character_def subset_closed_def by blast
  note C'' = C[unfolded pcp_alt, THEN bspec]
  have CON: "{G,H} \<union> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
             if si: "\<And>s. \<lbrakk>s\<subseteq>S; finite s\<rbrakk> \<Longrightarrow> s \<in> C" and
    un: "Con F G H" and el: " F \<in> S" for F G H S 
  proof -
    have k: "\<forall>s \<subseteq> S. finite s \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C"
      using si un C'' by simp
    have "{G,H} \<union> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff proof safe
      fix s
      assume "s \<subseteq> {G,H} \<union> S" and f: "finite s"
      hence "insert F  (s - {G,H}) \<subseteq> S" using el by blast
      with k f have "insert G  (insert H (insert F (s - {G,H}))) \<in> C" by simp
      hence "insert F (insert G (insert H  s)) \<in> C" using insert_absorb by fastforce
      thus "s \<in> C" using S unfolding subset_closed_def by fast  
    qed
    thus "{G, H} \<union> S \<in> C \<union> ?E" by simp
  qed
  have DIS: "insert G S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> insert H S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
    if si: "\<And>s. s\<subseteq>S \<Longrightarrow> finite s \<Longrightarrow> s \<in> C" and un: "Dis F G H" and el: "F \<in> S"
    for F G H S proof -
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
    thus "insert G S \<in> C \<union> ?E \<or> insert H S \<in> C \<union> ?E" by blast
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
  son contables si sus átomos lo son. En caso contrario, hay interferencias
  entre los tipos.\<close>

lemma pcp_seq_in: "pcp C \<Longrightarrow> S \<in> C \<Longrightarrow> pcp_seq C S n \<in> C"
proof(induction n)
  case (Suc n)
  hence "pcp_seq C S n \<in> C" by simp
  thus ?case by(simp add: Let_def)
qed simp

text\<open>Lema: la sucesión es monónota.\<close>

lemma pcp_seq_mono: "n \<le> m \<Longrightarrow> pcp_seq C S n \<subseteq> pcp_seq C S m"
proof(induction m)
  case (Suc m)
  thus ?case by(cases "n = Suc m"; simp add: Let_def; blast)
qed simp

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
  
lemma pcp_seq_sub: "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def by(induction n; blast)
    
lemma pcp_lim_inserted_at_ex: 
    "x \<in> pcp_lim C S \<Longrightarrow> \<exists>k. x \<in> pcp_seq C S k"
  unfolding pcp_lim_def by blast

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

text \<open>\comentario{Modificar blast+ con el cambio de notación ya que no carga.}\<close>

(*lemma pcp_lim_Hintikka:
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
  for k F G H by blast+
  have "Con F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
       "Dis F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
    for F G H
       by(auto dest: d(3-) cl_max'[OF c sc])
  with d(1,2) show ?thesis unfolding Hintikka_alt by fast
qed*)
  
(*theorem pcp_sat: \<comment> \<open>model existence theorem\<close>
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
  with Hintikkas_lemma have "sat (pcp_lim Ce S)" .
  moreover have "S \<subseteq> pcp_lim Ce S" using pcp_seq.simps(1) pcp_seq_sub by fast
  ultimately show ?thesis unfolding sat_def by fast
qed
(* This and Hintikka's lemma are the only two where we need semantics. 
   Still, I don't think it's meaningful to separate those two into 
   an extra theory. *)
*)
(*<*)
end
(*>*) 
