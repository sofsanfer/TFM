(*<*) 
theory Consistencia
  imports 
    Sintaxis
    Semantica
    Hintikka
begin
(*>*)

text \<open>
\comentario{Localización de sello.png.}
\comentario{Cambiar los directores}
\comentario{Introducción. Mirar fitting p. 53 y 54}

\<close>

text \<open>En este capítulo nos centraremos en demostrar el \<open>teorema de existencia de modelos\<close>.
  Dicho teorema prueba la satisfacibilidad de un conjunto de fórmulas \<open>S\<close> si este pertenece a una 
  colección de conjuntos \<open>C\<close> que verifica la \<open>propiedad de consistencia proposicional\<close>. Para su 
  prueba, definiremos las propiedades de \<open>carácter finito\<close> y \<open>ser cerrada bajo subconjuntos\<close> para
  colecciones de conjuntos de fórmulas. De este modo, mediante distintos resultados que relacionan
  estas propiedades con la \<open>propiedad de consistencia proposicional\<close>, dada una colección \<open>C\<close> 
  cualquiera en las condiciones anteriormente descritas, podemos encontrar una colección \<open>C'\<close> que la 
  contenga que verifique la \<open>propiedad de consistencia proposicional\<close>, sea \<open>cerrada bajo 
  subconjuntos\<close> y de \<open>carácter finito\<close>. Por otro lado, definiremos una sucesión de conjuntos de
  fórmulas a partir de la colección \<open>C'\<close> y el conjunto \<open>S\<close>. Además, definiremos el límite de dicha
  sucesión que, en particular, contendrá al conjunto \<open>S\<close>. Finalmente probaremos que dicho límite es 
  un conjunto satisfacible por el \<open>lema de Hintikka\<close> y, por contención, quedará probada la 
  satisfacibilidad del conjunto \<open>S\<close>.\<close>

section \<open>Propiedad de consistencia proposicional\<close>

text \<open>En primer lugar, definamos la \<open>propiedad de consistencia proposicional\<close> para una colección 
  de conjuntos de fórmulas proposicionales.\<close>

text \<open>
  \begin{definicion}
    Sea \<open>C\<close> una colección de conjuntos de fórmulas proposicionales. Decimos que
    \<open>C\<close> verifica la \<open>propiedad de consistencia proposicional\<close> si, para todo
    conjunto \<open>S\<close> perteneciente a la colección, se verifica:
    \begin{enumerate}
      \item \<open>\<bottom> \<notin> S\<close>.
      \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
        simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
      \item Si \<open>F \<and> G \<in> S\<close>, entonces el conjunto \<open>{F,G} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>F \<or> G \<in> S\<close>, entonces o bien el conjunto \<open>{F} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
        conjunto \<open>{G} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>F \<rightarrow> G \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> F} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
        conjunto \<open>{G} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(\<not> F) \<in> S\<close>, entonces el conjunto \<open>{F} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(F \<and> G) \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> F} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
        conjunto \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(F \<or> G) \<in> S\<close>, entonces el conjunto \<open>{\<not> F, \<not> G} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(F \<rightarrow> G) \<in> S\<close>, entonces el conjunto \<open>{F, \<not> G} \<union> S\<close> pertenece a \<open>C\<close>.
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
  formada por el conjunto vacío de fórmulas verifica la propiedad de consistencia 
  proposicional.\<close>

lemma "pcp {{}}"
  unfolding pcp_def by simp

text \<open>Del mismo modo, aplicando la definición, se demuestra que los siguientes ejemplos
  de colecciones de conjuntos de fórmulas proposicionales verifican igualmente la 
  propiedad.\<close>

lemma "pcp {{Atom 0}}"
  unfolding pcp_def by simp

lemma "pcp {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))},
  {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1)),  Atom 1}}" 
  unfolding pcp_def by auto

text \<open>Por último, en contraposición podemos ilustrar un caso de colección que no verifique la 
  propiedad con la siguiente colección obtenida al modificar el último ejemplo. De
  esta manera, aunque la colección verifique correctamente la quinta condición de la
  definición, no cumplirá la sexta.\<close>

lemma "\<not> pcp {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))}}" 
  unfolding pcp_def by auto

section \<open>Notación uniforme: fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>\<close>

text \<open>En esta subsección introduciremos la notación uniforme inicialmente 
  desarrollada por \<open>R. M. Smullyan\<close> (añadir referencia bibliográfica). La finalidad
  de dicha notación es reducir el número de casos a considerar sobre la estructura de 
  las fórmulas al clasificar éstas en dos categorías, facilitando las demostraciones
  y métodos empleados en adelante.

  \comentario{Añadir referencia bibliográfica.}

  De este modo, las fórmulas proposicionales pueden ser de dos tipos: aquellas que 
  de tipo conjuntivo (las fórmulas \<open>\<alpha>\<close>) y las de tipo disyuntivo (las fórmulas \<open>\<beta>\<close>). 
  Cada fórmula de tipo \<open>\<alpha>\<close>, o \<open>\<beta>\<close> respectivamente, tiene asociada sus  
  dos componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, o \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> respectivamente. Para justificar dicha clasificación,
  introduzcamos inicialmente la definición de fórmulas semánticamente equivalentes.

  \begin{definicion}
    Dos fórmulas son \<open>semánticamente equivalentes\<close> si tienen el mismo valor para toda 
    interpretación.
  \end{definicion}

  En Isabelle podemos formalizar la definición de la siguiente manera.\<close>

definition "semanticEq F G \<equiv> \<forall>\<A>. (\<A> \<Turnstile> F) \<longleftrightarrow> (\<A> \<Turnstile> G)"

text \<open>De este modo, según la definición del valor de verdad de una fórmula proposicional en una 
  interpretación dada, podemos ver los siguientes ejemplos de fórmulas semánticamente equivalentes.\<close>

lemma "semanticEq (Atom p) ((Atom p) \<^bold>\<or> (Atom p))" 
  by (simp add: semanticEq_def)

lemma "semanticEq (Atom p) ((Atom p) \<^bold>\<and> (Atom p))" 
  by (simp add: semanticEq_def)

lemma "semanticEq \<bottom> (\<bottom> \<^bold>\<and> \<bottom>)" 
  by (simp add: semanticEq_def)

lemma "semanticEq \<bottom> (\<bottom> \<^bold>\<or> \<bottom>)" 
  by (simp add: semanticEq_def)

lemma "semanticEq \<bottom> (\<^bold>\<not> \<top>)"
  by (simp add: semanticEq_def top_semantics)

lemma "semanticEq F (\<^bold>\<not>(\<^bold>\<not> F))"
  by (simp add: semanticEq_def)

lemma "semanticEq (\<^bold>\<not>(\<^bold>\<not> F)) (F \<^bold>\<or> F)"
  by (simp add: semanticEq_def)

lemma "semanticEq (\<^bold>\<not>(\<^bold>\<not> F)) (F \<^bold>\<and> F)"
  by (simp add: semanticEq_def)

lemma "semanticEq (\<^bold>\<not> F \<^bold>\<and> \<^bold>\<not> G) (\<^bold>\<not>(F \<^bold>\<or> G))"
  by (simp add: semanticEq_def)

lemma "semanticEq (F \<^bold>\<rightarrow> G) (\<^bold>\<not> F \<^bold>\<or> G)"
  by (simp add: semanticEq_def)

text \<open>En contraposición, también podemos dar ejemplos de fórmulas que no son semánticamente 
  equivalentes.\<close>

lemma "\<not> semanticEq (Atom p) (\<^bold>\<not>(Atom p))"
  by (simp add: semanticEq_def)

lemma "\<not> semanticEq \<bottom> \<top>"
  by (simp add: semanticEq_def top_semantics)
  
text \<open>Por tanto, diremos intuitivamente que una fórmula es de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>
  si es semánticamente equivalente a la fórmula \<open>\<alpha>\<^sub>1 \<and> \<alpha>\<^sub>2\<close>. Del mismo modo, una fórmula será de tipo
  \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> si es semánticamente equivalente a la fórmula \<open>\<beta>\<^sub>1 \<or> \<beta>\<^sub>2\<close>.

  \begin{definicion}
    Las fórmulas de tipo \<open>\<alpha>\<close> (\<open>fórmulas conjuntivas\<close>) y sus correspondientes componentes
    \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se definen como sigue: dadas \<open>F\<close> y \<open>G\<close> fórmulas cualesquiera,
    \begin{enumerate}
      \item \<open>F \<and> G\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>G\<close>.
      \item \<open>\<not>(F \<or> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(F \<longrightarrow> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>\<not> G\<close>.
    \end{enumerate} 
  \end{definicion}

  De este modo, de los ejemplos anteriores podemos deducir que las fórmulas atómicas son de tipo \<open>\<alpha>\<close>
  y sus componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> son la propia fórmula. Del mismo modo, la constante \<open>\<bottom>\<close> también es 
  una fórmula conjuntiva cuyas componentes son ella misma. Por último, podemos observar que dada
  una fórmula cualquiera \<open>F\<close>, su doble negación \<open>\<not>(\<not> F)\<close> es una fórmula de tipo \<open>\<alpha>\<close> y componentes
  \<open>F\<close> y \<open>F\<close>.

  Formalizaremos en Isabelle el conjunto de fórmulas \<open>\<alpha>\<close> como un predicato inductivo. De este modo,
  las reglas anteriores que construyen el conjunto de fórmulas de tipo \<open>\<alpha>\<close> se formalizan en Isabelle 
  como reglas de introducción. Además, añadiremos explícitamente una cuarta regla que introduce la 
  doble negación de una fórmula como fórmula de tipo \<open>\<alpha>\<close>. De este modo, facilitaremos la prueba de 
  resultados posteriores relacionados con la definición de conjunto de Hintikka, que constituyen una
  base para la demostración del \<open>teorema de existencia de modelo\<close>.\<close>

inductive Con :: "'a formula => 'a formula => 'a formula => bool" where
"Con (And F G) F G" |
"Con (Not (Or F G)) (Not F) (Not G)" |
"Con (Not (Imp F G)) F (Not G)" |
"Con (Not (Not F)) F F"

text \<open>Las reglas de introducción que proporciona la definición anterior son
  las siguientes.

  \begin{itemize}
    \item[] @{thm[mode=Rule] Con.intros[no_vars]} 
      \hfill (@{text Con.intros})
  \end{itemize}
  
  Por otro lado, definamos las fórmulas disyuntivas.

  \begin{definicion}
    Las fórmulas de tipo \<open>\<beta>\<close> (\<open>fórmulas disyuntivas\<close>) y sus correspondientes componentes
    \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se definen como sigue: dadas \<open>F\<close> y \<open>G\<close> fórmulas cualesquiera,
    \begin{enumerate}
      \item \<open>F \<or> G\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>F\<close> y \<open>G\<close>.
      \item \<open>F \<longrightarrow> G\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>G\<close>.
      \item \<open>\<not>(F \<and> G)\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>\<not> G\<close>.
    \end{enumerate} 
  \end{definicion}

  De los ejemplos dados anteriormente, podemos deducir análogamente que las fórmulas atómicas, la
  constante \<open>\<bottom>\<close> y la doble negación sob también fórmulas disyuntivas con las mismas componentes que
  las dadas para el tipo conjuntivo.

  Del mismo modo, su formalización se realiza como un predicado inductivo, de manera que las reglas 
  que definen el conjunto de fórmulas de tipo \<open>\<beta>\<close> se formalizan en Isabelle como reglas de 
  introducción. Análogamente, introduciremos de manera explícita una regla que señala que la doble 
  negación de una fórmula es una fórmula de tipo disyuntivo.\<close>

inductive Dis :: "'a formula => 'a formula => 'a formula => bool" where
"Dis (Or F G) F G" |
"Dis (Imp F G) (Not F) G" |
"Dis (Not (And F G)) (Not F) (Not G)" |
"Dis (Not (Not F)) F F"

text \<open>Del mismo modo, las reglas de introducción que proporciona esta formalización se muestran a 
  continuación.

  \begin{itemize}
    \item[] @{thm[mode=Rule] Dis.intros[no_vars]} 
      \hfill (@{text Dis.intros})
  \end{itemize}

  Cabe observar que las formalizaciones de la definiciones de fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close> son 
  definiciones sintácticas, pues construyen los correspondientes conjuntos de fórmulas a partir de 
  una reglas sintácticas concretas. Se trata de una simplificación de la intuición original de la 
  clasificación de las fórmulas mediante notación uniforme, ya que se prescinde de la noción de 
  equivalencia semántica que permite clasificar la totalidad de las fórmulas proposicionales. 

  Veamos la clasificación de casos concretos de fórmulas. Por ejemplo, según hemos definido la 
  fórmula \<open>\<top>\<close>, es sencillo comprobar que se trata de una fórmula disyuntiva.\<close>

lemma "Dis \<top> (\<^bold>\<not> \<bottom>) \<bottom>" 
  unfolding Top_def by (simp only: Dis.intros(2))

text \<open>Por otro lado, se observa a partir de las correspondientes definiciones que la conjunción
  generalizada de una lista de fórmulas es una fórmula de tipo \<open>\<alpha>\<close> y la disyunción generalizada de
  una lista de fórmulas es una fórmula de tipo \<open>\<beta>\<close>.\<close>

lemma "Con (\<^bold>\<And>(F#Fs)) F (\<^bold>\<And>Fs)"
  by (simp only: BigAnd.simps Con.intros(1))

lemma "Dis (\<^bold>\<Or>(F#Fs)) F (\<^bold>\<Or>Fs)"
  by (simp only: BigOr.simps Dis.intros(1))

text \<open>Finalmente, de las reglas que definen las fórmulas conjuntivas y disyuntivas se deduce que
  la doble negación de una fórmula es una fórmula perteneciente a ambos tipos.\<close>

lemma notDisCon: "Con (Not (Not F)) F F" "Dis (Not (Not F)) F F" 
  by (simp only: Con.intros(4) Dis.intros(4))+

text \<open>A continuación vamos a introducir el siguiente lema que caracteriza las fórmulas de tipo \<open>\<alpha>\<close> 
  y \<open>\<beta>\<close>, facilitando el uso de la notación uniforme en Isabelle.\<close>

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

text\<open>Por último, introduzcamos resultados que permiten caracterizar los conjuntos de Hintikka y la 
  propiedad de consistencia proposicional empleando la notación uniforme.

  \begin{lema}[Caracterización de los conjuntos de Hintikka mediante la notación uniforme]
    Dado un conjunto de fórmulas proposicionales \<open>S\<close>, son equivalentes:
    \begin{enumerate}
      \item \<open>S\<close> es un conjunto de Hintikka.
      \item Se verifican las condiciones siguientes:
      \begin{itemize}
        \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
        \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
        simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
        \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica 
        que si la fórmula pertenece a \<open>S\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> también.
        \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se verifica 
        que si la fórmula pertenece a \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> pertenece
        a \<open>S\<close> o bien \<open>\<beta>\<^sub>2\<close> pertenece a \<open>S\<close>.
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
  fórmulas, tenemos que \<open>\<alpha>\<close> puede ser de la forma \<open>G \<and> H\<close>, \<open>\<not>(\<not> G)\<close>,\\ \<open>\<not>(G \<or> H)\<close> 
  o \<open>\<not>(G \<longrightarrow> H)\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera. Probemos que, para cada
  tipo de fórmula \<open>\<alpha>\<close> perteneciente a \<open>S\<close>, sus componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> están en
  \<open>S\<close>.

  \<open>\<sqdot> Fórmula del tipo G \<and> H\<close>: Sus componentes conjuntivas son \<open>G\<close> y \<open>H\<close>. 
  Por la tercera condición de la definición de conjunto de Hintikka, obtenemos 
  que si \<open>G \<and> H\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>H\<close> están ambas en el conjunto,
  lo que prueba este caso.
    
  \<open>\<sqdot> Fórmula del tipo \<not>(\<not> G)\<close>: Sus componentes conjuntivas son ambas \<open>G\<close>.
  Por la sexta condición de la definición de conjunto de Hintikka, obtenemos que
  si \<open>\<not>(\<not> G)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> pertenece al conjunto, lo que prueba
  este caso.

  \<open>\<sqdot> Fórmula del tipo \<not>(G \<or> H)\<close>: Sus componentes conjuntivas son \<open>\<not> G\<close> y \<open>\<not> H\<close>. 
  Por la octava condición de la definición de conjunto de Hintikka, obtenemos 
  que si \<open>\<not>(G \<or> H)\<close> pertenece a \<open>S\<close>, entonces \<open>\<not> G\<close> y \<open>\<not> H\<close> están ambas en el conjunto,
  lo que prueba este caso.

  \<open>\<sqdot> Fórmula del tipo \<not>(G \<longrightarrow> H)\<close>: Sus componentes conjuntivas son \<open>G\<close> y \<open>\<not> H\<close>. 
  Por la novena condición de la definición de conjunto de Hintikka, obtenemos 
  que si\\ \<open>\<not>(G \<longrightarrow> H)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>\<not> H\<close> están ambas en el conjunto,
  lo que prueba este caso.

  Finalmente, probemos que para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y 
  \<open>\<beta>\<^sub>2\<close> se verifica que si la fórmula pertenece al conjunto \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> 
  pertenece al conjunto o bien \<open>\<beta>\<^sub>2\<close> pertenece a conjunto. Para ello, supongamos que 
  una fórmula cualquiera de tipo \<open>\<beta>\<close> pertence a \<open>S\<close>. Por definición de este tipo de
  fórmulas, tenemos que \<open>\<beta>\<close> puede ser de la forma \<open>G \<or> H\<close>, \<open>G \<longrightarrow> H\<close>, \<open>\<not>(\<not> G)\<close> 
  o \<open>\<not>(G \<and> H)\<close> para fórmulas \<open>G\<close> y \<open>H\<close> cualesquiera. Probemos que, para cada
  tipo de fórmula \<open>\<beta>\<close> perteneciente a \<open>S\<close>, o bien su componente \<open>\<beta>\<^sub>1\<close> pertenece a \<open>S\<close> 
  o bien su componente \<open>\<beta>\<^sub>2\<close> pertenece a \<open>S\<close>.

  \<open>\<sqdot> Fórmula del tipo G \<or> H\<close>: Sus componentes disyuntivas son \<open>G\<close> y \<open>H\<close>. 
    Por la cuarta condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>G \<or> H\<close> pertenece a \<open>S\<close>, entonces o bien \<open>G\<close> está en \<open>S\<close> o bien \<open>H\<close> está
    en \<open>S\<close>, lo que prueba este caso.

  \<open>\<sqdot> Fórmula del tipo G \<longrightarrow> H\<close>: Sus componentes disyuntivas son \<open>\<not> G\<close> y \<open>H\<close>.
    Por la quinta condición de la definición de conjunto de Hintikka, obtenemos que
    si \<open>G \<longrightarrow> H\<close> pertenece a \<open>S\<close>, entonces o bien \<open>\<not> G\<close> pertenece al conjunto o bien
    \<open>H\<close> pertenece al conjunto, lo que prueba este caso.

  \<open>\<sqdot> Fórmula del tipo \<not>(\<not> G)\<close>: Sus componentes conjuntivas son ambas \<open>G\<close>.
    Por la sexta condición de la definición de conjunto de Hintikka, obtenemos 
    que si \<open>\<not>(\<not> G)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> pertenece al conjunto. De este modo,
    por la regla de introducción a la disyunción, se prueba que o bien una de las 
    componentes está en el conjunto o bien lo está la otra pues, en este caso,
    coinciden.

  \<open>\<sqdot> Fórmula del tipo \<not>(G \<and> H)\<close>: Sus componentes conjuntivas son \<open>\<not> G\<close> y \<open>\<not> H\<close>. 
    Por la séptima condición de la definición de conjunto de Hintikka, obtenemos 
    que si\\ \<open>\<not>(G \<and> H)\<close> pertenece a \<open>S\<close>, entonces o bien \<open>\<not> G\<close> pertenece al conjunto
    o bien \<open>\<not> H\<close> pertenece al conjunto, lo que prueba este caso.

\textbf{\<open>2) \<Longrightarrow> 1)\<close>}

  Supongamos que se verifican las condiciones del enunciado del lema:

  \begin{itemize}
    \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica 
    que si la fórmula pertenece a \<open>S\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> también.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se verifica 
    que si la fórmula pertenece a \<open>S\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> pertenece
    a \<open>S\<close> o bien \<open>\<beta>\<^sub>2\<close> pertenece a \<open>S\<close>.
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

  Para probar de manera detallada el lema en Isabelle vamos a demostrar
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
  proof (rule allI)+
    fix F G H
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
  have C4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
  proof (rule allI)+
    fix F G H
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
  show "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    using C1 C2 C3 C4 by (iprover intro: conjI)
qed

text \<open>Por último, probamos la implicación recíproca de forma detallada en Isabelle mediante
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
    proof (rule allI)+
      fix G H
      show "G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      proof (rule impI)
        assume "G \<^bold>\<and> H \<in> S"
        have "Con (G \<^bold>\<and> H) G H"
          by (simp only: Con.intros(1))
        have "Con (G \<^bold>\<and> H) G H \<longrightarrow> G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          using Con by (iprover elim: allE)
        then have "G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
          using \<open>Con (G \<^bold>\<and> H) G H\<close> by (rule mp)
        thus "G \<in> S \<and> H \<in> S"
          using \<open>G \<^bold>\<and> H \<in> S\<close> by (rule mp)
      qed
    qed
    have C4:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
    proof (rule allI)+
      fix G H
      show "G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
      proof (rule impI)
        assume "G \<^bold>\<or> H \<in> S"
        have "Dis (G \<^bold>\<or> H) G H"
          by (simp only: Dis.intros(1))
        have "Dis (G \<^bold>\<or> H) G H \<longrightarrow> G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          using Dis by (iprover elim: allE)
        then have "G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S"
          using \<open>Dis (G \<^bold>\<or> H) G H\<close> by (rule mp)
        thus "G \<in> S \<or> H \<in> S"
          using \<open>G \<^bold>\<or> H \<in> S\<close> by (rule mp)
      qed
    qed
    have C5:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
    proof (rule allI)+
      fix G H
      show "G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
      proof (rule impI)
        assume "G \<^bold>\<rightarrow> H \<in> S" 
        have "Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not> G) H"
          by (simp only: Dis.intros(2))
        have "Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not> G) H \<longrightarrow> G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
          using Dis by (iprover elim: allE)
        then have "G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S" 
          using \<open>Dis (G \<^bold>\<rightarrow> H) (\<^bold>\<not> G) H\<close> by (rule mp)
        thus "\<^bold>\<not> G \<in> S \<or> H \<in> S"
          using \<open>G \<^bold>\<rightarrow> H \<in> S\<close> by (rule mp)
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
    proof (rule allI)+
      fix G H
      show "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
      proof (rule impI)
        assume "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S"
        have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)"
          by (simp only: Dis.intros(3))
        have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not> G) (\<^bold>\<not> H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using Dis by (iprover elim: allE)
        then have "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using \<open>Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)\<close> by (rule mp)
        thus "\<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
          using \<open>\<^bold>\<not>(G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
      qed
    qed
    have C8:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    proof (rule allI)+
      fix G H
      show "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
      proof (rule impI)
        assume "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S"
        have "Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)"
          by (simp only: Con.intros(2))
        have "Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not> G) (\<^bold>\<not> H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using Con by (iprover elim: allE)
        then have "\<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using \<open>Con (\<^bold>\<not>(G \<^bold>\<or> H)) (\<^bold>\<not> G) (\<^bold>\<not> H)\<close> by (rule mp)
        thus "\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using \<open>\<^bold>\<not>(G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
      qed
    qed
    have C9:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    proof (rule allI)+
      fix G H
      show "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
      proof (rule impI)
        assume "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S"
        have "Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not> H)"
          by (simp only: Con.intros(3))
        have "Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not> H) \<longrightarrow> \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using Con by (iprover elim: allE)
        then have "\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using \<open>Con (\<^bold>\<not>(G \<^bold>\<rightarrow> H)) G (\<^bold>\<not> H)\<close> by (rule mp)
        thus "G \<in> S \<and> \<^bold>\<not> H \<in> S"
          using \<open>\<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
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

text\<open>Por otra parte, veamos un resultado que permite la caracterización de la 
  propiedad de consistencia proposicional mediante la notación uniforme.

  \begin{lema}[Caracterización de \<open>P.C.P\<close> mediante la notación uniforme]
    Dada una colección \<open>C\<close> de conjuntos de fórmulas proposicionales, son equivalentes:
    \begin{enumerate}
      \item \<open>C\<close> verifica la propiedad de consistencia proposicional.
      \item Para cualquier conjunto de fórmulas \<open>S\<close> de la colección, se verifican las 
      condiciones:
      \begin{itemize}
        \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
        \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
        simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
        \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
        pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
        \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
        pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> o 
        bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
      \end{itemize} 
    \end{enumerate}
  \end{lema}

  En Isabelle/HOL se formaliza el resultado como sigue.\<close>

lemma "pcp C = (\<forall>S \<in> C. \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))"
  oops

text \<open>En primer lugar, veamos la demostración del lema.

\begin{demostracion}
  Para probar la equivalencia, veamos cada una de las implicaciones por separado.

\textbf{\<open>1) \<Longrightarrow> 2)\<close>}
  
  Supongamos que \<open>C\<close> es una colección de conjuntos de fórmulas proposicionales que
  verifica la propiedad de consistencia proposicional. Vamos a probar que, en efecto,
  cumple las condiciones de \<open>2)\<close>. 

  Consideremos un conjunto de fórmulas \<open>S\<close> perteneciente a la colección \<open>C\<close>.
  Por hipótesis, de la definición de propiedad de consistencia proposicional obtenemos
  que \<open>S\<close> verifica las siguientes condiciones:
 \begin{enumerate}
      \item \<open>\<bottom> \<notin> S\<close>.
      \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
        simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
      \item Si \<open>G \<and> H \<in> S\<close>, entonces el conjunto \<open>{G,H} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>G \<or> H \<in> S\<close>, entonces o bien el conjunto \<open>{G} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
        conjunto \<open>{H} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>G \<rightarrow> H \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
        conjunto \<open>{H} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(\<not> G) \<in> S\<close>, entonces el conjunto \<open>{G} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(G \<and> H) \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
        conjunto \<open>{\<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(G \<or> H) \<in> S\<close>, entonces el conjunto \<open>{\<not> G, \<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
      \item Si \<open>\<not>(G \<rightarrow> H) \<in> S\<close>, entonces el conjunto \<open>{G, \<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
 \end{enumerate}

  Las dos primeras condiciones se corresponden con los dos primeros resultados que queríamos
  demostrar. De este modo, falta probar:
  \begin{itemize}
     \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
     pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
     \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
     pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> o 
     bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.   
  \end{itemize} 

  En primer lugar, vamos a deducir el primer resultado correspondiente a las fórmulas
  de tipo \<open>\<alpha>\<close> de las condiciones tercera, sexta, octava y novena de la definición de 
  propiedad de consistencia proposicional. En efecto, consideremos una fórmula de tipo 
  \<open>\<alpha>\<close> cualquiera con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close> pertenece a \<open>S\<close>. Sabemos que 
  la fórmula es de la forma \<open>G \<and> H\<close>, \<open>\<not> (\<not> G)\<close>, \<open>\<not> (G \<or> H)\<close> o 
  \<open>\<not>(G \<longrightarrow> H)\<close> para ciertas fórmulas \<open>G\<close> y \<open>H\<close>. Vamos a probar que para cada caso se cumple que 
  \<open>{\<alpha>\<^sub>1, \<alpha>\<^sub>2} \<union> S\<close> pertenece a la colección:

  \<open>\<sqdot> Fórmula de tipo G \<and> H\<close>: En este caso, sus componentes conjuntivas \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> son \<open>G\<close> 
    y \<open>H\<close> respectivamente. Luego tenemos que \<open>{\<alpha>\<^sub>1, \<alpha>\<^sub>2} \<union> S\<close>  pertenece a \<open>C\<close> por
    la tercera condición de la definición de propiedad de consistencia
    proposicional.

  \<open>\<sqdot> Fórmula de tipo \<not> (\<not> G)\<close>: En este caso, sus componentes conjuntivas \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> son 
    ambas \<open>G\<close>. Como el conjunto \<open>{\<alpha>\<^sub>1} \<union> S\<close> es equivalente a \<open>{\<alpha>\<^sub>1, \<alpha>\<^sub>2} \<union> S\<close> ya
    que \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> son iguales, tenemos que este último pertenece a \<open>C\<close> por la sexta 
    condición de la definición de propiedad de consistencia proposicional.

  \<open>\<sqdot> Fórmula de tipo \<not>(G \<or> H)\<close>: En este caso, sus componentes conjuntivas \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> son\\ 
    \<open>\<not> G\<close> y \<open>\<not> H\<close> respectivamente. Luego tenemos que \<open>{\<alpha>\<^sub>1, \<alpha>\<^sub>2} \<union> S\<close>  pertenece a \<open>C\<close> por
    la octava condición de la definición de propiedad de consistencia proposicional.

  \<open>\<sqdot> Fórmula de tipo \<not>(G \<longrightarrow> H)\<close>: En este caso, sus componentes conjuntivas \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> son \<open>G\<close> y 
    \<open>\<not> H\<close> respectivamente. Luego tenemos que \<open>{\<alpha>\<^sub>1, \<alpha>\<^sub>2} \<union> S\<close>  pertenece a \<open>C\<close> por la novena 
    condición de la definición de propiedad de consistencia proposicional.

  Finalmente, el resultado correspondiente a las fórmulas de tipo \<open>\<beta>\<close> se obtiene de las 
  condiciones cuarta, quinta, sexta y séptima de la definición de propiedad de consistencia 
  proposicional. Para probarlo, consideremos una fórmula cualquiera de tipo \<open>\<beta>\<close> perteneciente
  al conjunto \<open>S\<close> y cuyas componentes disyuntivas son \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>. Por simplificación, sabemos 
  que dicha fórmula es de la forma \<open>G \<or> H\<close>, \<open>G \<longrightarrow> H\<close>, \<open>\<not> (\<not> G)\<close> o \<open>\<not>(G \<and> H)\<close> para ciertas 
  fórmulas \<open>G\<close> y \<open>H\<close>. Deduzcamos que, en efecto, tenemos que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> está en \<open>C\<close> o bien 
  \<open>{\<beta>\<^sub>2} \<union> S\<close> está en \<open>C\<close>.

  \<open>\<sqdot> Fórmula de tipo G \<or> H\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son \<open>G\<close> y 
    \<open>H\<close> respectivamente. Luego tenemos que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close>  pertenece a \<open>C\<close> o bien\\
    \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close> por la cuarta condición de la definición de propiedad de 
    consistencia proposicional.

  \<open>\<sqdot> Fórmula de tipo G \<longrightarrow> H\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son\\ 
    \<open>\<not> G\<close> y \<open>H\<close> respectivamente. Luego tenemos que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close>  pertenece a \<open>C\<close> o 
    bien\\ \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close> por la quinta condición de la definición de propiedad 
    de consistencia proposicional.

  \<open>\<sqdot> Fórmula de tipo \<not>(\<not> G)\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son ambas 
    \<open>G\<close>. Luego tenemos que, en particular, el conjunto \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> por la 
    sexta condición de la definición de propiedad de consistencia proposicional. Por tanto, se 
    verifica que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> está en \<open>C\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S\<close> está en \<open>C\<close>.

  \<open>\<sqdot> Fórmula de tipo \<not>(G \<and> H)\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son \\ 
    \<open>\<not> G\<close> y \<open>\<not> H\<close> respectivamente. Luego tenemos que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close> por la séptima condición de la definición de propiedad 
    de consistencia proposicional.

  De este modo, queda probada la primera implicación de la equivalencia. Veamos la prueba de la 
  implicación contraria.

\textbf{\<open>2) \<Longrightarrow> 1)\<close>}

  Supongamos que, dada una colección de conjuntos de fórmulas proposicionales \<open>C\<close>, para cualquier
  conjunto \<open>S\<close> de la colección se verifica:
  \begin{itemize}
    \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
    pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
    pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
  \end{itemize}

  Probemos que \<open>C\<close> verifica la propiedad de consistencia proposicional. Por la definición
  de la propiedad basta probar que, dado un conjunto cualquiera \<open>S\<close> perteneciente a \<open>C\<close>, se
  verifican las siguientes condiciones:
  \begin{enumerate}
    \item \<open>\<bottom> \<notin> S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Si \<open>G \<and> H \<in> S\<close>, entonces el conjunto \<open>{G,H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Si \<open>G \<or> H \<in> S\<close>, entonces o bien el conjunto \<open>{G} \<union> S\<close> pertenece a \<open>C\<close>, o bien el conjunto 
      \<open>{H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Si \<open>G \<rightarrow> H \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
      conjunto \<open>{H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Si \<open>\<not>(\<not> G) \<in> S\<close>, entonces el conjunto \<open>{G} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Si \<open>\<not>(G \<and> H) \<in> S\<close>, entonces o bien el conjunto \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close>, o bien el 
      conjunto \<open>{\<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Si \<open>\<not>(G \<or> H) \<in> S\<close>, entonces el conjunto \<open>{\<not> G, \<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item Si \<open>\<not>(G \<rightarrow> H) \<in> S\<close>, entonces el conjunto \<open>{G, \<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
  \end{enumerate}

  En primer lugar, se observa que por hipótesis se cumplen las dos primeras condiciones de
  la definición.

  Por otra parte, vamos a deducir las condiciones tercera, sexta, octava y novena de la
  definición de la propiedad de consistencia proposicional a partir de la hipótesis sobre las 
  fórmulas de tipo \<open>\<alpha>\<close>.
  \begin{enumerate}
    \item[\<open>3)\<close>:] Supongamos que la fórmula \<open>G \<and> H\<close> pertenece a \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close>
    cualesquiera. Observemos que se trata de una fórmula de tipo \<open>\<alpha>\<close> de componentes conjuntivas
    \<open>G\<close> y \<open>H\<close>. Luego, por hipótesis, tenemos que \<open>{G, H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item[\<open>6)\<close>:] Supongamos que la fórmula \<open>\<not>(\<not> G)\<close> pertenece a \<open>S\<close> para la fórmula \<open>G\<close> 
    cualquiera. Observemos que se trata de una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes conjuntivas 
    son ambas la fórmula \<open>G\<close>. Por hipótesis, tenemos que el conjunto \<open>{G,G} \<union> S\<close> pertence a \<open>C\<close>
    y, puesto que dicho conjunto es equivalente a \<open>{G} \<union> S\<close>, tenemos el resultado.
    \item[\<open>8)\<close>:] Supongamos que la fórmula \<open>\<not>(G \<or> H)\<close> pertenece a \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close>
    cualesquiera. Observemos que se trata de una fórmula de tipo \<open>\<alpha>\<close> de componentes conjuntivas
    \<open>\<not> G\<close> y \<open>\<not> H\<close>. Luego, por hipótesis, tenemos que \<open>{\<not> G, \<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item[\<open>9)\<close>:] Supongamos que la fórmula \<open>\<not>(G \<longrightarrow> H)\<close> pertenece a \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close>
    cualesquiera. Observemos que se trata de una fórmula de tipo \<open>\<alpha>\<close> de componentes conjuntivas
    \<open>G\<close> y \<open>\<not> H\<close>. Luego, por hipótesis, tenemos que \<open>{G, \<not> H} \<union> S\<close> pertenece a \<open>C\<close>.
  \end{enumerate} 

  Finalmente, deduzcamos el resto de condiciones de la definición de propiedad de consistencia
  proposicional a partir de la hipótesis referente a las fórmulas de tipo \<open>\<beta>\<close>.
  \begin{enumerate}
    \item[\<open>4)\<close>:] Supongamos que la fórmula \<open>G \<or> H\<close> pertenece a \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close>
    cualesquiera. Observemos que se trata de una fórmula de tipo \<open>\<beta>\<close> de componentes disyuntivas
    \<open>G\<close> y \<open>H\<close>. Luego, por hipótesis, tenemos que o bien \<open>{G} \<union> S\<close> pertenece a \<open>C\<close> o bien\\
    \<open>{H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item[\<open>5)\<close>:] Supongamos que la fórmula \<open>G \<longrightarrow> H\<close> pertenece a \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close>
    cualesquiera. Observemos que se trata de una fórmula de tipo \<open>\<beta>\<close> de componentes disyuntivas
    \<open>\<not> G\<close> y \<open>H\<close>. Luego, por hipótesis, tenemos que o bien \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close> o
    bien \<open>{H} \<union> S\<close> pertenece a \<open>C\<close>.
    \item[\<open>7)\<close>:] Supongamos que la fórmula \<open>\<not>(G \<and> H)\<close> pertenece a \<open>S\<close> para fórmulas \<open>G\<close> y \<open>H\<close>
    cualesquiera. Observemos que se trata de una fórmula de tipo \<open>\<beta>\<close> de componentes disyuntivas
    \<open>\<not> G\<close> y \<open>\<not> H\<close>. Luego, por hipótesis, tenemos que o bien \<open>{\<not> G} \<union> S\<close> pertenece a \<open>C\<close> o
    bien \<open>{\<not> H} \<union> S\<close> pertenece \<open>C\<close>.
  \end{enumerate} 

  De este modo, hemos probado a partir de la hipótesis todas las condiciones que garantizan que la
  colección \<open>C\<close> cumple la propiedad de consistencia proposicional. Por lo tanto, queda demostrado el
  resultado.
\end{demostracion}

  Análogamente a la demostración del lema anterior de caracterización, para probar este resultado en 
  Isabelle vamos a demostrar cada una de las implicaciones de la equivalencia por separado. 

  La primera implicación del lema se basa en dos lemas auxiliares. El primero de ellos 
  deduce la condición de \<open>2)\<close> sobre fórmulas de tipo \<open>\<alpha>\<close> a partir de las condiciones tercera, sexta, 
  octava y novena de la definición de propiedad de consistencia proposicional. Su demostración 
  detallada en Isabelle se muestra a continuación.\<close>

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
  proof (rule allI)+
    fix F G H
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

text \<open>Finalmente, el siguiente lema auxiliar deduce la condición de \<open>2)\<close> sobre fórmulas de tipo \<open>\<beta>\<close> 
  a partir de las condiciones cuarta, quinta, sexta y séptima de la definición de propiedad de 
  consistencia proposicional.\<close>

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
  proof (rule allI)+
    fix F G H
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

text \<open>De esta manera, mediante los anteriores lemas auxiliares podemos probar la primera
  implicación detalladamente en Isabelle.\<close>

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

text \<open>Por otro lado, veamos la demostración detallada de la implicación recíproca de la
  equivalencia. Para ello, utilizaremos distintos lemas auxiliares para deducir cada una de las 
  condiciones de la definición de propiedad de consistencia proposicional a partir de las
  hipótesis sobre las fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>. En primer lugar, veamos los lemas que se deducen
  condiciones a partir de la hipótesis referente a las fórmulas de tipo \<open>\<alpha>\<close>.\<close>

lemma pcp_alt2Con1:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
proof (rule allI)+
  fix G H
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
proof (rule allI)+
  fix G H
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

lemma pcp_alt2Con4:
  assumes "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
  shows "\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
proof (rule allI)+
  fix G H
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

text \<open>Por otro lado, los siguientes lemas auxiliares prueban el resto de condiciones de la
  definición de propiedad de consistencia proposicional a partir de la hipótesis referente a 
  fórmulas de tipo \<open>\<beta>\<close>.\<close>

lemma pcp_alt2Dis1:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
proof (rule allI)+
  fix G H
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

lemma pcp_alt2Dis2:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
proof (rule allI)+
  fix G H
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

lemma pcp_alt2Dis3:
  assumes "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
  shows "\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
proof (rule allI)+
  fix G H
  show "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
  proof (rule impI)
    assume "\<^bold>\<not>(G \<^bold>\<and> H) \<in> S"
    then have "Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)"
      by (simp only: Dis.intros(3))
    let ?F="\<^bold>\<not>(G \<^bold>\<and> H)"
    have "Dis ?F (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> ?F \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
      using assms by (iprover elim: allE)
    then have "?F \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
      using \<open>Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)\<close> by (rule mp)
    thus "{\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
      using \<open>\<^bold>\<not>(G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
  qed
qed

text \<open>De este modo, procedemos a la demostración detallada de esta implicación en Isabelle.\<close>

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
  then have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    by (iprover elim: conjunct1 conjunct2)
  have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using H by (iprover elim: conjunct1 conjunct2)
  have 1:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
    using H by (iprover elim: conjunct1)
  have 2:"\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    using Con by (rule pcp_alt2Con1)
  have 3:"\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using Dis by (rule pcp_alt2Dis1)
  have 4:"\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using Dis by (rule pcp_alt2Dis2)
  have 5:"\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C"
    using Con by (rule pcp_alt2Con2)
  have 6:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C"
    using Dis by (rule pcp_alt2Dis3)
  have 7:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C"
    using Con by (rule pcp_alt2Con3)
  have 8:"\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C"
    using Con by (rule pcp_alt2Con4)
  have A:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using 1 2 3 4 by (iprover intro: conjI)
  have B:"(\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
    using 5 6 7 8 by (iprover intro: conjI)
  have "(\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))
    \<and> ((\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C))"
    using A B by (rule conjI)
  thus "\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>G H. G \<^bold>\<and> H \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<or> H \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G H. G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)
    \<and> (\<forall>G. \<^bold>\<not> (\<^bold>\<not>G) \<in> S \<longrightarrow> {G} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<and> H) \<in> S \<longrightarrow> {\<^bold>\<not> G} \<union> S \<in> C \<or> {\<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<or> H) \<in> S \<longrightarrow> {\<^bold>\<not> G, \<^bold>\<not> H} \<union> S \<in> C)
    \<and> (\<forall>G H. \<^bold>\<not>(G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> {G,\<^bold>\<not> H} \<union> S \<in> C)"
    by (iprover intro: conj_assoc)
qed

text \<open>Una vez probadas detalladamente en Isabelle cada una de las implicaciones de la
  equivalencia, podemos finalmente concluir con la demostración del lema completo.\<close>

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

text \<open>La demostración automática del resultado en Isabelle/HOL se muestra finalmente a 
  continuación.\<close>

lemma pcp_alt: "pcp C = (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))"
  apply(simp add: pcp_def con_dis_simps)
  apply(rule iffI; unfold Ball_def; elim all_forward)
  by (auto simp add: insert_absorb split: formula.splits)

section \<open>Colecciones cerradas bajo subconjuntos y colecciones de carácter finito\<close>

text \<open>En este apartado definiremos las propiedades sobre colecciones de conjuntos de ser \<open>cerrada 
  bajo subconjuntos\<close> y de \<open>carácter finito\<close>. Posteriormente daremos distintos resultados que las
  relacionan con la propiedad de consistencia proposicional y emplearemos en la prueba del 
  \<open>teorema de existencia de modelo\<close>.

\comentario{Volver a revisar el párrafo anterior al final de la
redacción de la sección.}


  \begin{definicion}
    Una colección de conjuntos es \<open>cerrada bajo subconjuntos\<close> si todo subconjunto de cada conjunto 
    de la colección pertenece a la colección.
  \end{definicion}

  En Isabelle se formaliza de la siguiente manera.\<close>

definition "subset_closed C \<equiv> (\<forall>S \<in> C. \<forall>S'\<subseteq>S. S' \<in> C)"

text \<open>Mostremos algunos ejemplos para ilustrar la definición. Para ello, veamos si las colecciones
  de conjuntos de fórmulas proposicionales expuestas en los ejemplos anteriores son cerradas bajo 
  subconjuntos.\<close>

lemma "subset_closed {{}}"
  unfolding subset_closed_def by simp

lemma "\<not> subset_closed {{Atom 0}}"
  unfolding subset_closed_def by auto

text \<open>Observemos que, puesto que el conjunto vacío es subconjunto de todo conjunto, una
  condición necesaria para que una colección sea cerrada bajo subconjuntos es que contenga al
  conjunto vacío.\<close>

lemma "subset_closed {{Atom 0},{}}"
  unfolding subset_closed_def by auto

text \<open>De este modo, se deduce fácilmente que el resto de colecciones expuestas en los ejemplos
  anteriores no son cerradas bajo subconjuntos.\<close>

lemma "\<not> subset_closed {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))},
  {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1)),  Atom 1}}" 
  unfolding subset_closed_def by auto

lemma "\<not> subset_closed {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))}}" 
  unfolding subset_closed_def by auto

text \<open>Continuemos con la noción de propiedad de carácter finito.

\begin{definicion}
  Una colección de conjuntos tiene la \<open>propiedad de carácter finito\<close> si para cualquier conjunto
  son equivalentes:
  \begin{enumerate}
    \item El conjunto pertenece a la colección.
    \item Todo subconjunto finito suyo pertenece a la colección.
  \end{enumerate}
\end{definicion}

  La formalización en Isabelle/HOL de dicha definición se muestra a continuación.\<close>

definition "finite_character C \<equiv> 
            (\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C))"

text \<open>Distingamos las colecciones de los ejemplos anteriores que tengan la propiedad de carácter 
  finito. Análogamente, puesto que el conjunto vacío es finito y subconjunto de cualquier conjunto, 
  se observa que una condición necesaria para que una colección tenga la propiedad de carácter 
  finito es que contenga al conjunto vacío.\<close>

lemma "finite_character {{}}"
  unfolding finite_character_def by auto

lemma "\<not> finite_character {{Atom 0}}"
  unfolding finite_character_def by auto

lemma "finite_character {{Atom 0},{}}"
  unfolding finite_character_def by auto

text \<open>Una vez introducidas las definiciones anteriores, veamos los resultados que las relacionan
  con la propiedad de consistencia proposicional. De este modo, combinándolos en la prueba del 
  \<open>teorema de existencia de modelo\<close>, dada una colección \<open>C\<close> cualquiera que verifique la propiedad 
  de consistencia proposicional, podemos extenderla a una colección \<open>C'\<close> que también la verifique y 
  además sea cerrada bajo subconjuntos y de carácter finito.

\comentario{Volver a revisar el párrafo anterior al final de la
redacción de la sección.}

  \begin{lema}
    Toda colección de conjuntos con la propiedad de consistencia proposicional se puede extender a
    una colección que también verifique la propiedad de consistencia proposicional y sea cerrada 
    bajo subconjuntos.
  \end{lema}

  En Isabelle se formaliza el resultado de la siguiente manera.\<close>

lemma "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
  oops

text \<open>Procedamos con su demostración.

\begin{demostracion}
  Dada una colección de conjuntos cualquiera \<open>C\<close>, consideremos la colección formada por los 
  conjuntos tales que son subconjuntos de algún conjunto de \<open>C\<close>. Notemos esta colección por 
  \<open>C' = {S'. \<exists>S\<in>C. S' \<subseteq> S}\<close>. Vamos a probar que, en efecto, \<open>C'\<close> verifica  las condiciones del lema.

  En primer lugar, veamos que \<open>C\<close> está contenida en \<open>C'\<close>. Para ello, consideremos un conjunto
  cualquiera perteneciente a \<open>C\<close>. Puesto que la propiedad de contención es reflexiva, dicho conjunto 
  es subconjunto de sí mismo. De este modo, por definición de \<open>C'\<close>, se verifica que el conjunto 
  pertenece a \<open>C'\<close>.

  Por otro lado, comprobemos que \<open>C'\<close> tiene la propiedad de consistencia proposicional.
  Por el lema de caracterización de la propiedad de consistencia proposicional mediante la
  notación uniforme basta probar que, para cualquier conjunto de fórmulas \<open>S\<close> de \<open>C'\<close>, se 
  verifican las condiciones:
  \begin{itemize}
    \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
    pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
    pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
  \end{itemize} 

  De este modo, sea \<open>S\<close> un conjunto de fórmulas cualquiera de la colección \<open>C'\<close>. Por definición de
  dicha colección, existe un conjunto \<open>S'\<close> pertenciente a \<open>C\<close> tal que \<open>S\<close> está contenido en \<open>S'\<close>.
  Como \<open>C\<close> tiene la propiedad de consistencia proposicional por hipótesis, verifica las condiciones
  del lema de caracterización de la propiedad de consistencia proposicional mediante la notación 
  uniforme. En particular, puesto que \<open>S'\<close> pertenece a \<open>C\<close>, se verifica: 
  \begin{itemize}
    \item \<open>\<bottom>\<close> no pertenece a \<open>S'\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S'\<close> y \<open>\<not> p \<in> S'\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
    pertenece a \<open>S'\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S'\<close> pertenece a \<open>C\<close>.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
    pertenece a \<open>S'\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S'\<close> pertenece a \<open>C\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S'\<close> pertenece a \<open>C\<close>.
  \end{itemize} 

  Por tanto, como \<open>S\<close> está contenida en \<open>S'\<close>, se verifica análogamente que \<open>\<bottom>\<close> no pertence a \<open>S\<close>
  y que dada una fórmula atómica cualquiera \<open>p\<close>, no se tiene simultáneamente que\\ \<open>p \<in> S\<close> y 
  \<open>\<not> p \<in> S.\<close> Veamos que se verifican el resto de condiciones del lema de caracterización:

  \<open>\<sqdot> Condición para fórmulas de tipo \<alpha>\<close>: Sea una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y 
    \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close> pertenece a \<open>S\<close>. Como \<open>S\<close> está contenida en \<open>S'\<close>, tenemos que la fórmula 
    pertence también a \<open>S'\<close>. De este modo, se verifica que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S'\<close> pertenece a la colección 
    \<open>C\<close>. Por otro lado, como el conjunto \<open>S\<close> está contenido en \<open>S'\<close>, se observa fácilmente que\\
    \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> está contenido en \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S'\<close>. Por lo tanto, el conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> está en 
    \<open>C'\<close> por definición de esta, ya que es subconjunto de \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S'\<close> que pertence a \<open>C\<close>.

  \<open>\<sqdot> Condición para fórmulas de tipo \<beta>\<close>: Sea una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y
    \<open>\<beta>\<^sub>2\<close> tal que la fórmula pertenece a \<open>S\<close>. Como el conjunto \<open>S\<close> está contenido en \<open>S'\<close>, tenemos 
    que la fórmula pertence, a su vez, a \<open>S'\<close>. De este modo, se verifica que o bien \<open>{\<beta>\<^sub>1} \<union> S'\<close>
    pertenece a \<open>C\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S'\<close> pertence a \<open>C\<close>. Por eliminación de la disyunción anterior, 
    vamos a probar que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
    \begin{itemize}
      \item Supongamos, en primer lugar, que \<open>{\<beta>\<^sub>1} \<union> S'\<close> pertenece a \<open>C\<close>. Puesto que el conjunto \<open>S\<close>
      está contenido en \<open>S'\<close>, se observa fácilmente que \<open>{\<beta>\<^sub>1} \<union> S\<close> está contenido en\\ \<open>{\<beta>\<^sub>1} \<union> S'\<close>.
      Por definición de la colección \<open>C'\<close>, tenemos que \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close>, ya que es
      subconjunto de \<open>{\<beta>\<^sub>1} \<union> S'\<close> que pertenece a \<open>C\<close>. Por tanto, hemos probado que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> 
      pertenece a \<open>C'\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
      \item Supongamos, finalmente, que \<open>{\<beta>\<^sub>2} \<union> S'\<close> pertenece a \<open>C\<close>. Análogamente obtenemos que
      \<open>{\<beta>\<^sub>2} \<union> S\<close> está contenido en \<open>{\<beta>\<^sub>2} \<union> S'\<close>, luego \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close> por definición.
      Por tanto, o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
    \end{itemize}
    De esta manera, queda probado que dada una fórmula de tipo \<open>\<beta>\<close> y componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que
    pertenezca al conjunto \<open>S\<close>, se verifica que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S\<close>
    pertenece a \<open>C'\<close>.

  En conclusión, por el lema de caracterización de la propiedad de consistencia proposicional
  mediante la notación uniforme, queda probado que \<open>C'\<close> tiene la propiedad de consistencia
  proposicional. 

  Finalmente probemos que, además, \<open>C'\<close> es cerrada bajo subconjuntos. Por definición de ser cerrado
  bajo subconjuntos, basta probar que dado un conjunto perteneciente a \<open>C'\<close> verifica que todo 
  subconjunto suyo pertenece a \<open>C'\<close>. Consideremos \<open>S\<close> un conjunto cualquiera de \<open>C'\<close>. Por
  definición de \<open>C'\<close>, existe un conjunto \<open>S'\<close> perteneciente a la colección \<open>C\<close> tal que \<open>S\<close> es
  subconjunto de \<open>S'\<close>. Sea \<open>S''\<close> un subconjunto cualquiera de \<open>S\<close>. Como \<open>S\<close> es subconjunto de \<open>S'\<close>,
  se tiene que \<open>S''\<close> es, a su vez, subconjunto de \<open>S'\<close>. De este modo, existe un conjunto 
  perteneciente a la colección \<open>C\<close> del cual \<open>S''\<close> es subconjunto. Por tanto, por definición de \<open>C'\<close>, 
  \<open>S''\<close> pertenece a la colección \<open>C'\<close>, como quería demostrar.
\end{demostracion}

  Procedamos con las demostraciones del lema en Isabelle/HOL.

  En primer lugar, vamos a introducir dos lemas auxiliares que emplearemos a lo largo de
  esta sección. El primero se trata de un lema similar al lema \<open>ballI\<close> definido en Isabelle pero 
  considerando la relación de contención en lugar de la de pertenencia.\<close>

lemma sallI: "(\<And>S. S \<subseteq> A \<Longrightarrow> P S) \<Longrightarrow> \<forall>S \<subseteq> A. P S"
  by simp

text \<open>Por último definimos el siguiente lema auxiliar similar al lema \<open>bspec\<close> de Isabelle/HOL
  considerando, análogamente, la relación de contención en lugar de la de pertenencia.\<close>

lemma sspec: "\<forall>S \<subseteq> A. P S \<Longrightarrow> S \<subseteq> A \<Longrightarrow> P S"
  by simp

text \<open>Veamos la prueba detallada del lema en Isabelle/HOL. Esta se fundamenta en tres lemas
  auxiliares: el primero prueba que la colección \<open>C\<close> está contenida en \<open>C'\<close>, el segundo que
  \<open>C'\<close> tiene la propiedad de consistencia proposicional y, finalmente, el tercer lema demuestra que
  \<open>C'\<close> es cerrada bajo subconjuntos. En primer lugar, dada una colección cualquiera \<open>C\<close>, definiremos 
  en Isabelle su extensión \<open>C'\<close> como sigue.\<close>

definition extensionSC :: "(('a formula) set) set \<Rightarrow> (('a formula) set) set"
  where extensionSC: "extensionSC C = {s. \<exists>S\<in>C. s \<subseteq> S}"

text \<open>Una vez formalizada la extensión en Isabelle, comencemos probando de manera detallada que toda
  colección está contenida en su extensión así definida.\<close>

lemma ex1_subset: "C \<subseteq> (extensionSC C)"
proof (rule subsetI)
  fix s
  assume "s \<in> C"
  have "s \<subseteq> s"
    by (rule subset_refl)
  then have "\<exists>S\<in>C. s \<subseteq> S"
    using \<open>s \<in> C\<close> by (rule bexI)
  thus "s \<in> (extensionSC C)"
    by (simp only: mem_Collect_eq extensionSC)
qed

text \<open>Prosigamos con la prueba del lema auxiliar que demuestra que \<open>C'\<close> tiene la propiedad
  de consistencia proposicional. Para ello, emplearemos un lema auxiliar que amplia el lema de 
  Isabelle \<open>insert_is_Un\<close> para la unión de dos elementos y un conjunto, como se muestra a 
  continuación.\<close>

lemma insertSetElem: "insert a (insert b C) = {a,b} \<union> C"
  by simp

text \<open>Una vez introducido dicho lema auxiliar, podemos dar la prueba detallada del lema que 
  demuestra que \<open>C'\<close> tiene la propiedad de consistencia proposicional.\<close>

lemma ex1_pcp: 
  assumes "pcp C"
  shows "pcp (extensionSC C)"
proof -
  have C1: "C \<subseteq> (extensionSC C)"
    by (rule ex1_subset)
  show "pcp (extensionSC C)"
  proof (rule pcp_alt2)
    show "\<forall>S \<in> (extensionSC C). (\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> (extensionSC C))
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionSC C) \<or> {H} \<union> S \<in> (extensionSC C)))"
    proof (rule ballI)
      fix S'
      assume "S' \<in> (extensionSC C)"
      then have 1:"\<exists>S \<in> C. S' \<subseteq> S"
        unfolding extensionSC by (rule CollectD)  
      obtain S where "S \<in> C" "S' \<subseteq> S"
        using 1 by (rule bexE)
      have "\<forall>S \<in> C.
      \<bottom> \<notin> S
      \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
        using assms by (rule pcp_alt1)
      then have H:"\<bottom> \<notin> S
      \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
        using \<open>S \<in> C\<close> by (rule bspec)
      then have "\<bottom> \<notin> S"
        by (rule conjunct1)
      have S1:"\<bottom> \<notin> S'"
        using \<open>S' \<subseteq> S\<close> \<open>\<bottom> \<notin> S\<close> by (rule contra_subsetD)
      have Atom:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
        using H by (iprover elim: conjunct1 conjunct2)
      have S2:"\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
      proof (rule allI)
        fix k
        show "Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
        proof (rule impI)+
          assume "Atom k \<in> S'"
          assume "\<^bold>\<not> (Atom k) \<in> S'"
          have "Atom k \<in> S" 
            using \<open>S' \<subseteq> S\<close> \<open>Atom k \<in> S'\<close> by (rule set_mp)
          have "\<^bold>\<not> (Atom k) \<in> S"
            using \<open>S' \<subseteq> S\<close> \<open>\<^bold>\<not> (Atom k) \<in> S'\<close> by (rule set_mp)
          have "Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
            using Atom by (rule allE)
          then have "\<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
            using \<open>Atom k \<in> S\<close> by (rule mp)
          thus "False"
            using \<open>\<^bold>\<not> (Atom k) \<in> S\<close> by (rule mp)
        qed
      qed
      have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        using H by (iprover elim: conjunct1 conjunct2)
      have S3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> (extensionSC C)"
      proof (rule allI)+
        fix F G H
        show "Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> (extensionSC C)"
        proof (rule impI)+
          assume "Con F G H"
          assume "F \<in> S'"
          have "F \<in> S"
            using \<open>S' \<subseteq> S\<close> \<open>F \<in> S'\<close> by (rule set_mp)
          have "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
            using Con by (iprover elim: allE)
          then have "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
            using \<open>Con F G H\<close> by (rule mp)
          then have "{G,H} \<union> S \<in> C"
            using \<open>F \<in> S\<close> by (rule mp)
          have "S' \<subseteq> insert H S"
            using \<open>S' \<subseteq> S\<close> by (rule subset_insertI2) 
          then have "insert H S' \<subseteq> insert H (insert H S)"
            by (simp only: insert_mono)
          then have "insert H S' \<subseteq> insert H S"
            by (simp only: insert_absorb2)
          then have "insert G (insert H S') \<subseteq> insert G (insert H S)"
            by (simp only: insert_mono)
          have A:"insert G (insert H S') = {G,H} \<union> S'"
            by (rule insertSetElem) 
          have B:"insert G (insert H S) = {G,H} \<union> S"
            by (rule insertSetElem)
          have "{G,H} \<union> S' \<subseteq> {G,H} \<union> S" 
            using \<open>insert G (insert H S') \<subseteq> insert G (insert H S)\<close> by (simp only: A B)
          then have "\<exists>S \<in> C. {G,H} \<union> S' \<subseteq> S"
            using \<open>{G,H} \<union> S \<in> C\<close> by (rule bexI)
          thus "{G,H} \<union> S' \<in> (extensionSC C)" 
            unfolding extensionSC by (rule CollectI)
        qed
      qed
      have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using H by (iprover elim: conjunct2)
      have S4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> (extensionSC C) \<or> {H} \<union> S' \<in> (extensionSC C)"
      proof (rule allI)+
        fix F G H
        show "Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> (extensionSC C) \<or> {H} \<union> S' \<in> (extensionSC C)"
        proof (rule impI)+
          assume "Dis F G H"
          assume "F \<in> S'"
          have "F \<in> S"
            using \<open>S' \<subseteq> S\<close> \<open>F \<in> S'\<close> by (rule set_mp)
          have "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
            using Dis by (iprover elim: allE)
          then have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
            using \<open>Dis F G H\<close> by (rule mp)
          then have 9:"{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
            using \<open>F \<in> S\<close> by (rule mp)
          show "{G} \<union> S' \<in> (extensionSC C) \<or> {H} \<union> S' \<in> (extensionSC C)"
            using 9
          proof (rule disjE)
            assume "{G} \<union> S \<in> C"
            have "insert G S' \<subseteq> insert G S"
              using \<open>S' \<subseteq> S\<close> by (simp only: insert_mono)
            have C:"insert G S' = {G} \<union> S'"
              by (rule insert_is_Un)
            have D:"insert G S = {G} \<union> S"
              by (rule insert_is_Un)
            have "{G} \<union> S' \<subseteq> {G} \<union> S"
              using \<open>insert G S' \<subseteq> insert G S\<close> by (simp only: C D)
            then have "\<exists>S \<in> C. {G} \<union> S' \<subseteq> S"
              using \<open>{G} \<union> S \<in> C\<close> by (rule bexI)
            then have "{G} \<union> S' \<in> (extensionSC C)"
              unfolding extensionSC by (rule CollectI)
            thus "{G} \<union> S' \<in> (extensionSC C) \<or> {H} \<union> S' \<in> (extensionSC C)"
              by (rule disjI1)
          next
            assume "{H} \<union> S \<in> C"
            have "insert H S' \<subseteq> insert H S"
              using \<open>S' \<subseteq> S\<close> by (simp only: insert_mono)
            have E:"insert H S' = {H} \<union> S'"
              by (rule insert_is_Un)
            have F:"insert H S = {H} \<union> S"
              by (rule insert_is_Un)
            then have "{H} \<union> S' \<subseteq> {H} \<union> S"
              using \<open>insert H S' \<subseteq> insert H S\<close> by (simp only: E F)
            then have "\<exists>S \<in> C. {H} \<union> S' \<subseteq> S"
              using \<open>{H} \<union> S \<in> C\<close> by (rule bexI)
            then have "{H} \<union> S' \<in> (extensionSC C)"
              unfolding extensionSC by (rule CollectI)
            thus "{G} \<union> S' \<in> (extensionSC C) \<or> {H} \<union> S' \<in> (extensionSC C)"
              by (rule disjI2)
          qed
        qed
      qed
      show "\<bottom> \<notin> S'
    \<and> (\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> (extensionSC C))
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> (extensionSC C) \<or> {H} \<union> S' \<in> (extensionSC C))"
        using S1 S2 S3 S4 by (iprover intro: conjI)
    qed
  qed
qed

text \<open>Finalmente, el siguiente lema auxiliar prueba que \<open>C'\<close> es cerrada bajo subconjuntos.\<close>

lemma ex1_subset_closed:
  assumes "pcp C"
  shows "subset_closed (extensionSC C)"
  unfolding subset_closed_def
proof (rule ballI)
  fix S'
  assume "S' \<in> (extensionSC C)"
  then have H:"\<exists>S \<in> C. S' \<subseteq> S"
    unfolding extensionSC by (rule CollectD)
  obtain S where \<open>S \<in> C\<close> and \<open>S' \<subseteq> S\<close> 
    using H by (rule bexE) 
  show "\<forall>S'' \<subseteq> S'. S'' \<in> (extensionSC C)"
  proof (rule sallI)
    fix S''
    assume "S'' \<subseteq> S'" 
    then have "S'' \<subseteq> S"
      using \<open>S' \<subseteq> S\<close> by (rule subset_trans)
    then have "\<exists>S \<in> C. S'' \<subseteq> S"
      using \<open>S \<in> C\<close> by (rule bexI)
    thus "S'' \<in> (extensionSC C)"
      unfolding extensionSC by (rule CollectI)
  qed
qed

text \<open>En conclusión, la prueba detallada del lema completo se muestra a continuación.\<close>

lemma ex1: 
  assumes "pcp C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof -
  have C1:"C \<subseteq> (extensionSC C)"
    by (rule ex1_subset)
  have C2:"pcp (extensionSC C)"
    using assms by (rule ex1_pcp)
  have C3:"subset_closed (extensionSC C)"
    using assms by (rule ex1_subset_closed)
  have "C \<subseteq> (extensionSC C) \<and> pcp (extensionSC C) \<and> subset_closed (extensionSC C)" 
    using C1 C2 C3 by (iprover intro: conjI)
  thus ?thesis
    by (rule exI)
qed

text\<open>Continuemos con el segundo resultado de este apartado.

  \begin{lema}
  Toda colección de conjuntos con la propiedad de carácter finito es cerrada bajo subconjuntos.
  \end{lema}

  En Isabelle, se formaliza como sigue.\<close>

lemma 
  assumes "finite_character C"
  shows "subset_closed C"
  oops

text \<open>Procedamos con la demostración del resultado.

  \begin{demostracion}
    Consideremos una colección de conjuntos \<open>C\<close> con la propiedad de carácter finito. Probemos que, 
    en efecto, es cerrada bajo subconjuntos. Por definición de esta última propiedad, basta 
    demostrar que todo subconjunto de cada conjunto de \<open>C\<close> pertenece también a \<open>C\<close>.

    Para ello, tomemos un conjunto \<open>S\<close> cualquiera perteneciente a \<open>C\<close> y un subconjunto cualquiera 
    \<open>S'\<close> de \<open>S\<close>. Probemos que \<open>S'\<close> está en \<open>C\<close>. Por hipótesis, como \<open>C\<close> tiene la propiedad de carácter 
    finito, verifica que, para cualquier conjunto \<open>A\<close>, son equivalentes:
    \begin{enumerate}
      \item \<open>A\<close> pertenece a \<open>C\<close>.
      \item Todo subconjunto finito de \<open>A\<close> pertenece a \<open>C\<close>.
    \end{enumerate}

    Para probar que el subconjunto \<open>S'\<close> pertenece a \<open>C\<close>, vamos a demostrar que todo subconjunto 
    finito de \<open>S'\<close> pertenece a \<open>C\<close>.

    De este modo, consideremos un subconjunto cualquiera \<open>S''\<close> de \<open>S'\<close>. Como \<open>S'\<close> es subconjunto de \<open>S\<close>, 
    por la transitividad de la relación de contención de conjuntos, se tiene que \<open>S''\<close> es subconjunto 
    de \<open>S\<close>. Aplicando la definición de propiedad de carácter finito de \<open>C\<close> para el conjunto \<open>S\<close>, 
    como este pertenece a \<open>C\<close>, verifica que todo subconjunto finito de \<open>S\<close> pertenece a \<open>C\<close>. En
    particular, como \<open>S''\<close> es subconjunto de \<open>S\<close>, verifica que, si \<open>S''\<close> es finito, entonces \<open>S''\<close> 
    pertenece a \<open>C\<close>. Por tanto, hemos probado que cualquier conjunto finito de \<open>S'\<close> pertenece a la
    colección. Finalmente por la propiedad de carácter finito de \<open>C\<close>, se verifica que \<open>S'\<close> pertenece 
    a \<open>C\<close>, como queríamos demostrar.
  \end{demostracion}

  Veamos, a continuación, la demostración detallada del resultado en Isabelle.\<close>

lemma
  assumes "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix S' S
  assume  \<open>S \<in> C\<close> and \<open>S' \<subseteq> S\<close>
  have H:"\<forall>A. A \<in> C \<longleftrightarrow> (\<forall>A' \<subseteq> A. finite A' \<longrightarrow> A' \<in> C)"
    using assms unfolding finite_character_def by this
  have QPQ:"\<forall>S'' \<subseteq> S'. finite S'' \<longrightarrow> S'' \<in> C"
  proof (rule sallI)
    fix S''
    assume "S'' \<subseteq> S'"
    then have "S'' \<subseteq> S"
      using \<open>S' \<subseteq> S\<close> by (simp only: subset_trans)
    have 1:"S \<in> C \<longleftrightarrow> (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C)"
      using H by (rule allE)
    have "\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
      using \<open>S \<in> C\<close> 1 by (rule back_subst)
    thus "finite S'' \<longrightarrow> S'' \<in> C"
      using \<open>S'' \<subseteq> S\<close> by (rule sspec)
  qed
  have "S' \<in> C \<longleftrightarrow> (\<forall>S'' \<subseteq> S'. finite S'' \<longrightarrow> S'' \<in> C)"
    using H by (rule allE)
  thus "S' \<in> C"
    using QPQ by (rule forw_subst)
qed

text \<open>Finalmente, su prueba automática en Isabelle/HOL es la siguiente.\<close>

lemma ex2: 
  assumes fc: "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix S' S
  assume e: \<open>S \<in> C\<close> and s: \<open>S' \<subseteq> S\<close>
  hence *: "S'' \<subseteq> S' \<Longrightarrow> S'' \<subseteq> S" for S'' by simp
  from fc have "S'' \<subseteq> S \<Longrightarrow> finite S'' \<Longrightarrow> S'' \<in> C" for S'' 
    unfolding finite_character_def using e by blast
  hence "S'' \<subseteq> S' \<Longrightarrow> finite S'' \<Longrightarrow> S'' \<in> C" for S'' using * by simp
  with fc show \<open>S' \<in> C\<close> unfolding finite_character_def by blast
qed

text\<open>Introduzcamos el último resultado de la sección.

 \begin{lema}
    Toda colección de conjuntos con la propiedad de consistencia proposicional y cerrada bajo 
    subconjuntos se puede extender a una colección que también verifique la propiedad de 
    consistencia proposicional y sea de carácter finito.
 \end{lema}

 \begin{demostracion}
   Dada una colección de conjuntos \<open>C\<close> en las condiciones del enunciado, vamos a considerar su 
   extensión \<open>C'\<close> definida como la unión de \<open>C\<close> y la colección formada por aquellos conjuntos
   cuyos subconjuntos finitos pertenecen a \<open>C\<close>. Es decir,\\ \<open>C' = C \<union> E\<close> donde 
   \<open>E = {S. \<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C}\<close>. Es evidente que es extensión pues contiene 
   a la colección \<open>C\<close>. Vamos a probar que, además es de carácter finito y verifica la 
   propiedad de consistencia proposicional.

   En primer lugar, demostremos que \<open>C'\<close> es de carácter finito. Por definición de dicha propiedad, 
   basta probar que, para cualquier conjunto, son equivalentes:
   \begin{enumerate}
    \item El conjunto pertenece \<open>C'\<close>.
    \item Todo subconjunto finito suyo pertenece a \<open>C'\<close>.
   \end{enumerate}

   Comencemos probando \<open>1) \<Longrightarrow> 2)\<close>. Para ello, sea un conjunto \<open>S\<close> de \<open>C'\<close> de modo que \<open>S'\<close> es un
   subconjunto finito suyo. Como \<open>S\<close> pertenece a la extensión, por definición de la misma tenemos
   que o bien \<open>S\<close> está en \<open>C\<close> o bien \<open>S\<close> está en \<open>E\<close>. Vamos a probar que \<open>S'\<close> está en \<open>C'\<close> por
   eliminación de la disyunción anterior. En primer lugar, si suponemos que \<open>S\<close> está en \<open>C\<close>, como
   se trata de una colección cerrada bajo subconjuntos, tenemos que todo subconjunto de \<open>S\<close> está en 
   \<open>C\<close>. En particular, \<open>S'\<close> está en \<open>C\<close> y, por definición de la extensión, se prueba
   que \<open>S'\<close> está en \<open>C'\<close>. Por otro lado, suponiendo que \<open>S\<close> esté en \<open>E\<close>, por definición de dicha 
   colección tenemos que todo subconjunto finito de \<open>S\<close> está en \<open>C\<close>. De este modo, por las hipótesis 
   se prueba que \<open>S'\<close> está en \<open>C\<close> y, por tanto, pertenece a la extensión. 

   Por último, probemos la implicación \<open>2) \<Longrightarrow> 1)\<close>. Sea un conjunto cualquiera \<open>S\<close> tal que todo
   subconjunto finito suyo pertenece a \<open>C'\<close>. Vamos a probar que \<open>S\<close> también pertenece a \<open>C'\<close>. En
   particular, probaremos que pertenece a \<open>E\<close>. Luego basta probar que todo subconjunto finito de 
   \<open>S\<close> pertenece a \<open>C\<close>. Para ello, consideremos \<open>S'\<close> un subconjunto finito cualquiera de \<open>S\<close>. Por
   hipótesis, tenemos que \<open>S'\<close> pertenece a \<open>C'\<close>. Por definición de la extensión, tenemos entonces
   que o bien \<open>S'\<close> está en \<open>C\<close> (lo que daría por concluida la prueba) o bien \<open>S'\<close> está en \<open>E\<close>. 
   De este modo, si suponemos que \<open>S'\<close> está en \<open>E\<close>, por definición de dicha colección tenemos que
   todo subconjunto finito suyo está en \<open>C\<close>. En particular, como todo conjunto es subconjunto de si
   mismo y como hemos supuesto que \<open>S'\<close> es finito, tenemos que \<open>S'\<close> está en \<open>C\<close>, lo que prueba la
   implicación.

   Probemos, finalmente, que \<open>C'\<close> verifica la propiedad de consistencia proposicional. Para ello,
   vamos a considerar un conjunto cualquiera \<open>S\<close> perteneciente a \<open>C'\<close> y probaremos que se verifican 
   las cuatro condiciones del lema de caracterización de la propiedad de consistencia proposicional
   mediante la notación uniforme. Como el conjunto \<open>S\<close> pertenece a \<open>C'\<close>, se observa fácilmente por
   definición de la extensión que, o bien \<open>S\<close> está en \<open>C\<close> o bien \<open>S\<close> está en \<open>E\<close>. Veamos que, para 
   ambos casos, se verifican dichas condiciones.

   En primer lugar, supongamos que \<open>S\<close> está en \<open>C\<close>. Como \<open>C\<close> verifica la propiedad de consistencia 
   proposicional por hipótesis, verifica el lema de caracterización en particular para el conjunto 
   \<open>S\<close>. De este modo, se cumple:
   \begin{itemize}
     \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
     \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
     \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
      pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
     \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
      pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> o 
      bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>.
   \end{itemize} 
  
  Por lo tanto, puesto que \<open>C\<close> está contenida en la extensión \<open>C'\<close>, se verifican las cuatro
  condiciones del lema para \<open>C'\<close>.

  Supongamos ahora que \<open>S\<close> está en \<open>E\<close>. Probemos que, en efecto, verifica las condiciones del lema 
  de caracterización.

  En primer lugar vamos a demostrar que \<open>\<bottom> \<notin> S\<close> por reducción al absurdo. Si suponemos que \<open>\<bottom> \<in> S\<close>,
  se deduce que el conjunto \<open>{\<bottom>}\<close> es un subconjunto finito de \<open>S\<close>. Como \<open>S\<close> está en \<open>E\<close>, por
  definición tenemos que \<open>{\<bottom>} \<in> C\<close>. De este modo, aplicando el lema de\\ caracterización de la
  propiedad de consistencia proposicional para la colección \<open>C\<close> y el conjunto \<open>{\<bottom>}\<close>, por la primera
  condición obtenemos que \<open>\<bottom> \<notin> {\<bottom>}\<close>, llegando a una contradicción.

  Demostremos que se verifica la segunda condición del lema para las fórmulas atómicas. De este
  modo, vamos a probar que dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene simultáneamente que
  \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>. La prueba se realizará por reducción al absurdo, luego supongamos que para
  cierta fórmula atómica se verifica \<open>p \<in> S\<close> y\\ \<open>\<not> p \<in> S\<close>. Análogamente, se observa que el conjunto
  \<open>{p, \<not> p}\<close> es un subconjunto finito de \<open>S\<close>, luego pertenece a \<open>C\<close>. Aplicando el lema de
  caracterización de la propiedad de consistencia proposicional para la colección \<open>C\<close> y el conjunto
  \<open>{p, \<not> p}\<close>, por la segunda condición obtenemos que no se tiene simultáneamente \<open>q \<in> {p, \<not> p}\<close> y
  \<open>\<not> q \<in> {p, \<not> p}\<close> para ninguna fórmula atómica \<open>q\<close>, llegando así a una contradicción para la
  fórmula atómica \<open>p\<close>.

  Por otro lado, vamos a probar que se verifica la tercera condición del lema de\\ caracterización
  sobre las fórmulas de tipo \<open>\<alpha>\<close>. Consideremos una fórmula cualquiera \<open>F\<close> de tipo \<open>\<alpha>\<close> y componentes 
  \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, y supongamos que \<open>F \<in> S\<close>. Demostraremos que\\ \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S \<in> C'\<close>. 

  Para ello, probaremos inicialmente que todo subconjunto finito \<open>S'\<close> de \<open>S\<close> tal que\\ \<open>F \<in> S'\<close> 
  verifica \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S' \<in> C\<close>. Consideremos \<open>S'\<close> subconjunto finito cualquiera de \<open>S\<close> en las
  condiciones anteriores. Como \<open>S \<in> E\<close>, por definición tenemos que \<open>S' \<in> C\<close>. Aplicando el lema de 
  caracterización de la propiedad de consistencia proposicional para la colección \<open>C\<close> y el conjunto
  \<open>S'\<close>, por la tercera condición obtenemos que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S' \<in> C\<close> ya que hemos supuesto que 
  \<open>F \<in> S'\<close>.

  Una vez probado el resultado anterior, demostremos que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S \<in> E\<close> y, por definición de 
  \<open>C'\<close>, obtendremos \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S \<in> C'\<close>. Además, por definición de \<open>E\<close>, basta probar que todo 
  subconjunto finito de \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close>. Consideremos \<open>S'\<close> un subconjunto finito 
  cualquiera de \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close>. Como \<open>F \<in> S\<close>, es sencillo comprobar que el conjunto 
  \<open>{F} \<union> (S' - {\<alpha>\<^sub>1,\<alpha>\<^sub>2})\<close> es un subconjunto finito de \<open>S\<close>. Por el resultado probado anteriormente, 
  tenemos que el conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> ({F} \<union> (S' - {\<alpha>\<^sub>1,\<alpha>\<^sub>2})) = \<close> \\ \<open>= {F,\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S'\<close> pertenece a \<open>C\<close>. 
  Además, como \<open>C\<close> es cerrada bajo subconjuntos, todo conjunto de \<open>C\<close> verifica que cualquier 
  subconjunto suyo pertenece a la colección. Luego, como \<open>S'\<close> es un subconjunto de 
  \<open>{F,\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S'\<close>, queda probado que \<open>S' \<in> C\<close>.

  Finalmente, veamos que se verifica la última condición del lema de caracterización de la propiedad
  de consistencia proposicional referente a las fórmulas de tipo \<open>\<beta>\<close>. Consideremos una fórmula 
  cualquiera \<open>F\<close> de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>F \<in> S\<close>. Vamos a probar que se
  tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> E\<close> o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> E\<close>. En tal caso, por definición de \<open>C'\<close> se
  cumple que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close> o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close>. La prueba se realizará por reducción al
  absurdo. Para ello, probemos inicialmente dos resultados previos.

  \begin{description}
    \item[\<open>\<one>)\<close>] En las condiciones anteriores, si consideramos \<open>S\<^sub>1\<close> y \<open>S\<^sub>2\<close> subconjuntos finitos 
    cualesquiera de \<open>S\<close> tales que \<open>F \<in> S\<^sub>1\<close> y \<open>F \<in> S\<^sub>2\<close>, entonces existe una fórmula \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal 
    que se verifica que tanto \<open>{I} \<union> S\<^sub>1\<close> como \<open>{I} \<union> S\<^sub>2\<close> están en \<open>C\<close>.
  \end{description}
  
  Para probar \<open>\<one>)\<close>, consideremos el conjunto finito \<open>S\<^sub>1 \<union> S\<^sub>2\<close> que es subconjunto de \<open>S\<close> por las 
  hipótesis. De este modo, como \<open>S \<in> E\<close>, tenemos que \<open>S\<^sub>1 \<union> S\<^sub>2 \<in> C\<close>. Aplicando el lema de 
  caracterización de la propiedad de consistencia proposicional para la colección \<open>C\<close> y el conjunto 
  \<open>S\<^sub>1 \<union> S\<^sub>2\<close>, por la última condición sobre las fórmulas de tipo \<open>\<beta>\<close>, como\\ \<open>F \<in> S\<^sub>1 \<union> S\<^sub>2\<close> por las 
  hipótesis, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<^sub>1 \<union> S\<^sub>2 \<in> C\<close> o bien\\ \<open>{\<beta>\<^sub>2} \<union> S\<^sub>1 \<union> S\<^sub>2 \<in> C\<close>. Por tanto, 
  existe una fórmula \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal que\\ \<open>{I} \<union> S\<^sub>1 \<union> S\<^sub>2 \<in> C\<close>. Sea \<open>I\<close> la fórmula que cumple lo 
  anterior. Como \<open>C\<close> es cerrada bajo subconjuntos, los subconjuntos \<open>{I} \<union> S\<^sub>1\<close> y \<open>{I} \<union> S\<^sub>2\<close> de 
  \<open>{I} \<union> S\<^sub>1 \<union> S\<^sub>2\<close> pertenecen también a \<open>C\<close>. Por tanto, hemos probado que existe una fórmula 
  \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal que \<open>{I} \<union> S\<^sub>1 \<in> C\<close> y \<open>{I} \<union> S\<^sub>2 \<in> C\<close>.

  Por otra parte, veamos el segundo resultado. 

  \begin{description}
    \item[\<open>\<two>)\<close>] En las condiciones de \<open>\<one>)\<close> para conjuntos cualesquiera \<open>S\<^sub>1\<close> y \<open>S\<^sub>2\<close>, si además 
    suponemos que \<open>{\<beta>\<^sub>1} \<union> S\<^sub>1 \<notin> C\<close> y \<open>{\<beta>\<^sub>2} \<union> S\<^sub>2 \<notin> C\<close>, llegamos a una contradicción. 
  \end{description}

  Para probarlo, utilizaremos \<open>\<one>)\<close> para los conjuntos \<open>{F} \<union> S\<^sub>1\<close> y \<open>{F} \<union> S\<^sub>2\<close>. Como es evidente, 
  puesto que \<open>F \<in> S\<close>, se verifica que ambos conjuntos son subconjuntos de \<open>S\<close>. Además, como \<open>S\<^sub>1\<close> y 
  \<open>S\<^sub>2\<close> son finitos, se tiene que \<open>{F} \<union> S\<^sub>1\<close> y \<open>{F} \<union> S\<^sub>2\<close> también lo son. Por último, es claro que 
  \<open>F\<close> pertenece a ambos conjuntos. Por lo tanto, por \<open>\<one>)\<close> tenemos que existe una fórmula 
  \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal que \<open>{I} \<union> {F} \<union> S\<^sub>1 \<in> C\<close> y \<open>{I} \<union> {F} \<union> S\<^sub>2 \<in> C\<close>. Por otro lado, podemos probar 
  que \<open>{\<beta>\<^sub>1} \<union> {F} \<union> S\<^sub>1 \<notin> C\<close>. Esto se debe a que, en caso contrario, como \<open>C\<close> es cerrado bajo 
  subconjuntos, tendríamos que el subconjunto\\ \<open>{\<beta>\<^sub>1} \<union> S\<^sub>1\<close> pertenecería a \<open>C\<close>, lo que contradice las 
  hipótesis. Análogamente, obtenemos que \<open>{\<beta>\<^sub>2} \<union> {F} \<union> S\<^sub>2 \<notin> C\<close>. De este modo, obtenemos que para 
  toda fórmula \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> se cumple que o bien \<open>{I} \<union> {F} \<union> S\<^sub>1 \<notin> C\<close> o bien \<open>{I} \<union> {F} \<union> S\<^sub>2 \<notin> C\<close>. 
  Esto es equivalente a que no existe ninguna fórmula \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal que \<open>{I} \<union> {F} \<union> S\<^sub>1 \<in> C\<close> y\\ 
  \<open>{I} \<union> {F} \<union> S\<^sub>2 \<in> C\<close>, lo que contradice lo obtenido para los conjuntos \<open>{F} \<union> S\<^sub>1\<close> y\\ \<open>{F} \<union> S\<^sub>2\<close> 
  por \<open>\<one>)\<close>.

  Finalmente, con los resultados anteriores, podemos probar que o bien\\ \<open>{\<beta>\<^sub>1} \<union> S \<in> E\<close> o bien 
  \<open>{\<beta>\<^sub>2} \<union> S \<in> E\<close> por reducción al absurdo. Supongamos que\\ \<open>{\<beta>\<^sub>1} \<union> S \<notin> E\<close> y \<open>{\<beta>\<^sub>2} \<union> S \<notin> E\<close>. Por
  definición de \<open>E\<close>, se verifica que existe algún subconjunto finito de \<open>{\<beta>\<^sub>1} \<union> S\<close> y existe algún 
  subconjunto finito de \<open>{\<beta>\<^sub>2} \<union> S\<close> tales que no pertenecen a \<open>C\<close>. Notemos por \<open>S\<^sub>1\<close> y \<open>S\<^sub>2\<close> 
  respectivamente a los subconjuntos anteriores. Vamos a aplicar \<open>\<two>)\<close> para los conjuntos \<open>S\<^sub>1 - {\<beta>\<^sub>1}\<close> 
  y \<open>S\<^sub>2 - {\<beta>\<^sub>2}\<close> para llegar a la contradicción.

  Para ello, debemos probar que se verifican las hipótesis del resultado para los conjuntos
  señalados. Es claro que tanto \<open>S\<^sub>1 - {\<beta>\<^sub>1}\<close> como \<open>S\<^sub>2 - {\<beta>\<^sub>2}\<close> son subconjuntos de \<open>S\<close>, ya que \<open>S\<^sub>1\<close> y
  \<open>S\<^sub>2\<close> son subconjuntos de \<open>{\<beta>\<^sub>1} \<union> S\<close> y \<open>{\<beta>\<^sub>2} \<union> S\<close> respectivamente. Además, como \<open>S\<^sub>1\<close> y \<open>S\<^sub>2\<close> son
  finitos, es evidente que \<open>S\<^sub>1 - {\<beta>\<^sub>1}\<close> y \<open>S\<^sub>2 - {\<beta>\<^sub>2}\<close> también lo son. Queda probar que los conjuntos 
  \<open>{\<beta>\<^sub>1} \<union> (S\<^sub>1 - {\<beta>\<^sub>1}) = {\<beta>\<^sub>1} \<union> S\<^sub>1\<close> y \<open>{\<beta>\<^sub>2} \<union> (S\<^sub>2 - {\<beta>\<^sub>2}) = {\<beta>\<^sub>2} \<union> S\<^sub>2\<close> no pertenecen a \<open>C\<close>. Como ni 
  \<open>S\<^sub>1\<close> ni \<open>S\<^sub>2\<close> están en la colección \<open>C\<close> cerrada bajo subconjuntos, se cumple que ninguno de ellos 
  son subconjuntos de \<open>S\<close>. Sin embargo, se verifica que \<open>S\<^sub>1\<close> es subconjunto de \<open>{\<beta>\<^sub>1} \<union> S\<close> y \<open>S\<^sub>2\<close> es 
  subconjunto de \<open>{\<beta>\<^sub>2} \<union> S\<close>. Por tanto, se cumple que\\ \<open>\<beta>\<^sub>1 \<in> S\<^sub>1\<close> y \<open>\<beta>\<^sub>2 \<in> S\<^sub>2\<close>. Por lo tanto,
  tenemos finalmente que los conjuntos \<open>{\<beta>\<^sub>1} \<union> S\<^sub>1 = S\<^sub>1\<close> y\\ \<open>{\<beta>\<^sub>2} \<union> S\<^sub>2 = S\<^sub>2\<close> no pertenecen a \<open>C\<close>.
  Finalmente, como se cumplen las condiciones del resultado \<open>2)\<close>, llegamos a una contradicción para 
  los conjuntos \<open>S\<^sub>1 - {\<beta>\<^sub>1}\<close> y \<open>S\<^sub>2 - {\<beta>\<^sub>2}\<close>, probando que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> E\<close> o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> E\<close>. 
  Por lo tanto, obtenemos por definición de \<open>C'\<close> que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close> o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close>.
 \end{demostracion}

  Finalmente, veamos la demostración detallada del lema en Isabelle. Debido a la cantidad de lemas
  auxiliares empleados en la prueba detallada, para facilitar la comprensión mostraremos a
  continuación un grafo que estructura las relaciones de necesidad de los lemas introducidos.
  
 \begin{tikzpicture}
  [
    grow                    = down,
    level 1/.style          = {sibling distance=7cm},
    level 2/.style          = {sibling distance=4cm},
    level 3/.style          = {sibling distance=5.7cm},
    level distance          = 1.5cm,
    edge from parent/.style = {draw},
    every node/.style       = {font=\tiny},
    sloped
  ]
  \node [root] {\<open>ex3\<close>\\ \<open>(Lema 1.3.5)\<close>}
    child { node [env] {\<open>ex3_finite_character\<close>\\ \<open>(C' tiene la propiedad de carácter finito)\<close>}}
    child { node [env] {\<open>ex3_pcp\<close>\\ \<open>(C' tiene la propiedad de consistencia proposicional)\<close>}
      		child { node [env] {\<open>ex3_pcp_SinC\<close>\\ \<open>(Caso del conjunto en C)\<close>}}
      		child { node [env] {\<open>ex3_pcp_SinE\<close>\\ \<open>(Caso del conjunto en E)\<close>}
        				child { node [env] {\<open>ex3_pcp_SinE_CON\<close>\\ \<open>(Condición fórmulas de tipo \<alpha>)\<close>}}
        				child { node [env] {\<open>ex3_pcp_SinE_DIS\<close>\\ \<open>(Condición fórmulas de tipo \<beta>)\<close>}
                      child { node [env] {\<open>ex3_pcp_SinE_DIS_auxFalse\<close>\\ \<open>(Resultado \<one>)\<close>}
                            child { node [env] {\<open>ex3_pcp_SinE_DIS_auxEx\<close>\\ \<open>(Resultado \<two>)\<close>}}}}}};
\end{tikzpicture}

  De este modo, la prueba del \<open>lema 1.3.5\<close> se estructura fundamentalmente en dos lemas auxiliares. 
  El primero, formalizado como \<open>ex3_finite_character\<close> en Isabelle, prueba que la extensión 
  \<open>C' = C \<union> E\<close>, donde \<open>E\<close> es la colección formada por aquellos conjuntos cuyos subconjuntos finitos 
  pertenecen a \<open>C\<close>, tiene la propiedad de carácter finito. El segundo, formalizado como \<open>ex3_pcp\<close>, 
  demuestra que \<open>C'\<close> verifica la propiedad de consistencia proposicional demostrando que cumple las 
  condiciones suficientes de dicha propiedad por el lema de caracterización \<open>1.2.5\<close>. De este modo, 
  considerando un conjunto \<open>S \<in> C'\<close>, \<open>ex3_pcp\<close> precisa, a su vez, de dos lemas auxiliares que 
  prueben las condiciones suficientes de \<open>1.2.5\<close>: uno para el caso en que \<open>S \<in> C\<close> (\<open>ex3_pcp_SinC\<close>) y 
  otro para el caso en que \<open>S \<in> E\<close> (\<open>ex3_pcp_SinE\<close>). Por otro lado, para el último caso en que 
  \<open>S \<in> E\<close>, utilizaremos dos lemas auxiliares. El primero, formalizado como \<open>ex3_pcp_SinE_CON\<close>, 
  prueba que para \<open>C\<close> una colección con la propiedad de consistencia proposicional y cerrada bajo 
  subconjuntos, \<open>S \<in> E\<close> y sea \<open>F\<close> una fórmula de tipo \<open>\<alpha>\<close> y componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, se tiene que 
  \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S \<in> C'\<close>. El segundo lema, formalizado como \<open>ex3_pcp_SinE_DIS\<close>, prueba que para \<open>C\<close> una 
  colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, \<open>S \<in> E\<close> y 
  sea \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> y componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close> o 
  bien \<open>{\<beta>\<^sub>2} \<union> S \<in> C'\<close>. Por último, este segundo lema auxiliar se probará por reducción al absurdo, 
  precisando para ello de los siguientes resultados auxiliares:
  
  \begin{description}
    \item[\<open>Resultado \<one>\<close>] Formalizado como \<open>ex3_pcp_SinE_DIS_auxEx\<close>. Prueba que dada \<open>C\<close> una 
    colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, \<open>S \<in> E\<close> y 
    sea \<open>F\<close> es una fórmula de tipo \<open>\<beta>\<close> de componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, si consideramos \<open>S\<^sub>1\<close> y \<open>S\<^sub>2\<close> 
    subconjuntos finitos cualesquiera de \<open>S\<close> tales que \<open>F \<in> S\<^sub>1\<close> y \<open>F \<in> S\<^sub>2\<close>, entonces existe una 
    fórmula \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal que se verifica que tanto \<open>{I} \<union> S\<^sub>1\<close> como \<open>{I} \<union> S\<^sub>2\<close> están en \<open>C\<close>. 
    \item[\<open>Resultado \<two>\<close>] Formalizado como \<open>ex3_pcp_SinE_DIS_auxFalse\<close>. Utiliza 
    \<open>ex3_pcp_SinE_DIS_auxEx\<close> como lema auxiliar. Prueba que, en las condiciones del \<open>Resultado \<one>\<close>, 
    si además suponemos que \<open>{\<beta>\<^sub>1} \<union> S\<^sub>1 \<notin> C\<close> y \<open>{\<beta>\<^sub>2} \<union> S\<^sub>2 \<notin> C\<close>, llegamos a una contradicción.
  \end{description} 

  Por otro lado, para facilitar la notación, dada una colección cualquiera \<open>C\<close>, formalizamos las 
  colecciones \<open>E\<close> y \<open>C'\<close> como \<open>extF C\<close> y \<open>extensionFin C\<close> respectivamente como se muestra a 
  continuación.\<close>

definition extF :: "(('a formula) set) set \<Rightarrow> (('a formula) set) set"
  where extF: "extF C = {S. \<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C}"

definition extensionFin :: "(('a formula) set) set \<Rightarrow> (('a formula) set) set"
  where extensionFin: "extensionFin C = C \<union> (extF C)"

text \<open>Una vez hechas las aclaraciones anteriores, procedamos ordenadamente con la demostración 
  detallada de cada lema auxiliar que conforma la prueba del lema \<open>1.3.5\<close>. En primer lugar, probemos 
  detalladamente que la extensión \<open>C'\<close> tiene la propiedad de carácter finito.\<close>

lemma ex3_finite_character:
  assumes "subset_closed C"
        shows "finite_character (extensionFin C)"
proof -
  show "finite_character (extensionFin C)"
    unfolding finite_character_def
  proof (rule allI)
   fix S
   show "S \<in> (extensionFin C) \<longleftrightarrow> (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> (extensionFin C))"
   proof (rule iffI)
     assume "S \<in> (extensionFin C)"
     show "\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> (extensionFin C)"
     proof (intro sallI impI)
       fix S'
       assume "S' \<subseteq> S"
       assume "finite S'"
       have "S \<in> C \<or> S \<in> (extF C)"
         using \<open>S \<in> (extensionFin C)\<close> by (simp only: extensionFin Un_iff)
       thus "S' \<in> (extensionFin C)"
       proof (rule disjE)
         assume "S \<in> C"
         have "\<forall>S \<in> C. \<forall>S' \<subseteq> S. S' \<in> C"
           using assms by (simp only: subset_closed_def)
         then have "\<forall>S' \<subseteq> S. S' \<in> C"
           using \<open>S \<in> C\<close> by (rule bspec)
         then have "S' \<in> C"
           using \<open>S' \<subseteq> S\<close> by (rule sspec)
         thus "S' \<in> (extensionFin C)" 
           by (simp only: extensionFin UnI1)
       next
         assume "S \<in> (extF C)"
         then have "\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
           unfolding extF by (rule CollectD)
         then have "finite S' \<longrightarrow> S' \<in> C"
           using \<open>S' \<subseteq> S\<close> by (rule sspec)
         then have "S' \<in> C"
           using \<open>finite S'\<close> by (rule mp)
         thus "S' \<in> (extensionFin C)"
           by (simp only: extensionFin UnI1)
       qed
     qed
   next
     assume "\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> (extensionFin C)"
     then have F:"\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C \<or> S' \<in> (extF C)"
       by (simp only: extensionFin Un_iff)
     have "\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
     proof (rule sallI)
       fix S'
       assume "S' \<subseteq> S"
       show "finite S' \<longrightarrow> S' \<in> C"
       proof (rule impI)
         assume "finite S'"
         have "finite S' \<longrightarrow> S' \<in> C \<or> S' \<in> (extF C)" 
           using F \<open>S' \<subseteq> S\<close> by (rule sspec)
         then have "S' \<in> C \<or> S' \<in> (extF C)"
           using \<open>finite S'\<close> by (rule mp)
         thus "S' \<in> C"
         proof (rule disjE)
           assume "S' \<in> C"
           thus "S' \<in> C"
             by this
         next
           assume "S' \<in> (extF C)"
           then have S':"\<forall>S'' \<subseteq> S'. finite S'' \<longrightarrow> S'' \<in> C"
             unfolding extF by (rule CollectD)
           have "S' \<subseteq> S'"
             by (simp only: subset_refl)
           have "finite S' \<longrightarrow> S' \<in> C"
             using S' \<open>S' \<subseteq> S'\<close> by (rule sspec)
           thus "S' \<in> C"
             using \<open>finite S'\<close> by (rule mp)
         qed
       qed
     qed
     then have "S \<in> {S. \<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C}"
       by (rule CollectI)
     thus "S \<in> (extensionFin C)"
       by (simp only: extF extensionFin UnI2)
   qed
 qed
qed

text \<open>Por otro lado, para probar que  \<open>C' = C \<union> E \<close>  verifica la propiedad de consistencia 
  proposicional, consideraremos un conjunto \<open>S \<in> C'\<close> y utilizaremos fundamentalmente dos lemas 
  auxiliares: uno para el caso en que \<open>S \<in> C\<close> y otro para el caso en que \<open>S \<in> E\<close>. 

  En primer lugar, vamos a probar el primer lema auxiliar para el caso en que \<open>S \<in> C\<close>, formalizado
  como \<open>ex3_pcp_SinC\<close>. Dicho lema prueba que, si \<open>C\<close> es una colección con la propiedad de 
  consistencia proposicional y cerrada bajo subconjuntos, y sea \<open>S \<in> C\<close>, se verifican
  las condiciones del lema de caracterización de la propiedad de consistencia proposicional para
  la extensión \<open>C'\<close>:
  \begin{itemize}
    \item \<open>\<bottom> \<notin> S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
    pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
    pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
  \end{itemize}\<close>

lemma ex3_pcp_SinC:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> C" 
  shows "\<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> (extensionFin C)) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in>(extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C))"
proof -
  have PCP:"\<forall>S \<in> C.
    \<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have H:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
     using PCP \<open>S \<in> C\<close> by (rule bspec)
  then have A1:"\<bottom> \<notin> S"
    by (rule conjunct1)
  have A2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
    using H by (iprover elim: conjunct2 conjunct1)
  have S3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
    using H by (iprover elim: conjunct2 conjunct1)
  have A3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> (extensionFin C)"
  proof (rule allI)+
    fix F G H
    show "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> (extensionFin C)"
    proof (rule impI)+
      assume "Con F G H"
      assume "F \<in> S" 
      have "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        using S3 by (iprover elim: allE)
      then have "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
        using \<open>Con F G H\<close> by (rule mp)
      then have "{G,H} \<union> S \<in> C"
        using \<open>F \<in> S\<close> by (rule mp)
      thus "{G,H} \<union> S \<in> (extensionFin C)"
        unfolding extensionFin by (rule UnI1)
    qed
  qed
  have S4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
    using H by (iprover elim: conjunct2)
  have A4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
  proof (rule allI)+
    fix F G H
    show "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
    proof (rule impI)+
      assume "Dis F G H"
      assume "F \<in> S" 
      have "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using S4 by (iprover elim: allE)
      then have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using \<open>Dis F G H\<close> by (rule mp)
      then have "{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
        using \<open>F \<in> S\<close> by (rule mp)
      thus "{G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
      proof (rule disjE)
        assume "{G} \<union> S \<in> C"
        then have "{G} \<union> S \<in> (extensionFin C)"
          unfolding extensionFin by (rule UnI1)
        thus "{G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
          by (rule disjI1)
      next
        assume "{H} \<union> S \<in> C"
        then have "{H} \<union> S \<in> (extensionFin C)"
          unfolding extensionFin by (rule UnI1)
        thus "{G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
          by (rule disjI2)
      qed
    qed
  qed
  show "\<bottom> \<notin> S \<and>
        (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
        (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> (extensionFin C)) \<and>
        (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C))"
    using A1 A2 A3 A4 by (iprover intro: conjI)
qed

text \<open>Como hemos señalado con anterioridad, para probar el caso en que \<open>S \<in> E\<close>, donde \<open>E\<close> es la 
  colección formada por aquellos conjuntos cuyos subconjuntos finitos pertenecen a \<open>C\<close>, precisaremos 
  de distintos lemas auxiliares. El primero de ellos demuestra detalladamente que si \<open>C\<close> es una
  colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, \<open>S \<in> E\<close>
  y sea \<open>F\<close> una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, se verifica que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> 
  pertenece a la extensión \<open>C' = C \<union> E\<close>.\<close>

lemma ex3_pcp_SinE_CON:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> (extF C)"
          "Con F G H"
          "F \<in> S"
  shows "{G,H} \<union> S \<in> (extensionFin C)" 
proof -
  have PCP:"\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have 1:"\<forall>S' \<subseteq> S. finite S' \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
  proof (rule sallI)
    fix S'
    assume "S' \<subseteq> S"
    show "finite S' \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
    proof (rule impI)+
      assume "finite S'"
      assume "F \<in> S'"
      have E:"\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
        using assms(3) unfolding extF by (rule CollectD)
      then have "finite S' \<longrightarrow> S' \<in> C"
        using \<open>S' \<subseteq> S\<close> by (rule sspec)
      then have "S' \<in> C"
        using \<open>finite S'\<close> by (rule mp)
      have "\<bottom> \<notin> S'
            \<and> (\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False)
            \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C)
            \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C)"
        using PCP \<open>S' \<in> C\<close> by (rule bspec)
      then have "\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G, H} \<union> S' \<in> C"
        by (iprover elim: conjunct2 conjunct1)
      then have "Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G, H} \<union> S' \<in> C"
        by (iprover elim: allE)
      then have "F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
        using assms(4) by (rule mp)
      thus "{G, H} \<union> S' \<in> C"
        using \<open>F \<in> S'\<close> by (rule mp)
    qed
  qed
  have "{G,H} \<union> S \<in> (extF C)"
    unfolding mem_Collect_eq Un_iff extF
  proof (rule sallI)
    fix S'
    assume H:"S' \<subseteq> {G,H} \<union> S"
    show "finite S' \<longrightarrow> S' \<in> C"
    proof (rule impI)
      assume "finite S'"
      have "S' - {G,H} \<subseteq> S"
        using H by (simp only: Diff_subset_conv)
      have "F \<in> S \<and> (S' - {G,H} \<subseteq> S)"
        using assms(5) \<open>S' - {G,H} \<subseteq> S\<close> by (rule conjI)
      then have "insert F  (S' - {G,H}) \<subseteq> S" 
        by (simp only: insert_subset)
      have F1:"finite (insert F  (S' - {G,H})) \<longrightarrow> F \<in> (insert F  (S' - {G,H})) \<longrightarrow> {G,H} \<union> (insert F  (S' - {G,H})) \<in> C"
        using 1 \<open>insert F  (S' - {G,H}) \<subseteq> S\<close> by (rule sspec)
      have "finite (S' - {G,H})"
        using \<open>finite S'\<close> by (rule finite_Diff)
      then have "finite (insert F (S' - {G,H}))" 
        by (rule finite.insertI)
      have F2:"F \<in> (insert F  (S' - {G,H})) \<longrightarrow> {G,H} \<union> (insert F  (S' - {G,H})) \<in> C"
        using F1 \<open>finite (insert F (S' - {G,H}))\<close> by (rule mp)
      have "F \<in> (insert F  (S' - {G,H}))"
        by (simp only: insertI1)
      have F3:"{G,H} \<union> (insert F (S' - {G,H})) \<in> C"
        using F2 \<open>F \<in> insert F (S' - {G,H})\<close> by (rule mp)
      have IU1:"insert F (S' - {G,H}) = {F} \<union> (S' - {G,H})"
        by (rule insert_is_Un)
      have IU2:"insert F ({G,H} \<union> S') = {F} \<union> ({G,H} \<union> S')"
        by (rule insert_is_Un)
      have GH:"insert G (insert H S') = {G,H} \<union> S'"
        by (rule insertSetElem)
      have "{G,H} \<union> (insert F (S' - {G,H})) = {G,H} \<union> ({F} \<union> (S' - {G,H}))"
        by (simp only: IU1)
      also have "\<dots> = {F} \<union> ({G,H} \<union> (S' - {G,H}))"
        by (simp only: Un_left_commute)
      also have "\<dots> = {F} \<union> ({G,H} \<union> S')"
        by (simp only: Un_Diff_cancel)
      also have "\<dots> = insert F ({G,H} \<union> S')"
        by (simp only: IU2)
      also have "\<dots> = insert F (insert G (insert H S'))"
        by (simp only: GH)
      finally have F4:"{G,H} \<union> (insert F (S' - {G,H})) = insert F (insert G (insert H S'))"
        by this
      have C1:"insert F (insert G (insert H S')) \<in> C"
        using F3 by (simp only: F4)
      have "S' \<subseteq> insert F S'"
        by (rule subset_insertI)
      then have C2:"S' \<subseteq> insert F (insert G (insert H S'))"
        by (simp only: subset_insertI2)
      let ?S="insert F (insert G (insert H S'))"
      have "\<forall>S \<in> C. \<forall>S' \<subseteq> S. S' \<in> C"
        using assms(2) by (simp only: subset_closed_def)
      then have "\<forall>S' \<subseteq> ?S. S' \<in> C"
        using C1 by (rule bspec)
      thus "S' \<in> C"
        using C2 by (rule sspec)
    qed
  qed
  thus "{G,H} \<union> S \<in> (extensionFin C)"
    unfolding extensionFin by (rule UnI2)
qed

text \<open>Seguidamente, vamos a probar el lema auxiliar \<open>ex3_pcp_SinE_DIS\<close>. Este demuestra que si \<open>C\<close> es 
  una colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, \<open>S \<in> E\<close>
  y sea \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, se verifica que o bien 
  \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S \<in> C'\<close>. Dicha prueba se realizará por reducción al absurdo. Para
  ello precisaremos de dos lemas previos que nos permitan llegar a una contradicción: 
  \<open>ex3_pcp_SinE_DIS_auxEx\<close> y \<open>ex3_pcp_SinE_DIS_auxFalse\<close>.

  En primer lugar, veamos la demostración del lema \<open>ex3_pcp_SinE_DIS_auxEx\<close>. Este prueba que dada 
  \<open>C\<close> una colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, 
  \<open>S \<in> E\<close> y sea \<open>F\<close> es una fórmula de tipo \<open>\<beta>\<close> de componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, si consideramos \<open>S\<^sub>1\<close> y 
  \<open>S\<^sub>2\<close> subconjuntos finitos cualesquiera de \<open>S\<close> tales que \<open>F \<in> S\<^sub>1\<close> y \<open>F \<in> S\<^sub>2\<close>, entonces existe una 
  fórmula \<open>I \<in> {\<beta>\<^sub>1,\<beta>\<^sub>2}\<close> tal que se verifica que tanto \<open>{I} \<union> S\<^sub>1\<close> como \<open>{I} \<union> S\<^sub>2\<close> están en \<open>C\<close>.\<close>

lemma ex3_pcp_SinE_DIS_auxEx:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> (extF C)"
          "Dis F G H"
          "S1 \<subseteq> S"
          "finite S1"
          "F \<in> S1"
          "S2 \<subseteq> S"
          "finite S2"
          "F \<in> S2"
  shows "\<exists>I\<in>{G,H}. insert I S1 \<in> C \<and> insert I S2 \<in> C" 
proof -
  let ?S = "S1 \<union> S2"
  have "S1 \<subseteq> ?S"
    by (simp only: Un_upper1)
  have "S2 \<subseteq> ?S"
    by (simp only: Un_upper2)
  have "finite ?S"
    using assms(6) assms(9) by (rule finite_UnI)
  have "?S \<subseteq> S" 
    using assms(5) assms(8) by (simp only: Un_subset_iff)
  have "\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
    using assms(3) unfolding extF by (rule CollectD)
  then have "finite ?S \<longrightarrow> ?S \<in> C"
    using \<open>?S \<subseteq> S\<close> by (rule sspec)
  then have "?S \<in> C" 
    using \<open>finite ?S\<close> by (rule mp)
  have "F \<in> ?S" 
    using assms(7) by (rule UnI1)
  have "\<forall>S \<in> C. \<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  then have "\<bottom> \<notin> ?S
        \<and> (\<forall>k. Atom k \<in> ?S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?S \<longrightarrow> False)
        \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?S \<longrightarrow> {G,H} \<union> ?S \<in> C)
        \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?S \<longrightarrow> {G} \<union> ?S \<in> C \<or> {H} \<union> ?S \<in> C)"
    using \<open>?S \<in> C\<close> by (rule bspec)
  then have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?S \<longrightarrow> {G} \<union> ?S \<in> C \<or> {H} \<union> ?S \<in> C"
    by (iprover elim: conjunct2)
  then have "Dis F G H \<longrightarrow> F \<in> ?S \<longrightarrow> {G} \<union> ?S \<in> C \<or> {H} \<union> ?S \<in> C"
    by (iprover elim: allE)
  then have "F \<in> ?S \<longrightarrow> {G} \<union> ?S \<in> C \<or> {H} \<union> ?S \<in> C"
    using assms(4) by (rule mp)
  then have insIsUn:"{G} \<union> ?S \<in> C \<or> {H} \<union> ?S \<in> C"
    using \<open>F \<in> ?S\<close> by (rule mp)
  have insG:"insert G ?S = {G} \<union> ?S" 
    by (rule insert_is_Un)
  have insH:"insert H ?S = {H} \<union> ?S"
    by (rule insert_is_Un)
  have "insert G ?S \<in> C \<or> insert H ?S \<in> C"
    using insG insH by (simp only: insIsUn)
  then have "(insert G ?S \<in> C \<or> insert H ?S \<in> C) \<or> (\<exists>I \<in> {}. insert I ?S \<in> C)"
    by (simp only: disjI1)
  then have "insert G ?S \<in> C \<or> (insert H ?S \<in> C \<or> (\<exists>I \<in> {}. insert I ?S \<in> C))"
    by (simp only: disj_assoc)
  then have "insert G ?S \<in> C \<or> (\<exists>I \<in> {H}. insert I ?S \<in> C)"
    by (simp only: bex_simps(5))
  then have 1:"\<exists>I \<in> {G,H}. insert I ?S \<in> C" 
    by (simp only: bex_simps(5))
  obtain I where "I \<in> {G,H}" and "insert I ?S \<in> C"
    using 1 by (rule bexE)
  have SC:"\<forall>S \<in> C. \<forall>S'\<subseteq>S. S' \<in> C"
    using assms(2) by (simp only: subset_closed_def)
  then have 2:"\<forall>S' \<subseteq> (insert I ?S). S' \<in> C"
    using \<open>insert I ?S \<in> C\<close> by (rule bspec)
  have "insert I S1 \<subseteq> insert I ?S" 
    using \<open>S1 \<subseteq> ?S\<close> by (rule insert_mono)
  have "insert I S1 \<in> C"
    using 2 \<open>insert I S1 \<subseteq> insert I ?S\<close> by (rule sspec)
  have "insert I S2 \<subseteq> insert I ?S"
    using \<open>S2 \<subseteq> ?S\<close> by (rule insert_mono)
  have "insert I S2 \<in> C"
    using 2 \<open>insert I S2 \<subseteq> insert I ?S\<close> by (rule sspec)
  have "insert I S1 \<in> C \<and> insert I S2 \<in> C"
    using \<open>insert I S1 \<in> C\<close> \<open>insert I S2 \<in> C\<close> by (rule conjI)
  thus "\<exists>I\<in>{G,H}. insert I S1 \<in> C \<and> insert I S2 \<in> C"
    using \<open>I \<in> {G,H}\<close> by (rule bexI)
qed

text \<open>Finalmente, el lema \<open>ex3_pcp_SinE_DIS_auxFalse\<close> prueba que dada una colección \<open>C\<close> con la 
  propiedad de consistencia proposicional y cerrada bajo subconjuntos, \<open>S \<in> E\<close> y sea \<open>F\<close> es una 
  fórmula de tipo \<open>\<beta>\<close> de componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, si consideramos \<open>S\<^sub>1\<close> y \<open>S\<^sub>2\<close> subconjuntos finitos 
  cualesquiera de \<open>S\<close> tales que \<open>F \<in> S\<^sub>1\<close>, \<open>F \<in> S\<^sub>2\<close>, \<open>{\<beta>\<^sub>1} \<union> S\<^sub>1 \<notin> C\<close> y \<open>{\<beta>\<^sub>2} \<union> S\<^sub>2 \<notin> C\<close>, llegamos a 
  una contradicción.\<close>

lemma ex3_pcp_SinE_DIS_auxFalse:
  assumes "pcp C" 
          "subset_closed C"
          "S \<in> (extF C)"
          "Dis F G H"
          "F \<in> S"
          "S1 \<subseteq> S" 
          "finite S1" 
          "insert G S1 \<notin> C" 
          "S2 \<subseteq> S" 
          "finite S2" 
          "insert H S2 \<notin> C"
        shows "False"
proof -
  let ?S1="insert F S1"
  let ?S2="insert F S2"
  have SC:"\<forall>S \<in> C. \<forall>S'\<subseteq>S. S' \<in> C"
    using assms(2) by (simp only: subset_closed_def)
  have 1:"?S1 \<subseteq> S"
    using \<open>F \<in> S\<close> \<open>S1 \<subseteq> S\<close> by (simp only: insert_subset) 
  have 2:"finite ?S1"
    using \<open>finite S1\<close> by (simp only: finite_insert) 
  have 3:"F \<in> ?S1"
    by (simp only: insertI1) 
  have 4:"insert G ?S1 \<notin> C" 
  proof (rule ccontr)
    assume "\<not>(insert G ?S1 \<notin> C)"
    then have "insert G ?S1 \<in> C"
      by (rule notnotD)
    have SC1:"\<forall>S' \<subseteq> (insert G ?S1). S' \<in> C"
      using SC \<open>insert G ?S1 \<in> C\<close> by (rule bspec)
    have "insert G S1 \<subseteq> insert F (insert G S1)"
      by (rule subset_insertI)
    then have "insert G S1 \<subseteq> insert G ?S1"
      by (simp only: insert_commute)
    have "insert G S1 \<in> C"
      using SC1 \<open>insert G S1 \<subseteq> insert G ?S1\<close> by (rule sspec)
    show "False"
      using assms(8) \<open>insert G S1 \<in> C\<close> by (rule notE)
  qed
  have 5:"?S2 \<subseteq> S"
    using \<open>F \<in> S\<close> \<open>S2 \<subseteq> S\<close> by (simp only: insert_subset)
  have 6:"finite ?S2"
    using \<open>finite S2\<close> by (simp only: finite_insert)
  have 7:"F \<in> ?S2"
    by (simp only: insertI1)
  have 8:"insert H ?S2 \<notin> C" 
  proof (rule ccontr)
    assume "\<not>(insert H ?S2 \<notin> C)"
    then have "insert H ?S2 \<in> C"
      by (rule notnotD)
    have SC2:"\<forall>S' \<subseteq> (insert H ?S2). S' \<in> C"
      using SC \<open>insert H ?S2 \<in> C\<close> by (rule bspec)
    have "insert H S2 \<subseteq> insert F (insert H S2)"
      by (rule subset_insertI)
    then have "insert H S2 \<subseteq> insert H ?S2"
      by (simp only: insert_commute)
    have "insert H S2 \<in> C"
      using SC2 \<open>insert H S2 \<subseteq> insert H ?S2\<close> by (rule sspec)
    show "False"
      using assms(11) \<open>insert H S2 \<in> C\<close> by (rule notE)
  qed
  have Ex:"\<exists>I \<in> {G,H}. insert I ?S1 \<in> C \<and> insert I ?S2 \<in> C"
    using assms(1) assms(2) assms(3) assms(4) 1 2 3 5 6 7 by (rule ex3_pcp_SinE_DIS_auxEx)
  have "\<forall>I \<in> {G,H}. insert I ?S1 \<notin> C \<or> insert I ?S2 \<notin> C"
    using 4 8 by simp
  then have "\<forall>I \<in> {G,H}. \<not>(insert I ?S1 \<in> C \<and> insert I ?S2 \<in> C)"
    by (simp only: de_Morgan_conj)
  then have "\<not>(\<exists>I \<in> {G,H}. insert I ?S1 \<in> C \<and> insert I ?S2 \<in> C)"
    by (simp only: bex_simps(8)) 
  thus "False"
    using Ex by (rule notE)
qed

text \<open>Una vez introducidos los lemas anteriores, podemos probar el lema \<open>ex3_pcp_SinE_DIS\<close> que
  demuestra que si \<open>C\<close> es una colección con la propiedad de consistencia proposicional y cerrada 
  bajo subconjuntos, \<open>S \<in> E\<close> y sea \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, se 
  verifica que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S \<in> C'\<close>. Además, para dicha prueba 
  necesitaremos los siguientes lemas auxiliares en Isabelle.\<close>

lemma sall_simps_not_all:
  assumes "\<not>(\<forall>x \<subseteq> A. P x)"
  shows "\<exists>x \<subseteq> A. (\<not> P x)"
  using assms by blast

lemma subexE: "\<exists>x\<subseteq>A. P x \<Longrightarrow> (\<And>x. x\<subseteq>A \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by blast

text \<open>De este modo, procedamos con la demostración detallada de \<open>ex3_pcp_SinE_DIS\<close>.\<close>

lemma ex3_pcp_SinE_DIS:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> (extF C)"
          "Dis F G H"
          "F \<in> S"
  shows "{G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
proof -
  have "(extF C) \<subseteq> (extensionFin C)" 
    unfolding extensionFin by (rule Un_upper2) 
  have PCP:"\<forall>S \<in> C.
            \<bottom> \<notin> S
            \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
            \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
            \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have E:"\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
    using assms(3) unfolding extF by (rule CollectD)
  then have E':"\<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> C"
    by blast
  have SC:"\<forall>S \<in> C. \<forall>S'\<subseteq>S. S' \<in> C"
    using assms(2) by (simp only: subset_closed_def)
  have "insert G S \<in> (extF C) \<or> insert H S \<in> (extF C)" 
  proof (rule ccontr)
    assume "\<not>(insert G S \<in> (extF C) \<or> insert H S \<in> (extF C))"  
    then have Conj:"\<not>(insert G S \<in> (extF C)) \<and> \<not>(insert H S \<in> (extF C))" 
      by (simp only: simp_thms(8,25) de_Morgan_disj)
    then have "\<not>(insert G S \<in> (extF C))"
      by (rule conjunct1)
    then have "\<not>(\<forall>S' \<subseteq> (insert G S). finite S' \<longrightarrow> S' \<in> C)"
      unfolding extF by (simp add: mem_Collect_eq)
    then have Ex1:"\<exists>S'\<subseteq> (insert G S). \<not>(finite S' \<longrightarrow> S' \<in> C)"
      by (rule sall_simps_not_all)
    obtain S1 where "S1 \<subseteq> insert G S" and "\<not>(finite S1 \<longrightarrow> S1 \<in> C)"
      using Ex1 by (rule subexE)
    have "finite S1 \<and> S1 \<notin> C" 
      using \<open>\<not>(finite S1 \<longrightarrow> S1 \<in> C)\<close> by (simp only: simp_thms(8) not_imp)
    then have "finite S1"
      by (rule conjunct1)
    have "S1 \<notin> C"
      using \<open>finite S1 \<and> S1 \<notin> C\<close> by (rule conjunct2)
    then have "insert G S1 \<notin> C"
    proof - 
      have "S1 \<subseteq> S \<longrightarrow> finite S1 \<longrightarrow> S1 \<in> C"
        using E' by (rule allE)
      then have "\<not> S1 \<subseteq> S"
        using \<open>\<not> (finite S1 \<longrightarrow> S1 \<in> C)\<close> by (rule mt)
      then have "(S1 \<subseteq> insert G S) \<noteq> (S1 \<subseteq> S)"
        using \<open>S1 \<subseteq> insert G S\<close> by simp
      then have notSI:"\<not>(S1 \<subseteq> insert G S \<longleftrightarrow> S1 \<subseteq> S)"
        by blast
      have subsetInsert:"G \<notin> S1 \<Longrightarrow> S1 \<subseteq> insert G S \<longleftrightarrow> S1 \<subseteq> S"
        by (rule subset_insert)
      have "\<not>(G \<notin> S1)"
        using notSI subsetInsert by (rule contrapos_nn)
      then have "G \<in> S1"
        by (rule notnotD)
      then have "insert G S1 = S1"
        by (rule insert_absorb)
      show ?thesis
        using \<open>S1 \<notin> C\<close> by (simp only: simp_thms(8) \<open>insert G S1 = S1\<close>)
    qed 
    let ?S1="S1 - {G}"
    have "insert G S = {G} \<union> S"
      by (rule insert_is_Un)
    have "S1 \<subseteq> {G} \<union> S"
      using \<open>S1 \<subseteq> insert G S\<close> by (simp only: \<open>insert G S = {G} \<union> S\<close>)
    have 1:"?S1 \<subseteq> S" 
      using \<open>S1 \<subseteq> {G} \<union> S\<close> by (simp only: Diff_subset_conv)
    have 2:"finite ?S1"
      using \<open>finite S1\<close> by (simp only: finite_Diff)
    have "insert G ?S1 = insert G S1"
      by (simp only: insert_Diff_single)
    then have 3:"insert G ?S1 \<notin> C"
      using \<open>insert G S1 \<notin> C\<close> by (simp only: simp_thms(6,8) \<open>insert G ?S1 = insert G S1\<close>)
    have "insert H S \<notin> (extF C)"
      using Conj by (rule conjunct2)
    then have "\<not>(\<forall>S' \<subseteq> (insert H S). finite S' \<longrightarrow> S' \<in> C)"
      unfolding extF by (simp add: mem_Collect_eq)
    then have Ex2:"\<exists>S'\<subseteq> (insert H S). \<not>(finite S' \<longrightarrow> S' \<in> C)"
      by (rule sall_simps_not_all)
    obtain S2 where "S2 \<subseteq> insert H S" and "\<not>(finite S2 \<longrightarrow> S2 \<in> C)"
      using Ex2 by (rule subexE)
    have "finite S2 \<and> S2 \<notin> C"
      using \<open>\<not>(finite S2 \<longrightarrow> S2 \<in> C)\<close> by (simp only: simp_thms(8,25) not_imp)
    then have "finite S2"
      by (rule conjunct1)
    have "S2 \<notin> C"
      using \<open>finite S2 \<and> S2 \<notin> C\<close> by (rule conjunct2)
    then have "insert H S2 \<notin> C"
    proof -
      have "S2 \<subseteq> S \<longrightarrow> finite S2 \<longrightarrow> S2 \<in> C"
        using E' by (rule allE)
      then have "\<not> S2 \<subseteq> S"
        using \<open>\<not> (finite S2 \<longrightarrow> S2 \<in> C)\<close> by (rule mt)
      then have "(S2 \<subseteq> insert H S) \<noteq> (S2 \<subseteq> S)"
        using \<open>S2 \<subseteq> insert H S\<close> by simp 
      then have notSI:"\<not>(S2 \<subseteq> insert H S \<longleftrightarrow> S2 \<subseteq> S)"
        by blast 
      have subsetInsert:"H \<notin> S2 \<Longrightarrow> S2 \<subseteq> insert H S \<longleftrightarrow> S2 \<subseteq> S"
        by (rule subset_insert)
      have "\<not>(H \<notin> S2)"
        using notSI subsetInsert by (rule contrapos_nn)
      then have "H \<in> S2"
        by (rule notnotD)
      then have "insert H S2 = S2"
        by (rule insert_absorb)
      show ?thesis
        using \<open>S2 \<notin> C\<close> by (simp only: simp_thms(8) \<open>insert H S2 = S2\<close>)
    qed 
    let ?S2="S2 - {H}"
    have "insert H S = {H} \<union> S"
      by (rule insert_is_Un)
    have "S2 \<subseteq> {H} \<union> S"
      using \<open>S2 \<subseteq> insert H S\<close> by (simp only: \<open>insert H S = {H} \<union> S\<close>)
    have 4:"?S2 \<subseteq> S" 
      using \<open>S2 \<subseteq> {H} \<union> S\<close> by (simp only: Diff_subset_conv)
    have 5:"finite ?S2" 
      using \<open>finite S2\<close> by (simp only: finite_Diff)
    have "insert H ?S2 = insert H S2"
      by (simp only: insert_Diff_single)
    then have 6:"insert H ?S2 \<notin> C"
      using \<open>insert H S2 \<notin> C\<close> by (simp only: simp_thms(6,8) \<open>insert H ?S2 = insert H S2\<close>)
    show "False"
      using assms(1) assms(2) assms(3) assms(4) assms(5) 1 2 3 4 5 6 by (rule ex3_pcp_SinE_DIS_auxFalse)
  qed
  thus ?thesis
  proof (rule disjE)
    assume "insert G S \<in> (extF C)"
    have insG:"insert G S \<in> (extensionFin C)"
      using \<open>(extF C) \<subseteq> (extensionFin C)\<close> \<open>insert G S \<in> (extF C)\<close> by (simp only: in_mono)
    have "insert G S = {G} \<union> S"
      by (rule insert_is_Un)
    then have "{G} \<union> S \<in> (extensionFin C)"
      using insG \<open>insert G S = {G} \<union> S\<close> by (simp only: insG)
    thus ?thesis
      by (rule disjI1)
  next
    assume "insert H S \<in> (extF C)"
    have insH:"insert H S \<in> (extensionFin C)"
      using \<open>(extF C) \<subseteq> (extensionFin C)\<close> \<open>insert H S \<in> (extF C)\<close> by (simp only: in_mono)
    have "insert H S = {H} \<union> S"
      by (rule insert_is_Un)
    then have "{H} \<union> S \<in> (extensionFin C)"
      using insH \<open>insert H S = {H} \<union> S\<close> by (simp only: insH)
    thus ?thesis
      by (rule disjI2)
  qed
qed

text \<open>Probados los lemas \<open>ex3_pcp_SinE_CON\<close> y \<open>ex3_pcp_SinE_DIS\<close>, podemos demostrar que \<open>C' = C \<union> E\<close> 
  verifica las condiciones del lema de caracterización de la propiedad de consistencia proposicional 
  para el caso en que \<open>S \<in> E\<close>, formalizado como \<open>ex3_pcp_SinE\<close>. Dicho lema prueba que, si \<open>C\<close> es 
  una colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, y sea 
  \<open>S \<in> E\<close>, se verifican las condiciones:
  \begin{itemize}
    \item \<open>\<bottom> \<notin> S\<close>.
    \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
    simultáneamente que\\ \<open>p \<in> S\<close> y \<open>\<not> p \<in> S\<close>.
    \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
    pertenece a \<open>S\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
    \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
    pertenece a \<open>S\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C'\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C'\<close>.
  \end{itemize}\<close>

lemma ex3_pcp_SinE:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> (extF C)" 
  shows "\<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> (extensionFin C)) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C))"
proof -
  have PCP:"\<forall>S \<in> C.
         \<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have E:"\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C"
    using assms(3) unfolding extF by (rule CollectD)
  have "{} \<subseteq> S"
    by (rule empty_subsetI)
  have C1:"\<bottom> \<notin> S"
  proof (rule ccontr)
    assume "\<not>(\<bottom> \<notin> S)"
    then have "\<bottom> \<in> S"
      by (rule notnotD)
    then have "\<bottom> \<in> S \<and> {} \<subseteq> S"
      using \<open>{} \<subseteq> S\<close> by (rule conjI)
    then have "insert \<bottom> {} \<subseteq> S" 
      by (simp only: insert_subset)
    have "finite {}"
      by (rule finite.emptyI)
    then have "finite (insert \<bottom> {})"
      by (rule finite.insertI)
    have "finite (insert \<bottom> {}) \<longrightarrow> (insert \<bottom> {}) \<in> C"
      using E \<open>(insert \<bottom> {}) \<subseteq> S\<close> by simp 
    then have "(insert \<bottom> {}) \<in> C"
      using \<open>finite (insert \<bottom> {})\<close> by (rule mp)
    have "\<bottom> \<notin> (insert \<bottom> {}) \<and>
         (\<forall>k. Atom k \<in> (insert \<bottom> {}) \<longrightarrow> \<^bold>\<not> (Atom k) \<in> (insert \<bottom> {}) \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> (insert \<bottom> {}) \<longrightarrow> {G, H} \<union> (insert \<bottom> {}) \<in> C) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> (insert \<bottom> {}) \<longrightarrow> {G} \<union> (insert \<bottom> {}) \<in> C \<or> {H} \<union> (insert \<bottom> {}) \<in> C)"
      using PCP \<open>(insert \<bottom> {}) \<in> C\<close> by blast 
    then have "\<bottom> \<notin> (insert \<bottom> {})"
      by (rule conjunct1)
    have "\<bottom> \<in> (insert \<bottom> {})"
      by (rule insertI1)
    show "False"
      using \<open>\<bottom> \<notin> (insert \<bottom> {})\<close> \<open>\<bottom> \<in> (insert \<bottom> {})\<close> by (rule notE)
  qed
  have C2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
  proof (rule allI)
    fix k
    show "Atom k \<in> S \<longrightarrow> \<^bold>\<not>(Atom k) \<in> S \<longrightarrow> False"
    proof (rule impI)+
      assume "Atom k \<in> S"
      assume "\<^bold>\<not>(Atom k) \<in> S"
      let ?A="insert (Atom k) (insert (\<^bold>\<not>(Atom k)) {})"
      have "Atom k \<in> ?A"
        by (simp only: insert_iff simp_thms) 
      have "\<^bold>\<not>(Atom k) \<in> ?A"
        by (simp only: insert_iff simp_thms) 
      have inSubset:"insert (\<^bold>\<not>(Atom k)) {} \<subseteq> S"
        using \<open>\<^bold>\<not>(Atom k) \<in> S\<close> \<open>{} \<subseteq> S\<close> by (simp only: insert_subset)
      have "?A \<subseteq> S"
        using inSubset \<open>Atom k \<in> S\<close> by (simp only: insert_subset)
      have "finite {}"
        by (simp only: finite.emptyI)
      then have "finite (insert (\<^bold>\<not>(Atom k)) {})"
        by (rule finite.insertI)
      then have "finite ?A"
        by (rule finite.insertI)
      have "finite ?A \<longrightarrow> ?A \<in> C"
        using E \<open>?A \<subseteq> S\<close> by (rule sspec)
      then have "?A \<in> C"
        using \<open>finite ?A\<close> by (rule mp)
      have "\<bottom> \<notin> ?A
            \<and> (\<forall>k. Atom k \<in> ?A \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?A \<longrightarrow> False)
            \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?A \<longrightarrow> {G,H} \<union> ?A \<in> C)
            \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?A \<longrightarrow> {G} \<union> ?A \<in> C \<or> {H} \<union> ?A \<in> C)"
        using PCP \<open>?A \<in> C\<close> by (rule bspec)
      then have "\<forall>k. Atom k \<in> ?A \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?A \<longrightarrow> False"
        by (iprover elim: conjunct2 conjunct1)
      then have "Atom k \<in> ?A \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?A \<longrightarrow> False"
        by (iprover elim: allE)
      then have "\<^bold>\<not>(Atom k) \<in> ?A \<longrightarrow> False"
        using \<open>Atom k \<in> ?A\<close> by (rule mp)
      thus "False"
        using \<open>\<^bold>\<not>(Atom k) \<in> ?A\<close> by (rule mp)
    qed
  qed
  have C3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> (extensionFin C)"
  proof (rule allI)+
    fix F G H
    show "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> (extensionFin C)"
    proof (rule impI)+
      assume "Con F G H"
      assume "F \<in> S" 
      show "{G,H} \<union> S \<in> (extensionFin C)" 
        using assms(1) assms(2) assms(3) \<open>Con F G H\<close> \<open>F \<in> S\<close> by (simp only: ex3_pcp_SinE_CON)
    qed
  qed
  have C4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
  proof (rule allI)+
    fix F G H
    show "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
    proof (rule impI)+
      assume "Dis F G H"
      assume "F \<in> S" 
      show "{G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C)"
        using assms(1) assms(2) assms(3) \<open>Dis F G H\<close> \<open>F \<in> S\<close> by (rule ex3_pcp_SinE_DIS)
    qed
  qed
  show ?thesis
    using C1 C2 C3 C4 by (iprover intro: conjI)
qed

text \<open>En conclusión, la prueba detallada completa en Isabelle que demuestra que la extensión \<open>C'\<close> 
  verifica la propiedad de consistencia proposicional dada una colección \<open>C\<close> que también la
  verifique y sea cerrada bajo subconjuntos es la siguiente.\<close>

lemma ex3_pcp:
  assumes "pcp C"
          "subset_closed C"
        shows "pcp (extensionFin C)"
  unfolding pcp_alt
proof (rule ballI)
  have PCP:"\<forall>S \<in> C.
    \<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  fix S
  assume "S \<in> (extensionFin C)"
  then have "S \<in> C \<or> S \<in> (extF C)"
    unfolding extensionFin by (simp only: Un_iff)
  thus "\<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> (extensionFin C)) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> (extensionFin C) \<or> {H} \<union> S \<in> (extensionFin C))"
  proof (rule disjE)
    assume "S \<in> C"
    show ?thesis
      using assms \<open>S \<in> C\<close> by (rule ex3_pcp_SinC)
  next
    assume "S \<in> (extF C)"
    show ?thesis
      using assms \<open>S \<in> (extF C)\<close> by (rule ex3_pcp_SinE)
  qed
qed

text \<open>Por último, podemos dar la prueba completa del lema \<open>1.3.5\<close> en Isabelle.\<close>

lemma ex3:
  assumes "pcp C"
          "subset_closed C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof -
  let ?C'="extensionFin C"
  have C1:"C \<subseteq> ?C'"
    unfolding extensionFin by (simp only: Un_upper1)
  have C2:"finite_character (?C')"
    using assms(2) by (rule ex3_finite_character)
  have C3:"pcp (?C')"
    using assms by (rule ex3_pcp)
  have "C \<subseteq> ?C' \<and> pcp ?C' \<and> finite_character ?C'"
    using C1 C2 C3 by (iprover intro: conjI)
  thus ?thesis
    by (rule exI)
qed

section \<open>Sucesiones de conjuntos de una colección\<close>

text\<open>En este apartado daremos una introducción sobre sucesiones de conjuntos de fórmulas a 
  partir de una colección y un conjunto de la misma. De este modo, se mostrarán distintas 
  características sobre las sucesiones y se definirá su límite. En la siguiente sección 
  probaremos que dicho límite constituye un conjunto satisfacible por el lema de Hintikka.

\comentario{Revisar el párrafo anterior al final}

  Recordemos que el conjunto de las fórmulas proposicionales se define recursivamente a partir 
  de un alfabeto numerable de variables proposicionales. Por lo tanto, el conjunto de fórmulas 
  proposicionales es igualmente numerable, de modo que es posible enumerar sus elementos. Una vez 
  realizada esta observación, veamos la definición de sucesión de conjuntos de fórmulas 
  proposicionales a partir de una colección y un conjunto de la misma.

\begin{definicion}
  Sea \<open>C\<close> una colección, \<open>S\<close> un conjunto perteneciente a ella y \<open>F\<^sub>1, F\<^sub>2, F\<^sub>3 \<dots>\<close> una enumeración de 
  las fórmulas proposicionales. Se define la \<open>sucesión de conjuntos de C a partir de S\<close> como sigue:

  $S_{0} = S$

  $S_{n+1} = \left\{ \begin{array}{lcc} S_{n} \cup \{F_{n}\} &  si  & S_{n} \cup \{F_{n}\} \in C \\ \\ S_{n} & c.c \end{array} \right.$ 
\end{definicion}

  Para su formalización en Isabelle se ha introducido una instancia en la teoría de \<open>Sintaxis\<close> que 
  indica explícitamente que el conjunto de las fórmulas proposicionales es numerable.

  \<open>instance formula :: (countable) countable by countable_datatype\<close>

  De esta manera, se genera paralelamente el método de prueba \<open>countable_datatype\<close> sobre dicho 
  conjunto, que proporciona una enumeración predeterminada de sus elementos junto con herramientas 
  para probar propiedades referentes a la numerabilidad. En particular, en la formalización de la
  definición \<open>1.4.1\<close> se utilizará la función \<open>from_nat\<close> que, al aplicarla a un número natural \<open>n\<close>, 
  nos devuelve la \<open>n\<close>-ésima fórmula proposicional según una enumeración predeterminada en Isabelle. 

  Por otro lado, puesto que la definición de las sucesiones en \<open>1.4.1\<close> se trata de una definición 
  recursiva sobre la estructura recursiva de los números naturales, se formalizará en Isabelle
  mediante el tipo de funciones primitivas recursivas de la siguiente manera.\<close>

primrec pcp_seq where
"pcp_seq C S 0 = S" |
"pcp_seq C S (Suc n) = (let Sn = pcp_seq C S n; Sn1 = insert (from_nat n) Sn in
                        if Sn1 \<in> C then Sn1 else Sn)" 

text\<open>Veamos el primer resultado sobre dichas sucesiones.

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos con la propiedad de consistencia proposicional, \<open>S \<in> C\<close> y 
    \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close> construida según la definición \<open>1.4.1\<close>. 
    Entonces, para todo \<open>n \<in> \<nat>\<close> se verifica que \<open>S\<^sub>n \<in> C\<close>.
  \end{lema}

  Procedamos con su demostración.

  \begin{demostracion}
    El resultado se prueba por inducción en los números naturales que conforman los subíndices de la 
    sucesión.

    En primer lugar, tenemos que \<open>S\<^sub>0 = S\<close> pertenece a \<open>C\<close> por hipótesis.

    Por otro lado, supongamos que \<open>S\<^sub>n \<in> C\<close>. Probemos que \<open>S\<^sub>n\<^sub>+\<^sub>1 \<in> C\<close>. Si suponemos que \<open>S\<^sub>n \<union> {F\<^sub>n} \<in> C\<close>,
    por definición tenemos que \<open>S\<^sub>n\<^sub>+\<^sub>1 = S\<^sub>n \<union> {F\<^sub>n}\<close>, luego pertenece a \<open>C\<close>. En caso contrario, si
    suponemos que \<open>S\<^sub>n \<union> {F\<^sub>n} \<notin> C\<close>, por definición tenemos que \<open>S\<^sub>n\<^sub>+\<^sub>1 = S\<^sub>n\<close>, que pertenece igualmente
    a \<open>C\<close> por hipótesis de inducción. Por tanto, queda probado el resultado.
  \end{demostracion}

  La formalización y demostración detallada del lema en Isabelle son las siguientes.\<close>

lemma 
  assumes "pcp C" 
          "S \<in> C"
        shows "pcp_seq C S n \<in> C"
proof (induction n)
  show "pcp_seq C S 0 \<in> C"
    by (simp only: pcp_seq.simps(1) \<open>S \<in> C\<close>)
next
  fix n
  assume HI:"pcp_seq C S n \<in> C"
  have "pcp_seq C S (Suc n) = (let Sn = pcp_seq C S n; Sn1 = insert (from_nat n) Sn in
                        if Sn1 \<in> C then Sn1 else Sn)" 
    by (simp only: pcp_seq.simps(2))
  then have SucDef:"pcp_seq C S (Suc n) = (if insert (from_nat n) (pcp_seq C S n) \<in> C then 
                    insert (from_nat n) (pcp_seq C S n) else pcp_seq C S n)" 
    by (simp only: Let_def)
  show "pcp_seq C S (Suc n) \<in> C"
  proof (cases)
    assume 1:"insert (from_nat n) (pcp_seq C S n) \<in> C"
    have "pcp_seq C S (Suc n) = insert (from_nat n) (pcp_seq C S n)"
      using SucDef 1 by (simp only: if_True)
    thus "pcp_seq C S (Suc n) \<in> C"
      by (simp only: 1)
  next
    assume 2:"insert (from_nat n) (pcp_seq C S n) \<notin> C"
    have "pcp_seq C S (Suc n) = pcp_seq C S n"
      using SucDef 2 by (simp only: if_False)
    thus "pcp_seq C S (Suc n) \<in> C"
      by (simp only: HI)
  qed
qed

text \<open>Del mismo modo, podemos probar el lema de manera automática en Isabelle.\<close>

lemma pcp_seq_in: "pcp C \<Longrightarrow> S \<in> C \<Longrightarrow> pcp_seq C S n \<in> C"
proof(induction n)
  case (Suc n)  
  hence "pcp_seq C S n \<in> C" by simp
  thus ?case by (simp add: Let_def)
qed simp

text\<open>Por otro lado, veamos la monotonía de dichas sucesiones.

  \begin{lema}
    Toda sucesión de conjuntos construida a partir de una colección y un conjunto según la
    definición \<open>1.4.1\<close> es monótona.
  \end{lema}

  En Isabelle, se formaliza de la siguiente forma.\<close>

lemma "pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
  oops

text \<open>Procedamos con la demostración del lema.

  \begin{demostracion}
    Sea una colección de conjuntos \<open>C\<close>, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de 
    \<open>S\<close> según la definición \<open>1.4.1\<close>. Para probar que \<open>{S\<^sub>n}\<close> es monótona, basta probar que \<open>S\<^sub>n \<subseteq> S\<^sub>n\<^sub>+\<^sub>1\<close> 
    para todo \<open>n \<in> \<nat>\<close>. En efecto, el resultado es inmediato al considerar dos casos para todo 
    \<open>n \<in> \<nat>\<close>: \<open>S\<^sub>n \<union> {F\<^sub>n} \<in> C\<close> o \<open>S\<^sub>n \<union> {F\<^sub>n} \<notin> C\<close>. Si suponemos que \<open>S\<^sub>n \<union> {F\<^sub>n} \<in> C\<close>, por definición 
    tenemos que \<open>S\<^sub>n\<^sub>+\<^sub>1 = S\<^sub>n \<union> {F\<^sub>n}\<close>, luego es claro que \<open>S\<^sub>n \<subseteq> S\<^sub>n\<^sub>+\<^sub>1\<close>. En caso contrario, si 
    \<open>S\<^sub>n \<union> {F\<^sub>n} \<notin> C\<close>, por definición se tiene que \<open>S\<^sub>n\<^sub>+\<^sub>1 = S\<^sub>n\<close>, obteniéndose igualmente el resultado
    por la propiedad reflexiva de la contención de conjuntos. 
  \end{demostracion}

  La prueba detallada en Isabelle se muestra a continuación.\<close>

lemma "pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
proof -
  have "pcp_seq C S (Suc n) = (let Sn = pcp_seq C S n; Sn1 = insert (from_nat n) Sn in
                        if Sn1 \<in> C then Sn1 else Sn)" 
    by (simp only: pcp_seq.simps(2))
  then have SucDef:"pcp_seq C S (Suc n) = (if insert (from_nat n) (pcp_seq C S n) \<in> C then 
                    insert (from_nat n) (pcp_seq C S n) else pcp_seq C S n)" 
    by (simp only: Let_def)
  thus "pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
  proof (cases)
    assume 1:"insert (from_nat n) (pcp_seq C S n) \<in> C"
    have "pcp_seq C S (Suc n) = insert (from_nat n) (pcp_seq C S n)"
      using SucDef 1 by (simp only: if_True)
    thus "pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
      by (simp only: subset_insertI)
  next
    assume 2:"insert (from_nat n) (pcp_seq C S n) \<notin> C"
    have "pcp_seq C S (Suc n) = pcp_seq C S n"
      using SucDef 2 by (simp only: if_False)
    thus "pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
      by (simp only: subset_refl)
  qed
qed

text \<open>Del mismo modo, se puede probar automáticamente en Isabelle/HOL.\<close>

lemma pcp_seq_monotonicity:"pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
  by (smt eq_iff pcp_seq.simps(2) subset_insertI)

text \<open>Por otra lado, para facilitar posteriores demostraciones en Isabelle/HOL, vamos a formalizar 
  el lema anterior empleando la siguiente definición generalizada de monotonía.\<close>

lemma pcp_seq_mono:
  assumes "n \<le> m" 
  shows "pcp_seq C S n \<subseteq> pcp_seq C S m"
  using pcp_seq_monotonicity assms by (rule lift_Suc_mono_le)

text \<open>A continuación daremos un lema que permite caracterizar un elemento de la sucesión en función 
  de los anteriores.

\begin{lema}
  Sea \<open>C\<close> una colección de conjuntos, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de 
  \<open>S\<close> construida según la definición \<open>1.4.1\<close>. Entonces, para todos \<open>n\<close>,\\\<open>m \<in> \<nat>\<close> 
  se verifica $\bigcup_{n \leq m} S_{n} = S_{m}$
\end{lema}

\begin{demostracion}
  En las condiciones del enunciado, la prueba se realiza por inducción en \<open>m \<in> \<nat>\<close>.

  En primer lugar, consideremos el caso base \<open>m = 0\<close>. El resultado se obtiene directamente:

  $\bigcup_{n \leq 0} S_{n} = \bigcup_{n = 0} S_{n} = S_{0} = S_{m}$

  Por otro lado, supongamos por hipótesis de inducción que $\bigcup_{n \leq m} S_{n} = S_{m}$.
  Veamos que se verifica $\bigcup_{n \leq m + 1} S_{n} = S_{m + 1}$. Observemos que si \<open>n \<le> m + 1\<close>,
  entonces se tiene que, o bien \<open>n \<le> m\<close>, o bien \<open>n = m + 1\<close>. De este modo, aplicando la 
  hipótesis de inducción, deducimos lo siguiente.

  $\bigcup_{n \leq m + 1} S_{n} = \bigcup_{n \leq m} S_{n} \cup \bigcup_{n = m + 1} S_{n} = \bigcup_{n \leq m} S_{n} \cup S_{m + 1} = S_{m} \cup S_{m + 1}$

  Por la monotonía de la sucesión, se tiene que \<open>S\<^sub>m \<subseteq> S\<^sub>m\<^sub>+\<^sub>1\<close>. Luego, se verifica:

  $\bigcup_{n \leq m + 1} S_{n} = S_{m} \cup S_{m + 1} = S_{m + 1}$

  Lo que prueba el resultado.
\end{demostracion}

  Procedamos a su formalización y demostración detallada. Para ello, emplearemos la unión 
  generalizada en Isabelle/HOL perteneciente a la teoría 
  \href{https://n9.cl/gtf5x}{Complete-Lattices.thy}. Además, la prueba ha precisado del 
  siguiente lema auxiliar que define la imagen de un conjunto con un único elemento.\<close>

lemma imageElem: "f ` {x} = {f x}"
  by simp

text \<open>De este modo, la prueba detallada en Isabelle/HOL es la siguiente.\<close>

lemma "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof (induct m)
  have "(pcp_seq C S)`{n. n = 0} = {pcp_seq C S 0}"
    by (simp only: singleton_conv imageElem)
  then have 1:"\<Union>{pcp_seq C S n | n. n = 0} = \<Union>{pcp_seq C S 0}"
    by (simp only: image_Collect)
  show "\<Union>{pcp_seq C S n|n. n \<le> 0} = pcp_seq C S 0"
    by (simp only: canonically_ordered_monoid_add_class.le_zero_eq 1 conditionally_complete_lattice_class.cSup_singleton)
next
  fix m
  assume HI:"\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
  have "m \<le> Suc m" 
    by (simp only: monoid_add_class.add_0_right)
  then have Mon:"pcp_seq C S m \<subseteq> pcp_seq C S (Suc m)"
    by (rule pcp_seq_mono)
  have S:"{n. n \<le> Suc m}  = {Suc m} \<union> {n. n \<le> m}"
    by (simp only: le_Suc_eq Collect_disj_eq Un_commute singleton_conv)
  have "{pcp_seq C S n |n. n \<le> Suc m} = (pcp_seq C S) ` {n. n \<le> Suc m}" 
    by (simp only: image_Collect)
  then have "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = 
          \<Union>({pcp_seq C S (Suc m)} \<union> {pcp_seq C S n |n. n \<le> m})"
    by (simp only: S image_Un imageElem image_Collect)
  then have "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = (pcp_seq C S m) \<union> (pcp_seq C S (Suc m))"
    by (simp only: complete_lattice_class.Sup_union_distrib conditionally_complete_lattice_class.cSup_singleton HI Un_commute)
  thus "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = pcp_seq C S (Suc m)"
    using Mon by (simp only: subset_Un_eq)
qed

text \<open>Análogamente, podemos dar una prueba automática del resultado en Isabelle/HOL.\<close>

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

text \<open>Finalmente, definamos el límite de las sucesiones presentadas en la definición \<open>1.4.1\<close>.

 \begin{definicion}
  Sea \<open>C\<close> una colección, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la
  definición \<open>1.4.1\<close>. Se define el \<open>límite de la sucesión de conjuntos de C a partir de S\<close> como 
  $\bigcup_{n = 0}^{\infty} S_{n}$
 \end{definicion}

  La definición del límite se formaliza utilizando la unión generalizada de Isabelle como sigue.\<close>

definition "pcp_lim C S \<equiv> \<Union>{pcp_seq C S n|n. True}"

text \<open>Veamos el primer resultado sobre el límite.

\begin{lema}
  Sea \<open>C\<close> una colección de conjuntos, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de
  \<open>S\<close> según la definición \<open>1.4.1\<close>. Entonces, para todo \<open>n \<in> \<nat>\<close>, se verifica:

  $S_{n} \subseteq \bigcup_{n = 0}^{\infty} S_{n}$
\end{lema}

\begin{demostracion}
  El resultado se obtiene de manera inmediata ya que, para todo \<open>n \<in> \<nat>\<close>, se verifica que 
  $S_{n} \in \{S_{n}\}_{n = 0}^{\infty}$. Por tanto, es claro que 
  $S_{n} \subseteq \bigcup_{n = 0}^{\infty} S_{n}$.
\end{demostracion}

  Su formalización y demostración detallada en Isabelle se muestran a continuación.\<close>

lemma "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def
proof -
  have "n \<in> {n | n. True}" 
    by (simp only: simp_thms(21,38) Collect_const if_True UNIV_I) 
  then have "pcp_seq C S n \<in> (pcp_seq C S)`{n | n. True}"
    by (simp only: imageI)
  then have "pcp_seq C S n \<in> {pcp_seq C S n | n. True}"
    by (simp only: image_Collect simp_thms(40))
  thus "pcp_seq C S n \<subseteq> \<Union>{pcp_seq C S n | n. True}"
    by (simp only: Union_upper)
qed

text \<open>Podemos probarlo de manera automática como sigue.\<close>

lemma pcp_seq_sub: "pcp_seq C S n \<subseteq> pcp_lim C S" 
  unfolding pcp_lim_def by blast

text \<open>Por otra parte, mostremos el siguiente lema que relaciona la pertenencia de una fórmula 
  proposicional al límite definido en \<open>1.4.5\<close> y su pertenencia a un elemento de la sucesión definida
  en \<open>1.4.1\<close>. 

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos de fórmulas proposicionales, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de 
    conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la definición \<open>1.4.1\<close>. Sea \<open>F\<close> una fórmula tal que
    pertenece al límite $\bigcup_{n = 0}^{\infty} S_{n}$ de la sucesión. Entonces existe un \<open>k \<in> \<nat>\<close> 
    tal que \<open>F \<in> S\<^sub>k\<close>. 
  \end{lema}

  \begin{demostracion}
    La prueba es inmediata de la definición del límite de la sucesión de conjuntos \<open>{S\<^sub>n}\<close>: si
    \<open>F\<close> pertenece a la unión generalizada $\bigcup_{n = 0}^{\infty} S_{n}$, entonces existe algún
    conjunto \<open>S\<^sub>k\<close> tal que \<open>F \<in> S\<^sub>k\<close>. Es decir, existe \<open>k \<in> \<nat>\<close> tal que \<open>F \<in> S\<^sub>k\<close>, como queríamos
    demostrar.
  \end{demostracion} 

  Su prueba detallada en Isabelle/HOL es la siguiente. \<close>

lemma 
  assumes "F \<in> pcp_lim C S"
  shows "\<exists>k. F \<in> pcp_seq C S k" 
proof -
  have "F \<in> \<Union>((pcp_seq C S) ` {n | n. True})"
    using assms by (simp only: pcp_lim_def image_Collect simp_thms(40))
  then have "\<exists>k \<in> {n. True}. F \<in> pcp_seq C S k"
    by (simp only: UN_iff simp_thms(40))
  then have "\<exists>k \<in> UNIV. F \<in> pcp_seq C S k" 
    by (simp only: UNIV_def)
  thus "\<exists>k. F \<in> pcp_seq C S k" 
    by (simp only: bex_UNIV)
qed

text \<open>Mostremos, a continuación, la demostración automática del resultado.\<close>

lemma pcp_lim_inserted_at_ex: 
    "S' \<in> pcp_lim C S \<Longrightarrow> \<exists>k. S' \<in> pcp_seq C S k"
  unfolding pcp_lim_def by blast

text \<open>Por último, veamos la siguiente propiedad sobre conjuntos finitos contenidos en el límite de 
  las sucesiones definido en \<open>1.4.5\<close>.

\begin{lema}
  Sea \<open>C\<close> una colección, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la
  definición \<open>1.4.1\<close>. Si \<open>S'\<close> es un conjunto finito tal que \<open>S' \<subseteq>\<close> $\bigcup_{n = 0}^{\infty} S_{n}$, 
  entonces existe un \<open>k \<in> \<nat>\<close> tal que \<open>S' \<subseteq> S\<^sub>k\<close>.
\end{lema}

\begin{demostracion}
  La prueba del resultado se realiza por inducción sobre la estructura recursiva de los conjuntos 
  finitos.

  En primer lugar, consideremos que el conjunto vacío está contenido en el límite de la sucesión de
  conjuntos de \<open>C\<close> a partir de \<open>S\<close>. Como \<open>{}\<close> es subconjunto de todo conjunto, en particular lo es 
  de \<open>S = S\<^sub>0\<close>, probando así el primer caso.

  Por otra parte, sea \<open>S'\<close> un conjunto finito contenido en el límite de la sucesión de conjuntos de 
  \<open>C\<close> a partir de \<open>S\<close>, de modo que también está contenido en algún \<open>S\<^sub>k\<^sub>'\<close> para cierto \<open>k' \<in> \<nat>\<close>. Sea 
  \<open>F\<close> una fórmula cualquiera no perteneciente a \<open>S'\<close>. Supongamos que\\ \<open>{F} \<union> S'\<close> está también 
  contenido en el límite. Probemos que \<open>{F} \<union> S'\<close> está contenido \<open>S\<^sub>k\<close> para algún \<open>k \<in> \<nat>\<close>. 

  Como hemos supuesto que \<open>{F} \<union> S'\<close> está contenido en el límite, entonces se verifica que \<open>F\<close>
  pertenece al límite y \<open>S'\<close> está contenido en él. Por el lema \<open>1.4.7\<close>, como \<open>F\<close> pertenece al 
  límite, deducimos que existe un \<open>k \<in> \<nat>\<close> tal que \<open>x \<in> S\<^sub>k\<close>. Por otro lado, como \<open>S'\<close> está contenido
  en el límite, por hipótesis de inducción existe algún \<open>k' \<in> \<nat>\<close> tal que \<open>S' \<subseteq> S\<^sub>k\<^sub>'\<close>. El resultado 
  se obtiene considerando el máximo entre \<open>k\<close> y \<open>k'\<close>, que notaremos por \<open>k''\<close>. En efecto, por la 
  monotonía de la sucesión, se verifica que tanto \<open>S\<^sub>k\<close> como \<open>S\<^sub>k\<^sub>'\<close> están contenidos en \<open>S\<^sub>k\<^sub>'\<^sub>'\<close>. De este 
  modo, como \<open>S' \<subseteq> S\<^sub>k\<^sub>'\<close>, por la transitividad de la contención de conjuntos se tiene que 
  \<open>S' \<subseteq> S\<^sub>k\<^sub>'\<^sub>'\<close>. Además, como \<open>F \<in> S\<^sub>k\<close>, se tiene que \<open>F \<in> S\<^sub>k\<^sub>'\<^sub>'\<close>. Por lo tanto, \<open>{F} \<union> S' \<subseteq> S\<^sub>k\<^sub>'\<^sub>'\<close>, como 
  queríamos demostrar. 
\end{demostracion}

  Procedamos con la demostración detallada en Isabelle.\<close>

lemma 
  assumes "finite S'"
          "S' \<subseteq> pcp_lim C S"
        shows "\<exists>k. S' \<subseteq> pcp_seq C S k"
  using assms
proof (induction S' rule: finite_induct)
  case empty
  have "pcp_seq C S 0 = S"
    by (simp only: pcp_seq.simps(1))
  have "{} \<subseteq> S"
    by (rule order_bot_class.bot.extremum)
  then have "{} \<subseteq> pcp_seq C S 0"
    by (simp only: \<open>pcp_seq C S 0 = S\<close>)
  then show ?case 
    by (rule exI)
next
  case (insert F S')
  then have "insert F S' \<subseteq> pcp_lim C S"
    by (simp only: insert.prems)
  then have C:"F \<in> (pcp_lim C S) \<and> S' \<subseteq> pcp_lim C S"
    by (simp only: insert_subset) 
  then have "S' \<subseteq> pcp_lim C S"
    by (rule conjunct2)
  then have EX1:"\<exists>k. S' \<subseteq> pcp_seq C S k"
    by (simp only: insert.IH)
  obtain k1 where "S' \<subseteq> pcp_seq C S k1"
    using EX1 by (rule exE)
  have "F \<in> pcp_lim C S"
    using C by (rule conjunct1)
  then have EX2:"\<exists>k. F \<in> pcp_seq C S k"
    by (rule pcp_lim_inserted_at_ex)
  obtain k2 where "F \<in> pcp_seq C S k2" 
    using EX2 by (rule exE)
  have "k1 \<le> max k1 k2"
    by (simp only: linorder_class.max.cobounded1)
  then have "pcp_seq C S k1 \<subseteq> pcp_seq C S (max k1 k2)"
    by (rule pcp_seq_mono)
  have "k2 \<le> max k1 k2"
    by (simp only: linorder_class.max.cobounded2)
  then have "pcp_seq C S k2 \<subseteq> pcp_seq C S (max k1 k2)"
    by (rule pcp_seq_mono)
  have "S' \<subseteq> pcp_seq C S (max k1 k2)"
    using \<open>S' \<subseteq> pcp_seq C S k1\<close> \<open>pcp_seq C S k1 \<subseteq> pcp_seq C S (max k1 k2)\<close> by (rule subset_trans)
  have "F \<in> pcp_seq C S (max k1 k2)"
    using \<open>F \<in> pcp_seq C S k2\<close> \<open>pcp_seq C S k2 \<subseteq> pcp_seq C S (max k1 k2)\<close> by (rule rev_subsetD)
  then have 1:"insert F S' \<subseteq> pcp_seq C S (max k1 k2)"
    using \<open>S' \<subseteq> pcp_seq C S (max k1 k2)\<close> by (simp only: insert_subset)
  thus ?case
    by (rule exI)
qed

text \<open>Finalmente, su demostración automática en Isabelle/HOL es la siguiente.\<close>

lemma finite_pcp_lim_EX:
  assumes "finite S'"
          "S' \<subseteq> pcp_lim C S"
        shows "\<exists>k. S' \<subseteq> pcp_seq C S k"
  using assms
proof(induction S' rule: finite_induct) 
  case (insert F S')
  hence "\<exists>k. S' \<subseteq> pcp_seq C S k" by fast
  then guess k1 ..
  moreover obtain k2 where "F \<in> pcp_seq C S k2"
    by (meson pcp_lim_inserted_at_ex insert.prems insert_subset)
  ultimately have "insert F S' \<subseteq> pcp_seq C S (max k1 k2)"
    by (meson pcp_seq_mono dual_order.trans insert_subset max.bounded_iff order_refl subsetCE)
  thus ?case by blast
qed simp

section \<open>El teorema de existencia de modelo\<close>

text \<open>\comentario{Añadir explicación}\<close>

text \<open>
  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional, es 
    cerrada bajo subconjuntos y es de carácter finito. Sea \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos
    de \<open>C\<close> a partir de \<open>S\<close> según la definición \<open>1.4.1\<close>. Entonces, el límite de la sucesión está en
    \<open>C\<close>.
  \end{lema}\<close>

lemma pcp_lim_in_detallada:
  assumes "pcp C"
          "S \<in> C"
          "subset_closed C"
          "finite_character C"
  shows "pcp_lim C S \<in> C" 
proof -
  have "\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C)"
    using assms(4) unfolding finite_character_def by this
  then have FC1:"pcp_lim C S \<in> C \<longleftrightarrow> (\<forall>S' \<subseteq> (pcp_lim C S). finite S' \<longrightarrow> S' \<in> C)"
    by (rule allE)
  have SC:"\<forall>S \<in> C. \<forall>S'\<subseteq>S. S' \<in> C"
    using assms(3) unfolding subset_closed_def by this
  have "\<forall>n. pcp_seq C S n \<in> C" 
  proof (rule allI)
    fix n
    show "pcp_seq C S n \<in> C" 
      using assms(1) assms(2) by (rule pcp_seq_in)
  qed
  then have "\<forall>m. \<Union>{pcp_seq C S n|n. n \<le> m} \<in> C" 
    unfolding pcp_seq_UN by this
  have FC2:"\<forall>S' \<subseteq> pcp_lim C S. finite S' \<longrightarrow> S' \<in> C"
  proof (rule sallI)
    fix S' :: "'a formula set"
    assume "S' \<subseteq> pcp_lim C S"
    show "finite S' \<longrightarrow> S' \<in> C"
    proof (rule impI)
      assume "finite S'"
      then have EX:"\<exists>k. S' \<subseteq> pcp_seq C S k" 
        using \<open>S' \<subseteq> pcp_lim C S\<close> by (rule finite_pcp_lim_EX)
      obtain n where "S' \<subseteq> pcp_seq C S n"
        using EX by (rule exE)
      have "pcp_seq C S n \<in> C"
        using assms(1) assms(2) by (rule pcp_seq_in)
      have "\<forall>S' \<subseteq> (pcp_seq C S n). S' \<in> C"
        using SC \<open>pcp_seq C S n \<in> C\<close> by (rule bspec)
      thus "S' \<in> C"
        using \<open>S' \<subseteq> pcp_seq C S n\<close> by (rule sspec)
    qed
  qed
  show "pcp_lim C S \<in> C" 
    using FC1 FC2 by (rule forw_subst)
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
  have "\<forall>S' \<subseteq> ?cl. finite S' \<longrightarrow> S' \<in> C"
  proof safe
    fix S' :: "'a formula set"
    have "pcp_seq C S (Suc (Max (to_nat ` S'))) \<subseteq> pcp_lim C S" 
      using pcp_seq_sub by blast
    assume \<open>finite S'\<close> \<open>S' \<subseteq> pcp_lim C S\<close>
    hence "\<exists>k. S' \<subseteq> pcp_seq C S k" 
    proof(induction S' rule: finite_induct) 
      case (insert x S')
      hence "\<exists>k. S' \<subseteq> pcp_seq C S k" by fast
      then guess k1 ..
      moreover obtain k2 where "x \<in> pcp_seq C S k2"
        by (meson pcp_lim_inserted_at_ex insert.prems insert_subset)
      ultimately have "insert x S' \<subseteq> pcp_seq C S (max k1 k2)"
        by (meson pcp_seq_mono dual_order.trans insert_subset max.bounded_iff order_refl subsetCE)
      thus ?case by blast
    qed simp
    with pcp_seq_in[OF c el] sc
    show "S' \<in> C" unfolding subset_closed_def by blast
  qed
  thus "?cl \<in> C" using fc unfolding finite_character_def by blast
qed

text \<open>

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional y
    es cerrada bajo subconjuntos, \<open>S\<close> un conjunto y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir 
    de \<open>S\<close> según la definición \<open>1.4.1\<close>. Entonces, el límite de la sucesión es un elemento maximal 
    de \<open>C\<close>.
  \end{lema}\<close>

lemma cl_max_detallada:
  assumes "pcp C"
          "subset_closed C"
          "K \<in> C"
          "pcp_lim C S \<subseteq> K"
  shows "pcp_lim C S = K"
proof (rule ccontr)
  assume H:"\<not>(pcp_lim C S = K)"
  have CE:"pcp_lim C S \<subseteq> K \<and> pcp_lim C S \<noteq> K"
    using assms(4) H by (rule conjI)
  have "pcp_lim C S \<subseteq> K \<and> pcp_lim C S \<noteq> K \<longleftrightarrow> pcp_lim C S \<subset> K"
    by (simp only: psubset_eq)
  then have "pcp_lim C S \<subset> K" 
    using CE by (rule iffD1)
  then have "\<exists>F. F \<in> (K - (pcp_lim C S))"
    by (simp only: psubset_imp_ex_mem) 
  then have E:"\<exists>F. F \<in> K \<and> F \<notin> (pcp_lim C S)"
    by (simp only: Diff_iff)
  obtain F where F:"F \<in> K \<and> F \<notin> pcp_lim C S" 
    using E by (rule exE)
  have "F \<in> K" 
    using F by (rule conjunct1)
  have "F \<notin> pcp_lim C S"
    using F by (rule conjunct2)
  have "pcp_seq C S (Suc (to_nat F)) \<subseteq> pcp_lim C S"
    by (rule pcp_seq_sub)
  then have "F \<in> pcp_seq C S (Suc (to_nat F)) \<longrightarrow> F \<in> pcp_lim C S"
    by (rule in_mono)
  then have 1:"F \<notin> pcp_seq C S (Suc (to_nat F))"
    using \<open>F \<notin> pcp_lim C S\<close> by (rule mt)
  have 2: "insert F (pcp_seq C S (to_nat F)) \<notin> C" 
    using 1  by (simp add: Let_def split: if_splits) (*Pendiente*)
  have "pcp_seq C S (to_nat F) \<subseteq> pcp_lim C S"
    by (rule pcp_seq_sub)
  then have "pcp_seq C S (to_nat F) \<subseteq> K"
    using assms(4) by (rule subset_trans)
  then have "insert F (pcp_seq C S (to_nat F)) \<subseteq> K" 
    using \<open>F \<in> K\<close> by (simp only: insert_subset)
  have "\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C"
    using assms(2) by (simp only: subset_closed_def)
  then have "\<forall>s \<subseteq> K. s \<in> C"
    using assms(3) by (rule bspec)
  then have 3:"insert F (pcp_seq C S (to_nat F)) \<in> C" 
    using \<open>insert F (pcp_seq C S (to_nat F)) \<subseteq> K\<close> by (rule sspec)
  show "False"
    using 2 3 by (rule notE)
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

text \<open>\comentario{Es una adaptación concreta del lema anterior para el caso en
  que K se forme añadiendo 1 elemento o 2 al límite.}\<close>

lemma cl_max'_detallada:
  assumes "pcp C"
  assumes "subset_closed C"
  shows "insert F (pcp_lim C S) \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
        "insert F (insert G (pcp_lim C S)) \<in> C \<Longrightarrow> F \<in> pcp_lim C S \<and> G \<in> pcp_lim C S"
proof -
  show "insert F (pcp_lim C S) \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
  proof -
    assume "insert F (pcp_lim C S) \<in> C"
    have "pcp_lim C S \<subseteq> insert F (pcp_lim C S)"
      by (rule subset_insertI) 
    have "pcp_lim C S = insert F (pcp_lim C S)"
      using assms(1) assms(2) \<open>insert F (pcp_lim C S) \<in> C\<close> \<open>pcp_lim C S \<subseteq> insert F (pcp_lim C S)\<close> by (rule cl_max)
    then have "insert F (pcp_lim C S) \<subseteq> pcp_lim C S"
      by (rule equalityD2)
    then have "F \<in> pcp_lim C S \<and> pcp_lim C S \<subseteq> pcp_lim C S"
      by (simp only: insert_subset)
    thus "F \<in> pcp_lim C S"
      by (rule conjunct1)
  qed
  show "insert F (insert G (pcp_lim C S)) \<in> C \<Longrightarrow> F \<in> pcp_lim C S \<and> G \<in> pcp_lim C S"
  proof (rule conjI)
    assume "insert F (insert G (pcp_lim C S)) \<in> C"
    have "pcp_lim C S \<subseteq> insert G (pcp_lim C S)"
      by (rule subset_insertI)
    then have "pcp_lim C S \<subseteq> insert F (insert G (pcp_lim C S))"
      by (rule subset_insertI2)
    have "pcp_lim C S = insert F (insert G (pcp_lim C S))"
      using assms(1) assms(2) \<open>insert F (insert G (pcp_lim C S)) \<in> C\<close> \<open>pcp_lim C S \<subseteq> insert F (insert G (pcp_lim C S))\<close> by (rule cl_max)
    then have "insert F (insert G (pcp_lim C S)) \<subseteq> pcp_lim C S"
      by (rule equalityD2)
    then have 1:"F \<in> pcp_lim C S \<and> (insert G (pcp_lim C S)) \<subseteq> pcp_lim C S"
      by (simp only: insert_subset)
    thus "F \<in> pcp_lim C S"
      by (rule conjunct1)
    have "insert G (pcp_lim C S) \<subseteq> pcp_lim C S"
      using 1 by (rule conjunct2)
    then have "G \<in> pcp_lim C S \<and> pcp_lim C S \<subseteq> pcp_lim C S"
      by (simp only: insert_subset)
    thus "G \<in> pcp_lim C S"
      by (rule conjunct1)
  qed
qed

lemma cl_max':
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  shows "insert F (pcp_lim C S) \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
    "insert F (insert G (pcp_lim C S)) \<in> C \<Longrightarrow> F \<in> pcp_lim C S \<and> G \<in> pcp_lim C S"
  using cl_max[OF assms] by blast+

text \<open>
\begin{lema}
  Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional, es
  es cerrada bajo subconjuntos y es de carácter finito. Sea \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de
  conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la definición \<open>1.4.1\<close>. Entonces, el límite de la sucesión
  es un conjunto de Hintikka.
\end{lema}\<close>

lemma pcp_lim_Hintikka_detallada:
  assumes "pcp C"
  assumes "subset_closed C"
  assumes "finite_character C"
  assumes "S \<in> C"
  shows "Hintikka (pcp_lim C S)"
proof (rule Hintikka_alt2)
  let ?cl = "pcp_lim C S"
  have "?cl \<in> C"
    using assms(1) assms(4) assms(2) assms(3) by (rule pcp_lim_in)
  have "(\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C))"
    using assms(1) by (rule pcp_alt1)
  then have d:"\<bottom> \<notin> ?cl
\<and> (\<forall>k. Atom k \<in> ?cl \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?cl \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G,H} \<union> ?cl \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G} \<union> ?cl \<in> C \<or> {H} \<union> ?cl \<in> C)"
    using \<open>?cl \<in> C\<close> by (rule bspec)
  then have H1:"\<bottom> \<notin> ?cl"
    by (rule conjunct1)
  have H2:"\<forall>k. Atom k \<in> ?cl \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?cl \<longrightarrow> False"
    using d by (iprover elim: conjunct2 conjunct1)
  have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G,H} \<union> ?cl \<in> C"
    using d by (iprover elim: conjunct2 conjunct1)
  have H3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
  proof (rule allI)+
    fix F G H
    show "Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
    proof (rule impI)+
      assume "Con F G H"
      assume "F \<in> ?cl"
      have "Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G,H} \<union> ?cl \<in> C"
        using Con by (iprover elim: allE)
      then have "F \<in> ?cl \<longrightarrow> {G,H} \<union> ?cl \<in> C"
        using \<open>Con F G H\<close> by (rule mp)
      then have "{G,H} \<union> ?cl \<in> C"
        using \<open>F \<in> ?cl\<close> by (rule mp)
      have "(insert G (insert H ?cl)) = {G,H} \<union> ?cl"
        by (rule insertSetElem)
      then have "(insert G (insert H ?cl)) \<in> C"
        using \<open>{G,H} \<union> ?cl \<in> C\<close> by (simp only: \<open>(insert G (insert H ?cl)) = {G,H} \<union> ?cl\<close>)
      have "(insert G (insert H ?cl)) \<in> C \<Longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
        using assms(1) assms(2) by (rule cl_max')
      thus "G \<in> ?cl \<and> H \<in> ?cl"
        by (simp only: \<open>insert G (insert H ?cl) \<in> C\<close>) 
    qed
  qed
  have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G} \<union> ?cl \<in> C \<or> {H} \<union> ?cl \<in> C"
    using d by (iprover elim: conjunct2 conjunct1)
  have H4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
  proof (rule allI)+
    fix F G H
    show "Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
    proof (rule impI)+
      assume "Dis F G H"
      assume "F \<in> ?cl"
      have "Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G} \<union> ?cl \<in> C \<or> {H} \<union> ?cl \<in> C"
        using Dis by (iprover elim: allE)
      then have "F \<in> ?cl \<longrightarrow> {G} \<union> ?cl \<in> C \<or> {H} \<union> ?cl \<in> C"
        using \<open>Dis F G H\<close> by (rule mp)
      then have "{G} \<union> ?cl \<in> C \<or> {H} \<union> ?cl \<in> C"
        using \<open>F \<in> ?cl\<close> by (rule mp)
      thus "G \<in> ?cl \<or> H \<in> ?cl"
      proof (rule disjE)
        assume "{G} \<union> ?cl \<in> C"
        have "insert G ?cl = {G} \<union> ?cl"
          by (rule insert_is_Un)
        have "insert G ?cl \<in> C"
          using \<open>{G} \<union> ?cl \<in> C\<close> by (simp only: \<open>insert G ?cl = {G} \<union> ?cl\<close>)
        have "insert G ?cl \<in> C \<Longrightarrow> G \<in> ?cl"
          using assms(1) assms(2) by (rule cl_max')
        then have "G \<in> ?cl"
          by (simp only: \<open>insert G ?cl \<in> C\<close>)
        thus "G \<in> ?cl \<or> H \<in> ?cl"
          by (rule disjI1)
      next
        assume "{H} \<union> ?cl \<in> C"
        have "insert H ?cl = {H} \<union> ?cl"
          by (rule insert_is_Un)
        have "insert H ?cl \<in> C"
          using \<open>{H} \<union> ?cl \<in> C\<close> by (simp only: \<open>insert H ?cl = {H} \<union> ?cl\<close>)
        have "insert H ?cl \<in> C \<Longrightarrow> H \<in> ?cl"
          using assms(1) assms(2) by (rule cl_max')
        then have "H \<in> ?cl"
          by (simp only: \<open>insert H ?cl \<in> C\<close>)
        thus "G \<in> ?cl \<or> H \<in> ?cl"
          by (rule disjI2)
      qed
    qed
  qed
  show "\<bottom> \<notin> ?cl \<and>
    (\<forall>k. Atom k \<in> ?cl \<longrightarrow> \<^bold>\<not> (Atom k) \<in> ?cl \<longrightarrow> False) \<and>
    (\<forall>F G H. Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl) \<and>
    (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl)"
    using H1 H2 H3 H4 by (iprover intro: conjI)
qed

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

text \<open>
\begin{lema}
  Todo subconjunto de un conjunto de fórmulas satisfacible es satisfacible.
\end{lema}\<close>

lemma sat_mono:
  assumes "A \<subseteq> B"
          "sat B"
        shows "sat A"
  unfolding sat_def
proof -
 have satB:"\<exists>\<A>. \<forall>F \<in> B. \<A> \<Turnstile> F"
   using assms(2) by (simp only: sat_def)
 obtain \<A> where "\<forall>F \<in> B. \<A> \<Turnstile> F"
    using satB by (rule exE)
 have "\<forall>F \<in> A. \<A> \<Turnstile> F"
  proof (rule ballI)
    fix F
    assume "F \<in> A"
    have "F \<in> A \<longrightarrow> F \<in> B"
      using assms(1) by (rule in_mono)
    then have "F \<in> B"
      using \<open>F \<in> A\<close> by (rule mp)
    show "\<A> \<Turnstile> F"
      using \<open>\<forall>F \<in> B. \<A> \<Turnstile> F\<close> \<open>F \<in> B\<close> by (rule bspec)
  qed
  thus "\<exists>\<A>. \<forall>F \<in> A. \<A> \<Turnstile> F"
    by (simp only: exI)
qed

text\<open>
  \begin{teorema}[Teorema de Existencia de Modelo]
    Todo conjunto de fórmulas perteneciente a una colección que verifique la propiedad de
    consistencia proposicional es satisfacible. 
  \end{teorema}\<close>

theorem pcp_sat_detallada:
  fixes S :: "'a :: countable formula set"
  assumes "pcp C"
  assumes "S \<in> C"
  shows "sat S"
proof -
  have "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
    by (rule ex1)
  then have E1:"\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
    by (simp only: assms(1))
  obtain Ce' where H1:"C \<subseteq> Ce' \<and> pcp Ce' \<and> subset_closed Ce'"
    using E1 by (rule exE)
  have "C \<subseteq> Ce'"
    using H1 by (rule conjunct1)
  have "pcp Ce'"
    using H1 by (iprover elim: conjunct2 conjunct1)
  have "subset_closed Ce'"
    using H1 by (iprover elim: conjunct2 conjunct1)
  have E2:"\<exists>Ce. Ce' \<subseteq> Ce \<and> pcp Ce \<and> finite_character Ce"
    using \<open>pcp Ce'\<close> \<open>subset_closed Ce'\<close> by (rule ex3)
  obtain Ce where H2:"Ce' \<subseteq> Ce \<and> pcp Ce \<and> finite_character Ce"
    using E2 by (rule exE)
  have "Ce' \<subseteq> Ce"
    using H2 by (rule conjunct1)
  then have Subset:"C \<subseteq> Ce"
    using \<open>C \<subseteq> Ce'\<close> by (simp only: subset_trans)
  have Pcp:"pcp Ce"
    using H2 by (iprover elim: conjunct2 conjunct1)
  have FC:"finite_character Ce"
    using H2 by (iprover elim: conjunct2 conjunct1)
  then have SC:"subset_closed Ce"
    by (rule ex2)
  have "S \<in> C \<longrightarrow> S \<in> Ce"
    using \<open>C \<subseteq> Ce\<close> by (rule in_mono)
  then have "S \<in> Ce" 
    using assms(2) by (rule mp)
  have "Hintikka (pcp_lim Ce S)"
    using Pcp SC FC \<open>S \<in> Ce\<close> by (rule pcp_lim_Hintikka)
  then have "sat (pcp_lim Ce S)"
    by (rule Hintikkaslemma)
  then have E3:"\<exists>\<A>. \<forall>F \<in> (pcp_lim Ce S). \<A> \<Turnstile> F"
    by (simp only: sat_def)
  obtain \<A> where H3:"\<forall>F \<in> (pcp_lim Ce S). \<A> \<Turnstile> F" 
    using E3 by (rule exE)
  have "pcp_seq Ce S 0 = S"
    by (simp only: pcp_seq.simps(1))
  have "pcp_seq Ce S 0 \<subseteq> pcp_lim Ce S"
    by (rule pcp_seq_sub)
  then have "S \<subseteq> pcp_lim Ce S"
    by (simp only: \<open>pcp_seq Ce S 0 = S\<close>)
  thus "sat S"
    using \<open>sat (pcp_lim Ce S)\<close> by (rule sat_mono)
qed

theorem pcp_sat:
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

(*<*)
end
(*>*) 
