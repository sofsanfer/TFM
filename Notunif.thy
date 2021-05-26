(*<*) 
theory Notunif
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

text \<open>En esta sección introduciremos la notación uniforme inicialmente 
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

text \<open>Según la definición del valor de verdad de una fórmula proposicional en una 
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

text \<open>Las reglas de introducción que proporciona esta formalización se muestran a continuación.

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

text\<open>Por último, introduzcamos un resultado que permite caracterizar los conjuntos de Hintikka 
  empleando la notación uniforme.

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

text \<open>Por último, veamos su demostración automática.\<close>

lemma Hintikka_alt: "Hintikka S = (\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S))"  
  apply(simp add: Hintikka_def con_dis_simps)
  apply(rule iffI)
   subgoal by blast
  subgoal by safe metis+
  done

(*<*)
end
(*>*) 