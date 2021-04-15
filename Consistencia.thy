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

\comentario{Pone trabajo fin de grado}
\comentario{Cambiar los directores}
\comentario{Introducción}

\<close>

text \<open>En esta sección probaremos la consistencia de la lógica proposicional demostrando el \<open>teorema 
  de existencia de modelos\<close>. Para ello, consideraremos colecciones de conjuntos de fórmulas 
  proposicionales y definiremos propiedades y resultados sobre las
  mismas.

\comentario{Ver Fitting pg. 53 y 54}

\<close>

section \<open>Propiedad de consistencia proposicional\<close>

text \<open>En primer lugar, definiremos la propiedad de consistencia proposicional para una colección 
  de conjuntos de fórmulas proposicionales. Probaremos que cualquier conjunto de fórmulas 
  proposicionales perteneciente a una colección que verifique dicha propiedad será satisfacible por 
  el \<open>teorema de existencia de modelos\<close>.\<close>

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

text \<open>En esta subsección vamos a introducir la notación uniforme inicialmente 
  desarrollada por \<open>R. M. Smullyan\<close> (añadir referencia bibliográfica). La finalidad
  de dicha notación es reducir el número de casos a considerar sobre la estructura de 
  las fórmulas al clasificar éstas en dos categorías, facilitando las demostraciones
  y métodos empleados en adelante.

  \comentario{Añadir referencia bibliográfica.}

  De este modo, las fórmulas proposicionales pueden ser de dos tipos: aquellas que 
  de tipo conjuntivo (las fórmulas \<open>\<alpha>\<close>) y las de tipo disyuntivo (las fórmulas \<open>\<beta>\<close>). 
  Cada fórmula de tipo \<open>\<alpha>\<close>, o \<open>\<beta>\<close> respectivamente, tiene asociada sus  
  dos componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, o \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> respectivamente. 

  \begin{definicion}
    Las fórmulas de tipo \<open>\<alpha>\<close> (\<open>fórmulas conjuntivas\<close>) y sus correspondientes componentes
    \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se definen como sigue: dadas \<open>F\<close> y \<open>G\<close> fórmulas cualesquiera,
    \begin{enumerate}
      \item \<open>F \<and> G\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>G\<close>.
      \item \<open>\<not>(F \<or> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(F \<longrightarrow> G)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(\<not> F)\<close> es una fórmula de tipo \<open>\<alpha>\<close> cuyas componentes son \<open>F\<close> y \<open>F\<close>.
    \end{enumerate} 
  \end{definicion}

  Realizamos su formalización en Isabelle como un predicado definido de
  forma inductiva, es decir, especificando las reglas que cumple.

\comentario {He modificado ligeramente el párrafo anterior. Cambiar explicaciones y def.}\<close>

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

  A continuación, definamos las fórmulas disyuntivas.

  \begin{definicion}
    Las fórmulas de tipo \<open>\<beta>\<close> (\<open>fórmulas disyuntivas\<close>) y sus correspondientes componentes
    \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se definen como sigue: dadas \<open>F\<close> y \<open>G\<close> fórmulas cualesquiera,
    \begin{enumerate}
      \item \<open>F \<or> G\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>F\<close> y \<open>G\<close>.
      \item \<open>F \<longrightarrow> G\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>G\<close>.
      \item \<open>\<not>(F \<and> G)\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>\<not> F\<close> y \<open>\<not> G\<close>.
      \item \<open>\<not>(\<not> F)\<close> es una fórmula de tipo \<open>\<beta>\<close> cuyas componentes son \<open>F\<close> y \<open>F\<close>.
    \end{enumerate} 
  \end{definicion}

  Análogamente, su formalización en Isabelle se realiza como un predicado
  definido de forma inductiva, como se muestra a continuación.\<close>

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

\comentario{Comentar si todas las fórmulas proposicionales son de uno de estos dos
tipos, p. ejemplo, las atómicas. Comentar si ee usa el esquema de inducción proporcionado
por la definición inductiva. }

  Observando las definiciones dadas de las fórmulas \<open>\<alpha>\<close> y \<open>\<beta>\<close>, podemos trivialmente
  deducir el siguiente lema.

  \begin{lema}
    La doble negación de una fórmula cualquiera es una fórmula conjuntiva y disyuntiva
    simultáneamente.
  \end{lema}

  Su formalización y demostración detallada en Isabelle se muestran a continuación.\<close>

lemma notDisCon: "Con (Not (Not F)) F F" "Dis (Not (Not F)) F F" 
  by (simp only: Con.intros(4) Dis.intros(4))+

text \<open>Por otra parte, de la propia definición de las fórmulas de tipo \<open>\<alpha>\<close> y \<open>\<beta>\<close>
  obtenemos reglas de simplificación. De este modo, dada una fórmula de tipo
  \<open>\<alpha>\<close> o \<open>\<beta>\<close> deducimos que se corresponde con uno de los cuatro casos de fórmula 
  definidos para cada tipo con sus correspondientes componentes.
  En Isabelle, hemos formalizado las reglas de simplificación de ambos tipos de 
  fórmulas en un resultado conjunto.

\comentario{Creo que el siguiente lema es facilitar el uso de las fórmulas
en notación uniforme, pues caracteriza como son las fórmulas  \<open>\<alpha>\<close> y las \<open>\<beta>\<close>.}
\<close>

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
  de Hintikka y la propiedad de consistencia proposicional empleando la 
  notación uniforme.

  \begin{lema}[Caracterización de los conjuntos de Hintikka mediante la
  notación uniforme]
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

text\<open>A continuación veamos un resultado que permite la caracterización de la 
  propiedad de consistencia proposicional mediante la notación uniforme.

  \begin{lema}[Caracterización de \<open>pcp\<close> mediante la notación uniforme]
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

  \comentario{No consigo hacer que baje de línea el título del lema.}

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
    \<open>H\<close> respectivamente. Luego tenemos que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close>  pertenece a \<open>C\<close> o bien 
    \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close> por la cuarta condición de la definición de propiedad de 
    consistencia proposicional.

  \<open>\<sqdot> Fórmula de tipo G \<longrightarrow> H\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son 
    \<open>\<not> G\<close> y \<open>H\<close> respectivamente. Luego tenemos que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close>  pertenece a \<open>C\<close> o 
    bien \<open>{\<beta>\<^sub>2} \<union> S\<close> pertenece a \<open>C\<close> por la quinta condición de la definición de propiedad 
    de consistencia proposicional.

  \<open>\<sqdot> Fórmula de tipo \<not>(\<not> G)\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son ambas 
    \<open>G\<close>. Luego tenemos que, en particular, el conjunto \<open>{\<beta>\<^sub>1} \<union> S\<close> pertenece a \<open>C\<close> por la 
    sexta condición de la definición de propiedad de consistencia proposicional. Por tanto, se 
    verifica que o bien \<open>{\<beta>\<^sub>1} \<union> S\<close> está en \<open>C\<close> o bien \<open>{\<beta>\<^sub>2} \<union> S\<close> está en \<open>C\<close>.

  \<open>\<sqdot> Fórmula de tipo \<not>(G \<and> H)\<close>: En este caso, sus componentes disyuntivas \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son\\ 
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
    \<open>G\<close> y \<open>H\<close>. Luego, por hipótesis, tenemos que o bien \<open>{G} \<union> S\<close> pertenece a \<open>C\<close> o bien
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

text \<open>De esta manera, mediante los anteriores lemas auxiliares, podemos probar la primera
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

text \<open>Por otro lado, los siguientes lemas auxiliares prueban el resto de condiciones de la
  definición de propiedad de consistencia proposicional a partir de la hipótesis referente a 
  fórmulas de tipo \<open>\<beta>\<close>.\<close>

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
      let ?F="\<^bold>\<not>(G \<^bold>\<and> H)"
      have "Dis ?F (\<^bold>\<not>G) (\<^bold>\<not>H) \<longrightarrow> ?F \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        using assms by (iprover elim: allE)
      then have "?F \<in> S \<longrightarrow> {\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>Dis (\<^bold>\<not>(G \<^bold>\<and> H)) (\<^bold>\<not>G) (\<^bold>\<not>H)\<close> by (rule mp)
      thus "{\<^bold>\<not>G} \<union> S \<in> C \<or> {\<^bold>\<not>H} \<union> S \<in> C"
        using \<open>\<^bold>\<not>(G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
    qed
  qed
qed

text \<open>De este modo, procedemos a la demostración detallada de esta implicación en Isabelle como
  sigue.\<close>

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

text\<open>
\comentario{Explicar lo que se quiere demostrar en esta sección, dar
la idea de la prueba  y cómo se necesita la propiedad de que una clase 
sea cerrada bajo subconjunto (ver Fitting pg. 53 y 54)}
\<close>

text \<open>En este apartado definiremos dos propiedades referentes a colecciones que utilizaremos 
  posteriormente para la probar la consistencia de la lógica proposicional.

  \comentario{Explicar mejor la relación de las propiedades con el th de ex. de modelos. Redactar
  bien el párrafo anterior.}

  \begin{definicion}
    Una colección de conjuntos es cerrada bajo subconjuntos si todo subconjunto de cada conjunto 
    de la colección pertenece a la colección.
  \end{definicion}

  En Isabelle se formaliza de la siguiente manera.\<close>

definition "subset_closed C \<equiv> (\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C)"

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
  Una colección de conjuntos tiene la propiedad de carácter finito si para cualquier conjunto
  son equivalentes:
  \begin{enumerate}
    \item El conjunto pertenece a la colección.
    \item Todo subconjunto finito suyo pertenece a la colección.
  \end{enumerate}
\end{definicion}

  La formalización en Isabelle/HOL de dicha definición se muestra a continuación.\<close>

definition "finite_character C \<equiv> 
            (\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C))"

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

text \<open>Una vez introducidas las definiciones anteriores, veamos tres resultados sobre colecciones
  de conjuntos.

\comentario{La descripción previa es excesivamente genérica. Es conveniente 
precisar más.}

  \begin{lema}
    Si una colección de conjuntos tiene la propiedad de consistencia proposicional, entonces
    podemos hallar una colección que la contenga de manera que también verifique la propiedad de 
    consistencia proposicional y sea cerrada bajo subconjuntos.
  \end{lema}

  En Isabelle se formaliza el resultado de la siguiente manera.\<close>

lemma "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
  oops

text \<open>Procedamos con su demostración.

\begin{demostracion}
  Dada una colección de conjuntos cualquiera \<open>C\<close>, consideremos la colección formada por los 
  conjuntos tales que son subconjuntos de algún conjunto de \<open>C\<close>. Notemos esta clase por \<open>C' = {s. \<exists>S\<in>C. s \<subseteq> S}\<close>. 
 Vamos a probar que, en efecto, \<open>C'\<close> verifica  las condiciones del lema.

  En primer lugar, veamos que \<open>C\<close> está contenida en \<open>C'\<close>. Para ello, consideremos un conjunto
  cualquiera perteneciente a la colección inicial \<open>C\<close>. Puesto que la propiedad de contención es 
  reflexiva, dicho conjunto es subconjunto de sí mismo. De este modo, por definición de la 
  colección \<open>C'\<close>, se verifica que el conjunto pertenece a \<open>C'\<close>.

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
  subconjunto de \<open>S'\<close>. Sea \<open>s\<close> un subconjunto cualquiera de \<open>S\<close>. Como \<open>S\<close> es subconjunto de \<open>S'\<close>,
  se tiene que \<open>s\<close> es, a su vez, subconjunto de \<open>S'\<close>. De este modo, existe un conjunto perteneciente
  a la colección \<open>C\<close> del cual \<open>s\<close> es subconjunto. Por tanto, por definición de \<open>C'\<close>, \<open>s\<close> pertenece
  a la colección \<open>C'\<close>, como quería demostrar.
\end{demostracion}

  Procedamos con las demostraciones del lema en Isabelle/HOL.

  En primer lugar, vamos a introducir dos lemas auxiliares que emplearemos a lo largo de
  esta sección. El primero se trata de un lema similar al lema \<open>ballI\<close> definido en Isabelle pero 
  considerando la relación de contención en lugar de la de pertenencia.\<close>

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

text \<open>Por último definimos el siguiente lema auxiliar similar al lema \<open>bspec\<close> de Isabelle/HOL
  considerando, análogamente, la relación de contención en lugar de la de pertenencia.\<close>

lemma 
  assumes "\<forall>x \<subseteq> A. P x"
          "x \<subseteq> A"
  shows "P x"
proof -
  show "P x"
    using assms(1) assms(2) by simp (*Pendiente*)
qed

lemma sspec: "\<forall>x \<subseteq> A. P x \<Longrightarrow> x \<subseteq> A \<Longrightarrow> P x"
  by simp

text \<open>Veamos la prueba detallada del lema en Isabelle/HOL. Esta se fundamenta en tres lemas
  auxiliares: el primero prueba que la colección \<open>C\<close> está contenida en \<open>C'\<close>, el segundo que
  \<open>C'\<close> tiene la propiedad de consistencia proposicional y, finalmente, el tercer lema demuestra que
  \<open>C'\<close> es cerrada bajo subconjuntos. En primer lugar, mostremos la demostración detallada de 
  la relación de contención de las colecciones.\<close>

lemma ex1_subset: "C \<subseteq> {s. \<exists>S\<in>C. s \<subseteq> S}"
proof (rule subsetI)
  fix s
  assume "s \<in> C"
  have "s \<subseteq> s"
    by (rule subset_refl)
  then have "\<exists>S\<in>C. s \<subseteq> S"
    using \<open>s \<in> C\<close> by (rule bexI)
  thus "s \<in> {s. \<exists>S\<in>C. s \<subseteq> S}" 
    by (simp only: mem_Collect_eq)
qed

text \<open>Prosigamos con la prueba del lema auxiliar que demuestra que \<open>C'\<close> tiene la propiedad
  de consistencia proposicional. Para ello, emplearemos un lema auxiliar que amplia el lema de 
  Isabelle \<open>insert_is_Un\<close> para la unión de dos elementos y un conjunto, como se muestra a 
  continuación.\<close>

lemma "insert a (insert b C) = {a,b} \<union> C"
  oops

text \<open>Emplearemos para demostrarlo, a su vez, el siguiente lema auxiliar que prueba una propiedad 
  trivial sobre conjuntos de dos elementos.\<close>

lemma elemSet: "{b} \<union> {a} = {a,b}"
proof -
  have C1:"{b} \<union> {a} \<subseteq> {a,b}" 
  proof -
    have "\<forall>x \<in> ({b} \<union> {a}). x \<in> {a,b}"
    proof (rule ballI)
      fix x
      assume "x \<in> {b} \<union> {a}"
      then have "x \<in> {b} \<or> x \<in> {a}"
        by (simp only: Un_iff)
      thus "x \<in> {a,b}"
      proof (rule disjE)
        assume "x \<in> {b}"
        then have "x = b" 
          by (simp only: singleton_iff) 
        then have "x \<in> {b}"
          by (simp only: singletonI)
        then have "x = a \<or> x \<in> {b}"
          by (simp only: disjI2)
        thus "x \<in> {a,b}"
          by (simp only: insert_iff)
      next
        assume "x \<in> {a}"
        then have "x = a"
          by (simp only: singleton_iff) 
        then have "x = a \<or> x \<in> {b}"
          by (simp only: disjI1)
        thus "x \<in> {a,b}"
          by (simp only: insert_iff)
      qed
    qed
    thus "{b} \<union> {a} \<subseteq> {a,b}"
      by (simp only: subset_eq)
  qed
  have C2:"{a,b} \<subseteq> {b} \<union> {a}"
  proof -
    have "\<forall>x \<in> {a,b}. x \<in> {b} \<union> {a}"
    proof (rule ballI)
      fix x
      assume "x \<in> {a,b}"
      then have "x = a \<or> x \<in> {b}"
        by (simp only: insert_iff)
      thus "x \<in> {b} \<union> {a}"
      proof (rule disjE)
        assume "x \<in> {b}"
        thus "x \<in> {b} \<union> {a}"
          by (simp only: UnI1)
      next
        assume "x = a"
        then have "x \<in> {a}"
          by (simp only: singletonI)
        thus "x \<in> {b} \<union> {a}"
          by (simp only: UnI2)
      qed
    qed
    thus "{a,b} \<subseteq> {b} \<union> {a}"
      by (simp only: subset_eq)
  qed
  show "{b} \<union> {a} = {a,b}"
    using C1 C2 by (simp only: set_eq_subset) 
qed

text \<open>De este modo, podemos demostrar el lema auxiliar \<open>insertSetElem\<close> de manera detallada como
  sigue.\<close>

lemma insertSetElem: "insert a (insert b C) = {a,b} \<union> C"
proof -
  have "insert a C = {a} \<union> C"
    by (rule insert_is_Un)
  have "{b} \<union> {a} = {a,b}"
    by (rule elemSet)
  have "insert a (insert b C) = insert b (insert a C)"
    by (rule insert_commute)
  also have "\<dots> = {b} \<union> (insert a C)"
    by (rule insert_is_Un)
  also have "\<dots> = {b} \<union> ({a} \<union> C)"
    by (simp only: \<open>insert a C = {a} \<union> C\<close>)
  also have "\<dots> = {b} \<union> {a} \<union> C"
    by (simp only: Un_assoc)
  also have "\<dots> = {a,b} \<union> C"
    by (simp only: \<open>{b} \<union> {a} = {a,b}\<close>) 
  finally show ?thesis
    by this
qed

text \<open>Una vez introducidos los lemas auxiliares anteriores, podemos dar la prueba detallada del
  lema que demuestra que \<open>C'\<close> tiene la propiedad de consistencia proposicional.\<close>

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
      have "\<forall>S \<in> C.
      \<bottom> \<notin> S
      \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
        using assms by (rule pcp_alt1)
      then have H:"\<bottom> \<notin> S'
      \<and> (\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False)
      \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C)
      \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C)"
        using \<open>S' \<in> C\<close> by (rule bspec)
      then have "\<bottom> \<notin> S'"
        by (rule conjunct1)
      have S1:"\<bottom> \<notin> S"
        using \<open>S \<subseteq> S'\<close> \<open>\<bottom> \<notin> S'\<close> by (rule contra_subsetD)
      have Atom:"\<forall>k. Atom k \<in> S' \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
        using H by (iprover elim: conjunct1 conjunct2)
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
              using Atom by (rule allE)
            then have "\<^bold>\<not> (Atom k) \<in> S' \<longrightarrow> False"
              using \<open>Atom k \<in> S'\<close> by (rule mp)
            thus "False"
              using \<open>\<^bold>\<not> (Atom k) \<in> S'\<close> by (rule mp)
          qed
        qed
      qed
      have Con:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
        using H by (iprover elim: conjunct1 conjunct2)
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
                  using Con by (iprover elim: allE)
                then have "F \<in> S' \<longrightarrow> {G,H} \<union> S' \<in> C"
                  using \<open>Con F G H\<close> by (rule mp)
                then have "{G,H} \<union> S' \<in> C"
                  using \<open>F \<in> S'\<close> by (rule mp)
                have "S \<subseteq> insert H S'"
                  using \<open>S \<subseteq> S'\<close> by (rule subset_insertI2) 
                then have "insert H S \<subseteq> insert H (insert H S')"
                  by (simp only: insert_mono)
                then have "insert H S \<subseteq> insert H S'"
                  by (simp only: insert_absorb2)
                then have "insert G (insert H S) \<subseteq> insert G (insert H S')"
                  by (simp only: insert_mono)
                have A:"insert G (insert H S) = {G,H} \<union> S"
                  by (rule insertSetElem) 
                have B:"insert G (insert H S') = {G,H} \<union> S'"
                  by (rule insertSetElem)
                have "{G,H} \<union> S \<subseteq> {G,H} \<union> S'" 
                  using \<open>insert G (insert H S) \<subseteq> insert G (insert H S')\<close> by (simp only: A B)
                then have "\<exists>S' \<in> C. {G,H} \<union> S \<subseteq> S'"
                  using \<open>{G,H} \<union> S' \<in> C\<close> by (rule bexI)
                thus "{G,H} \<union> S \<in> ?E" 
                  by (rule CollectI)
              qed
            qed
          qed
        qed
      qed
      have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
        using H by (iprover elim: conjunct2)
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
                  using Dis by (iprover elim: allE)
                then have "F \<in> S' \<longrightarrow> {G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
                  using \<open>Dis F G H\<close> by (rule mp)
                then have 9:"{G} \<union> S' \<in> C \<or> {H} \<union> S' \<in> C"
                  using \<open>F \<in> S'\<close> by (rule mp)
                show "{G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
                  using 9
                proof (rule disjE)
                  assume "{G} \<union> S' \<in> C"
                  have "insert G S \<subseteq> insert G S'"
                    using \<open>S \<subseteq> S'\<close> by (simp only: insert_mono)
                  have C:"insert G S = {G} \<union> S"
                    by (rule insert_is_Un)
                  have D:"insert G S' = {G} \<union> S'"
                    by (rule insert_is_Un)
                  have "{G} \<union> S \<subseteq> {G} \<union> S'"
                    using \<open>insert G S \<subseteq> insert G S'\<close> by (simp only: C D)
                  then have "\<exists>S' \<in> C. {G} \<union> S \<subseteq> S'"
                    using \<open>{G} \<union> S' \<in> C\<close> by (rule bexI)
                  then have "{G} \<union> S \<in> ?E"
                    by (rule CollectI)
                  thus "{G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
                    by (rule disjI1)
                next
                  assume "{H} \<union> S' \<in> C"
                  have "insert H S \<subseteq> insert H S'"
                    using \<open>S \<subseteq> S'\<close>by (simp only: insert_mono)
                  have E:"insert H S = {H} \<union> S"
                    by (rule insert_is_Un)
                  have F:"insert H S' = {H} \<union> S'"
                    by (rule insert_is_Un)
                  then have "{H} \<union> S \<subseteq> {H} \<union> S'"
                    using \<open>insert H S \<subseteq> insert H S'\<close> by (simp only: E F)
                  then have "\<exists>S' \<in> C. {H} \<union> S \<subseteq> S'"
                    using \<open>{H} \<union> S' \<in> C\<close> by (rule bexI)
                  then have "{H} \<union> S \<in> ?E"
                    by (rule CollectI)
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

text \<open>Finalmente, el siguiente lema auxiliar prueba que \<open>C'\<close> es cerrada bajo subconjuntos.\<close>

lemma ex1_subset_closed:
  assumes "pcp C"
  shows "subset_closed {s. \<exists>S\<in>C. s \<subseteq> S}"
  unfolding subset_closed_def
proof (rule ballI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  fix S
  assume "S \<in> ?E"
  then have H:"\<exists>S'\<in> C. S \<subseteq> S'"
    by (rule CollectD)
  obtain S' where \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close> 
    using H by (rule bexE) 
  show "\<forall>s \<subseteq> S. s \<in> ?E"
  proof (rule sallI)
    fix s
    assume "s \<subseteq> S" 
    then have "s \<subseteq> S'"
      using \<open>S \<subseteq> S'\<close> by (rule subset_trans)
    then have "\<exists>S' \<in> C. s \<subseteq> S'"
      using \<open>S' \<in> C\<close> by (rule bexI)
    thus "s \<in> ?E"
      by (rule CollectI)
  qed
qed

text \<open>En conclusión, la prueba detallada del lema completo se muestra a continuación.\<close>

lemma 
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

text \<open>Por último, su demostración automática es la siguiente.\<close>

lemma ex1: "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof(intro exI[of _ "{s . \<exists>S \<in> C. s \<subseteq> S}"] conjI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  show "C \<subseteq> ?E" by blast
  show "subset_closed ?E" unfolding subset_closed_def by blast
  assume C: \<open>pcp C\<close>
  show "pcp ?E" using C unfolding pcp_alt
    by (intro ballI conjI; simp; meson insertI1 rev_subsetD subset_insertI subset_insertI2)
qed

text \<open>\comentario{Voy redactando por aquí.}\<close>

text\<open> Lema: Si C tiene la propiedad de carácter finito, entonces C es 
cerrado bajo subconjunto.\<close>

lemma
  assumes "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix s S
  assume  \<open>S \<in> C\<close> and \<open>s \<subseteq> S\<close>
  have H:"\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C)"
    using assms unfolding finite_character_def by this
  then have 1:"S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C)"
    by (rule allE)
  have 2:"\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
    using \<open>S \<in> C\<close> 1 by (rule back_subst)
  have 3:"t \<subseteq> s \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t 
  proof -
    assume "t \<subseteq> s" and "finite t"
    then have "t \<subseteq> S"
      using \<open>s \<subseteq> S\<close> by (simp only: subset_trans)
    have "finite t \<longrightarrow> t \<in> C"
      using 2  \<open>t \<subseteq> S\<close> by (rule sspec)
    thus "t \<in> C"
      using \<open>finite t\<close> by (rule mp)
  qed
  have 4:"\<forall>t \<subseteq> s. finite t \<longrightarrow> t \<in> C"
  proof (rule sallI)
    fix t
    assume "t \<subseteq> s"
    show "finite t \<longrightarrow> t \<in> C"
    proof (rule impI)
      assume "finite t"
      show "t \<in> C"
        using \<open>t \<subseteq> s\<close> \<open>finite t\<close> by (simp only: 3)
    qed
  qed
  have "s \<in> C \<longleftrightarrow> (\<forall>t \<subseteq> s. finite t \<longrightarrow> t \<in> C)"
    using H by (rule allE)
  thus "s \<in> C"
    using 4 by (rule forw_subst)
qed

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
           using \<open>S \<in> C \<union> ?E\<close> by (simp only: Un_iff)
         thus "s \<in> C \<union> ?E"
         proof (rule disjE)
           assume "S \<in> C"
           have "\<forall>S \<in> C. \<forall>s \<subseteq> S. s \<in> C"
             using assms by (simp only: subset_closed_def)
           then have "\<forall>s \<subseteq> S. s \<in> C"
             using \<open>S \<in> C\<close> by (rule bspec)
           then have "s \<in> C"
             using \<open>s \<subseteq> S\<close> by (rule sspec)
           thus "s \<in> C \<union> ?E" 
             by (simp only: UnI1)
         next
           assume "S \<in> ?E"
           then have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
             by (rule CollectD)
           then have "finite s \<longrightarrow> s \<in> C"
             using \<open>s \<subseteq> S\<close> by (rule sspec)
           then have "s \<in> C"
             using \<open>finite s\<close> by (rule mp)
           thus "s \<in> C \<union> ?E"
             by (simp only: UnI1)
        qed
       qed
      qed
   next
     assume "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<union> ?E"
     then have F:"\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C \<or> s \<in> ?E"
       by (simp only: Un_iff)
     have "\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
     proof (rule sallI)
       fix s
       assume "s \<subseteq> S"
       show "finite s \<longrightarrow> s \<in> C"
       proof (rule impI)
         assume "finite s"
         have "finite s \<longrightarrow> s \<in> C \<or> s \<in> ?E"
           using F \<open>s \<subseteq> S\<close> by (rule sspec)
         then have "s \<in> C \<or> s \<in> ?E"
           using \<open>finite s\<close> by (rule mp)
         thus "s \<in> C"
         proof (rule disjE)
           assume "s \<in> C"
           thus "s \<in> C"
             by this
         next
           assume "s \<in> ?E"
           then have S':"\<forall>s' \<subseteq> s. finite s' \<longrightarrow> s' \<in> C"
             by (rule CollectD)
           have "s \<subseteq> s"
             by (simp only: subset_refl)
           have "finite s \<longrightarrow> s \<in> C"
             using S' \<open>s \<subseteq> s\<close> by (rule sspec)
           thus "s \<in> C"
             using \<open>finite s\<close> by (rule mp)
         qed
       qed
     qed
     then have "S \<in> ?E"
       by (rule CollectI)
     thus "S \<in> C \<union> ?E"
       by (simp only: UnI2)
   qed
 qed
qed

lemma ex3_pcp_CON:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}"
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
        have E:"\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
          using \<open>S \<in> ?E\<close> by (rule CollectD)
        then have "finite s \<longrightarrow> s \<in> C"
          using \<open>s \<subseteq> S\<close> by (rule sspec)
        then have "s \<in> C"
          using \<open>finite s\<close> by (rule mp)
        have "\<bottom> \<notin> s
              \<and> (\<forall>k. Atom k \<in> s \<longrightarrow> \<^bold>\<not> (Atom k) \<in> s \<longrightarrow> False)
              \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> s \<longrightarrow> {G,H} \<union> s \<in> C)
              \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> s \<longrightarrow> {G} \<union> s \<in> C \<or> {H} \<union> s \<in> C)"
          using 1 \<open>s \<in> C\<close> by (rule bspec)
        then have "\<forall>F G H. Con F G H \<longrightarrow> F \<in> s \<longrightarrow> {G, H} \<union> s \<in> C"
          by (iprover elim: conjunct2 conjunct1)
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
      have "s - {G,H} \<subseteq> S"
        using H by (simp only: Diff_subset_conv)
      have "F \<in> S \<and> (s - {G,H} \<subseteq> S)"
        using assms(5) \<open>s - {G,H} \<subseteq> S\<close> by (rule conjI)
      then have "insert F  (s - {G,H}) \<subseteq> S" 
        by (simp only: insert_subset)
      have F1:"finite (insert F  (s - {G,H})) \<longrightarrow> F \<in> (insert F  (s - {G,H})) \<longrightarrow> {G,H} \<union> (insert F  (s - {G,H})) \<in> C"
        using 2 \<open>insert F  (s - {G,H}) \<subseteq> S\<close> by (rule sspec)
      have "finite (s - {G,H})"
        using \<open>finite s\<close> by (rule finite_Diff)
      then have "finite (insert F (s - {G,H}))" 
        by (rule finite.insertI)
      have F2:"F \<in> (insert F  (s - {G,H})) \<longrightarrow> {G,H} \<union> (insert F  (s - {G,H})) \<in> C"
        using F1 \<open>finite (insert F (s - {G,H}))\<close> by (rule mp)
      have "F \<in> (insert F  (s - {G,H}))"
        by (simp only: insertI1)
      have F3:"{G,H} \<union> (insert F (s - {G,H})) \<in> C"
        using F2 \<open>F \<in> insert F (s - {G,H})\<close> by (rule mp)
      have IU1:"insert F (s - {G,H}) = {F} \<union> (s - {G,H})"
        by (rule insert_is_Un)
      have IU2:"insert F ({G,H} \<union> s) = {F} \<union> ({G,H} \<union> s)"
        by (rule insert_is_Un)
      have GH:"insert G (insert H s) = {G,H} \<union> s"
        by (rule insertSetElem)
      have "{G,H} \<union> (insert F (s - {G,H})) = {G,H} \<union> ({F} \<union> (s - {G,H}))"
        by (simp only: IU1)
      also have "\<dots> = {F} \<union> ({G,H} \<union> (s - {G,H}))"
        by (simp only: Un_left_commute)
      also have "\<dots> = {F} \<union> ({G,H} \<union> s)"
        by (simp only: Un_Diff_cancel)
      also have "\<dots> = insert F ({G,H} \<union> s)"
        by (simp only: IU2)
      also have "\<dots> = insert F (insert G (insert H s))"
        by (simp only: GH)
      finally have F4:"{G,H} \<union> (insert F (s - {G,H})) = insert F (insert G (insert H s))"
        by this
      have C1:"insert F (insert G (insert H s)) \<in> C"
        using F3 by (simp only: F4)
      have "s \<subseteq> insert F s"
        by (rule subset_insertI)
      then have C2:"s \<subseteq> insert F (insert G (insert H s))"
        by (simp only: subset_insertI2)
      have "\<forall>S \<in> C. \<forall>s \<subseteq> S. s \<in> C"
        using assms(2) by (simp only: subset_closed_def)
      thus "s \<in> C"
        using C1 C2 by blast (*Pendiente*)
    qed
  qed
  thus "{G,H} \<union> S \<in> C \<union> ?E"
    by (rule UnI2)
qed

lemma ex3_pcp_DIS:
  assumes "pcp C"
          "subset_closed C"
          "S \<in> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}"
          "Dis F G H"
          "F \<in> S"
  shows "{G} \<union> S \<in> (C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}) \<or> {H} \<union> S \<in> (C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C})"
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have PCP:"\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  have E:"\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
    using assms(3) by (rule CollectD)
  have SC:"\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C"
    using assms(2) by (simp only: subset_closed_def)
  have "{G} \<union> S \<in> (C \<union> ?E) \<or> {H} \<union> S \<in> (C \<union> ?E)"
  proof (cases)
    assume "S \<in> C"
    have "\<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
      using PCP \<open>S \<in> C\<close> by (rule bspec)
    then have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      by (iprover elim: conjunct2)
    then have "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      by (iprover elim: allE)
    then have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using assms(4) by (rule mp)
    then have "{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using assms(5) by (rule mp)
    thus "{G} \<union> S \<in> (C \<union> ?E) \<or> {H} \<union> S \<in> (C \<union> ?E)"
      by blast (*Pendiente*)
  next
    assume "S \<notin> C" 
  (*proof (cases)
    assume "finite S"
    have "S \<subseteq> S"
      by (rule subset_refl)
    have "finite S \<longrightarrow> S \<in> C"
      using E \<open>S \<subseteq> S\<close> by (rule sspec)
    then have "S \<in> C"
      using \<open>finite S\<close> by (rule mp)
    have "\<bottom> \<notin> S
          \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
          \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
          \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
      using PCP \<open>S \<in> C\<close> by (rule bspec)
    then have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      by (iprover elim: conjunct2)
    then have "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      by (iprover elim: allE)
    then have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using assms(4) by (rule mp)
    then have "{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using assms(5) by (rule mp)
    thus "{G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
      by blast
  next
    assume "\<not>(finite S)"
    have "{G} \<union> S \<in> ?E"
    proof (rule CollectD)
      have "\<forall>s \<subseteq> ({G} \<union> S). finite s \<longrightarrow> s \<in> C"
      proof (rule sallI)
        fix s
        assume "s \<subseteq> ({G} \<union> S)"
        show "finite s \<longrightarrow> s \<in> C"
        proof (rule impI)
          assume "finite s"
          obtain s1 s2 where "s1 \<subseteq> {G}" "s2 \<subseteq> S" "s = s1 \<union> s2"
            using \<open>s \<subseteq> ({G} \<union> S)\<close> by (rule subset_UnE)
          have "s \<in> C"
          proof -
            have "s1 = {} \<or> s1 = {G}"
              using \<open>s1 \<subseteq> {G}\<close> by blast (*Pendiente*)
            thus "s \<in> C"
            proof (rule disjE)
              assume "s1 = {}"
              then have "s = s2"
                using \<open>s = s1 \<union> s2\<close> by blast (*Pendiente*)
              then have "s \<subseteq> S"
                using \<open>s2 \<subseteq> S\<close> by blast (*Pendiente*)
              have "finite s \<longrightarrow> s \<in> C"
                using E \<open>s \<subseteq> S\<close> by (rule sspec)
              thus "s \<in> C"
                using \<open>finite s\<close> by (rule mp)
            next
              assume "s1 = {G}"
              have "finite s2"
                using \<open>finite s\<close> \<open>s = s1 \<union> s2\<close> by blast (*Pendiente*) (*s \<subseteq> ({G} \<union> S)*)
              have "finite s2 \<longrightarrow> s2 \<in> C"
                using E \<open>s2 \<subseteq> S\<close> by (rule sspec)
              then have "s2 \<in> C"
                using \<open>finite s2\<close> by (rule mp)
              have "\<bottom> \<notin> s2
                    \<and> (\<forall>k. Atom k \<in> s2 \<longrightarrow> \<^bold>\<not> (Atom k) \<in> s2 \<longrightarrow> False)
                    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> s2 \<longrightarrow> {G,H} \<union> s2 \<in> C)
                    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> s2 \<longrightarrow> {G} \<union> s2 \<in> C \<or> {H} \<union> s2 \<in> C)"
                using PCP \<open>s2 \<in> C\<close> by (rule bspec)
              then have "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> s2 \<longrightarrow> {G} \<union> s2 \<in> C \<or> {H} \<union> s2 \<in> C"
                by (iprover elim: conjunct2)
              then have "Dis F G H \<longrightarrow> F \<in> s2 \<longrightarrow> {G} \<union> s2 \<in> C \<or> {H} \<union> s2 \<in> C"
                by (iprover elim: allE)
              then have "F \<in> s2 \<longrightarrow> {G} \<union> s2 \<in> C \<or> {H} \<union> s2 \<in> C"
                using assms(4) by (rule mp)
              have "F \<in> s2" 
                oops*)

    have "{G} \<union> S \<in> ?E \<or> {H} \<union> S \<in> ?E"
      oops

    proof 
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
  unfolding pcp_alt
proof (rule ballI)
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have  1:"\<forall>S \<in> C.
    \<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
    using assms(1) by (rule pcp_alt1)
  fix S
  assume "S \<in> C \<union> ?E"
  then have "S \<in> C \<or> S \<in> ?E"
    by (simp only: Un_iff)
  thus "\<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E)"
  proof (rule disjE)
    assume "S \<in> C"
    have 2:"\<bottom> \<notin> S
    \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
    \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C)
    \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C)"
      using 1 \<open>S \<in> C\<close> by (rule bspec)
    then have A1:"\<bottom> \<notin> S"
      by (rule conjunct1)
    have A2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
      using 2 by (iprover elim: conjunct2 conjunct1)
    have A3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
      using 2 by (iprover elim: conjunct2 conjunct1)
    have S3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E"
    proof (rule allI)
      fix F
      show "\<forall>G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E"
      proof (rule allI)
        fix G
        show "\<forall>H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E"
        proof (rule allI)
          fix H
          show "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E"
          proof (rule impI)
            assume "Con F G H"
            show "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E"
            proof (rule impI)
              assume "F \<in> S"
              have "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
                using A3 by (iprover elim: allE)
              then have "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C"
                using \<open>Con F G H\<close> by (rule mp)
              then have "{G,H} \<union> S \<in> C"
                using \<open>F \<in> S\<close> by (rule mp)
              thus "{G,H} \<union> S \<in> C \<union> ?E"
                by blast (*Pendiente*)
            qed
          qed
        qed
      qed
    qed
    have A4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
      using 2 by (iprover elim: conjunct2)
    have S4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
    proof (rule allI)
      fix F 
      show "\<forall>G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
      proof (rule allI)
        fix G
        show "\<forall>H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
        proof (rule allI)
          fix H
          show "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
          proof (rule impI)
            assume "Dis F G H"
            show "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
            proof (rule impI)
              assume "F \<in> S" 
              have "Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
                using A4 by (iprover elim: allE)
              then have "F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
                using \<open>Dis F G H\<close> by (rule mp)
              then have "{G} \<union> S \<in> C \<or> {H} \<union> S \<in> C"
                using \<open>F \<in> S\<close> by (rule mp)
              thus "{G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
              proof (rule disjE)
                assume "{G} \<union> S \<in> C"
                then have "{G} \<union> S \<in> C \<union> ?E"
                  by blast (*Pendiente*)
                thus "{G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
                  by (rule disjI1)
              next
                assume "{H} \<union> S \<in> C"
                then have "{H} \<union> S \<in> C \<union> ?E"
                  by blast (*Pendiente*)
                thus "{G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E"
                  by (rule disjI2)
              qed
            qed
          qed
        qed
      qed
    qed
    show "\<bottom> \<notin> S \<and>
         (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False) \<and>
         (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G, H} \<union> S \<in> C \<union> ?E) \<and>
         (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> {G} \<union> S \<in> C \<union> ?E \<or> {H} \<union> S \<in> C \<union> ?E)"
      using A1 A2 A3 A4 by blast (*Pendiente*)
  next
    assume "S \<in> ?E"
    then have E:"\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C"
      by (rule CollectD)
    have "{} \<subseteq> S"
      by (rule empty_subsetI)
    have "finite {}"
      by (rule finite.emptyI)
    have "finite {} \<longrightarrow> {} \<in> C"
      using E \<open>{} \<subseteq> S\<close> by blast (*Pendiente*)
    then have "{} \<in> C"
      using \<open>finite {}\<close> by (rule mp)
    have 3:"\<bottom> \<notin> {}
  \<and> (\<forall>k. Atom k \<in> {} \<longrightarrow> \<^bold>\<not> (Atom k) \<in> {} \<longrightarrow> False)
  \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> {} \<longrightarrow> {G,H} \<union> {} \<in> C)
  \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> {} \<longrightarrow> {G} \<union> {} \<in> C \<or> {H} \<union> {} \<in> C)"
      using 1 \<open>{} \<in> C\<close> by auto (*Pendiente*)
    then have "\<bottom> \<notin> {}"
      by (rule conjunct1)
    have C1:"\<bottom> \<notin> S"
      using E assms(1) insert_absorb2 insert_is_Un pcp_alt1 by force (*Pendiente*)
    have B2:"\<forall>k. Atom k \<in> {} \<longrightarrow> \<^bold>\<not> (Atom k) \<in> {} \<longrightarrow> False"
      using 3 by (iprover elim: conjunct2 conjunct1)
    have C2:"\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False"
      sorry
    have C3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E"
    proof (rule allI)
      fix F
      show "\<forall>G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E"
      proof (rule allI)
        fix G
        show "\<forall>H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E"
        proof (rule allI)
          fix H
          show "Con F G H \<longrightarrow> F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E"
          proof (rule impI)
            assume "Con F G H"
            show "F \<in> S \<longrightarrow> {G,H} \<union> S \<in> C \<union> ?E"
            proof (rule impI)
              assume "F \<in> S"
              show "{G,H} \<union> S \<in> C \<union> ?E" 
                using \<open>pcp C\<close> \<open>subset_closed C\<close> \<open>S \<in> ?E\<close> \<open>Con F G H\<close> \<open>F \<in> S\<close> by (simp only: ex3_pcp_CON)
            qed
          qed
        qed
      qed
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

lemma
  assumes "pcp C"
          "subset_closed C"
  shows "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof -
  let ?E = "{S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  have C1:"C \<subseteq> C \<union> ?E"
    by (simp only: Un_upper1)
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

section \<open>Sucesiones de conjuntos en una colección\<close>

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
        else (pcp_seq C S n)) \<in> C" using [[simp_trace]]
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
    then have "pcp_seq C S n \<subseteq> (if (insert (from_nat m) (pcp_seq C S m) \<in> C) 
          then (insert (from_nat m) (pcp_seq C S m)) else (pcp_seq C S m))"
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

lemma imageUnElem: "f ` {x} = {f x}"
proof -
  have "f`{x} = f`(insert x {})" 
    by (simp only: insert_def)
  then have "f`{x} = insert (f x) (f`{})"
    by (simp only: image_insert)
  then have "f`{x} = insert (f x) {}"
    by (simp only: image_empty)
  thus "f`{x} = {f x}"
    by (simp only: insert_def)
qed

lemma pcp_seq_UN_detallada: "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof(induct m)
  have n0:"{n. n = 0} = {0}"
    by (simp only: singleton_conv)
  have "(pcp_seq C S)`{n. n = 0} = (pcp_seq C S)`{0}"
    by (simp only: n0)
  then have "(pcp_seq C S)`{n. n = 0} = {pcp_seq C S 0}"
    by (simp only: imageUnElem)
  then have 1:"{pcp_seq C S n | n. n = 0} = {pcp_seq C S 0}"
    by (simp only: image_Collect)
  have 0:"\<Union>{pcp_seq C S n|n. n = 0} = \<Union>{pcp_seq C S 0}" 
    by (simp only: 1)
  have "\<Union>{pcp_seq C S n|n. n \<le> 0} = \<Union>{pcp_seq C S n|n. n = 0}"
    by (simp only: canonically_ordered_monoid_add_class.le_zero_eq)
  also have "\<dots> = \<Union>{pcp_seq C S 0}"
    by (simp only: 0)
  also have "\<dots> = pcp_seq C S 0"
    by (simp only: conditionally_complete_lattice_class.cSup_singleton)
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
  have "{n. n \<le> Suc m}  = {n. (n \<le> m \<or> n = Suc m)}"
    by (simp only: le_Suc_eq)
  also have "\<dots> = {n. n \<le> m} \<union> {n. n = Suc m}"
    by (rule Collect_disj_eq) 
  also have "\<dots> = {n. n = Suc m} \<union> {n. n \<le> m}" 
    by (rule Un_commute)
  also have "\<dots> = {Suc m} \<union> {n. n \<le> m}"
    by (simp only: singleton_conv)
  finally have S:"{n. n \<le> Suc m} = {Suc m} \<union> {n. n \<le> m}"
    by this
  have "{pcp_seq C S n |n. n \<le> Suc m} = (pcp_seq C S) ` {n. n \<le> Suc m}" 
    by (simp only: image_Collect)
  also have "\<dots> = (pcp_seq C S) ` ({Suc m} \<union> {n. n \<le> m})"
    by (simp only: S)
  also have "\<dots> = (pcp_seq C S) ` {Suc m} \<union> (pcp_seq C S) ` {n. n \<le> m}"
    by (simp only: image_Un)
  also have "\<dots> = {pcp_seq C S (Suc m)} \<union> (pcp_seq C S) ` {n. n \<le> m}" 
    by (simp only: imageUnElem)
  also have "\<dots> = {pcp_seq C S (Suc m)} \<union> {pcp_seq C S n | n. n \<le> m}"
    by (simp only: image_Collect)
  finally have 3:"{pcp_seq C S n |n. n \<le> Suc m} = 
          {pcp_seq C S (Suc m)} \<union> {pcp_seq C S n |n. n \<le> m}"
    by this
  have "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = \<Union>({pcp_seq C S (Suc m)} \<union> {pcp_seq C S n |n. n \<le> m})"
    by (simp only: 3)
  also have "\<dots> = \<Union>({pcp_seq C S (Suc m)}) \<union> (\<Union>{pcp_seq C S n |n. n \<le> m})"
    by (simp only: complete_lattice_class.Sup_union_distrib)
  also have "\<dots> = (pcp_seq C S (Suc m)) \<union> \<Union>{pcp_seq C S n |n. n \<le> m}"
    by (simp only: conditionally_complete_lattice_class.cSup_singleton)
  also have "\<dots> = pcp_seq C S (Suc m) \<union> (pcp_seq C S m)"
    by (simp only: HI)
  also have "\<dots> = (pcp_seq C S m) \<union> (pcp_seq C S (Suc m))"
    by (simp only: Un_commute)
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
  have U:"(pcp_seq C S)`({n | n. True}) = {pcp_seq C S n | n. True}"
    by (simp only: image_Collect simp_thms(40))
  have 0:"{0} \<union> {n | n. True} = {n | n. True}"
    by (simp only: Collect_const if_True bounded_lattice_top_class.sup_top_right simp_thms(40))
  have "(pcp_seq C S)`({0} \<union> {n | n. True}) = (pcp_seq C S)`{n | n. True}" 
    by (simp only: 0) 
  then have "(pcp_seq C S)`{0} \<union> (pcp_seq C S)`{n | n. True} = (pcp_seq C S)`{n | n. True}"
    by (simp only: image_Un)
  then have 1:"(pcp_seq C S)`{0} \<subseteq> (pcp_seq C S)`{n | n. True}"
    by (simp only: subset_Un_eq)
  then have "{pcp_seq C S 0} \<subseteq> (pcp_seq C S)`{n | n. True}"
    by (simp only: imageUnElem) 
  then have "{pcp_seq C S 0} \<subseteq> {pcp_seq C S n | n. True}"
    by (simp only: U)
  then have 3:"\<Union>{pcp_seq C S 0} \<subseteq> \<Union>{pcp_seq C S n | n. True}"
    by (simp only: Union_mono)
  thus "pcp_seq C S 0 \<subseteq> \<Union>{pcp_seq C S n | n. True}" 
    using 3 by (simp only: conditionally_complete_lattice_class.cSup_singleton)
next
  fix n
  assume "pcp_seq C S n \<subseteq> \<Union>{pcp_seq C S n|n. True}"
  have U:"(pcp_seq C S)`({n | n. True}) = {pcp_seq C S n | n. True}"
    by (simp only: image_Collect simp_thms(40)) 
  have n:"{Suc n} \<union> {n | n. True} = {n | n. True}" 
    by (simp only: Collect_const if_True bounded_lattice_top_class.sup_top_right simp_thms(40))
  have "(pcp_seq C S)`({Suc n} \<union> {n | n. True}) = (pcp_seq C S)`{n | n. True}" 
    by (simp only: n) 
  then have "(pcp_seq C S)`{Suc n} \<union> (pcp_seq C S)`{n | n. True} = (pcp_seq C S)`{n | n. True}"
    by (simp only: image_Un)
  then have 1:"(pcp_seq C S)`{Suc n} \<subseteq> (pcp_seq C S)`{n | n. True}"
    by (simp only: subset_Un_eq)
  then have "{pcp_seq C S (Suc n)} \<subseteq> (pcp_seq C S)`{n | n. True}"
    by (simp only: imageUnElem) 
  then have "{pcp_seq C S (Suc n)} \<subseteq> {pcp_seq C S n | n. True}"
    by (simp only: U)
  then have 3:"\<Union>{pcp_seq C S (Suc n)} \<subseteq> \<Union>{pcp_seq C S n | n. True}"
    by (simp only: Union_mono)
  thus "pcp_seq C S (Suc n) \<subseteq> \<Union>{pcp_seq C S n | n. True}" 
    by (simp only: conditionally_complete_lattice_class.cSup_singleton)
qed

lemma pcp_seq_sub: "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def by(induction n; blast)

lemma pcp_lim_inserted_at_ex_detallada: 
  assumes "x \<in> pcp_lim C S"
  shows "\<exists>k. x \<in> pcp_seq C S k"
proof -
  have H:"x \<in> \<Union>{pcp_seq C S n|n. True}"
    using assms by (simp only: pcp_lim_def)
  have 1:"(pcp_seq C S) ` {n | n. True} = {pcp_seq C S n | n. True}"
    by (simp only: image_Collect simp_thms(40))
  have 2:"\<Union>((pcp_seq C S) ` {n | n. True}) = \<Union>{pcp_seq C S n | n. True}"
    by (simp only: 1)
  have "x \<in> \<Union>((pcp_seq C S) ` {n | n. True})"
    using H by (simp only: 2)
  then have "\<exists>k \<in> {n. True}. x \<in> pcp_seq C S k"
    by (simp only: UN_iff simp_thms(40))
  then have "\<exists>k \<in> UNIV. x \<in> pcp_seq C S k" 
    by (simp only: UNIV_def)
  thus "\<exists>k. x \<in> pcp_seq C S k" 
    by (simp only: bex_UNIV)
qed

lemma pcp_lim_inserted_at_ex: 
    "x \<in> pcp_lim C S \<Longrightarrow> \<exists>k. x \<in> pcp_seq C S k"
  unfolding pcp_lim_def by blast

section \<open>El teorema de existencia de modelo\<close>

lemma finite_pcp_lim_EX:
  assumes "finite s"
          "s \<subseteq> pcp_lim C S"
        shows "\<exists>k. s \<subseteq> pcp_seq C S k"
  using assms
proof (induction s rule: finite_induct)
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
  case (insert x s)
  then have "insert x s \<subseteq> pcp_lim C S"
    by (simp only: insert.prems)
  then have C:"x \<in> (pcp_lim C S) \<and> s \<subseteq> pcp_lim C S"
    by (simp only: insert_subset) 
  then have "s \<subseteq> pcp_lim C S"
    by (rule conjunct2)
  then have EX1:"\<exists>k. s \<subseteq> pcp_seq C S k"
    by (simp only: insert.IH)
  obtain k1 where "s \<subseteq> pcp_seq C S k1"
    using EX1 by (rule exE)
  have "x \<in> pcp_lim C S"
    using C by (rule conjunct1)
  then have EX2:"\<exists>k. x \<in> pcp_seq C S k"
    by (rule pcp_lim_inserted_at_ex)
  obtain k2 where "x \<in> pcp_seq C S k2" 
    using EX2 by (rule exE)
  have "k1 \<le> max k1 k2"
    by (simp only: linorder_class.max.cobounded1)
  then have "pcp_seq C S k1 \<subseteq> pcp_seq C S (max k1 k2)"
    by (rule pcp_seq_mono)
  have "k2 \<le> max k1 k2"
    by (simp only: linorder_class.max.cobounded2)
  then have "pcp_seq C S k2 \<subseteq> pcp_seq C S (max k1 k2)"
    by (rule pcp_seq_mono)
  have "s \<subseteq> pcp_seq C S (max k1 k2)"
    using \<open>s \<subseteq> pcp_seq C S k1\<close> \<open>pcp_seq C S k1 \<subseteq> pcp_seq C S (max k1 k2)\<close> by (rule subset_trans)
  have "x \<in> pcp_seq C S (max k1 k2)"
    using \<open>x \<in> pcp_seq C S k2\<close> \<open>pcp_seq C S k2 \<subseteq> pcp_seq C S (max k1 k2)\<close> by (rule rev_subsetD)
  then have 1:"insert x s \<subseteq> pcp_seq C S (max k1 k2)"
    using \<open>s \<subseteq> pcp_seq C S (max k1 k2)\<close> by (simp only: insert_subset)
  thus ?case
    by (rule exI)
qed
          
lemma pcp_lim_in_detallada:
  assumes "pcp C"
          "S \<in> C"
          "subset_closed C"
          "finite_character C"
  shows "pcp_lim C S \<in> C" 
proof -
  have "\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C)"
    using assms(4) unfolding finite_character_def by this
  then have FC1:"pcp_lim C S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> (pcp_lim C S). finite s \<longrightarrow> s \<in> C)"
    by (rule allE)
  have SC:"\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C"
    using assms(3) unfolding subset_closed_def by this
  have "\<forall>n. pcp_seq C S n \<in> C" 
  proof (rule allI)
    fix n
    show "pcp_seq C S n \<in> C" 
      using assms(1) assms(2) by (rule pcp_seq_in)
  qed
  then have "\<forall>m. \<Union>{pcp_seq C S n|n. n \<le> m} \<in> C" 
    unfolding pcp_seq_UN by this
  have FC2:"\<forall>s \<subseteq> pcp_lim C S. finite s \<longrightarrow> s \<in> C"
  proof (rule sallI)
    fix s :: "'a formula set"
    assume "s \<subseteq> pcp_lim C S"
    show "finite s \<longrightarrow> s \<in> C"
    proof (rule impI)
      assume "finite s"
      then have EX:"\<exists>k. s \<subseteq> pcp_seq C S k" 
        using \<open>s \<subseteq> pcp_lim C S\<close> by (rule finite_pcp_lim_EX)
      obtain n where "s \<subseteq> pcp_seq C S n"
        using EX by (rule exE)
      have "pcp_seq C S n \<in> C"
        using assms(1) assms(2) by (rule pcp_seq_in)
      have "\<forall>s \<subseteq> (pcp_seq C S n). s \<in> C"
        using SC \<open>pcp_seq C S n \<in> C\<close> by (rule bspec)
      thus "s \<in> C"
        using \<open>s \<subseteq> pcp_seq C S n\<close> by (rule sspec)
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

lemma cl_max_detallada:
  assumes "pcp C"
  assumes "subset_closed C"
  assumes "K \<in> C"
  assumes "pcp_lim C S \<subseteq> K"
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
  then have "F \<notin> pcp_seq C S (Suc (to_nat F))"
    using \<open>F \<notin> pcp_lim C S\<close> by (rule mt)
  then have 1: "insert F (pcp_seq C S (to_nat F)) \<notin> C" 
    by (simp add: Let_def split: if_splits) (*Pendiente*)
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
  then have 2:"insert F (pcp_seq C S (to_nat F)) \<in> C" 
    using \<open>insert F (pcp_seq C S (to_nat F)) \<subseteq> K\<close> by (rule sspec)
  show "False"
    using 1 2 by (rule notE)
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
  proof (rule allI)
    fix F
    show "\<forall>G H. Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
    proof (rule allI)
      fix G
      show "\<forall>H. Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
      proof (rule allI)
        fix H
        show "Con F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
        proof (rule impI)
          assume "Con F G H"
          show "F \<in> ?cl \<longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
          proof (rule impI)
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
      qed
    qed
  qed
  have Dis:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> {G} \<union> ?cl \<in> C \<or> {H} \<union> ?cl \<in> C"
    using d by (iprover elim: conjunct2 conjunct1)
  have H4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
  proof (rule allI)
    fix F
    show "\<forall>G H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
    proof (rule allI)
      fix G
      show "\<forall>H. Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
      proof (rule allI)
        fix H
        show "Dis F G H \<longrightarrow> F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
        proof (rule impI)
          assume "Dis F G H"
          show "F \<in> ?cl \<longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
          proof (rule impI)
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

theorem pcp_sat_detallada:
  fixes S :: "'a :: countable formula set"
  assumes "pcp C"
  assumes "S \<in> C"
  shows "sat S"
  unfolding sat_def
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
  have "\<forall>F \<in> S. \<A> \<Turnstile> F"
  proof (rule ballI)
    fix F
    assume "F \<in> S"
    have "F \<in> S \<longrightarrow> F \<in> pcp_lim Ce S"
      using \<open>S \<subseteq> pcp_lim Ce S\<close> by (rule in_mono)
    then have "F \<in> pcp_lim Ce S"
      using \<open>F \<in> S\<close> by (rule mp)
    show "\<A> \<Turnstile> F"
      using H3 \<open>F \<in> pcp_lim Ce S\<close> by (rule bspec)
  qed
  thus "\<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F"
    by (simp only: exI)
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
