(*<*) 
theory Pcp
  imports 
    Sintaxis
    Semantica
    Hintikka
    Notunif
begin
(*>*)


text \<open>En este capítulo se define la \<open>propiedad de consistencia proposicional\<close> para una 
  colección de conjuntos de fórmulas proposicionales y se caracteriza la propiedad 
  de consistencia proposicional mediante la notación uniforme.

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

  Para probar este resultado de manera detallada en Isabelle vamos a demostrar cada una de las 
  implicaciones de la equivalencia por separado. La primera implicación del lema se basa en dos 
  lemas auxiliares. El primero de ellos deduce la condición de \<open>2)\<close> sobre fórmulas de tipo \<open>\<alpha>\<close> a 
  partir de las condiciones tercera, sexta, octava y novena de la definición de propiedad de 
  consistencia proposicional. Su demostración detallada en Isabelle se muestra a continuación.\<close>

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

(*<*)
end
(*>*) 
