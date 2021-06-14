(*<*) 
theory ColecScfc
  imports 
    Sintaxis
    Semantica
    Hintikka
    Notunif
    Pcp
begin
(*>*)

text \<open>En este apartado definiremos colecciones de conjuntos \<open>cerradas bajo subconjuntos\<close> y de 
  \<open>carácter finito\<close>, junto con tres resultados sobre las mismas. El primero de ellos permite
  extender una colección que verifique la propiedad de consistencia proposicional a otra que 
  también la verifique y sea cerrada bajo subconjuntos. Posteriormente probaremos que toda colección
  de carácter finito es cerrada bajo subconjuntos. Finalmente, mostraremos un resultado que 
  permite extender una colección cerrada bajo subconjuntos que verifique la propiedad de
  consistencia proposicional a otra que también verifique dicha propiedad y sea de carácter 
  finito.

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
  \node [root] {\<open>ex3\<close>\\ \<open>(Lema 3.0.5)\<close>}
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
  subconjuntos, \<open>S \<in> E\<close> y sea \<open>F\<close> una fórmula de tipo \<open>\<alpha>\<close> y componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, se tiene que\\ 
  \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> S \<in> C'\<close>. El segundo lema, formalizado como \<open>ex3_pcp_SinE_DIS\<close>, prueba que para \<open>C\<close> una 
  colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos, \<open>S \<in> E\<close> y 
  sea \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> y componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> S \<in> C'\<close> o 
  bien \<open>{\<beta>\<^sub>2} \<union> S \<in> C'\<close>. Por último, este segundo lema auxiliar se probará por reducción al absurdo, 
  precisando para ello de los siguientes resultados auxiliares:
  
  \begin{description}
    \item[\<open>Resultado \<one>\<close>] Formalizado como \<open>ex3_pcp_SinE_DIS_auxEx\<close>. Prueba que dada \<open>C\<close> una 
    colección con la propiedad de consistencia proposicional y cerrada bajo subconjuntos,\\ \<open>S \<in> E\<close> y 
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

  En primer lugar, vamos a probar el primer lema auxiliar para el caso en que\\ \<open>S \<in> C\<close>, formalizado
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
  \<open>S\<^sub>2\<close> subconjuntos finitos cualesquiera de \<open>S\<close> tales que \<open>F \<in> S\<^sub>1\<close> y\\ \<open>F \<in> S\<^sub>2\<close>, entonces existe una 
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

text \<open>Por último, podemos dar la prueba completa del lema \<open>3.0.5\<close> en Isabelle.\<close>

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

(*<*)
end
(*>*) 
