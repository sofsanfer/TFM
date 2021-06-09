(*<*) 
theory TeoremaEx
  imports 
    Sintaxis
    Semantica
    Hintikka
    Notunif
    Pcp
    ColecScfc
begin
(*>*)

text \<open>\comentario{Añadir introducción.}\<close>

text \<open>\comentario{Cambiar referencias de los lemas tras el cambio de índice.}\<close>

section \<open>Sucesiones de conjuntos\<close>

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
  Sea \<open>C\<close> una colección de conjuntos de fórmulas proposicionales, \<open>S \<in> C\<close> y \<open>F\<^sub>1, F\<^sub>2, F\<^sub>3 \<dots>\<close> una 
  enumeración de las fórmulas proposicionales. Se define la \<open>sucesión de conjuntos de C a partir de 
  S\<close> como sigue:

  $S_{0} = S$

  $S_{n+1} = \left\{ \begin{array}{lcc} S_{n} \cup \{F_{n}\} &  si  & S_{n} \cup \{F_{n}\} \in C \\ \\ S_{n} & c.c \end{array} \right.$ 
\end{definicion}

  Para su formalización en Isabelle se ha introducido una instancia en la teoría de \<open>Sintaxis\<close> que 
  indica explícitamente que el conjunto de las fórmulas proposicionales es numerable, probado
  mediante el método \<open>countable_datatype\<close> de Isabelle.

  \<open>instance formula :: (countable) countable by countable_datatype\<close>

  De esta manera se genera en Isabelle una enumeración predeterminada de los elementos del conjunto,
  junto con herramientas para probar propiedades referentes a la numerabilidad. En particular, en la 
  formalización de la definición \<open>4.1.1\<close> se utilizará la función \<open>from_nat\<close> que, al aplicarla a un 
  número natural \<open>n\<close>, nos devuelve la \<open>n\<close>-ésima fórmula proposicional según una enumeración 
  predeterminada en Isabelle. 

  Puesto que la definición de las sucesiones en \<open>4.1.1\<close> se trata de una definición 
  recursiva sobre la estructura recursiva de los números naturales, se formalizará en Isabelle
  mediante el tipo de funciones primitivas recursivas de la siguiente manera.\<close>

primrec pcp_seq where
"pcp_seq C S 0 = S" |
"pcp_seq C S (Suc n) = (let Sn = pcp_seq C S n; Sn1 = insert (from_nat n) Sn in
                        if Sn1 \<in> C then Sn1 else Sn)" 

text\<open>Veamos el primer resultado sobre dichas sucesiones.

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos con la propiedad de consistencia proposicional,\\ \<open>S \<in> C\<close> y 
    \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close> construida según la definición \<open>4.1.1\<close>. 
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
    definición \<open>4.1.1\<close> es monótona.
  \end{lema}

  En Isabelle, se formaliza de la siguiente forma.\<close>

lemma "pcp_seq C S n \<subseteq> pcp_seq C S (Suc n)"
  oops

text \<open>Procedamos con la demostración del lema.

  \begin{demostracion}
    Sea una colección de conjuntos \<open>C\<close>, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de 
    \<open>S\<close> según la definición \<open>4.1.1\<close>. Para probar que \<open>{S\<^sub>n}\<close> es monótona, basta probar que \<open>S\<^sub>n \<subseteq> S\<^sub>n\<^sub>+\<^sub>1\<close> 
    para todo \<open>n \<in> \<nat>\<close>. En efecto, el resultado es inmediato al considerar dos casos para todo 
    \<open>n \<in> \<nat>\<close>: \<open>S\<^sub>n \<union> {F\<^sub>n} \<in> C\<close> o \<open>S\<^sub>n \<union> {F\<^sub>n} \<notin> C\<close>. Si suponemos que\\ \<open>S\<^sub>n \<union> {F\<^sub>n} \<in> C\<close>, por definición 
    tenemos que \<open>S\<^sub>n\<^sub>+\<^sub>1 = S\<^sub>n \<union> {F\<^sub>n}\<close>, luego es claro que\\ \<open>S\<^sub>n \<subseteq> S\<^sub>n\<^sub>+\<^sub>1\<close>. En caso contrario, si 
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
  \<open>S\<close> construida según la definición \<open>4.1.1\<close>. Entonces, para todos \<open>n\<close>, \<open>m \<in> \<nat>\<close> 
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
  \href{https://n9.cl/gtf5x}{Complete-Lattices.thy}, junto con distintas propiedades sobre la misma
  definidas en dicha teoría. El uso de teoría de retículos en este caso se debe a que, en Isabelle,
  los conjuntos se han formalizado como predicados según la teoría 
  \href{https://bit.ly/3ibCuje}{Set.thy}. De esta manera, un elemento pertenece a un conjunto si 
  verifica el predicado que lo caracteriza. Además, en dicha teoría se instancia que el tipo de los 
  conjuntos es un álgebra de \<open>Boole\<close> acotada, es decir, es un retículo distributivo para las 
  operaciones unión e intersección que tiene un supremo y un ínfimo. En consecuencia, la unión 
  generalizada de conjuntos se formaliza en Isabelle como el supremo del retículo completo que 
  conforman.

  Veamos la prueba detallada del resultado en Isabelle/HOL.\<close>

lemma "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof (induct m)
  have  "\<Union>{pcp_seq C S n|n. n \<le> 0} = \<Union>{pcp_seq C S n|n. n = 0}"
    by (simp only: le_zero_eq)
  also have "\<dots> = \<Union>((pcp_seq C S)`{n. n = 0})"
    by (simp only: image_Collect)
  also have "\<dots> = \<Union>{pcp_seq C S 0}"
    by (simp only: singleton_conv image_insert image_empty)
  also have "\<dots> = pcp_seq C S 0" 
    by  (simp only:cSup_singleton)
  finally show "\<Union>{pcp_seq C S n|n. n \<le> 0} = pcp_seq C S 0" 
    by this
next
  fix m
  assume HI:"\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
  have "m \<le> Suc m" 
    by (simp only: add_0_right)
  then have Mon:"pcp_seq C S m \<subseteq> pcp_seq C S (Suc m)"
    by (rule pcp_seq_mono)
  have "\<Union>{pcp_seq C S n | n. n \<le> Suc m} = \<Union>((pcp_seq C S)`({n. n \<le> Suc m}))"
    by (simp only: image_Collect)
  also have "\<dots> = \<Union>((pcp_seq C S)`({Suc m} \<union> {n. n \<le> m}))"
    by (simp only: le_Suc_eq Collect_disj_eq Un_commute singleton_conv)
  also have "\<dots> = \<Union>({pcp_seq C S (Suc m)} \<union> {pcp_seq C S n | n. n \<le> m})"
    by (simp only: image_Un image_insert image_empty image_Collect)
  also have "\<dots> = \<Union>{pcp_seq C S (Suc m)} \<union> \<Union>{pcp_seq C S n | n. n \<le> m}"
    by (simp only: Union_Un_distrib)
  also have "\<dots> = (pcp_seq C S (Suc m)) \<union> \<Union>{pcp_seq C S n | n. n \<le> m}"
    by (simp only: cSup_singleton)
  also have "\<dots> = (pcp_seq C S (Suc m)) \<union> (pcp_seq C S m)"
    by (simp only: HI)
  also have "\<dots> = pcp_seq C S (Suc m)"
    using Mon by (simp only: Un_absorb2)
  finally show "\<Union>{pcp_seq C S n|n. n \<le> (Suc m)} = pcp_seq C S (Suc m)"
    by this
qed

text \<open>Análogamente, podemos dar una prueba automática.\<close>

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

text \<open>Finalmente, definamos el límite de las sucesiones presentadas en la definición \<open>4.1.1\<close>.

 \begin{definicion}
  Sea \<open>C\<close> una colección, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la
  definición \<open>4.1.1\<close>. Se define el \<open>límite de la sucesión de conjuntos de C a partir de S\<close> como 
  $\bigcup_{n = 0}^{\infty} S_{n}$
 \end{definicion}

  La definición del límite se formaliza utilizando la unión generalizada de Isabelle como sigue.\<close>

definition "pcp_lim C S \<equiv> \<Union>{pcp_seq C S n|n. True}"

text \<open>Veamos el primer resultado sobre el límite.

\begin{lema}
  Sea \<open>C\<close> una colección de conjuntos, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de
  \<open>S\<close> según la definición \<open>4.1.1\<close>. Entonces, para todo \<open>n \<in> \<nat>\<close>, se verifica:

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

text \<open>Mostremos otro resultado. 

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos de fórmulas proposicionales, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de 
    conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la definición \<open>4.1.1\<close>. Si \<open>F\<close> es una fórmula tal que
    $F \in \bigcup_{n = 0}^{\infty} S_{n}$, entonces existe un \<open>k \<in> \<nat>\<close> tal que \<open>F \<in> S\<^sub>k\<close>. 
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
  las sucesiones definido en \<open>4.1.5\<close>.

\begin{lema}
  Sea \<open>C\<close> una colección, \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la
  definición \<open>4.1.1\<close>. Si \<open>S'\<close> es un conjunto finito tal que \<open>S' \<subseteq>\<close> $\bigcup_{n = 0}^{\infty} S_{n}$, 
  entonces existe un\\ \<open>k \<in> \<nat>\<close> tal que \<open>S' \<subseteq> S\<^sub>k\<close>.
\end{lema}

\begin{demostracion}
  La prueba del resultado se realiza por inducción sobre la estructura recursiva de los conjuntos 
  finitos.

  En primer lugar, probemos el caso base correspondiente al conjunto vacío. Supongamos que \<open>{}\<close> está 
  contenido en el límite de la sucesión de conjuntos de \<open>C\<close> a partir de \<open>S\<close>. Como \<open>{}\<close> es 
  subconjunto de todo conjunto, en particular lo es de \<open>S = S\<^sub>0\<close>, probando así el primer caso.

  Por otra parte, probemos el paso de inducción. Sea \<open>S'\<close> un conjunto finito verificando la 
  hipótesis de inducción: si \<open>S'\<close> está contenido en el límite de la sucesión de conjuntos de 
  \<open>C\<close> a partir de \<open>S\<close>, entonces también está contenido en algún \<open>S\<^sub>k\<^sub>'\<close> para cierto \<open>k' \<in> \<nat>\<close>. Sea 
  \<open>F\<close> una fórmula tal que \<open>F \<notin> S'\<close>. Vamos a probar que si \<open>{F} \<union> S'\<close> está contenido en el límite, 
  entonces está contenido en \<open>S\<^sub>k\<close> para algún \<open>k \<in> \<nat>\<close>. 

  Como hemos supuesto que \<open>{F} \<union> S'\<close> está contenido en el límite, entonces se verifica que \<open>F\<close>
  pertenece al límite y \<open>S'\<close> está contenido en él. Por el lema \<open>4.1.7\<close>, como \<open>F\<close> pertenece al 
  límite, deducimos que existe un \<open>k \<in> \<nat>\<close> tal que \<open>F \<in> S\<^sub>k\<close>. Por otro lado, como \<open>S'\<close> está contenido
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

section \<open>El Teorema de Existencia de Modelo\<close>

text \<open>En esta sección demostraremos finalmente el 
  \<open>teorema de existencia de modelo\<close>, el cual prueba que todo conjunto de fórmulas perteneciente a 
  una colección que verifique la propiedad de consistencia proposicional es satisfacible. Para ello, 
  considerando una colección \<open>C\<close> cualquiera y \<open>S \<in> C\<close>, empleando resultados anteriores extenderemos 
  la colección a una colección \<open>C''\<close> que tenga la propiedad de consistencia proposicional, sea
  cerrada bajo subconjuntos y sea de carácter finito. De este modo, en esta sección probaremos que el 
  límite de la sucesión formada a partir de una colección que tenga dichas condiciones y un conjunto
  cualquiera \<open>S\<close> como se indica en la definición \<open>1.4.1\<close> pertenece a la colección. Es más, 
  demostraremos que dicho límite se trata de un conjunto de \<open>Hintikka\<close> luego, por el \<open>teorema de 
  Hintikka\<close>, es satisfacible. Finalmente, como \<open>S\<close> está contenido en el límite, quedará demostrada 
  la satisfacibilidad del conjunto \<open>S\<close> al heredarla por contención.

  \comentario{Habrá que modificar el párrafo anterior al final.}\<close>

text \<open>En primer lugar, probemos que si \<open>C\<close> es una colección que verifica la propiedad de 
  consistencia proposicional, es cerrada bajo subconjuntos y es de carácter finito, entonces el 
  límite de toda sucesión de conjuntos de \<open>C\<close> según la definición \<open>4.1.1\<close> pertenece a \<open>C\<close>.

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional, es 
    cerrada bajo subconjuntos y es de carácter finito. Sea \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos
    de \<open>C\<close> a partir de \<open>S\<close> según la definición \<open>4.1.1\<close>. Entonces, el límite de la sucesión está en
    \<open>C\<close>.
  \end{lema}

  \begin{demostracion}
    Por definición, como \<open>C\<close> es de carácter finito, para todo conjunto son equivalentes:
    \begin{enumerate}
      \item El conjunto pertenece a \<open>C\<close>.
      \item Todo subconjunto finito suyo pertenece a \<open>C\<close>.
    \end{enumerate}

    De este modo, para demostrar que el límite de la sucesión \<open>{S\<^sub>n}\<close> pertenece a \<open>C\<close>, basta probar
    que todo subconjunto finito suyo está en \<open>C\<close>.

    Sea \<open>S'\<close> un subconjunto finito del límite de la sucesión. Por el lema \<open>1.4.8\<close>, existe un
    \<open>k \<in> \<nat>\<close> tal que \<open>S' \<subseteq> S\<^sub>k\<close>. Por tanto, como \<open>S\<^sub>k \<in> C\<close> para todo \<open>k \<in> \<nat>\<close> y \<open>C\<close> es cerrada bajo
    subconjuntos, por definición se tiene que \<open>S' \<in> C\<close>, como queríamos demostrar.
  \end{demostracion}

  En Isabelle se formaliza y demuestra detalladamente como sigue.\<close>

lemma
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
  have FC2:"\<forall>S' \<subseteq> pcp_lim C S. finite S' \<longrightarrow> S' \<in> C"
  proof (rule sallI)
    fix S' :: "'a formula set"
    assume "S' \<subseteq> pcp_lim C S"
    show "finite S' \<longrightarrow> S' \<in> C"
    proof (rule impI)
      assume "finite S'"
      then have EX:"\<exists>k. S' \<subseteq> pcp_seq C S k" 
        using \<open>S' \<subseteq> pcp_lim C S\<close> by (rule finite_pcp_lim_EX)
      obtain k where "S' \<subseteq> pcp_seq C S k"
        using EX by (rule exE)
      have "pcp_seq C S k \<in> C"
        using assms(1) assms(2) by (rule pcp_seq_in)
      have "\<forall>S' \<subseteq> (pcp_seq C S k). S' \<in> C"
        using SC \<open>pcp_seq C S k \<in> C\<close> by (rule bspec)
      thus "S' \<in> C"
        using \<open>S' \<subseteq> pcp_seq C S k\<close> by (rule sspec)
    qed
  qed
  show "pcp_lim C S \<in> C" 
    using FC1 FC2 by (rule forw_subst)
qed

text \<open>Por otra parte, podemos dar una prueba automática del resultado.\<close>

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

text \<open>Probemos que, además, el límite de las sucesión definida en \<open>4.1.1\<close> se trata de un elemento 
  maximal de la colección que lo define si esta verifica la propiedad de consistencia proposicional
  y es cerrada bajo subconjuntos.

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional y
    es cerrada bajo subconjuntos, \<open>S\<close> un conjunto y \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir 
    de \<open>S\<close> según la definición \<open>4.1.1\<close>. Entonces, el límite de la sucesión \<open>{S\<^sub>n}\<close> es un elemento 
    maximal de \<open>C\<close>.
  \end{lema}

  \begin{demostracion}
    Por definición de elemento maximal, basta probar que para cualquier conjunto \<open>K \<in> C\<close> que
    contenga al límite de la sucesión se tiene que \<open>K\<close> y el límite coinciden.

    La demostración se realizará por reducción al absurdo. Consideremos un conjunto \<open>K \<in> C\<close> que 
    contenga estrictamente al límite de la sucesión \<open>{S\<^sub>n}\<close>. De este modo, existe una fórmula \<open>F\<close> tal 
    que \<open>F \<in> K\<close> y \<open>F\<close> no está en el límite. Supongamos que \<open>F\<close> es la \<open>n\<close>-ésima fórmula según la 
    enumeración de la definición \<open>4.1.1\<close> utilizada para construir la sucesión. 

    Por un lado, hemos probado que todo elemento de la sucesión está contenido en el límite, luego 
    en particular obtenemos que \<open>S\<^sub>n\<^sub>+\<^sub>1\<close> está contenido en el límite. De este modo, como \<open>F\<close> no 
    pertenece al límite, es claro que \<open>F \<notin> S\<^sub>n\<^sub>+\<^sub>1\<close>. Además, \<open>{F} \<union> S\<^sub>n \<notin> C\<close> ya que, en caso contrario, 
    por la definición \<open>4.1.1\<close> de la sucesión obtendríamos que\\ \<open>S\<^sub>n\<^sub>+\<^sub>1 = {F} \<union> S\<^sub>n\<close>, lo que contradice 
    que \<open>F \<notin> S\<^sub>n\<^sub>+\<^sub>1\<close>. 

    Por otro lado, como \<open>S\<^sub>n\<close> también está contenida en el límite que, a su vez, está contenido en 
    \<open>K\<close>, se obtiene por transitividad que \<open>S\<^sub>n \<subseteq> K\<close>. Además, como \<open>F \<in> K\<close>, se verifica que 
    \<open>{F} \<union> S\<^sub>n \<subseteq> K\<close>. Como \<open>C\<close> es una colección cerrada bajo subconjuntos por hipótesis y \<open>K \<in> C\<close>, 
    por definición se tiene que \<open>{F} \<union> S\<^sub>n \<in> C\<close>, llegando así a una contradicción con lo demostrado 
    anteriormente.
  \end{demostracion}

  Su formalización y prueba detallada en Isabelle/HOL se muestran a continuación.\<close>

lemma
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
  proof (rule ccontr)
    assume "\<not>(insert F (pcp_seq C S (to_nat F)) \<notin> C)"
    then have "insert F (pcp_seq C S (to_nat F)) \<in> C"
      by (rule notnotD)
    then have C:"insert (from_nat (to_nat F)) (pcp_seq C S (to_nat F)) \<in> C"
      by (simp only: from_nat_to_nat)
    have "pcp_seq C S (Suc (to_nat F)) = (let Sn = pcp_seq C S (to_nat F); 
          Sn1 = insert (from_nat (to_nat F)) Sn in if Sn1 \<in> C then Sn1 else Sn)" 
      by (simp only: pcp_seq.simps(2))
    then have SucDef:"pcp_seq C S (Suc (to_nat F)) = (if insert (from_nat (to_nat F)) (pcp_seq C S (to_nat F)) \<in> C 
          then insert (from_nat (to_nat F)) (pcp_seq C S (to_nat F)) else pcp_seq C S (to_nat F))" 
      by (simp only: Let_def)
    then have "pcp_seq C S (Suc (to_nat F)) = insert (from_nat (to_nat F)) (pcp_seq C S (to_nat F))" 
      using C by (simp only: if_True)
    then have "pcp_seq C S (Suc (to_nat F)) = insert F (pcp_seq C S (to_nat F))"
      by (simp only: from_nat_to_nat)
    then have "F \<in> pcp_seq C S (Suc (to_nat F))"
      by (simp only: insertI1)
    show "False"
      using \<open>F \<notin> pcp_seq C S (Suc (to_nat F))\<close> \<open>F \<in> pcp_seq C S (Suc (to_nat F))\<close> by (rule notE)
  qed
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

text \<open>Análogamente a resultados anteriores, veamos su prueba automática.\<close>

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

text \<open>A continuación mostremos un resultado sobre el límite de la sucesión de \<open>4.1.1\<close> que es 
  consecuencia de que dicho límite sea un elemento maximal de la colección que lo define si esta
  verifica la propiedad de consistencia proposicional y es cerrada bajo subconjuntos.
  
  \begin{corolario}
    Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional y
    es cerrada bajo subconjuntos, \<open>S\<close> un conjunto, \<open>{S\<^sub>n}\<close> la sucesión de conjuntos de \<open>C\<close> a partir 
    de \<open>S\<close> según la definición \<open>4.1.1\<close> y \<open>F\<close> una fórmula proposicional. Entonces, si\\
    $\{F\} \cup \bigcup_{n = 0}^{\infty} S_{n} \in C$, se verifica que 
    $F \in \bigcup_{n = 0}^{\infty} S_{n}$. 
  \end{corolario}

  \begin{demostracion}
    Como \<open>C\<close> es una colección que verifica la propiedad de consistencia proposicional y es cerrada 
    bajo subconjuntos, se tiene que el límite $\bigcup_{n = 0}^{\infty} S_{n}$ es maximal en \<open>C\<close>. Por 
    lo tanto, si suponemos que $\{F\} \cup \bigcup_{n = 0}^{\infty} S_{n} \in C$, como el límite 
    está contenido en dicho conjunto, se cumple que 
    $\{F\} \cup \bigcup_{n = 0}^{\infty} S_{n} = \bigcup_{n = 0}^{\infty} S_{n}$, luego \<open>F\<close> 
    pertenece al límite, como queríamos demostrar.
  \end{demostracion}

  Veamos su formalización y prueba detallada en Isabelle/HOL.\<close>

lemma
  assumes "pcp C"
  assumes "subset_closed C"
  shows "insert F (pcp_lim C S) \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
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

text \<open>Mostremos su demostración automática.\<close>

lemma cl_max':
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  shows "insert F (pcp_lim C S) \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
  using cl_max[OF assms] by blast+

text \<open>El siguiente resultado prueba que el límite de la sucesión definida en \<open>4.1.1\<close> es un conjunto
  de Hintikka si la colección que lo define verifica la propiedad de consistencia proposicional, es
  es cerrada bajo subconjuntos y es de carácter finito. Como consecuencia del \<open>teorema de Hintikka\<close>,
  se trata en particular de un conjunto satisfacible. 

  \begin{lema}
    Sea \<open>C\<close> una colección de conjuntos que verifica la propiedad de consistencia proposicional, es
    es cerrada bajo subconjuntos y es de carácter finito. Sea \<open>S \<in> C\<close> y \<open>{S\<^sub>n}\<close> la sucesión de
    conjuntos de \<open>C\<close> a partir de \<open>S\<close> según la definición \<open>4.1.1\<close>. Entonces, el límite de la sucesión
    \<open>{S\<^sub>n}\<close> es un conjunto de Hintikka.
  \end{lema}

  \begin{demostracion}
    Para facilitar la lectura, vamos a notar por \<open>L\<^sub>S\<^sub>C\<close> al límite de la sucesión \<open>{S\<^sub>n}\<close> descrita 
    en el enunciado.

    Por resultados anteriores, como \<open>C\<close> verifica la propiedad de consistencia proposicional, es
    es cerrada bajo subconjuntos y es de carácter finito, se tiene que \<open>L\<^sub>S\<^sub>C \<in> C\<close>. En particular, por 
    verificar la propiedad de consistencia proposicional, por el lema de\\ caracterización de dicha
    propiedad mediante notación uniforme, se cumplen las siguientes condiciones para \<open>L\<^sub>S\<^sub>C\<close>:

    \begin{itemize}
      \item \<open>\<bottom> \<notin> L\<^sub>S\<^sub>C\<close>.
      \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> L\<^sub>S\<^sub>C\<close> y \<open>\<not> p \<in> L\<^sub>S\<^sub>C\<close>.
      \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
      pertenece a \<open>L\<^sub>S\<^sub>C\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> L\<^sub>S\<^sub>C\<close> pertenece a \<open>C\<close>.
      \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
      pertenece a \<open>L\<^sub>S\<^sub>C\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> L\<^sub>S\<^sub>C\<close> pertenece a \<open>C\<close> o 
      bien \<open>{\<beta>\<^sub>2} \<union> L\<^sub>S\<^sub>C\<close> pertenece a \<open>C\<close>.
    \end{itemize}

    Veamos que \<open>L\<^sub>S\<^sub>C\<close> es un conjunto de Hintikka probando que cumple las condiciones del
    lema de caracterización de los conjuntos de Hintikka mediante notación uniforme, es decir,
    probaremos que \<open>L\<^sub>S\<^sub>C\<close> verifica:

    \begin{itemize}
      \item \<open>\<bottom> \<notin> L\<^sub>S\<^sub>C\<close>.
      \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> L\<^sub>S\<^sub>C\<close> y \<open>\<not> p \<in> L\<^sub>S\<^sub>C\<close>.
      \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> se verifica 
      que si la fórmula pertenece a \<open>L\<^sub>S\<^sub>C\<close>, entonces \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> también.
      \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> se verifica 
      que si la fórmula pertenece a \<open>L\<^sub>S\<^sub>C\<close>, entonces o bien \<open>\<beta>\<^sub>1\<close> pertenece
      a \<open>L\<^sub>S\<^sub>C\<close> o bien \<open>\<beta>\<^sub>2\<close> pertenece a \<open>L\<^sub>S\<^sub>C\<close>.
    \end{itemize} 

    Observemos que las dos primeras condiciones coinciden con las obtenidas anteriormente para \<open>L\<^sub>S\<^sub>C\<close> 
    por el lema de caracterización de la propiedad de consistencia proposicional mediante notación
    uniforme. Veamos que, en efecto, se cumplen el resto de condiciones.

    En primer lugar, probemos que para una fórmula \<open>F\<close> de tipo \<open>\<alpha>\<close> y componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que 
    \<open>F \<in> L\<^sub>S\<^sub>C\<close> se verifica que tanto \<open>\<alpha>\<^sub>1\<close> como \<open>\<alpha>\<^sub>2\<close> pertenecen a \<open>L\<^sub>S\<^sub>C\<close>. Por la tercera condición 
    obtenida anteriormente para \<open>L\<^sub>S\<^sub>C\<close> por el lema de caracterización de la propiedad de consistencia 
    proposicional mediante notación uniforme, se cumple que\\ \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> L\<^sub>S\<^sub>C \<in> C\<close>. Observemos que
    se verifica \<open>L\<^sub>S\<^sub>C \<subseteq> {\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> L\<^sub>S\<^sub>C\<close>. De este modo, como \<open>C\<close> es una colección con la propiedad de 
    consistencia proposicional y cerrada bajo subconjuntos, por el lema \<open>4.2.2\<close> se tiene que 
    los conjuntos \<open>L\<^sub>S\<^sub>C\<close> y \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> L\<^sub>S\<^sub>C\<close> coinciden. Por tanto, es claro que \<open>\<alpha>\<^sub>1 \<in> L\<^sub>S\<^sub>C\<close> y \<open>\<alpha>\<^sub>2 \<in> L\<^sub>S\<^sub>C\<close>, 
    como queríamos demostrar.

    Por último, demostremos que para una fórmula \<open>F\<close> de tipo \<open>\<beta>\<close> y componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que
    \<open>F \<in> L\<^sub>S\<^sub>C\<close> se verifica que o bien \<open>\<beta>\<^sub>1 \<in> L\<^sub>S\<^sub>C\<close> o bien \<open>\<beta>\<^sub>2 \<in> L\<^sub>S\<^sub>C\<close>. Por la cuarta condición obtenida 
    anteriormente para \<open>L\<^sub>S\<^sub>C\<close> por el lema de caracterización de la propiedad de consistencia 
    proposicional mediante notación uniforme, se cumple que o bien\\ \<open>{\<beta>\<^sub>1} \<union> L\<^sub>S\<^sub>C \<in> C\<close> o bien 
    \<open>{\<beta>\<^sub>2} \<union> L\<^sub>S\<^sub>C \<in> C\<close>. De este modo, si suponemos que \<open>{\<beta>\<^sub>1} \<union> L\<^sub>S\<^sub>C \<in> C\<close>, como \<open>C\<close> tiene la propiedad de 
    consistencia proposicional y es cerrada bajo subconjuntos, por el corolario \<open>4.2.3\<close> se tiene 
    que \<open>\<beta>\<^sub>1 \<in> L\<^sub>S\<^sub>C\<close>. Por tanto, se cumple que o bien \<open>\<beta>\<^sub>1 \<in> L\<^sub>S\<^sub>C\<close> o bien \<open>\<beta>\<^sub>2 \<in> L\<^sub>S\<^sub>C\<close>. Si suponemos que 
    \<open>{\<beta>\<^sub>2} \<union> L\<^sub>S\<^sub>C \<in> C\<close>, se observa fácilmente que llegamos a la misma conclusión de manera análoga. 
    Por lo tanto, queda probado el resultado.
  \end{demostracion}

  Veamos su formalización y prueba detallada en Isabelle.\<close>

lemma
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
      have "?cl \<subseteq> insert H ?cl"
        by (rule subset_insertI)
      then have "?cl \<subseteq> insert G (insert H ?cl)"
        by (rule subset_insertI2)
      have "?cl = insert G (insert H ?cl)" 
        using assms(1) assms(2) \<open>insert G (insert H ?cl) \<in> C\<close> \<open>?cl \<subseteq> insert G (insert H ?cl)\<close> by (rule cl_max)
      then have "insert G (insert H ?cl) \<subseteq> ?cl"
        by (simp only: equalityD2)
      then have "G \<in> ?cl \<and> insert H ?cl \<subseteq> ?cl"
        by (simp only: insert_subset)
      then have "G \<in> ?cl"
        by (rule conjunct1)
      have "insert H ?cl \<subseteq> ?cl"
        using \<open>G \<in> ?cl \<and> insert H ?cl \<subseteq> ?cl\<close> by (rule conjunct2)
      then have "H \<in> ?cl \<and> ?cl \<subseteq> ?cl"
        by (simp only: insert_subset)
      then have "H \<in> ?cl"
        by (rule conjunct1)
      show "G \<in> ?cl \<and> H \<in> ?cl"
        using \<open>G \<in> ?cl\<close> \<open>H \<in> ?cl\<close> by (rule conjI)
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

text \<open>Del mismo modo, podemos probar el resultado de manera automática como sigue.\<close>

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
  with d(1,2) show "Hintikka ?cl" unfolding Hintikka_alt 
    using c cl_max cl_max' d(4) sc by blast
qed

text \<open>Finalmente, vamos a demostrar el \<open>teorema de existencia de modelo\<close>. Para ello precisaremos de
  un resultado que indica que la satisfacibilidad de conjuntos de fórmulas se hereda por la 
  contención.

  \begin{lema}
    Todo subconjunto de un conjunto de fórmulas satisfacible es satisfacible.
  \end{lema}

  \begin{demostracion}
    Sea \<open>B\<close> un conjunto de fórmulas satisfacible y \<open>A \<subseteq> B\<close>. Veamos que \<open>A\<close> es satisfacible.
    Por definición, como \<open>B\<close> es satisfacible, existe una interpretación \<open>\<A>\<close> que es modelo de cada 
    fórmula de \<open>B\<close>. Como \<open>A \<subseteq> B\<close>, en particular \<open>\<A>\<close> es modelo de toda fórmula de \<open>A\<close>. Por tanto, 
    \<open>A\<close> es satisfacible, ya que existe una interpretación que es modelo de todas sus fórmulas.
  \end{demostracion}

  Su prueba detallada en Isabelle/HOL es la siguiente.\<close>

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

text\<open>De este modo, procedamos finalmente con la demostración del teorema.

  \begin{teorema}[Teorema de Existencia de Modelo]
    Todo conjunto de fórmulas perteneciente a una colección que verifique la propiedad de
    consistencia proposicional es satisfacible. 
  \end{teorema}

  \begin{demostracion}
    Sea \<open>C\<close> una colección de conjuntos de fórmulas proposicionales que verifique la propiedad de 
    consistencia proposicional y \<open>S \<in> C\<close>. Vamos a probar que \<open>S\<close> es satisfacible.

    En primer lugar, como \<open>C\<close> verifica la propiedad de consistencia proposicional, por el lema 
    \<open>3.0.3\<close> podemos extenderla a una colección \<open>C'\<close> que también verifique la propiedad y
    sea cerrada bajo subconjuntos. A su vez, por el lema \<open>3.0.5\<close>, como la extensión 
    \<open>C'\<close> es una colección con la propiedad de consistencia proposicional y cerrada bajo 
    subconjuntos, podemos extenderla a otra colección \<open>C''\<close> que también verifica la propiedad de
    consistencia proposicional y sea de carácter finito. De este modo, por la transitividad de la 
    contención, es claro que \<open>C''\<close> es una extensión de \<open>C\<close>, luego \<open>S \<in> C''\<close> por hipótesis. 
    Por otro lado, por el lema \<open>3.0.4\<close>, como \<open>C''\<close> es de carácter finito, se tiene que es 
    cerrada bajo subconjuntos. 

    En suma, \<open>C''\<close> es una extensión de \<open>C\<close> que verifica la propiedad de consistencia proposicional, 
    es cerrada bajo subconjuntos y es de carácter finito. Luego, por el lema \<open>4.2.4\<close>, el límite de 
    la sucesión \<open>{S\<^sub>n}\<close> de conjuntos de \<open>C''\<close> a partir de \<open>S\<close> según la definición \<open>4.1.1\<close> es un 
    conjunto de Hintikka. Por tanto, por el \<open>teorema de Hintikka\<close>, se trata de un conjunto 
    satisfacible. 

    Finalmente, puesto que para todo \<open>n \<in> \<nat>\<close> se tiene que \<open>S\<^sub>n\<close> está contenido en el límite, en 
    particular el conjunto \<open>S\<^sub>0\<close> está contenido en él. Por definición de la sucesión, dicho conjunto 
    coincide con \<open>S\<close>. Por tanto, como \<open>S\<close> está contenido en el límite que es un conjunto 
    satisfacible, queda demostrada la satisfacibilidad de \<open>S\<close>.
  \end{demostracion}

  \comentario{Tal vez sería buena idea hacer un grafo similar al de ex3.}

  Mostremos su formalización y demostración detallada en Isabelle.\<close>

theorem
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
  have "pcp_seq Ce S 0 = S"
    by (simp only: pcp_seq.simps(1))
  have "pcp_seq Ce S 0 \<subseteq> pcp_lim Ce S"
    by (rule pcp_seq_sub)
  then have "S \<subseteq> pcp_lim Ce S"
    by (simp only: \<open>pcp_seq Ce S 0 = S\<close>)
  thus "sat S"
    using \<open>sat (pcp_lim Ce S)\<close> by (rule sat_mono)
qed

text \<open>Finalmente, demostremos el teorema de manera automática.\<close>

theorem pcp_sat:
  fixes S :: "'a :: countable formula set"
  assumes c: "pcp C"
  assumes el: "S \<in> C"
  shows "sat S"
proof -
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

section \<open>Teorema de Compacidad\<close>

text \<open>En esta sección vamos demostrar el \<open>Teorema de Compacidad\<close> para la lógica proposicional
  como consecuencia del \<open>Teorema de Existencia de Modelo\<close>.

  \begin{teorema}[Teorema de Compacidad]
    Todo conjunto de fórmulas finitamente satisfacible es satisfacible.
  \end{teorema}

  Para su demostración consideraremos la colección formada por los conjuntos de fórmulas finitamente 
  satisfacibles. Probaremos que dicha colección verifica la propiedad de consistencia proposicional
  y, por el \<open>Teorema de Existencia de Modelo\<close>, todo conjunto perteneciente a ella será
  satisfacible, demostrando así el teorema.

  Mostremos previamente dos resultados sobre subconjuntos finitos que emplearemos en la 
  demostración del teorema.

  \begin{lema}
    Sea un conjunto de la forma \<open>{a} \<union> B\<close> y \<open>S\<close> un subconjunto finito suyo. Entonces,
    existe un subconjunto finito \<open>S'\<close> de \<open>B\<close> tal que o bien \<open>S = {a} \<union> S'\<close> o bien \<open>S = S'\<close>.
  \end{lema}

  \begin{demostracion}
    La prueba del resultado se realiza por inducción en la estructura recursiva de los conjuntos 
    finitos.

    En primer lugar, probemos el caso base correspondiente al conjunto vacío. Si consideramos 
    \<open>S = {}\<close>, tomando también \<open>S' = {}\<close> es claro que verifica que es subconjunto finito de \<open>B\<close>
    y o bien \<open>S = {a} \<union> S'\<close> o bien \<open>S = S'\<close>.

    Veamos el caso de inducción. Sea \<open>S\<close> un conjunto finito verificando la hipótesis de inducción:
    
    \<open>(HI): Si S \<subseteq> {a} \<union> B, entonces existe un subconjunto finito S' de B tal que o bien\<close>

    \hspace{1cm}\<open>S = {a} \<union> S' o bien S = S'.\<close>

    Sea un elemento cualquiera \<open>x \<notin> S\<close>. Vamos a probar que se verifica el resultado para el conjunto
    \<open>{x} \<union> S\<close>. Es decir, si \<open>{x} \<union> S \<subseteq> {a} \<union> B\<close>, vamos a encontrar un subconjunto finito \<open>S''\<close> de 
    \<open>B\<close> tal que o bien \<open>{x} \<union> S = {a} \<union> S''\<close> o bien \<open>{x} \<union> S = S''\<close>.

    Supongamos, pues, que \<open>{x} \<union> S \<subseteq> {a} \<union> B\<close>. En este caso, es claro que se verifica que
    \<open>x \<in> {a} \<union> B\<close> y \<open>S \<subseteq> {a} \<union> B\<close>. Por lo último, aplicando hipótesis de inducción, podemos hallar 
    un subconjunto finito \<open>S'\<close> de \<open>B\<close> tal que o bien \<open>S = {a} \<union> S'\<close> o bien \<open>S = S'\<close>. Por otro lado,
    como \<open>x \<in> {a} \<union> B\<close>, deducimos que o bien \<open>x = a\<close> o bien \<open>x \<in> B\<close>. En efecto, probemos que se 
    verifica el resultado para ambos casos de la última disyunción.

    En primer lugar, supongamos que \<open>x = a\<close>. En este caso, veremos que el conjunto \<open>S''\<close> que 
    verifica el resultado es el propio \<open>S'\<close>. Se observa fácilmente ya que, si \<open>S = {a} \<union> S'\<close>, como 
    \<open>x = a\<close> se obtiene que \<open>{x} \<union> S = {a} \<union> S'\<close>, de modo que \<open>S'' = S'\<close> es un subconjunto finito de 
    \<open>B\<close> tal que o bien \<open>{x} \<union> S = {a} \<union> S''\<close> o bien \<open>{x} \<union> S = S''\<close>. Por otro lado, suponiendo que 
    \<open>S = S'\<close>, se deduce análogamente que \<open>{x} \<union> S = {a} \<union> S'\<close> pues se tiene que \<open>x = a\<close>, llegando
    a la misma conclusión.

    Por otra parte, supongamos que \<open>x \<in> B\<close>. En este caso, el conjunto \<open>S''\<close> que verifica el
    resultado es el conjunto \<open>{x} \<union> S'\<close>. Observemos que se trata de un subconjunto finito de \<open>B\<close> ya 
    que \<open>S'\<close> es un subconjunto finito de \<open>B\<close> y \<open>x \<in> B\<close>. Además, en efecto si \<open>S = {a} \<union> S'\<close>, se 
    deduce que \<open>{x} \<union> S = {x,a} \<union> S' = {a} \<union> S''\<close>, luego cumple que o bien\\ \<open>{x} \<union> S = {a} \<union> S''\<close> o 
    bien \<open>{x} \<union> S = S''\<close>. Por otro lado, en el caso en que \<open>S = S'\<close>, es claro que \<open>{x} \<union> S = S''\<close> 
    por la elección de \<open>S''\<close>, llegando la misma conclusión.
  \end{demostracion}

  Procedamos con la prueba detallada y formalización en Isabelle. Para ello, hemos utilizado el
  siguiente lema auxiliar.\<close>

lemma subexI [intro]: "P A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> \<exists>A\<subseteq>B. P A"
  by blast

text \<open>De este modo, probemos detalladamente el resultado.\<close>

lemma finite_subset_insert1:
  "\<lbrakk>finite S; S \<subseteq> {a} \<union> B \<rbrakk> \<Longrightarrow>
     \<exists>S' \<subseteq> B. finite S' \<and> (S = {a} \<union> S' \<or> S = S')"
proof (induct rule: finite_induct)
  case empty
  have "{} \<subseteq> B"
    by (rule empty_subsetI)
  have 1:"finite {}"
    by (simp only: finite.emptyI)
  have "{} = {}"
    by (simp only: simp_thms(6))
  then have 2:"{} = {a} \<union> {} \<or> {} = {}"
    by (rule disjI2)
  have "finite {} \<and> ({} = {a} \<union> {} \<or> {} = {})"
    using 1 2 by (rule conjI)
  thus "\<exists>S' \<subseteq> B. finite S' \<and> ({} = {a} \<union> S' \<or> {} = S')"
    using \<open>{} \<subseteq> B\<close> by (rule subexI)
next
  case (insert x S)
  assume "finite S"
  assume "x \<notin> S"
  assume HI:"S \<subseteq> {a} \<union> B \<Longrightarrow> \<exists>S'\<subseteq>B. finite S' \<and> (S = {a} \<union> S' \<or> S = S')"
  show "insert x S \<subseteq> {a} \<union> B \<Longrightarrow> \<exists>S''\<subseteq>B. finite S'' \<and> (insert x S = {a} \<union> S'' \<or> insert x S = S'')"
  proof -
    assume "insert x S \<subseteq> {a} \<union> B" 
    then have C:"x \<in> {a} \<union> B \<and> S \<subseteq> {a} \<union> B"
      by (simp only: insert_subset)
    then have "S \<subseteq> {a} \<union> B"
      by (rule conjunct2)
    have Ex1:"\<exists>S'\<subseteq>B. finite S' \<and> (S = {a} \<union> S' \<or> S = S')"
      using \<open>S \<subseteq> {a} \<union> B\<close> by (rule HI)
    obtain S' where "S' \<subseteq> B" and C1:"finite S' \<and> (S = {a} \<union> S' \<or> S = S')"
      using Ex1 by (rule subexE)
    have "finite S'"
      using C1 by (rule conjunct1)
    then have "finite (insert x S')"
      by (simp only: finite.insertI)
    have "x \<in> {a} \<union> B"
      using C by (rule conjunct1)
    then have "x \<in> {a} \<or> x \<in> B"
      by (simp only: Un_iff)
    then have "x = a \<or> x \<in> B"
      by (simp only: singleton_iff)
    thus "\<exists>S''\<subseteq>B. finite S'' \<and> (insert x S = {a} \<union> S'' \<or> insert x S = S'')"
    proof (rule disjE)
      assume "x = a"
      have "S = {a} \<union> S' \<or> S = S'"
        using C1 by (rule conjunct2)
      thus ?thesis
      proof (rule disjE)
        assume "S = {a} \<union> S'"
        have "x \<in> {a}"
          using \<open>x = a\<close> by (simp only: singleton_iff)
        then have "x \<in> {a} \<union> S'" 
          by (simp only: UnI1)
        then have "insert x ({a} \<union> S') = {a} \<union> S'"
          by (rule insert_absorb)
        have "insert x S = insert x ({a} \<union> S')"
          by (simp only: \<open>S = {a} \<union> S'\<close>)
        then have "insert x S = {a} \<union> S'"
          by (simp only: \<open>insert x ({a} \<union> S') = {a} \<union> S'\<close>)
        then have 1:"insert x S = {a} \<union> S' \<or> insert x S = S'"
          by (rule disjI1)
        have "finite S' \<and> (insert x S = {a} \<union> S' \<or> insert x S = S')"
          using \<open>finite S'\<close> 1 by (rule conjI)
        thus ?thesis
          using \<open>S' \<subseteq> B\<close> by (rule subexI)
      next
        assume "S = S'"
        have "insert x S = {x} \<union> S"
          by (rule insert_is_Un)
        then have "insert x S = {a} \<union> S'"
          by (simp only: \<open>x = a\<close> \<open>S = S'\<close>)
        then have 1:"insert x S = {a} \<union> S' \<or> insert x S = S'"
          by (rule disjI1)
        have "finite S' \<and> (insert x S = {a} \<union> S' \<or> insert x S = S')"
          using \<open>finite S'\<close> 1 by (rule conjI)
        thus ?thesis
          using \<open>S' \<subseteq> B\<close> by (rule subexI)
      qed
    next
      assume "x \<in> B"
      have "x \<in> B \<and> S' \<subseteq> B"
        using \<open>x \<in> B\<close> \<open>S' \<subseteq> B\<close> by (rule conjI)
      then have "insert x S' \<subseteq> B"
        by (simp only: insert_subset)
      have "finite (insert x S')"
        using \<open>finite S'\<close> by (simp only: finite.insertI)
      have "S = {a} \<union> S' \<or> S = S'"
        using C1 by (rule conjunct2)
      thus ?thesis
      proof (rule disjE)
        assume "S = {a} \<union> S'"
        have "insert x S = insert x ({a} \<union> S')"
          by (simp only: \<open>S = {a} \<union> S'\<close>)
        then have "insert x S = {a} \<union> (insert x S')"
          by blast
        then have 1:"insert x S = {a} \<union> (insert x S') \<or> insert x S = insert x S'"
          by (rule disjI1)
        have "finite (insert x S') \<and> (insert x S = {a} \<union> (insert x S') \<or> insert x S = insert x S')"
          using \<open>finite (insert x S')\<close> 1 by (rule conjI)
        thus ?thesis
          using \<open>insert x S' \<subseteq> B\<close> by (rule subexI)
      next
        assume "S = S'"
        have "insert x S = insert x S'"
          by (simp only: \<open>S = S'\<close>)
        then have 1:"insert x S = {a} \<union> (insert x S') \<or> insert x S = insert x S'"
          by (rule disjI2)
        have "finite (insert x S') \<and> (insert x S = {a} \<union> (insert x S') \<or> insert x S = insert x S')"
          using \<open>finite (insert x S')\<close> 1 by (rule conjI)
        thus ?thesis
          using \<open>insert x S' \<subseteq> B\<close> by (rule subexI)
      qed
    qed
  qed
qed

text \<open>El segundo resultado sobre subconjuntos finitos es consecuencia del anterior.

\begin{lema}
  Sea un conjunto de la forma \<open>{a,b} \<union> B\<close> y \<open>S\<close> un subconjunto finito suyo. Entonces, existe un
  subconjunto finito \<open>S'\<close> de \<open>B\<close> tal que se cumple \<open>S = {a,b} \<union> S'\<close>, \<open>S = {a} \<union> S'\<close>,\\ \<open>S = {b} \<union> S'\<close> 
  o \<open>S = S'\<close>.
\end{lema}

\begin{demostracion}
  En particular, \<open>S\<close> es un subconjunto finito de \<open>{a} \<union> ({b} \<union> B)\<close> luego, aplicando el lema \<open>4.3.2\<close>
  anterior, podemos hallar un subconjunto finito \<open>S\<^sub>1\<close> de \<open>{b} \<union> B\<close> tal que o bien \<open>S = {a} \<union> S\<^sub>1\<close> o 
  bien \<open>S = S\<^sub>1\<close>. A su vez, podemos aplicar dicho resultado para el subconjunto finito \<open>S\<^sub>1\<close> de 
  \<open>{b} \<union> B\<close>, obteniendo un subconjunto finito \<open>S\<^sub>2\<close> de \<open>B\<close> tal que o bien \<open>S\<^sub>1 = {b} \<union> S\<^sub>2\<close> o bien 
  \<open>S\<^sub>1 = S\<^sub>2\<close>. Veamos que el lema se verifica en ambas opciones posibles de \<open>S\<^sub>1\<close> para el conjunto 
  \<open>S' = S\<^sub>2\<close>.

  En primer lugar, supongamos que \<open>S\<^sub>1 = {b} \<union> S\<^sub>2\<close>. De este modo, se verifica el resultado tanto para
  \<open>S = {a} \<union> S\<^sub>1\<close> como para \<open>S = S\<^sub>1\<close>. En efecto, en la primera opción, por elección de \<open>S\<^sub>1\<close>, es claro
  que \<open>S = {a,b} \<union> S\<^sub>2\<close>. Finalmente, para \<open>S = S\<^sub>1\<close>, obtenemos que \<open>S = {b} \<union> S\<^sub>2\<close>, lo que prueba
  igualmente el lema para \<open>S' = S\<^sub>2\<close>.

  Por último, supongamos que \<open>S\<^sub>1 = S\<^sub>2\<close>. Análogamente, el resultado es inmediato pues si 
  \<open>S = {a} \<union> S\<^sub>1\<close> obtenemos que \<open>S = {a} \<union> S\<^sub>2\<close>, y si suponemos \<open>S = S\<^sub>1\<close> obtenemos\\ \<open>S = S\<^sub>2\<close>, probando
  así el lema.
\end{demostracion}

  Su formalización y prueba detallada en Isabelle/HOL son las siguientes.\<close>

lemma finite_subset_insert2:
  assumes "finite S"
          "S \<subseteq> {a,b} \<union> B"
        shows "\<exists>S' \<subseteq> B. finite S' \<and> (S = {a,b} \<union> S' \<or> S = {a} \<union> S' \<or> S = {b} \<union> S' \<or> S = S')"
proof -
  have "S \<subseteq> {a} \<union> ({b} \<union> B)"
    using assms(2) by blast
  then have Ex1:"\<exists>S1 \<subseteq> ({b} \<union> B). finite S1 \<and> (S = {a} \<union> S1 \<or> S = S1)"
    using assms(1) by (simp only: finite_subset_insert1)
  obtain S1 where "S1 \<subseteq> {b} \<union> B" and 1:"finite S1 \<and> (S = {a} \<union> S1 \<or> S = S1)"
    using Ex1 by (rule subexE)
  have "finite S1"
    using 1 by (rule conjunct1)
  have Ex2:"\<exists>S2 \<subseteq> B. finite S2 \<and> (S1 = {b} \<union> S2 \<or> S1 = S2)"
    using \<open>finite S1\<close> \<open>S1 \<subseteq> {b} \<union> B\<close> by (rule finite_subset_insert1)
  obtain S2 where "S2 \<subseteq> B" and 2:"finite S2 \<and> (S1 = {b} \<union> S2 \<or> S1 = S2)"
    using Ex2 by (rule subexE)
  have "finite S2"
    using 2 by (rule conjunct1)
  have "S1 = {b} \<union> S2 \<or> S1 = S2"
    using 2 by (rule conjunct2)
  thus ?thesis
  proof (rule disjE)
    assume "S1 = {b} \<union> S2"
    have "S = {a} \<union> S1 \<or> S = S1"
      using 1 by (rule conjunct2)
    thus ?thesis
    proof (rule disjE)
      assume "S = {a} \<union> S1"
      then have "S = {a} \<union> {b} \<union> S2"
        by (simp add: \<open>S1 = {b} \<union> S2\<close>)
      then have "S = {a,b} \<union> S2"
        by blast
      then have "S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2"
        by (iprover intro: disjI1)
      then have "finite S2 \<and> (S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2)"
        using \<open>finite S2\<close> by (iprover intro: conjI)
      thus ?thesis
        using \<open>S2 \<subseteq> B\<close> by (rule subexI)
    next
      assume "S = S1"
      then have "S = {b} \<union> S2"
        by (simp add: \<open>S1 = {b} \<union> S2\<close>)
      then have "S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2"
        by (iprover intro: disjI1)
      then have "finite S2 \<and> (S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2)"
        using \<open>finite S2\<close> by (iprover intro: conjI)
      thus ?thesis
        using \<open>S2 \<subseteq> B\<close> by (rule subexI)
    qed
  next
    assume "S1 = S2"
    have "S = {a} \<union> S1 \<or> S = S1"
      using 1 by (rule conjunct2)
    thus ?thesis
    proof (rule disjE)
      assume "S = {a} \<union> S1"
      then have "S = {a} \<union> S2"
        by (simp only: \<open>S1 = S2\<close>)
      then have "S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2"
        by (iprover intro: disjI1)
      then have "finite S2 \<and> (S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2)"
        using \<open>finite S2\<close> by (iprover intro: conjI)
      thus ?thesis
        using \<open>S2 \<subseteq> B\<close> by (rule subexI)
    next
      assume "S = S1"
      then have "S = S2"
        by (simp only: \<open>S1 = S2\<close>)
      then have "S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2"
        by (iprover intro: disjI1)
      then have "finite S2 \<and> (S = {a,b} \<union> S2 \<or> S = {a} \<union> S2 \<or> S = {b} \<union> S2 \<or> S = S2)"
        using \<open>finite S2\<close> by (iprover intro: conjI)
      thus ?thesis
        using \<open>S2 \<subseteq> B\<close> by (rule subexI)
    qed
  qed
qed

text \<open>Una vez introducidos los resultados anteriores, procedamos con la prueba del \<open>Teorema de
  Compacidad\<close>.

  \begin{demostracion}
    Consideremos la colección \<open>C\<close> formada por los conjuntos de fórmulas finitamente satisfacibles.
    Recordemos que un conjunto de fórmulas es finitamente satisfacible si todo subconjunto finito 
    suyo es satisfacible. Vamos a probar que dicho conjunto verifica la propiedad de consistencia 
    proposicional y, por el \<open>Teorema de Existencia de Modelo\<close>, quedará probado que todo conjunto de 
    \<open>C\<close> es satisfacible, lo que demuestra el teorema.

    Para probar que \<open>C\<close> verifica la propiedad de consistencia proposicional, por el lema \<open>2.0.2\<close> de 
    caracterización mediante notación uniforme, basta demostrar que se verifican las siguientes 
    condiciones para todo conjunto \<open>W \<in> C\<close>:
    \begin{itemize}
     \item \<open>\<bottom> \<notin> W\<close>.
     \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> W\<close> y \<open>\<not> p \<in> W\<close>.
     \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
      pertenece a \<open>W\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<close> pertenece a \<open>C\<close>.
     \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
      pertenece a \<open>W\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> W\<close> pertenece a \<open>C\<close> o 
      bien \<open>{\<beta>\<^sub>2} \<union> W\<close> pertenece a \<open>C\<close>.
    \end{itemize}

    De este modo, consideremos un conjunto cualquiera \<open>W \<in> C\<close> y procedamos a probar cada una de las
    condiciones anteriores.

    La primera condición se demuestra por reducción al absurdo. En efecto, si suponemos que 
    \<open>\<bottom> \<in> W\<close>, es claro que \<open>{\<bottom>}\<close> es un subconjunto finito de \<open>W\<close>. Como \<open>W\<close> es un conjunto
    finitamente satisfacible por pertenecer a \<open>C\<close>, se tiene por lo anterior que \<open>{\<bottom>}\<close> es 
    satisfacible. De este modo, llegamos a una contradicción pues, por definición, no existe ninguna 
    interpretación que sea modelo de \<open>\<bottom>\<close>.

    A continuación probaremos que, si \<open>W \<in> C\<close>, entonces dada \<open>p\<close> una fórmula atómica cualquiera, no 
    se tiene simultáneamente que \<open>p \<in> W\<close> y \<open>\<not> p \<in> W\<close>. Veamos dicho resultado por reducción al 
    absurdo, suponiendo que tanto \<open>p\<close> como \<open>\<not> p\<close> están en \<open>W\<close>. En este caso, \<open>{p,\<not> p}\<close> sería un
    subconjunto finito de \<open>W\<close> y, por ser \<open>W\<close> finitamente satisfacible ya que\\ \<open>W \<in> C\<close>, obtendríamos 
    que \<open>{p,\<not> p}\<close> es satisfacible. Sin embargo esto no es cierto ya que, en ese caso, existiría
    una interpretación que sería modelo tanto de \<open>p\<close> como de \<open>\<not> p\<close>, llegando así a una 
    contradicción.

    Probemos ahora que dada una fórmula \<open>F\<close> de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>F \<in> W\<close>,
    se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<close> pertenece a \<open>C\<close>. Por definición de la colección, basta probar que 
    \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<close> es finitamente satisfacible, es decir, que todo subconjunto finito suyo es
    satisfacible. Consideremos un subconjunto finito \<open>S\<close> de \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<close>. En estas condiciones,
    por el lema \<open>4.3.3\<close>, existe un subconjunto finito \<open>W\<^sub>0\<close> de \<open>W\<close> tal que\\ \<open>S = {\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<^sub>0\<close>,
    \<open>S = {\<alpha>\<^sub>1} \<union> W\<^sub>0\<close>, \<open>S = {\<alpha>\<^sub>2} \<union> W\<^sub>0\<close> o \<open>S = W\<^sub>0\<close>. Para probar que \<open>S\<close> es satisfacible en cada uno de 
    estos posibles casos, basta demostrar que el conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible. De este
    modo, puesto que todas las opciones posibles de \<open>S\<close> están contenidas en dicho conjunto, se
    tiene la satisfacibilidad de cada una de ellas.

    Para probar que el conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible en estas condiciones, demostremos 
    que se verifica para cada caso de la fórmula \<open>F\<close> de tipo \<open>\<alpha>\<close>:

      $\textbf{\<open>\<one>) F = G \<and> H, para ciertas fórmulas G y H\<close>:}$ Observemos que, como \<open>W\<^sub>0\<close> es un subconjunto 
      finito de \<open>W\<close> y \<open>F \<in> W\<close> por hipótesis, tenemos que \<open>{F} \<union> W\<^sub>0\<close> es un subconjunto finito de \<open>W\<close>. 
      Como \<open>W\<close> es finitamente satisfacible ya que pertenece a \<open>C\<close>, se tiene que \<open>{F} \<union> W\<^sub>0\<close> es 
      satisfacible. Luego, por definición, existe una interpretación \<open>\<A>\<close> que es modelo de todas sus 
      fórmulas y, en particular, \<open>\<A>\<close> es modelo de \<open>F\<close>. Como \<open>F = G \<and> H\<close>, obtenemos por definición 
      del valor de una fórmula en una interpretación que \<open>\<A>\<close> es modelo de \<open>G\<close> y de \<open>H\<close>. En este caso,
      las componentes conjuntivas son \<open>\<alpha>\<^sub>1 = G\<close> y \<open>\<alpha>\<^sub>2 = H\<close>, luego \<open>\<A>\<close> es modelo de ambas componentes.
      Por lo tanto, \<open>\<A>\<close> es modelo de todas las fórmulas del conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close>, lo que prueba 
      que se trata de un conjunto satisfacible.

      $\textbf{\<open>\<two>) F = \<not>(G \<or> H), para ciertas fórmulas G y H\<close>:}$ Análogamente al caso anterior, obtenemos 
      que el conjunto \<open>{F} \<union> W\<^sub>0\<close> es satisfacible. Luego, por definición, existe una interpretación 
      \<open>\<A>\<close> que es modelo de todas sus fórmulas y, en particular, de \<open>F\<close>. Por definición del valor de 
      una fórmula en una interpretación, como \<open>F = \<not>(G \<or> H)\<close>, obtenemos que no es cierto que \<open>\<A>\<close> 
      sea modelo de \<open>G \<or> H\<close>. Aplicando de nuevo la definición del valor de una fórmula en una 
      interpretación, se obtiene que no es cierto que \<open>\<A>\<close> se modelo de \<open>G\<close> o de \<open>H\<close>. Por las leyes 
      de \<open>Morgan\<close>, obtenemos equivalentemente que \<open>\<A>\<close> no es modelo de \<open>G\<close> y \<open>\<A>\<close> no es modelo de \<open>H\<close>. 
      Por lo tanto, por el valor de una fórmula en una interpretación, obtenemos que \<open>\<A>\<close> es 
      modelo de \<open>\<not> G\<close> y \<open>\<A>\<close> es modelo de \<open>\<not> H\<close>. Como las componentes conjuntivas en este caso son 
      \<open>\<alpha>\<^sub>1 = \<not> G\<close> y \<open>\<alpha>\<^sub>2 = \<not> H\<close>, es claro que \<open>\<A>\<close> es modelo de \<open>\<alpha>\<^sub>1\<close> y de \<open>\<alpha>\<^sub>2\<close>. Por lo tanto, la 
      interpretación \<open>\<A>\<close> es modelo de todas las fórmulas del conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close>, lo que 
      prueba por definición que se trata de un conjunto satisfacible. 

      $\textbf{\<open>\<three>) F = \<not>(G \<longrightarrow> H), para ciertas fórmulas G y H\<close>:}$ Como hemos visto que \<open>{F} \<union> W\<^sub>0\<close> 
      es un conjunto satisfacible, existe una interpretación \<open>\<A>\<close> que es modelo de todas sus 
      fórmulas. En particular, \<open>\<A>\<close> es modelo de \<open>F\<close> luego, por definición del valor de una fórmula 
      en una interpretación, es claro que \<open>\<A>\<close> no es modelo de \<open>G \<longrightarrow> H\<close>. De nuevo por el valor de 
      una fórmula en una interpretación, obtenemos que no es cierto que si \<open>\<A>\<close> es modelo de \<open>G\<close>, 
      entonces sea modelo de \<open>H\<close>. Equivalentemente, \<open>\<A>\<close> es modelo de \<open>G\<close> y no es modelo de \<open>H\<close>. Por 
      lo tanto, por la definición del valor de una fórmula en una interpretación, se obtiene que 
      \<open>\<A>\<close> es modelo de \<open>G\<close> y de \<open>\<not> H\<close>. Como en este caso las componentes conjuntivas son \<open>\<alpha>\<^sub>1 = G\<close> y
      \<open>\<alpha>\<^sub>2 = \<not> H\<close>, es claro que \<open>\<A>\<close> es modelo de \<open>\<alpha>\<^sub>1\<close> y de \<open>\<alpha>\<^sub>2\<close>. Por lo tanto, \<open>\<A>\<close> es modelo de 
      todas las fórmulas del conjunto  \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close>, probando así su satisfacibilidad.

      $\textbf{\<open>\<four>) F = \<not>(\<not> G), para cierta fórmula G\<close>:}$ Análogamente a los casos anteriores, se 
      prueba que existe una interpretación \<open>\<A>\<close> que es modelo de todas las fórmulas del conjunto 
      \<open>{F} \<union> W\<^sub>0\<close> por ser este satisfacible. En particular, \<open>\<A>\<close> es modelo de \<open>F\<close> luego, por 
      definición del valor de una fórmula en una interpretación, obtenemos que no es cierto que \<open>\<A>\<close> 
      no es modelo de \<open>G\<close>. Es decir, \<open>\<A>\<close> es modelo de \<open>G\<close> y, como en este caso ambas componentes 
      disyuntivas son \<open>G\<close>, es claro que \<open>\<A>\<close> es modelo de \<open>\<alpha>\<^sub>1\<close> y de \<open>\<alpha>\<^sub>2\<close>. Por tanto, \<open>\<A>\<close> es modelo 
      de todas las fórmulas del conjunto \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close>, lo que prueba su satisfacibilidad.

    Por lo tanto, \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es un conjunto satisfacible para todos los casos de la fórmula
    \<open>F\<close> de tipo \<open>\<alpha>\<close>. De este modo, como el subconjunto finito \<open>S\<close> de \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<close> es de la forma
    \<open>S = {\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<^sub>0\<close>, \<open>S = {\<alpha>\<^sub>1} \<union> W\<^sub>0\<close>, \<open>S = {\<alpha>\<^sub>2} \<union> W\<^sub>0\<close> o \<open>S = W\<^sub>0\<close>, se prueba la satisfacibilidad
    de \<open>S\<close> para cada uno de los casos por estar contenidos en el conjunto satisfacible
    \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close>. Por lo tanto, \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W\<close> es finitamente satisfacible y, por definición de 
    la colección \<open>C\<close>, pertenece a ella como queríamos demostrar.

    Finalmente probemos que para toda fórmula \<open>F\<close> de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que 
    \<open>F \<in> W\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> W \<in> C\<close> o bien \<open>{\<beta>\<^sub>2} \<union> W \<in> C\<close>. La
    demostración se realizará por reducción al absurdo, luego supongamos en estas condiciones que
    \<open>{\<beta>\<^sub>1} \<union> W \<notin> C\<close> y \<open>{\<beta>\<^sub>2} \<union> W \<notin> C\<close>. 

    En primer lugar, veamos que si \<open>{\<beta>\<^sub>i} \<union> W \<notin> C\<close>, entonces existe un subconjunto finito \<open>W\<^sub>i\<close> de 
    \<open>W\<close> tal que el conjunto \<open>{\<beta>\<^sub>i} \<union> W\<^sub>i\<close> no es satisfacible. En efecto, si \<open>{\<beta>\<^sub>i} \<union> W \<notin> C\<close>, por 
    definición de la colección \<open>C\<close> tenemos que \<open>{\<beta>\<^sub>i} \<union> W\<close> no es finitamente satisfacible. Por lo 
    tanto, existe un subconjunto finito \<open>W\<^sub>i'\<close> de \<open>{\<beta>\<^sub>i} \<union> W\<close> que no es satisfacible. Por el lema 
    \<open>4.3.2\<close>, obtenemos que existe un subconjunto finito \<open>W\<^sub>i\<close> de \<open>W\<close> tal que o bien \<open>W\<^sub>i' = {\<beta>\<^sub>i} \<union> W\<^sub>i\<close> 
    o bien \<open>W\<^sub>i' = W\<^sub>i\<close>. En efecto, si \<open>W\<^sub>i' = {\<beta>\<^sub>i} \<union> W\<^sub>i\<close>, como \<open>W\<^sub>i'\<close> no es satisfacible, se obtiene el
    resultado para \<open>W\<^sub>i\<close>. Por otro lado, supongamos que \<open>W\<^sub>i' = W\<^sub>i\<close>. Como \<open>W\<^sub>i'\<close> no es satisfacible, 
    entonces \<open>{\<beta>\<^sub>i} \<union> W\<^sub>i\<close> tampoco es satisfacible ya que, en caso contrario, obtendríamos que
    \<open>W\<^sub>i = W\<^sub>i'\<close> es satisfacible. Luego se verifica también el resultado para \<open>W\<^sub>i\<close>.

    De este modo, como \<open>{\<beta>\<^sub>1} \<union> W \<notin> C\<close> y \<open>{\<beta>\<^sub>2} \<union> W \<notin> C\<close>, obtenemos que existen subconjuntos finitos 
    \<open>W\<^sub>1\<close> y \<open>W\<^sub>2\<close> de \<open>W\<close> tales que los conjunto \<open>{\<beta>\<^sub>1} \<union> W\<^sub>1\<close> y \<open>{\<beta>\<^sub>2} \<union> W\<^sub>2\<close> no son satisfacibles. 
    Consideremos el conjunto \<open>W\<^sub>o = W\<^sub>1 \<union> W\<^sub>2\<close>. Es claro que se tiene que \<open>{\<beta>\<^sub>1} \<union> W\<^sub>1 \<subseteq> {\<beta>\<^sub>1,F} \<union> W\<^sub>o\<close> y 
    que \<open>{\<beta>\<^sub>2} \<union> W\<^sub>2 \<subseteq> {\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close>. Por lo tanto, los conjuntos \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>o\<close> y \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>o\<close> no son 
    satisfacibles ya que, en caso contrario, \<open>{\<beta>\<^sub>1} \<union> W\<^sub>1\<close> y \<open>{\<beta>\<^sub>2} \<union> W\<^sub>2\<close> serían satisfacibles. Para 
    llegar a la contradicción, basta probar que o bien \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>o\<close> es satisfacible o bien 
    \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>o\<close> es satisfacible. Para ello, veamos que se verifica el resultado para cada uno de 
    los casos posibles fórmula de tipo \<open>\<beta>\<close> para \<open>F\<close>.

      $\textbf{\<open>\<one>) F = G \<or> H, para ciertas fórmulas G y H\<close>:}$ Observemos que \<open>W\<^sub>0 = W\<^sub>1 \<union> W\<^sub>2\<close> es un 
      subconjunto finito de \<open>W\<close> por ser \<open>W\<^sub>1\<close> y \<open>W\<^sub>2\<close> subconjuntos finitos de \<open>W\<close>. Además, como 
      \<open>F \<in> W\<close> por hipótesis, tenemos que \<open>{F} \<union> W\<^sub>0\<close> es un subconjunto finito de \<open>W\<close>. Como \<open>W\<close> es 
      finitamente satisfacible ya que pertenece a \<open>C\<close>, se tiene que \<open>{F} \<union> W\<^sub>0\<close> es satisfacible. 
      Luego, por definición, existe una interpretación \<open>\<A>\<close> que es modelo de todas sus fórmulas y, 
      en particular, \<open>\<A>\<close> es modelo de \<open>F\<close>. Por definición del valor de una fórmula en una
      interpretación, obtenemos que o bien \<open>\<A>\<close> es modelo de \<open>G\<close> o bien \<open>\<A>\<close> es modelo de \<open>H\<close>.
      Como en este caso las componentes disyuntivas son \<open>\<beta>\<^sub>1 = G\<close> y \<open>\<beta>\<^sub>2 = H\<close>, se tiene que o bien \<open>\<A>\<close>
      es modelo de \<open>\<beta>\<^sub>1\<close> o bien \<open>\<A>\<close> es modelo de \<open>\<beta>\<^sub>2\<close>. Por lo tanto, es claro que o bien \<open>\<A>\<close> es
      modelo de todas las fórmulas del conjunto \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close> o bien es modelo de todas las fórmulas
      de \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close>. Luego, por definición de conjunto satisfacible tenemos que o bien 
      \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close> es satisfacible o bien \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible, como queríamos demostrar.

      $\textbf{\<open>\<three>) F = G \<longrightarrow> H, para ciertas fórmulas G y H\<close>:}$ Análogamente se tiene que el 
      conjunto \<open>{F} \<union> W\<^sub>0\<close> es satisfacible, luego existe una interpretación \<open>\<A>\<close> que es modelo de 
      todas sus fórmulas. En particular, \<open>\<A>\<close> es modelo de \<open>F\<close> y, por definición del valor de una 
      fórmula en una interpretación, se obtiene que si \<open>\<A>\<close> es modelo de \<open>G\<close>, entonces es modelo de 
      \<open>H\<close>. Equivalentemente, tenemos que \<open>\<A>\<close> no es modelo de \<open>G\<close> o \<open>\<A>\<close> es modelo de \<open>H\<close>. Por un 
      lado, si suponemos que \<open>\<A>\<close> no es modelo de \<open>G\<close>, por definición obtenemos que \<open>\<A>\<close> es modelo de 
      \<open>\<not> G\<close>. Como en este caso tenemos que \<open>\<beta>\<^sub>1 = \<not> G\<close>, es claro que \<open>\<A>\<close> es modelo de \<open>\<beta>\<^sub>1\<close>. Por 
      tanto, es modelo de todas las fórmulas de \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close>, luego es un conjunto satisfacible y 
      se verifica el resultado para este caso. Por otro lado, si suponemos que \<open>\<A>\<close> es modelo de \<open>H\<close>, 
      como \<open>\<beta>\<^sub>2 = H\<close>, obtenemos que \<open>\<A>\<close> es modelo de \<open>\<beta>\<^sub>2\<close>. Luego, análogamente, \<open>\<A>\<close> es modelo de toda
      fórmula de \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close>, lo que prueba que se trata de un conjunto satisfacible por
      definición, probando el resultado. 

      $\textbf{\<open>\<three>) F = \<not>(G \<and> H), para ciertas fórmulas G y H\<close>:}$ Como \<open>{F} \<union> W\<^sub>0\<close> es satisfacible,
      existe una interpretación \<open>\<A>\<close> que es modelo de todas sus fórmulas y, en particular, de \<open>F\<close>.
      Luego, por definición del valor de una fórmula en una interpretación, obtenemos que \<open>\<A>\<close> no
      es modelo de \<open>G \<and> H\<close>. De nuevo por definición, esto implica que no es cierto que \<open>\<A>\<close> sea 
      modelo de \<open>G\<close> y de \<open>H\<close>. Es decir, o bien \<open>\<A>\<close> no es modelo de \<open>G\<close> o bien \<open>\<A>\<close> no es modelo de
      \<open>H\<close>. Si suponemos que no es modelo de \<open>G\<close>, por definición se obtiene que \<open>\<A>\<close> es modelo de
      \<open>\<not> G\<close>. Como en este caso la componente disyuntiva \<open>\<beta>\<^sub>1\<close> es \<open>\<not> G\<close>, se deduce que \<open>\<A>\<close> es modelo
      de \<open>\<beta>\<^sub>1\<close>. Por tanto, \<open>\<A>\<close> es modelo de todas las fórmulas del conjunto \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close>, por lo que
      se demuestra que dicho conjunto es satisfacible, probando el resultado. Por otro lado, si
      suponemos que \<open>\<A>\<close> no es modelo de \<open>H\<close>, se tiene que sí lo es de \<open>\<not> H\<close>. Como \<open>\<beta>\<^sub>2\<close> es \<open>\<not> H\<close>
      en este caso, obtenemos que \<open>\<A>\<close> es modelo de \<open>\<beta>\<^sub>2\<close>. Luego \<open>\<A>\<close> es modelo de todas las fórmulas
      de \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close>, demostrando así que es un conjunto satisfacible. Por tanto, se demuestra
      el resultado en ambos casos.

      $\textbf{\<open>\<four>) F = \<not>(\<not> G), para cierta fórmula G\<close>:}$ Puesto que \<open>{F} \<union> W\<^sub>0\<close> es satisfacible, 
      existe una interpretación \<open>\<A>\<close> modelo de todas sus fórmulas y, en particular, modelo de \<open>F\<close>. 
      Luego, por definición del valor de una fórmula en una interpretación obtenemos que no es 
      cierto que \<open>\<A>\<close> no sea modelo de \<open>G\<close>, es decir, \<open>\<A>\<close> es modelo de \<open>G\<close>. Como las componentes 
      \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> son ambas \<open>G\<close> en este caso, se obtiene que \<open>\<A>\<close> es modelo suyo. En particular, lo 
      es de \<open>\<beta>\<^sub>1\<close>, de modo que \<open>\<A>\<close> es modelo de todas las fórmulas de \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close>, probando así que 
      es satisfacible. Por lo tanto, se verifica el resultado.
    
    En conclusión, hemos probado que o bien \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>o\<close> es satisfacible o bien \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>o\<close> es 
    satisfacible. Por lo tanto, se tiene que no es cierto que ninguno de los dos conjuntos sea
    insatisfacible. Esto contradice lo demostrado anteriormente, llegando así a una contradicción
    que prueba por reducción al absurdo la última condición del lema \<open>2.0.2\<close>. De este modo, queda
    probado que la colección formada por los conjuntos de fórmulas finitamente satisfacibles 
    verifica la propiedad de consistencia proposicional y, por el \<open>Teorema de Existencia de Modelo\<close>, 
    todo conjunto perteneciente a ella es satisfacible, lo que demuestra el teorema.
  \end{demostracion}

  Procedamos con la demostración detallada del \<open>Teorema de Compacidad\<close> en Isabelle/HOL. Para ello, 
  definamos la colección de conjuntos finitamente satisfacibles en Isabelle/HOL. En adelante
  notaremos por \<open>C\<close> a dicha colección.\<close>

definition colecComp :: "('a formula set) set"
  where colecComp: "colecComp = {W. fin_sat W}"

text \<open>Para facilitar la demostración introduciremos el siguiente lema auxiliar que prueba que
  todo subconjunto finito de un conjunto perteneciente a la colección anterior es satisfacible.\<close>

lemma colecComp_subset_finite: 
  assumes "W \<in> colecComp"
          "Wo \<subseteq> W"
          "finite Wo"
  shows "sat Wo" 
proof -
  have "\<forall>Wo \<subseteq> W. finite Wo \<longrightarrow> sat Wo"
    using assms(1) unfolding colecComp fin_sat_def by (rule CollectD)
  then have "finite Wo \<longrightarrow> sat Wo"
    using \<open>Wo \<subseteq> W\<close> by (rule sspec)
  thus "sat Wo"
    using \<open>finite Wo\<close> by (rule mp)
qed

text \<open>Para facilitar la comprensión de la demostración, mostraremos a continuación un grafo que 
  estructura las relaciones de necesidad de los lemas auxiliares empleados.

\comentario{Poner grafo bien.}

\begin{tikzpicture}
  [
    grow                    = down,
    level 1/.style          = {sibling distance=6cm},
    level 2/.style          = {sibling distance=4.5cm},
    level 3/.style          = {sibling distance=8cm}
    level 4/.style          = {sibling distance=4cm}
    level 5/.style          = {sibling distance=5cm}
    level 6/.style          = {sibling distance=5cm}
    level 7/.style          = {sibling distance=5cm};
    level distance          = 4cm,
    edge from parent/.style = {draw},
    every node/.style       = {font=\tiny},
    sloped
  ]
\raggedright
  \node [root] {\<open>prop_Compactness\<close>\\ \<open>(Teorema de Compacidad (4.3.1))\<close>}
    child { node [env] {\<open>set_in_colecComp\<close>\\ \<open>(W \<in> C)\<close>}}
    child { node [env] {\<open>pcp_colecComp\<close>\\ \<open>(C tiene la propiedad de consistencia proposicional)\<close>}
          child { node [env] {\<open>pcp_colecComp_bot\<close>\\ \<open>(\<bottom> \<notin> W)\<close>}
              child { node [env] {\<open>not_sat_bot\<close>\\ \<open>({\<bottom>} es insatisfacible)\<close>}}}
          child { node [env] {\<open>pcp_colecComp_atoms\<close>\\ \<open>(Cond. fórmulas atómicas)\<close>}
              child { node [env] {\<open>not_sat_atoms\<close>\\ \<open>({p,\<not> p} es insatisfacible)\<close>}}}
      		child { node [env] {\<open>pcp_colecComp_CON\<close>\\ \<open>(Cond. fórmulas de tipo \<alpha>)\<close>}
        			child { node [env] {\<open>pcp_colecComp_CON_sat\<close>\\ \<open>(Resultado \<one>)\<close>}
                      child { node [env] {\<open>pcp_colecComp_CON_sat1\<close>\\\<open>pcp_colecComp_CON_sat2\<close>\\\<open>pcp_colecComp_CON_sat3\<close>\\\<open>pcp_colecComp_CON_sat4\<close>}}}}
        			child { node [env] {\<open>pcp_colecComp_DIS\<close>\\ \<open>(Cond. fórmulas de tipo \<beta>)\<close>}
                      child { node [env] {\<open>not_colecComp\<close>\\ \<open>(Resultado \<two>)\<close>}
                            child { node [env] {\<open>sat_subset_ccontr\<close>\\ \<open>(Los conjuntos que\<close>\\ \<open>contienen algún\<close>\\ \<open>subconjunto insatisfacible\<close>\\ \<open>son insatisfacibles)\<close>}}}
                                  child { node [env] {\<open>pcp_colecComp_DIS_sat\<close>\\ \<open>(Resultado \<three>)\<close>}
                                  child { node [env] {\<open>pcp_colecComp_DIS_sat1\<close>\\\<open>pcp_colecComp_DIS_sat2\<close>\\\<open>pcp_colecComp_DIS_sat3\<close>\\\<open>pcp_colecComp_DIS_sat4\<close>}}}}};
\end{tikzpicture}

  De este modo, el \<open>Teorema de Compacidad\<close> se demuestra aplicando el \<open>Teorema de\<close>\\ \<open>Existencia de 
  Modelo\<close> a la colección \<open>C\<close>. Por tanto, basta probar que dado un conjunto finitamente satisfacible 
  \<open>W\<close> se tiene que \<open>W \<in> C\<close> (formalizado mediante el lema auxiliar \<open>set_in_colecComp\<close>) y que \<open>C\<close> 
  verifica la propiedad de consistencia proposicional (formalizado como \<open>pcp_colecComp\<close>). Por el 
  lema \<open>2.0.2\<close>, es suficiente probar las siguientes condiciones dado un conjunto \<open>W \<in> C\<close> cualquiera:
    \begin{enumerate}
     \item \<open>\<bottom> \<notin> W\<close>. (\<open>\<Longrightarrow>\<close> formalizado como \<open>pcp_colecComp_sat\<close>)
     \item Dada \<open>p\<close> una fórmula atómica cualquiera, no se tiene 
      simultáneamente que\\ \<open>p \<in> W\<close> y \<open>\<not> p \<in> W\<close>. (\<open>\<Longrightarrow>\<close> formalizado como \<open>pcp_colecComp_atoms\<close>)
     \item Para toda fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>\<alpha>\<close>
      pertenece a \<open>W\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W \<in> C\<close>. (\<open>\<Longrightarrow>\<close> formalizado como 
      \<open>pcp_colecComp_CON\<close>)
     \item Para toda fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>\<beta>\<close>
      pertenece a \<open>W\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> W \<in> C\<close> o 
      bien \<open>{\<beta>\<^sub>2} \<union> W \<in> C\<close>.\\ (\<open>\<Longrightarrow>\<close> formalizado como \<open>pcp_colecComp_DIS\<close>)
    \end{enumerate}
  A su vez, cada uno de los lemas auxiliares que prueban las condiciones anteriores precisa de los
  siguientes lemas:
  \begin{itemize}
    \item \<open>pcp_colecComp_sat\<close>: Se prueba por reducción al absurdo mediante el lema \<open>not_sat_bot\<close> que
    demuestra la insatisfacibilidad del conjunto \<open>{\<bottom>}\<close>.
    \item \<open>pcp_colecComp_atoms\<close>: Su demostración es por reducción al absurdo empleando el lema
    \<open>not_sat_atoms\<close> que prueba la insatisfacibilidad del conjunto \<open>{p,\<not> p}\<close> para cualquier fórmula
    atómica \<open>p\<close>.
    \item \<open>pcp_colecComp_CON\<close>: Para su prueba, se precisa del \<open>resultado \<one>\<close>, formalizado como 
    \<open>pcp_colecComp_CON_sat\<close>. Este demuestra que dados \<open>W \<in> C\<close>, \<open>F \<in> W\<close> una fórmula de tipo 
    \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, se verifica que 
    \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible. Para probar dicho resultado se emplean a su vez los lemas
    auxiliares \<open>pcp_colecComp_CON_sat1\<close>, \<open>pcp_colecComp_CON_sat2\<close>, \<open>pcp_colecComp_CON_sat3\<close> y 
    \<open>pcp_colecComp_CON_sat4\<close> que demuestran el enunciado para cada tipo de fórmula \<open>\<alpha>\<close>.
    \item \<open>pcp_colecComp_DIS\<close>: La prueba se realizará por reducción al absurdo. Para ello
    precisa de dos resultados.
    \begin{itemize}
      \item \<open>Resultado \<two>\<close>: Dados \<open>W \<in> C\<close> y \<open>\<beta>\<^sub>i\<close> una fórmula cualquiera tal que \<open>{\<beta>\<^sub>i} \<union> W \<notin> C\<close>, 
      entonces existe un subconjunto finito \<open>W\<^sub>i\<close> de \<open>W\<close> tal que el conjunto \<open>{\<beta>\<^sub>i} \<union> W\<^sub>i\<close> no es 
      satisfacible. En Isabelle ha sido formalizado como \<open>not_colecComp\<close>. A su vez, ha precisado
      para su prueba del lema auxiliar \<open>sat_subset_ccontr\<close> que demuestra que todo conjunto de 
      fórmulas que tenga un subconjunto insatisfacible es también insatisfacible.
      \item \<open>Resultado \<three>\<close>: Dados \<open>W \<in> C\<close>, \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> 
      tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, entonces se tiene que o bien 
      \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close> es satisfacible o bien \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible. En Isabelle se ha
      formalizado como \<open>pcp_colecComp_DIS_sat\<close>. Para su prueba, ha precisado de cuatro lemas
      auxiliares que prueban el resultado para cada caso de fórmula de tipo \<open>\<beta>\<close>: 
      \<open>pcp_colecComp_DIS_sat1\<close>, \<open>pcp_colecComp_DIS_sat2\<close>, \<open>pcp_colecComp_DIS_sat3\<close>,
      \<open>pcp_colecComp_DIS_sat4\<close>.
    \end{itemize}
  \end{itemize}

  Comencemos con las demostraciones de los lemas auxiliares empleados en la prueba del teorema.
  El siguiente lema prueba que si un conjunto es finitamente satisfacible, entonces pertenece a \<open>C\<close>.\<close>

lemma set_in_colecComp: 
  assumes "fin_sat S"
  shows "S \<in> colecComp"
  unfolding colecComp using assms unfolding fin_sat_def by (rule CollectI)

text \<open>Probemos ahora que \<open>C\<close> verifica la propiedad de consistencia proposicional. Para ello, dado un 
  conjunto \<open>W \<in> C\<close>, probaremos por separado que se verifican cada una de las condiciones del 
  lema \<open>2.0.2\<close>.
  
  En primer lugar, veamos que \<open>\<bottom> \<notin> W\<close> si \<open>W \<in> C\<close>. Para ello, precisaremos del siguiente lema 
  auxiliar que prueba que el conjunto \<open>{\<bottom>}\<close> no es satisfacible.\<close>

lemma not_sat_bot: "\<not> sat {\<bottom>}"
proof (rule ccontr)
  assume "\<not>(\<not>sat{\<bottom> :: 'a formula})"
  then have "sat {\<bottom> :: 'a formula}"
    by (rule notnotD)
  then have Ex:"\<exists>\<A>. \<forall>F \<in> {\<bottom> :: 'a formula}. \<A> \<Turnstile> F"
    by (simp only: sat_def)
  obtain \<A> where 1:"\<forall>F \<in> {\<bottom> :: 'a formula}. \<A> \<Turnstile> F"
    using Ex by (rule exE)
  have 2:"\<bottom> \<in> {\<bottom>:: 'a formula}"
    by (simp only: singletonI)
  have "\<A> \<Turnstile> \<bottom>"
    using 1 2 by (rule bspec)
  thus "False"
    by (simp only: formula_semantics.simps(2))
qed

text \<open>Por tanto, probemos que si \<open>W \<in> C\<close>, entonces \<open>\<bottom> \<notin> W\<close>.\<close>

lemma pcp_colecComp_bot:
  assumes "W \<in> colecComp"
  shows "\<bottom> \<notin> W"
proof (rule ccontr)
  assume "\<not>(\<bottom> \<notin> W)"
  then have "\<bottom> \<in> W"
    by (rule notnotD)
  have "{} \<subseteq> W" 
    by (simp only: empty_subsetI) 
  have "\<bottom> \<in> W \<and> {} \<subseteq> W"
    using \<open>\<bottom> \<in> W\<close> \<open>{} \<subseteq> W\<close> by (rule conjI)
  then have "{\<bottom>} \<subseteq> W"
    by (simp only: insert_subset)
  have "finite {\<bottom>}" 
    by (simp only: finite.emptyI finite_insert)
  have "sat {\<bottom> :: 'a formula}" 
    using assms \<open>{\<bottom>} \<subseteq> W\<close> \<open>finite {\<bottom>}\<close> by (rule colecComp_subset_finite)
  have "\<not> sat {\<bottom> :: 'a formula}" 
    by (rule not_sat_bot)
  then show False 
    using \<open>sat {\<bottom> :: 'a formula}\<close> by (rule notE)
qed

text \<open>Por otro lado, vamos a probar que dado un conjunto \<open>W \<in> C\<close> y \<open>p\<close> una fórmula atómica 
  cualquiera, no se tiene simultáneamente que \<open>p \<in> W\<close> y \<open>\<not> p \<in> W\<close>. Para ello, emplearemos el 
  siguiente lema auxiliar que prueba que el conjunto \<open>{p,\<not> p}\<close> es insatisfacible para cualquier 
  fórmula atómica \<open>p\<close>.\<close>

lemma not_sat_atoms: "\<not> sat({Atom k, \<^bold>\<not> (Atom k)})"
proof (rule ccontr)
  assume "\<not> \<not> sat({Atom k, \<^bold>\<not> (Atom k)})"
  then have "sat({Atom k, \<^bold>\<not> (Atom k)})"
    by (rule notnotD)
  then have Sat:"\<exists>\<A>. \<forall>F \<in> {Atom k, \<^bold>\<not>(Atom k)}. \<A> \<Turnstile> F"
    by (simp only: sat_def)
  obtain \<A> where H:"\<forall>F \<in> {Atom k, \<^bold>\<not>(Atom k)}. \<A> \<Turnstile> F"
    using Sat by (rule exE)
  have "Atom k \<in> {Atom k, \<^bold>\<not>(Atom k)}"
    by simp
  have "\<A> \<Turnstile> Atom k"
    using H \<open>Atom k \<in> {Atom k, \<^bold>\<not>(Atom k)}\<close> by (rule bspec)
  have "\<^bold>\<not>(Atom k) \<in> {Atom k, \<^bold>\<not>(Atom k)}"
    by simp
  have "\<A> \<Turnstile> \<^bold>\<not>(Atom k)"
    using H \<open>\<^bold>\<not>(Atom k) \<in> {Atom k, \<^bold>\<not>(Atom k)}\<close> by (rule bspec)
  then have "\<not> \<A> \<Turnstile> Atom k" 
    by (simp only: simp_thms(8) formula_semantics.simps(3))
  thus "False"
    using \<open>\<A> \<Turnstile> Atom k\<close> by (rule notE)
qed

text \<open>De este modo, podemos demostrar detalladamente la condición: dados \<open>W \<in> C\<close> y \<open>p\<close> una fórmula
  atómica cualquiera, no se tiene simultáneamente que \<open>p \<in> W\<close> y \<open>\<not> p \<in> W\<close>.\<close>

lemma pcp_colecComp_atoms:
  assumes "W \<in> colecComp"
  shows "\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False"
proof (rule allI)
  fix k
  show "Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False"
  proof (rule impI)+
    assume 1:"Atom k \<in> W"
    assume 2:"\<^bold>\<not> (Atom k) \<in> W"
    have "{} \<subseteq> W"
      by (simp only: empty_subsetI) 
    have "Atom k \<in> W \<and> {} \<subseteq> W"
      using 1 \<open>{} \<subseteq> W\<close> by (rule conjI)
    then have "{Atom k} \<subseteq> W"
      by (simp only: insert_subset)
    have "\<^bold>\<not> (Atom k) \<in> W \<and> {} \<subseteq> W"
      using 2 \<open>{} \<subseteq> W\<close> by (rule conjI)
    then have "{\<^bold>\<not>(Atom k)} \<subseteq> W"
      by (simp only: insert_subset)
    have "{Atom k} \<union> {\<^bold>\<not>(Atom k)} \<subseteq> W"
      using \<open>{Atom k} \<subseteq> W\<close> \<open>{\<^bold>\<not>(Atom k)} \<subseteq> W\<close> by (simp only: Un_least)
    then have "{Atom k, \<^bold>\<not>(Atom k)} \<subseteq> W"
      by simp 
    have "finite {Atom k, \<^bold>\<not>(Atom k)}"
      by blast
    have "sat ({Atom k, \<^bold>\<not>(Atom k)})"
      using assms \<open>{Atom k, \<^bold>\<not>(Atom k)} \<subseteq> W\<close> \<open>finite {Atom k, \<^bold>\<not>(Atom k)}\<close> by (rule colecComp_subset_finite)
    have "\<not> sat ({Atom k, \<^bold>\<not>(Atom k)})"
      by (rule not_sat_atoms)
    thus "False"
      using \<open>sat ({Atom k, \<^bold>\<not>(Atom k)})\<close> by (rule notE)
  qed
qed

text \<open>Demostremos la tercera condición del lema \<open>2.0.2\<close>: dados \<open>W \<in> C\<close> y \<open>F\<close> una fórmula de 
  tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>F \<in> W\<close>, se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W \<in> C\<close>. Para probar 
  dicho resultado, emplearemos un lema auxiliar que demuestra que dado un subconjunto finito \<open>W\<^sub>0\<close> de 
  \<open>W\<close> se tiene que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es un conjunto satisfacible. Mostraremos la prueba para cada
  caso de fórmula de tipo \<open>\<alpha>\<close>. Para ello, precisaremos del siguiente lema auxiliar que demuestra que 
  dado un conjunto \<open>W \<in> C\<close>, \<open>F\<close> una fórmula perteneciente a \<open>W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, 
  entonces \<open>{F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_elem_sat:
  assumes "W \<in> colecComp"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({F} \<union> Wo)"
proof -
  have 1:"insert F Wo = {F} \<union> Wo"
    by (rule insert_is_Un)
  have "finite (insert F Wo)"
    using assms(3) by (simp only: finite_insert)
  then have "finite ({F} \<union> Wo)"
    by (simp only: 1) 
  have "F \<in> W \<and> Wo \<subseteq> W"
    using assms(2) assms(4) by (rule conjI)
  then have "insert F Wo \<subseteq> W"
    by (simp only: insert_subset)
  then have "{F} \<union> Wo \<subseteq> W"
    by (simp only: 1)
  show "sat ({F} \<union> Wo)"
    using assms(1) \<open>{F} \<union> Wo \<subseteq> W\<close> \<open>finite ({F} \<union> Wo)\<close> by (rule colecComp_subset_finite)
qed

text \<open>De este modo, vamos a probar para cada caso de fórmula \<open>\<alpha>\<close> que dados \<open>W \<in> C\<close>, \<open>F\<close> una fórmula 
  de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, se 
  verifica que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible. Para ello, emplearemos el siguiente lema auxiliar
  en Isabelle.\<close>

lemma ball_Un: 
  assumes "\<forall>x \<in> A. P x"
          "\<forall>x \<in> B. P x"
        shows "\<forall>x \<in> (A \<union> B). P x" 
  using assms by blast

text \<open>En primer lugar, probemos que dados \<open>W \<in> C\<close>, una fórmula \<open>F = G \<and> H\<close> para ciertas fórmulas \<open>G\<close> 
  y \<open>H\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, se verifica que \<open>{G,H,F} \<union> W\<^sub>0\<close> es 
  satisfacible.\<close>

lemma pcp_colecComp_CON_sat1:
  assumes "W \<in> colecComp"
          "F = G \<^bold>\<and> H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by (simp add: insertI1)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> (G \<^bold>\<and> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<A> \<Turnstile> G \<and> \<A> \<Turnstile> H"
    by (simp only: formula_semantics.simps(4))
  then have "\<A> \<Turnstile> G"
    by (rule conjunct1)
  then have 1:"\<forall>F \<in> {G}. \<A> \<Turnstile> F"
    by simp
  have "\<A> \<Turnstile> H"
    using \<open>\<A> \<Turnstile> G \<and> \<A> \<Turnstile> H\<close> by (rule conjunct2)
  then have 2:"\<forall>F \<in> {H}. \<A> \<Turnstile> F"
    by simp
  have "\<forall>F \<in> ({G} \<union> {H}) \<union> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Forall1 1 2 by (iprover intro: ball_Un)
  then have "\<forall>F \<in> ({G,H,F} \<union> Wo). \<A> \<Turnstile> F"
    by simp
  then have "\<exists>\<A>. \<forall>F \<in> ({G,H,F} \<union> Wo). \<A> \<Turnstile> F"
    by (iprover intro: exI)
  thus "sat ({G,H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

text \<open>A continuación veamos la prueba detallada del resultado para el segundo caso de fórmula de 
  tipo \<open>\<alpha>\<close>: dados \<open>W \<in> C\<close>, una fórmula \<open>F = \<not>(G \<or> H)\<close> para ciertas fórmulas \<open>G\<close> y \<open>H\<close> tal que 
  \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, se verifica que \<open>{\<not> G,\<not> H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_CON_sat2:
  assumes "W \<in> colecComp"
          "F = \<^bold>\<not>(G \<^bold>\<or> H)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by (simp add: insertI1)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(G \<^bold>\<or> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not>(\<A> \<Turnstile> (G \<^bold>\<or> H))"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<not>(\<A> \<Turnstile> G \<or> \<A> \<Turnstile> H)"
    by (simp only: formula_semantics.simps(5) simp_thms(8))
  then have "\<not> \<A> \<Turnstile> G \<and> \<not> \<A> \<Turnstile> H" 
    by (simp only: de_Morgan_disj simp_thms(8))
  then have "\<A> \<Turnstile> \<^bold>\<not> G \<and> \<A> \<Turnstile> \<^bold>\<not> H"
    by (simp only: formula_semantics.simps(3) simp_thms(8)) 
  then have "\<A> \<Turnstile> \<^bold>\<not> G"
    by (rule conjunct1)
  then have 1:"\<forall>F \<in> {\<^bold>\<not> G}. \<A> \<Turnstile> F"
    by simp
  have "\<A> \<Turnstile> \<^bold>\<not> H"
    using \<open>\<A> \<Turnstile> \<^bold>\<not> G \<and> \<A> \<Turnstile> \<^bold>\<not> H\<close> by (rule conjunct2)
  then have 2:"\<forall>F \<in> {\<^bold>\<not> H}. \<A> \<Turnstile> F"
    by simp
  have "\<forall>F \<in> ({\<^bold>\<not> G} \<union> {\<^bold>\<not> H}) \<union> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Forall1 1 2 by (iprover intro: ball_Un)
  then have "\<forall>F \<in> ({\<^bold>\<not> G,\<^bold>\<not> H, F} \<union> Wo). \<A> \<Turnstile> F"
    by simp
  then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo). \<A> \<Turnstile> F"
    by (iprover intro: exI)
  thus "sat ({\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

text \<open>Probemos detalladamente el resultado para el tercer caso de fórmula de tipo \<open>\<alpha>\<close>: dados 
  \<open>W \<in> C\<close>, una fórmula \<open>F = \<not>(G \<longrightarrow> H)\<close> para ciertas fórmulas \<open>G\<close> y \<open>H\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un 
  subconjunto finito de \<open>W\<close>, se verifica que \<open>{G,\<not> H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_CON_sat3:
  assumes "W \<in> colecComp"
          "F = \<^bold>\<not> (G \<^bold>\<rightarrow> H)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,\<^bold>\<not> H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by (simp add: insertI1)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(G \<^bold>\<rightarrow> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not>(\<A> \<Turnstile> (G \<^bold>\<rightarrow> H))"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<not>(\<A> \<Turnstile> G \<longrightarrow> \<A> \<Turnstile> H)"
    by (simp only: formula_semantics.simps(6) simp_thms(8))
  then have "\<A> \<Turnstile> G \<and> \<not> \<A> \<Turnstile> H"
    by (simp only: not_imp simp_thms(8))
  then have "\<A> \<Turnstile> G \<and> \<A> \<Turnstile> \<^bold>\<not> H"
    by (simp only: formula_semantics.simps(3) simp_thms(8)) 
  then have "\<A> \<Turnstile> G"
    by (rule conjunct1)
  then have 1:"\<forall>F \<in> {G}. \<A> \<Turnstile> F"
    by simp
  have "\<A> \<Turnstile> \<^bold>\<not> H"
    using \<open>\<A> \<Turnstile> G \<and> \<A> \<Turnstile> \<^bold>\<not> H\<close> by (rule conjunct2)
  then have 2:"\<forall>F \<in> {\<^bold>\<not> H}. \<A> \<Turnstile> F"
    by simp
  have "\<forall>F \<in> ({G} \<union> {\<^bold>\<not> H}) \<union> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Forall1 1 2 by (iprover intro: ball_Un)
  then have "\<forall>F \<in> {G,\<^bold>\<not> H,F} \<union> Wo. \<A> \<Turnstile> F"
    by simp
  then have "\<exists>\<A>. \<forall>F \<in> ({G,\<^bold>\<not> H,F} \<union> Wo). \<A> \<Turnstile> F"
    by (iprover intro: exI)
  thus "sat ({G,\<^bold>\<not> H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

text \<open>Por último, la prueba detallada del resultado para el cuarto caso de fórmula de tipo \<open>\<alpha>\<close>: 
  dados \<open>W \<in> C\<close>, una fórmula \<open>F = \<not>(\<not> G)\<close> para cierta fórmula \<open>G\<close> tal que \<open>F \<in> W\<close>, \<open>H = G\<close> y \<open>W\<^sub>0\<close> 
  un subconjunto finito de \<open>W\<close>, se verifica que \<open>{G,H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_CON_sat4:
  assumes "W \<in> colecComp"
          "F = \<^bold>\<not> (\<^bold>\<not> G)"
          "H = G"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,4,5,6) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by (simp add: insertI1)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(\<^bold>\<not> G)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not> \<A> \<Turnstile> \<^bold>\<not> G"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<not> \<not>\<A> \<Turnstile> G"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<A> \<Turnstile> G"
    by (rule notnotD)
  then have 1:"\<forall>F \<in> {G}. \<A> \<Turnstile> F"
    by simp
  have "\<A> \<Turnstile> H"
    using \<open>\<A> \<Turnstile> G\<close> by (simp only: \<open>H = G\<close>)
  then have 2:"\<forall>F \<in> {H}. \<A> \<Turnstile> F"
    by simp
  have "\<forall>F \<in> ({G} \<union> {H}) \<union> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Forall1 1 2 by (iprover intro: ball_Un)
  then have "\<forall>F \<in> {G,H,F} \<union> Wo. \<A> \<Turnstile> F"
    by simp
  then have "\<exists>\<A>. \<forall>F \<in> ({G,H,F} \<union> Wo). \<A> \<Turnstile> F"
    by (iprover intro: exI)
  thus "sat ({G,H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

text \<open>Por tanto, por las pruebas detalladas de los casos anteriores, podemos demostrar que dados 
  \<open>W \<in> C\<close>, \<open>F \<in> W\<close> una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> y \<open>W\<^sub>0\<close> un subconjunto finito 
  de \<open>W\<close>, se verifica que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_CON_sat:
  assumes "W \<in> colecComp"
          "Con F G H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,H,F} \<union> Wo)"
proof -
  have "{G,H} \<union> Wo \<subseteq> {G,H,F} \<union> Wo"
    by blast
  have "F = G \<^bold>\<and> H \<or> 
    (\<exists>F1 G1. F = \<^bold>\<not> (F1 \<^bold>\<or> G1) \<and> G = \<^bold>\<not> F1 \<and> H = \<^bold>\<not> G1) \<or> 
    (\<exists>H1. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H1) \<and> H = \<^bold>\<not> H1) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
    using assms(2) by (simp only: con_dis_simps(1))
  thus "sat ({G,H,F} \<union> Wo)"
  proof (rule disjE)
    assume "F = G \<^bold>\<and> H"
    show "sat ({G,H,F} \<union> Wo)"
      using assms(1) \<open>F = G \<^bold>\<and> H\<close> assms(3,4,5) by (rule pcp_colecComp_CON_sat1)
  next
    assume "(\<exists>F1 G1. F = \<^bold>\<not> (F1 \<^bold>\<or> G1) \<and> G = \<^bold>\<not> F1 \<and> H = \<^bold>\<not> G1) \<or> 
    (\<exists>H1. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H1) \<and> H = \<^bold>\<not> H1) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
    thus "sat ({G,H,F} \<union> Wo)"
    proof (rule disjE)
      assume Ex2:"\<exists>F1 G1. F = \<^bold>\<not> (F1 \<^bold>\<or> G1) \<and> G = \<^bold>\<not> F1 \<and> H = \<^bold>\<not> G1" 
      obtain F1 G1 where 2:"F = \<^bold>\<not>(F1 \<^bold>\<or> G1) \<and> G = \<^bold>\<not> F1 \<and> H = \<^bold>\<not> G1"
        using Ex2 by (iprover elim: exE)
      have "G = \<^bold>\<not> F1"
        using 2 by (iprover elim: conjunct1)
      have "H = \<^bold>\<not> G1"
        using 2 by (iprover elim: conjunct2)
      have "F = \<^bold>\<not>(F1 \<^bold>\<or> G1)"
        using 2 by (rule conjunct1)
      have "sat ({\<^bold>\<not> F1, \<^bold>\<not> G1, F} \<union> Wo)"
        using assms(1) \<open>F = \<^bold>\<not>(F1 \<^bold>\<or> G1)\<close> assms(3,4,5) by (rule pcp_colecComp_CON_sat2)
      thus "sat ({G,H,F} \<union> Wo)"
        by (simp only: \<open>G = \<^bold>\<not> F1\<close> \<open>H = \<^bold>\<not> G1\<close>)
    next
      assume "(\<exists>H1. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H1) \<and> H = \<^bold>\<not> H1) \<or> 
              F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
      thus "sat ({G,H,F} \<union> Wo)"
      proof (rule disjE)
        assume Ex3:"\<exists>H1. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H1) \<and> H = \<^bold>\<not> H1"
        obtain H1 where 3:"F = \<^bold>\<not>(G \<^bold>\<rightarrow> H1) \<and> H = \<^bold>\<not> H1"
          using Ex3 by (rule exE)
        have "H = \<^bold>\<not> H1"
          using 3 by (rule conjunct2)
        have "F = \<^bold>\<not>(G \<^bold>\<rightarrow> H1)"
          using 3 by (rule conjunct1)
        have "sat ({G, \<^bold>\<not> H1, F} \<union> Wo)"
          using assms(1) \<open>F = \<^bold>\<not>(G \<^bold>\<rightarrow> H1)\<close> assms(3,4,5) by (rule pcp_colecComp_CON_sat3)
        thus "sat ({G,H,F} \<union> Wo)"
          by (simp only: \<open>H = \<^bold>\<not> H1\<close>)
      next
        assume "F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
        then have "H = G"
          by (rule conjunct2)
        have "F = \<^bold>\<not> (\<^bold>\<not> G)"
          using \<open>F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G\<close> by (rule conjunct1)
        show "sat ({G, H, F} \<union> Wo)"
          using assms(1) \<open>F = \<^bold>\<not>(\<^bold>\<not> G)\<close> \<open>H = G\<close> assms(3,4,5) by (rule pcp_colecComp_CON_sat4)
      qed
    qed
  qed
qed

text \<open>Finalmente, con el resultado anterior, podemos probar la tercera condición del lema \<open>2.0.2\<close>: 
  dados \<open>W \<in> C\<close> y \<open>F\<close> una fórmula de tipo \<open>\<alpha>\<close> con componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> tal que \<open>F \<in> W\<close>, se tiene 
  que \<open>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> W \<in> C\<close>.\<close>
      
lemma pcp_colecComp_CON:
  assumes "W \<in> colecComp"
  shows "\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> colecComp"
proof (rule allI)+
  fix F G H
  show "Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> colecComp"
  proof (rule impI)+
    assume "Con F G H"
    assume "F \<in> W"
    show "{G,H} \<union> W \<in> colecComp"
      unfolding colecComp fin_sat_def
    proof (rule CollectI)
      show "\<forall>S \<subseteq> {G,H} \<union> W. finite S \<longrightarrow> sat S"
      proof (rule sallI)
        fix S
        assume "S \<subseteq> {G,H} \<union> W"
        then have "S \<subseteq> {G} \<union> ({H} \<union> W)"
          by blast 
        show "finite S \<longrightarrow> sat S"
        proof (rule impI)
          assume "finite S" 
          have Ex:"\<exists>Wo \<subseteq> W. finite Wo \<and> (S = {G,H} \<union> Wo \<or> S = {G} \<union> Wo \<or> S = {H} \<union> Wo \<or> S = Wo)"
            using \<open>finite S\<close> \<open>S \<subseteq> {G,H} \<union> W\<close> by (rule finite_subset_insert2)
          obtain Wo where "Wo \<subseteq> W" and 1:"finite Wo \<and> (S = {G,H} \<union> Wo \<or> S = {G} \<union> Wo \<or> S = {H} \<union> Wo \<or> S = Wo)"
            using Ex by (rule subexE)
          have "finite Wo"
            using 1 by (rule conjunct1)
            have "sat ({G,H,F} \<union> Wo)" 
              using \<open>W \<in> colecComp\<close> \<open>Con F G H\<close> \<open>F \<in> W\<close> \<open>finite Wo\<close> \<open>Wo \<subseteq> W\<close> by (rule pcp_colecComp_CON_sat)
          have "S = {G,H} \<union> Wo \<or> S = {G} \<union> Wo \<or> S = {H} \<union> Wo \<or> S = Wo"
            using 1 by (rule conjunct2)
          thus "sat S"
          proof (rule disjE)
            assume "S = {G,H} \<union> Wo"
            then have "S \<subseteq> {G,H,F} \<union> Wo"
              by blast
            show "sat S"
              using \<open>sat({G,H,F} \<union> Wo)\<close> \<open>S \<subseteq> {G,H,F} \<union> Wo\<close> by (simp only: sat_mono)
          next
            assume "S = {G} \<union> Wo \<or> S = {H} \<union> Wo \<or> S = Wo"
            thus "sat S"
            proof (rule disjE)
              assume "S = {G} \<union> Wo"
              then have "S \<subseteq> {G,H,F} \<union> Wo"
                by blast 
              thus "sat S"
                using \<open>sat({G,H,F} \<union> Wo)\<close> by (rule sat_mono)
            next
              assume "S = {H} \<union> Wo \<or> S = Wo"
              thus "sat S"
              proof (rule disjE)
                assume "S = {H} \<union> Wo"
                then have "S \<subseteq> {G,H,F} \<union> Wo"
                  by blast 
                thus "sat S"
                  using \<open>sat({G,H,F} \<union> Wo)\<close> by (rule sat_mono)
              next
                assume "S = Wo"
                then have "S \<subseteq> {G,H,F} \<union> Wo"
                  by (simp only: Un_upper2)
                thus "sat S"
                  using \<open>sat({G,H,F} \<union> Wo)\<close> by (rule sat_mono)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Por último, probemos la cuarta condición del lema \<open>2.0.2\<close>: dados \<open>W \<in> C\<close> y \<open>F\<close> una 
  fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>F \<in> W\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> W \<in> C\<close> 
  o bien \<open>{\<beta>\<^sub>2} \<union> W \<in> C\<close>. 
  
  Por un lado, precisaremos para ello de un lema auxiliar que demuestre que dado \<open>W \<in> C\<close> y \<open>\<beta>\<^sub>i\<close> una 
  fórmula cualquiera tal que \<open>{\<beta>\<^sub>i} \<union> W \<notin> C\<close>, entonces existe un subconjunto finito \<open>W\<^sub>i\<close> de \<open>W\<close> tal 
  que el conjunto \<open>{\<beta>\<^sub>i} \<union> W\<^sub>i\<close> no es satisfacible. A su vez, para su demostración emplearemos un lema 
  que prueba que todo conjunto que contiene un subconjunto insatisfacible es también 
  insatisfacible.\<close>

lemma sat_subset_ccontr:
  assumes "A \<subseteq> B"
          "\<not> sat A"
        shows "\<not> sat B"
proof -
  have "A \<subseteq> B \<and> sat B \<longrightarrow> sat A"
    using sat_mono by blast
  then have "\<not>(A \<subseteq> B \<and> sat B)"
    using assms(2) by (rule mt)
  then have "\<not>(A \<subseteq> B) \<or> \<not>(sat B)"
    by (simp only: de_Morgan_conj)
  thus ?thesis
  proof (rule disjE)
    assume "\<not>(A \<subseteq> B)"
    thus ?thesis
      using assms(1) by (rule notE)
  next
    assume "\<not>(sat B)"
    thus ?thesis
      by this
  qed
qed

text \<open>De este modo, podemos demostrar que dados \<open>W \<in> C\<close> y \<open>\<beta>\<^sub>i\<close> una fórmula cualquiera tal que 
  \<open>{\<beta>\<^sub>i} \<union> W \<notin> C\<close>, entonces existe un subconjunto finito \<open>W\<^sub>i\<close> de \<open>W\<close> tal que el conjunto \<open>{\<beta>\<^sub>i} \<union> W\<^sub>F\<close> 
  no es satisfacible.\<close>

lemma not_colecComp:
  assumes "W \<in> colecComp"
          "{Gi} \<union> W \<notin> colecComp"
        shows "\<exists>Wi \<subseteq> W. finite Wi \<and> \<not>(sat ({Gi} \<union> Wi))"
proof -
  have WCol:"\<forall>S' \<subseteq> W. finite S' \<longrightarrow> sat S'"
    using assms(1) unfolding colecComp fin_sat_def by (rule CollectD) 
  have "\<not>(\<forall>Wo \<subseteq> {Gi} \<union> W. finite Wo \<longrightarrow> sat Wo)"
    using assms(2) unfolding colecComp fin_sat_def by (simp only: mem_Collect_eq simp_thms(8))
  then have "\<exists>Wo \<subseteq> {Gi} \<union> W. \<not>(finite Wo \<longrightarrow> sat Wo)"
    by (rule sall_simps_not_all)
  then have Ex1:"\<exists>Wo \<subseteq> {Gi} \<union> W. finite Wo \<and> \<not>(sat Wo)"
    by (simp only: not_imp)
  obtain Wo where "Wo \<subseteq> {Gi} \<union> W" and C1:"finite Wo \<and> \<not>(sat Wo)"
    using Ex1 by (rule subexE)
  have "finite Wo"
    using C1 by (rule conjunct1)
  have "\<not>(sat Wo)"
    using C1 by (rule conjunct2)
  have Ex2:"\<exists>Wo' \<subseteq> W. finite Wo' \<and> (Wo = {Gi} \<union> Wo' \<or> Wo = Wo')"
    using \<open>finite Wo\<close> \<open>Wo \<subseteq> {Gi} \<union> W\<close> by (rule finite_subset_insert1)
  obtain Wo' where "Wo' \<subseteq> W" and C2:"finite Wo' \<and> (Wo = {Gi} \<union> Wo' \<or> Wo = Wo')"
    using Ex2 by blast
  have "finite Wo'"
    using C2 by (rule conjunct1)
  have "Wo = {Gi} \<union> Wo' \<or> Wo = Wo'"
    using C2 by (rule conjunct2)
  thus ?thesis
  proof (rule disjE)
    assume "Wo = {Gi} \<union> Wo'"
    then have "\<not>(sat ({Gi} \<union> Wo'))" 
      using \<open>\<not> sat Wo\<close> by (simp only: \<open>Wo = {Gi} \<union> Wo'\<close> simp_thms(8))
    have "finite Wo' \<and> \<not>(sat ({Gi} \<union> Wo'))"
      using \<open>finite Wo'\<close> \<open>\<not>(sat ({Gi} \<union> Wo'))\<close> by (rule conjI)
    thus ?thesis
      using \<open>Wo' \<subseteq> W\<close> by (rule subexI)
  next
    assume "Wo = Wo'"
    then have "\<not> (sat Wo')"
      using \<open>\<not> sat Wo\<close> by (simp only: \<open>Wo = Wo'\<close> simp_thms(8))
    have "Wo' \<subseteq> {Gi} \<union> Wo'"
      by blast
    then have "\<not> (sat ({Gi} \<union> Wo'))"
      using \<open>\<not> (sat Wo')\<close> by (rule sat_subset_ccontr)
    have "finite Wo' \<and> \<not>(sat ({Gi} \<union> Wo'))"
      using \<open>finite Wo'\<close> \<open>\<not>(sat ({Gi} \<union> Wo'))\<close> by (rule conjI)
    thus ?thesis
      using \<open>Wo' \<subseteq> W\<close> by (rule subexI)
  qed
qed

text \<open>Por otro lado, para demostrar la cuarta condición del lema \<open>2.0.2\<close> que demuestra que \<open>C\<close> 
  verifica la propiedad de consistencia proposicional, precisaremos de un lema auxiliar que prueba 
  que dados \<open>W \<in> C\<close>, \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> y componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un 
  subconjunto finito de \<open>W\<close>, entonces se tiene que o bien \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close> es satisfacible o bien 
  \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible. Vamos a probar que, en efecto, se tiene el resultado para cada tipo de fórmula \<open>\<beta>\<close>.

  En primer lugar, probemos que dados \<open>W \<in> C\<close>, una fórmula \<open>F = G \<and> H\<close> para ciertas fórmulas \<open>G\<close> y 
  \<open>H\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, entonces se tiene que o bien 
  \<open>{G,F} \<union> W\<^sub>0\<close> es satisfacible o bien \<open>{H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_DIS_sat1:
  assumes "W \<in> colecComp"
          "F = G \<^bold>\<or> H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp 
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> (G \<^bold>\<or> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<A> \<Turnstile> G \<or> \<A> \<Turnstile> H"
    by (simp only: formula_semantics.simps(5))
  thus ?thesis
  proof (rule disjE)
    assume "\<A> \<Turnstile> G"
    then have "\<forall>F \<in> {G}. \<A> \<Turnstile> F"
      by simp
    then have "\<forall>F \<in> ({G} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
      using Forall1 by (rule ball_Un)
    then have "\<forall>F \<in> {G,F} \<union> Wo. \<A> \<Turnstile> F"
      by simp 
    then have "\<exists>\<A>. \<forall>F \<in> ({G,F} \<union> Wo). \<A> \<Turnstile> F"
      by (iprover intro: exI)
    then have "sat ({G,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI1)
  next
    assume "\<A> \<Turnstile> H"
    then have "\<forall>F \<in> {H}. \<A> \<Turnstile> F"
      by simp
    then have "\<forall>F \<in> ({H} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
      using Forall1 by (rule ball_Un)
    then have "\<forall>F \<in> {H,F} \<union> Wo. \<A> \<Turnstile> F"
      by simp
    then have "\<exists>\<A>. \<forall>F \<in> ({H,F} \<union> Wo). \<A> \<Turnstile> F"
      by (iprover intro: exI)
    then have "sat ({H,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI2)
  qed
qed

text \<open>El siguiente lema auxiliar demuestra que dados \<open>W \<in> C\<close>, una fórmula \<open>F = G \<longrightarrow> H\<close> para ciertas 
  fórmulas \<open>G\<close> y \<open>H\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, entonces se tiene que o 
  bien \<open>{\<not> G,F} \<union> W\<^sub>0\<close> es satisfacible o bien \<open>{H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_DIS_sat2:
  assumes "W \<in> colecComp"
          "F = G \<^bold>\<rightarrow> H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({\<^bold>\<not> G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> (G \<^bold>\<rightarrow> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<A> \<Turnstile> G \<longrightarrow> \<A> \<Turnstile> H"
    by (simp only: formula_semantics.simps(6))
  then have "(\<not>(\<not> \<A> \<Turnstile> G)) \<longrightarrow> \<A> \<Turnstile> H"
    by (simp only: not_not)
  then have "(\<not> \<A> \<Turnstile> G) \<or> \<A> \<Turnstile> H"
    by (simp only: disj_imp)
  thus ?thesis
  proof (rule disjE)
    assume "\<not> \<A> \<Turnstile> G"
    then have "\<A> \<Turnstile> (\<^bold>\<not> G)"
      by (simp only: formula_semantics.simps(3) simp_thms(8))
    then have "\<forall>F \<in> {\<^bold>\<not> G}. \<A> \<Turnstile> F"
      by simp
    then have "\<forall>F \<in> ({\<^bold>\<not> G} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
      using Forall1 by (rule ball_Un)
    then have "\<forall>F \<in> {\<^bold>\<not> G,F} \<union> Wo. \<A> \<Turnstile> F"
      by simp
    then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> G,F} \<union> Wo). \<A> \<Turnstile> F"
      by (iprover intro: exI)
    then have "sat ({\<^bold>\<not> G,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI1)
  next
    assume "\<A> \<Turnstile> H"
    then have "\<forall>F \<in> {H}. \<A> \<Turnstile> F"
      by simp
    then have "\<forall>F \<in> ({H} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
      using Forall1 by (rule ball_Un)
    then have "\<forall>F \<in> {H,F} \<union> Wo. \<A> \<Turnstile> F"
      by simp
    then have "\<exists>\<A>. \<forall>F \<in> ({H,F} \<union> Wo). \<A> \<Turnstile> F"
      by (iprover intro: exI)
    then have "sat ({H,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI2)
  qed
qed

text \<open>Por otro lado probemos que dados \<open>W \<in> C\<close>, una fórmula \<open>F = \<not>(G \<and> H)\<close> para ciertas fórmulas 
  \<open>G\<close> y \<open>H\<close> tal que \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, entonces se tiene que o bien 
  \<open>{\<not> G,F} \<union> W\<^sub>0\<close> es satisfacible o bien \<open>{\<not> H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_DIS_sat3:
  assumes "W \<in> colecComp"
          "F = \<^bold>\<not> (G \<^bold>\<and> H)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({\<^bold>\<not> G,F} \<union> Wo) \<or> sat ({\<^bold>\<not> H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not> (G \<^bold>\<and> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not> (\<A> \<Turnstile> (G \<^bold>\<and> H))"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<not>(\<A> \<Turnstile> G \<and> \<A> \<Turnstile> H)"
    by (simp only: formula_semantics.simps(4) simp_thms(8))
  then have "\<not> (\<A> \<Turnstile> G) \<or> \<not> (\<A> \<Turnstile> H)"
    by (simp only: de_Morgan_conj)
  thus ?thesis
  proof (rule disjE)
    assume "\<not> (\<A> \<Turnstile> G)"
    then have "\<A> \<Turnstile> \<^bold>\<not> G"
      by (simp only: formula_semantics.simps(3) simp_thms(8))
    then have "\<forall>F \<in> {\<^bold>\<not> G}. \<A> \<Turnstile> F"
      by simp
    then have "\<forall>F \<in> ({\<^bold>\<not> G} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
      using Forall1 by (rule ball_Un)
    then have "\<forall>F \<in> {\<^bold>\<not> G,F} \<union> Wo. \<A> \<Turnstile> F"
      by simp
    then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> G,F} \<union> Wo). \<A> \<Turnstile> F"
      by (iprover intro: exI)
    then have "sat ({\<^bold>\<not> G,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI1)
  next
    assume "\<not> (\<A> \<Turnstile> H)"
    then have "\<A> \<Turnstile> \<^bold>\<not> H"
      by (simp only: formula_semantics.simps(3) simp_thms(8))
    then have "\<forall>F \<in> {\<^bold>\<not> H}. \<A> \<Turnstile> F"
      by simp
    then have "\<forall>F \<in> ({\<^bold>\<not> H} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
      using Forall1 by (rule ball_Un)
    then have "\<forall>F \<in> {\<^bold>\<not> H,F} \<union> Wo. \<A> \<Turnstile> F"
      by simp
    then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> H,F} \<union> Wo). \<A> \<Turnstile> F"
      by (iprover intro: exI)
    then have "sat ({\<^bold>\<not> H,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI2)
  qed
qed

text \<open>Por último, probemos que dados \<open>W \<in> C\<close>, una fórmula \<open>F = \<not> (\<not> G)\<close> para cierta fórmula \<open>G\<close> tal 
  que \<open>F \<in> W\<close>, \<open>H = G\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, entonces se tiene que o bien 
  \<open>{G,F} \<union> W\<^sub>0\<close> es satisfacible o bien \<open>{H,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_DIS_sat4:
  assumes "W \<in> colecComp"
          "F = \<^bold>\<not> (\<^bold>\<not> G)"
          "H = G"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,4,5,6) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp 
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(\<^bold>\<not> G)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not> \<A> \<Turnstile> \<^bold>\<not> G"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<not> \<not>\<A> \<Turnstile> G"
    by (simp only: formula_semantics.simps(3) simp_thms(8))
  then have "\<A> \<Turnstile> G"
    by (rule notnotD)
  then have "\<forall>F \<in> {G}. \<A> \<Turnstile> F"
    by simp
  then have "\<forall>F \<in> ({G} \<union> ({F} \<union> Wo)). \<A> \<Turnstile> F"
    using Forall1 by (rule ball_Un)
  then have "\<forall>F \<in> {G,F} \<union> Wo. \<A> \<Turnstile> F"
    by simp
  then have "\<exists>\<A>. \<forall>F \<in> ({G,F} \<union> Wo). \<A> \<Turnstile> F"
    by (iprover intro: exI)
  then have "sat ({G,F} \<union> Wo)"
    by (simp only: sat_def)
  thus ?thesis
    by (rule disjI1)
qed

text \<open>De este modo, por los lemas anteriores para los distintos tipos de fórmula \<open>\<beta>\<close>, se
  demuestra que dados \<open>W \<in> C\<close>, \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> tal que 
  \<open>F \<in> W\<close> y \<open>W\<^sub>0\<close> un subconjunto finito de \<open>W\<close>, entonces se tiene que o bien \<open>{\<beta>\<^sub>1,F} \<union> W\<^sub>0\<close> es 
  satisfacible o bien \<open>{\<beta>\<^sub>2,F} \<union> W\<^sub>0\<close> es satisfacible.\<close>

lemma pcp_colecComp_DIS_sat:
  assumes "W \<in> colecComp"
          "Dis F G H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
proof -
  have "(F = G \<^bold>\<or> H \<or> 
        (\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
        (\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<and> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
        F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G)"
    using assms(2) by (simp only: con_dis_simps(2))
  thus ?thesis
  proof (rule disjE)
    assume "F = G \<^bold>\<or> H"
    show "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
      using assms(1) \<open>F = G \<^bold>\<or> H\<close> assms(3,4,5) by (rule pcp_colecComp_DIS_sat1)
  next
    assume "(\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
        (\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<and> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
        F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
    thus ?thesis
    proof (rule disjE)
      assume Ex1:"\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1"
      obtain G1 H1 where C1:"F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1"
        using Ex1 by (iprover elim: exE)
      have "F = G1 \<^bold>\<rightarrow> H1"
        using C1 by (rule conjunct1)
      have "G = \<^bold>\<not> G1"
        using C1 by (iprover elim: conjunct1)
      have "H = H1"
        using C1 by (iprover elim: conjunct2)
      have "sat ({\<^bold>\<not> G1,F} \<union> Wo) \<or> sat ({H1,F} \<union> Wo)"
        using assms(1) \<open>F = G1 \<^bold>\<rightarrow> H1\<close> assms(3,4,5) by (rule pcp_colecComp_DIS_sat2)
      thus "sat ({G, F} \<union> Wo) \<or> sat ({H, F} \<union> Wo)"
        by (simp only: \<open>G = \<^bold>\<not> G1\<close> \<open>H = H1\<close>) 
    next
      assume "(\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<and> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
        F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
      thus ?thesis
      proof (rule disjE)
        assume Ex2:"\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<and> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1"
        obtain G1 H1 where C2:"F = \<^bold>\<not> (G1 \<^bold>\<and> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1"
          using Ex2 by (iprover elim: exE)
        have "F = \<^bold>\<not> (G1 \<^bold>\<and> H1)"
          using C2 by (rule conjunct1)
        have "G = \<^bold>\<not> G1"
          using C2 by (iprover elim: conjunct1)
        have "H = \<^bold>\<not> H1"
          using C2 by (iprover elim: conjunct2)
        have "sat ({\<^bold>\<not> G1,F} \<union> Wo) \<or> sat ({\<^bold>\<not> H1,F} \<union> Wo)"
          using assms(1) \<open>F = \<^bold>\<not> (G1 \<^bold>\<and> H1)\<close> assms(3,4,5) by (rule pcp_colecComp_DIS_sat3)
        thus "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
          by (simp only: \<open>G = \<^bold>\<not> G1\<close> \<open>H = \<^bold>\<not> H1\<close>)
      next
        assume "F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
        then have "F = \<^bold>\<not> (\<^bold>\<not> G)"
          by (rule conjunct1)
        have "H = G"
          using \<open>F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G\<close> by (rule conjunct2)
        show "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
          using assms(1) \<open>F = \<^bold>\<not> (\<^bold>\<not> G)\<close> \<open>H = G\<close> assms(3,4,5) by (rule pcp_colecComp_DIS_sat4)
      qed
    qed
  qed
qed

text \<open>Finalmente, con los lemas auxiliares anteriores podemos demostrar detalladamente la cuarta 
  condición del lema \<open>2.0.2\<close>: dados \<open>W \<in> C\<close> y \<open>F\<close> una fórmula de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y 
  \<open>\<beta>\<^sub>2\<close> tal que \<open>F \<in> W\<close>, se tiene que o bien \<open>{\<beta>\<^sub>1} \<union> W \<in> C\<close> o bien \<open>{\<beta>\<^sub>2} \<union> W \<in> C\<close>.\<close>

lemma pcp_colecComp_DIS:
  assumes "W \<in> colecComp"
  shows "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp"
proof (rule allI)+
  fix F G H
  show "Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp"
  proof (rule impI)+
    assume "Dis F G H"
    assume "F \<in> W"
    show "{G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp"
    proof (rule ccontr)
      assume "\<not>({G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp)"
      then have C:"{G} \<union> W \<notin> colecComp \<and> {H} \<union> W \<notin> colecComp"
        by (simp only: de_Morgan_disj simp_thms(8))
      then have "{G} \<union> W \<notin> colecComp"
        by (rule conjunct1)
      have Ex1:"\<exists>Wo \<subseteq> W. finite Wo \<and> \<not>(sat ({G} \<union> Wo))"
        using assms \<open>{G} \<union> W \<notin> colecComp\<close> by (rule not_colecComp)
      obtain W1 where "W1 \<subseteq> W" and C1:"finite W1 \<and> \<not>(sat ({G} \<union> W1))"
        using Ex1 by (rule subexE)
      have "finite W1"
        using C1 by (rule conjunct1)
      have "\<not>(sat ({G} \<union> W1))"
        using C1 by (rule conjunct2)
      have "{H} \<union> W \<notin> colecComp"
        using C by (rule conjunct2) 
      have Ex2:"\<exists>Wo \<subseteq> W. finite Wo \<and> \<not>(sat ({H} \<union> Wo))"
        using assms \<open>{H} \<union> W \<notin> colecComp\<close> by (rule not_colecComp)
      obtain W2 where "W2 \<subseteq> W" and C2:"finite W2 \<and> \<not>(sat ({H} \<union> W2))"
        using Ex2 by (rule subexE)
      have "finite W2"
        using C2 by (rule conjunct1)
      have "\<not>(sat ({H} \<union> W2))"
        using C2 by (rule conjunct2)
      let ?Wo = "W1 \<union> W2"
      have "?Wo \<subseteq> W"
        using \<open>W1 \<subseteq> W\<close> \<open>W2 \<subseteq> W\<close> by (simp only: Un_least)
      have "finite ?Wo"
        using \<open>finite W1\<close> \<open>finite W2\<close> by (simp only: finite_Un)
      have "{G} \<union> W1 \<subseteq> ({G} \<union> W1) \<union> W2"
        by (simp only: Un_upper1)
      then have "{G} \<union> W1 \<subseteq> {G} \<union> ?Wo"
        by (simp only: Un_assoc)
      then have "{G} \<union> W1 \<subseteq> {G,F} \<union> ?Wo"
        by blast
      then have 1:"\<not>(sat({G,F} \<union> ?Wo))"
        using \<open>\<not>sat ({G} \<union> W1)\<close> by (rule sat_subset_ccontr)
      have "{H} \<union> W2 \<subseteq> ({H} \<union> W2) \<union> W1"
        by (simp only: Un_upper1)
      then have "{H} \<union> W2 \<subseteq> {H} \<union> (W2 \<union> W1)"
        by (simp only: Un_assoc) 
      then have "{H} \<union> W2 \<subseteq> {H} \<union> ?Wo"
        by (simp only: Un_commute)
      then have "{H} \<union> W2 \<subseteq> {H,F} \<union> ?Wo"
        by blast
      then have 2:"\<not>(sat({H,F} \<union> ?Wo))"
        using \<open>\<not>sat ({H} \<union> W2)\<close> by (rule sat_subset_ccontr)
      have "\<not> sat ({G,F} \<union> ?Wo) \<and> \<not> sat ({H,F} \<union> ?Wo)"
        using 1 2 by (rule conjI)
      have "sat ({G,F} \<union> ?Wo) \<or> sat ({H,F} \<union> ?Wo)"
        using assms(1) \<open>Dis F G H\<close> \<open>F \<in> W\<close> \<open>finite ?Wo\<close> \<open>?Wo \<subseteq> W\<close> by (rule pcp_colecComp_DIS_sat)
      then have "\<not>\<not>(sat ({G,F} \<union> ?Wo) \<or> sat ({H,F} \<union> ?Wo))"
        by (simp only: not_not)
      then have "\<not>(\<not>(sat ({G,F} \<union> ?Wo)) \<and> \<not>(sat ({H,F} \<union> ?Wo)))"
        by (simp only: de_Morgan_disj simp_thms(8))
      thus "False"
        using \<open>\<not>(sat ({G,F} \<union> ?Wo)) \<and> \<not>(sat ({H,F} \<union> ?Wo))\<close> by (rule notE)
    qed
  qed
qed

text \<open>En resumen, con los lemas \<open>pcp_colecComp_bot\<close>, \<open>pcp_colecComp_atoms\<close>, \<open>pcp_colecComp_CON\<close> y
  \<open>pcp_colecComp_DIS\<close> podemos probar de manera detallada que la colección \<open>C\<close> verifica la propiedad 
  de consistencia proposicional.\<close>

lemma pcp_colecComp: "pcp colecComp"
proof (rule pcp_alt2)
  show "\<forall>W \<in> colecComp. \<bottom> \<notin> W
        \<and> (\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False)
        \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> colecComp)
        \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp)"
  proof (rule ballI)
    fix W
    assume H:"W \<in> colecComp"
    have C1:"\<bottom> \<notin> W"
      using H by (rule pcp_colecComp_bot)
    have C2:"\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False"
      using H by (rule pcp_colecComp_atoms)
    have C3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> colecComp"
      using H by (rule pcp_colecComp_CON)
    have C4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp"
      using H by (rule pcp_colecComp_DIS)
    show "\<bottom> \<notin> W
          \<and> (\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False)
          \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> colecComp)
          \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> colecComp \<or> {H} \<union> W \<in> colecComp)"
      using C1 C2 C3 C4 by (iprover intro: conjI)
  qed
qed

text \<open>Finalmente, mostremos la demostración del \<open>Teorema de Compacidad\<close>.\<close>

theorem prop_Compactness:
  fixes W :: "'a :: countable formula set"
  assumes "fin_sat W"
  shows "sat W"
proof (rule pcp_sat)
  show "W \<in> colecComp"
    using assms by (simp only: set_in_colecComp)
  show "pcp colecComp"
    by (simp only: pcp_colecComp)
qed

(*<*)
end
(*>*) 
