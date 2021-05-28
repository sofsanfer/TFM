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
  Sea \<open>C\<close> una colección, \<open>S \<in> C\<close> y \<open>F\<^sub>1, F\<^sub>2, F\<^sub>3 \<dots>\<close> una enumeración de 
  las fórmulas proposicionales. Se define la \<open>sucesión de conjuntos de C a partir de S\<close> como sigue:

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
  definidas en dicha teoría. En Isabelle, los conjuntos se formalizan como equivalentes a los 
  predicados, de manera que un elemento pertenece a un conjunto si verifica el predicado que lo 
  caracteriza. De este modo, cada conjunto conforma un retículo cuyo orden parcial establecido es la 
  relación de contención. En consecuencia, los conjuntos de conjuntos forman un retículo completo 
  con dicho orden parcial, de manera que la unión generalizada de conjuntos se formaliza en Isabelle 
  como el supremo del retículo completo que conforman.

\comentario{No sé si está bien explicado.}

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

section \<open>El teorema de existencia de modelo\<close>

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

text \<open>\comentario{Añadir explicación nexo.}

  \begin{teorema}[Teorema de Compacidad]
    Todo conjunto de fórmulas finitamente satisfacible es satisfacible.
  \end{teorema}

  \comentario{Añadir demostracion y nexos.}


\<close>

definition colecComp :: "'a formula set \<Rightarrow> ('a formula set) set"
  where colecComp: "colecComp S = {W. fin_sat W}"

lemma set_in_colecComp: 
  assumes "fin_sat S"
  shows "S \<in> colecComp S"
  unfolding colecComp using assms unfolding fin_sat_def by (rule CollectI)

lemma colecComp_subset_finite: 
  assumes "W \<in> colecComp S"
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

lemma pcp_colecComp_bot:
  assumes "W \<in> (colecComp S)"
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
    by (simp add: sat_def)
  then show False 
    using \<open>sat {\<bottom> :: 'a formula}\<close> by (rule notE)
qed

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

lemma pcp_colecComp_atoms:
  assumes "W \<in> (colecComp S)"
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

(*lemma finite_subset_insert1_alt:
  "\<lbrakk>finite S'; S' \<subseteq> {a} \<union> B \<rbrakk> \<Longrightarrow>
     \<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a} \<union> Wo \<or> S' = Wo)"
proof (induct rule: finite_induct)
  assume "{} \<subseteq> {a} \<union> B"
  have "{} = {}"
    by blast (**Pendiente*)
  then have "{} = {a} \<union> {} \<or> {} = {}"
    by (rule disjI2)
  have "{} \<subseteq> B"
    by blast (*Pendiente*)
  have "finite {}"
    by simp (*Pendiente*)
  then have "finite {} \<and> ({} = {a} \<union> {} \<or> {} = {})"
    using \<open>{} = {a} \<union> {} \<or> {} = {}\<close> by (rule conjI)
  thus "\<exists>Wo \<subseteq> B. finite Wo \<and> ({} = {a} \<union> Wo \<or> {} = Wo)"
    using \<open>{} \<subseteq> B\<close> by smt (*Pendiente*)
next
  fix x A
  assume HI:"\<lbrakk>finite A; A \<subseteq> {a} \<union> B \<rbrakk> \<Longrightarrow> \<exists>Wo\<subseteq>B. finite Wo \<and> (A = {a} \<union> Wo \<or> A = Wo)"
  (*show "\<lbrakk>finite (insert x A); insert x A \<subseteq> {a} \<union> B \<rbrakk> \<Longrightarrow> \<exists>Wo\<subseteq>B. finite Wo \<and> (insert x A = {a} \<union> Wo \<or> insert x A = Wo)"*)
  assume "finite A"
  assume "x \<notin> A"
  (*assume HI:"A \<subseteq> {a} \<union> B \<Longrightarrow> \<exists>Wo\<subseteq>B. finite Wo \<and> (A = {a} \<union> Wo \<or> A = Wo)"*)
  assume "{x} \<union> A \<subseteq> {a} \<union> B"
  then have "A \<subseteq> {a} \<union> B"
    by blast (*Pendiente*)
  have "\<exists>Wo\<subseteq>B. finite Wo \<and> (insert x A = {a} \<union> Wo \<or> insert x A = Wo)"
  proof -
    have Ex1:"\<exists>Wo\<subseteq>B. finite Wo \<and> (A = {a} \<union> Wo \<or> A = Wo)"
      using \<open>finite A\<close> \<open>A \<subseteq> {a} \<union> B\<close> by (rule HI)
    obtain Wo where "Wo \<subseteq> B" and C1:"finite Wo \<and> (A = {a} \<union> Wo \<or> A = Wo)"
      using Ex1 by blast (*Pendiente*)
    have "finite Wo"
      using C1 by (rule conjunct1)
    then have "finite (insert x Wo)"
      by simp (*Pendiente*)
    have "A = {a} \<union> Wo \<or> A = Wo"
      using C1 by (rule conjunct2)
    thus "\<exists>Wo\<subseteq>B. finite Wo \<and> (insert x A = {a} \<union> Wo \<or> insert x A = Wo)"
    proof (rule disjE)
      assume "A = {a} \<union> Wo"
      then have "insert x A = insert x ({a} \<union> Wo)"
        by simp (*Pendiente*)
      then have "insert x A = {a} \<union> (insert x Wo)"
        by blast (*Pendiente*)
      then have 2:"insert x A = {a} \<union> (insert x Wo) \<or> insert x A = (insert x Wo)"
        by (rule disjI1)
      have "finite (insert x Wo) \<and> (insert x A = {a} \<union> (insert x Wo) \<or> insert x A = (insert x Wo))"
        using \<open>finite (insert x Wo)\<close> 2 by (rule conjI)
      thus "\<exists>Wo\<subseteq>B. finite Wo \<and> (insert x A = {a} \<union> Wo \<or> insert x A = Wo)"*)
  (*apply (induct rule: finite_induct)
  apply simp
  apply simp
  apply (erule exE)
  oops*)
 
lemma subexI [intro]: "P A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> \<exists>A\<subseteq>B. P A"
  by blast

lemma finite_subset_insert1:
  assumes "finite S'"
          "S' \<subseteq> {a} \<union> B"
   shows "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a} \<union> Wo \<or> S' = Wo)"
by (metis Diff_empty Diff_insert0 Diff_subset_conv 
     Un_Diff_cancel assms(1) assms(2) finite_Diff insert_Diff insert_is_Un)

lemma finite_subset_insert2:
  assumes "finite S'"
          "S' \<subseteq> {a,b} \<union> B"
        shows "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
proof -
  have "S' \<subseteq> {a} \<union> ({b} \<union> B)"
    using assms(2) by blast
  then have Ex1:"\<exists>Wo \<subseteq> ({b} \<union> B). finite Wo \<and> (S' = {a} \<union> Wo \<or> S' = Wo)"
    using assms(1) by (simp only: finite_subset_insert1)
  obtain Wo where "Wo \<subseteq> {b} \<union> B" and 1:"finite Wo \<and> (S' = {a} \<union> Wo \<or> S' = Wo)"
    using Ex1 by (rule subexE)
  have "finite Wo"
    using 1 by (rule conjunct1)
  have Ex2:"\<exists>Wo' \<subseteq> B. finite Wo' \<and> (Wo = {b} \<union> Wo' \<or> Wo = Wo')"
    using \<open>finite Wo\<close> \<open>Wo \<subseteq> {b} \<union> B\<close> by (rule finite_subset_insert1)
  obtain Wo' where "Wo' \<subseteq> B" and 2:"finite Wo' \<and> (Wo = {b} \<union> Wo' \<or> Wo = Wo')"
    using Ex2 by (rule subexE)
  have "finite Wo'"
    using 2 by (rule conjunct1)
  have "Wo = {b} \<union> Wo' \<or> Wo = Wo'"
    using 2 by (rule conjunct2)
  thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
  proof (rule disjE)
    assume "Wo = {b} \<union> Wo'"
    have "S' = {a} \<union> Wo \<or> S' = Wo"
      using 1 by (rule conjunct2)
    thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
    proof (rule disjE)
      assume "S' = {a} \<union> Wo"
      then have "S' = {a} \<union> {b} \<union> Wo'"
        by (simp add: \<open>Wo = {b} \<union> Wo'\<close>)
      then have "S' = {a,b} \<union> Wo'"
        by blast
      then have "S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo'"
        by (iprover intro: disjI1)
      then have "finite Wo' \<and> (S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo')"
        using \<open>finite Wo'\<close> by (iprover intro: conjI)
      thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
        using \<open>Wo' \<subseteq> B\<close> by (rule subexI)
    next
      assume "S' = Wo"
      then have "S' = {b} \<union> Wo'"
        by (simp add: \<open>Wo = {b} \<union> Wo'\<close>)
      then have "S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo'"
        by (iprover intro: disjI1)
      then have "finite Wo' \<and> (S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo')"
        using \<open>finite Wo'\<close> by (iprover intro: conjI)
      thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
        using \<open>Wo' \<subseteq> B\<close> by (rule subexI)
    qed
  next
    assume "Wo = Wo'"
    have "S' = {a} \<union> Wo \<or> S' = Wo"
      using 1 by (rule conjunct2)
    thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
    proof (rule disjE)
      assume "S' = {a} \<union> Wo"
      then have "S' = {a} \<union> Wo'"
        by (simp add: \<open>Wo = Wo'\<close>)
      then have "S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo'"
        by (iprover intro: disjI1)
      then have "finite Wo' \<and> (S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo')"
        using \<open>finite Wo'\<close> by (iprover intro: conjI)
      thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
        using \<open>Wo' \<subseteq> B\<close> by (rule subexI)
    next
      assume "S' = Wo"
      then have "S' = Wo'"
        by (simp add: \<open>Wo = Wo'\<close>)
      then have "S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo'"
        by (iprover intro: disjI1)
      then have "finite Wo' \<and> (S' = {a,b} \<union> Wo' \<or> S' = {a} \<union> Wo' \<or> S' = {b} \<union> Wo' \<or> S' = Wo')"
        using \<open>finite Wo'\<close> by (iprover intro: conjI)
      thus "\<exists>Wo \<subseteq> B. finite Wo \<and> (S' = {a,b} \<union> Wo \<or> S' = {a} \<union> Wo \<or> S' = {b} \<union> Wo \<or> S' = Wo)"
        using \<open>Wo' \<subseteq> B\<close> by (rule subexI)
    qed
  qed
qed

lemma pcp_colecComp_elem_sat:
  assumes "W \<in> (colecComp S)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({F} \<union> Wo)"
proof -
  have "finite ({F} \<union> Wo)"
    using assms(3) by blast (*Pendiente*)
  have "{F} \<union> Wo \<subseteq> W"
    using assms(2) assms(4) by blast (*Pendiente*)
  show "sat ({F} \<union> Wo)"
    using assms(1) \<open>{F} \<union> Wo \<subseteq> W\<close> \<open>finite ({F} \<union> Wo)\<close> by (rule colecComp_subset_finite)
qed

lemma pcp_colecComp_CON_sat1:
  assumes "W \<in> (colecComp S)"
          "F = G \<^bold>\<and> H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp (*Pendiente*)
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
  have "\<A> \<Turnstile> H"
    using \<open>\<A> \<Turnstile> G \<and> \<A> \<Turnstile> H\<close> by (rule conjunct2)
  have "\<forall>F \<in> {G,H,F} \<union> Wo. \<A> \<Turnstile> F"
    using Forall1 \<open>\<A> \<Turnstile> G\<close> \<open>\<A> \<Turnstile> H\<close> by blast (*Pendiente*)
  then have "\<exists>\<A>. \<forall>F \<in> ({G,H,F} \<union> Wo). \<A> \<Turnstile> F"
    by blast (*Pendiente*)
  thus "sat ({G,H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

lemma pcp_colecComp_CON_sat2:
  assumes "W \<in> (colecComp S)"
          "F = \<^bold>\<not>(G \<^bold>\<or> H)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp (*Pendiente*)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(G \<^bold>\<or> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not>(\<A> \<Turnstile> (G \<^bold>\<or> H))"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*)
  then have "\<not>(\<A> \<Turnstile> G \<or> \<A> \<Turnstile> H)"
    by (simp add: formula_semantics.simps(5)) (*Pendiente*)
  then have "\<not> \<A> \<Turnstile> G \<and> \<not> \<A> \<Turnstile> H"
    by simp (*Pendiente*)
  then have "\<A> \<Turnstile> \<^bold>\<not> G \<and> \<A> \<Turnstile> \<^bold>\<not> H"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*) 
  then have "\<A> \<Turnstile> \<^bold>\<not> G"
    by (rule conjunct1)
  have "\<A> \<Turnstile> \<^bold>\<not> H"
    using \<open>\<A> \<Turnstile> \<^bold>\<not> G \<and> \<A> \<Turnstile> \<^bold>\<not> H\<close> by (rule conjunct2)
  have "\<forall>F \<in> {\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo. \<A> \<Turnstile> F"
    using Forall1 \<open>\<A> \<Turnstile> \<^bold>\<not> G\<close> \<open>\<A> \<Turnstile> \<^bold>\<not> H\<close> by blast (*Pendiente*)
  then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo). \<A> \<Turnstile> F"
    by blast (*Pendiente*)
  thus "sat ({\<^bold>\<not> G,\<^bold>\<not> H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

lemma pcp_colecComp_CON_sat3:
  assumes "W \<in> (colecComp S)"
          "F = \<^bold>\<not> (G \<^bold>\<rightarrow> H)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,\<^bold>\<not> H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp (*Pendiente*)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(G \<^bold>\<rightarrow> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not>(\<A> \<Turnstile> (G \<^bold>\<rightarrow> H))"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*)
  then have "\<not>(\<A> \<Turnstile> G \<longrightarrow> \<A> \<Turnstile> H)"
    by (simp add: formula_semantics.simps(6)) (*Pendiente*)
  then have "\<A> \<Turnstile> G \<and> \<not> \<A> \<Turnstile> H"
    by simp (*Pendiente*)
  then have "\<A> \<Turnstile> G \<and> \<A> \<Turnstile> \<^bold>\<not> H"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*) 
  then have "\<A> \<Turnstile> G"
    by (rule conjunct1)
  have "\<A> \<Turnstile> \<^bold>\<not> H"
    using \<open>\<A> \<Turnstile> G \<and> \<A> \<Turnstile> \<^bold>\<not> H\<close> by (rule conjunct2)
  have "\<forall>F \<in> {G,\<^bold>\<not> H,F} \<union> Wo. \<A> \<Turnstile> F"
    using Forall1 \<open>\<A> \<Turnstile> G\<close> \<open>\<A> \<Turnstile> \<^bold>\<not> H\<close> by blast (*Pendiente*)
  then have "\<exists>\<A>. \<forall>F \<in> ({G,\<^bold>\<not> H,F} \<union> Wo). \<A> \<Turnstile> F"
    by blast (*Pendiente*)
  thus "sat ({G,\<^bold>\<not> H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

lemma pcp_colecComp_CON_sat4:
  assumes "W \<in> (colecComp S)"
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
    by simp (*Pendiente*)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(\<^bold>\<not> G)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not> \<A> \<Turnstile> \<^bold>\<not> G"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*)
  then have "\<not> \<not>\<A> \<Turnstile> G"
    by (simp add: formula_semantics.simps(3))
  then have "\<A> \<Turnstile> G"
    by (rule notnotD)
  then have "\<A> \<Turnstile> H"
    by (simp only: \<open>H = G\<close>)
  have "\<forall>F \<in> {G,H,F} \<union> Wo. \<A> \<Turnstile> F"
    using Forall1 \<open>\<A> \<Turnstile> G\<close> \<open>\<A> \<Turnstile> H\<close> by blast (*Pendiente*)
  then have "\<exists>\<A>. \<forall>F \<in> ({G,H,F} \<union> Wo). \<A> \<Turnstile> F"
    by blast (*Pendiente*)
  thus "sat ({G,H,F} \<union> Wo)"
    by (simp only: sat_def)
qed

lemma pcp_colecComp_CON_sat:
  assumes "W \<in> (colecComp S)"
          "Con F G H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,H} \<union> Wo)"
proof -
  have "{G,H} \<union> Wo \<subseteq> {G,H,F} \<union> Wo"
    by blast (*Pendiente*)
  have "F = G \<^bold>\<and> H \<or> 
    (\<exists>F1 G1. F = \<^bold>\<not> (F1 \<^bold>\<or> G1) \<and> G = \<^bold>\<not> F1 \<and> H = \<^bold>\<not> G1) \<or> 
    (\<exists>H1. F = \<^bold>\<not> (G \<^bold>\<rightarrow> H1) \<and> H = \<^bold>\<not> H1) \<or> 
    F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
    using assms(2) by (simp only: con_dis_simps(1))
  then have "sat ({G,H,F} \<union> Wo)"
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
  thus "sat ({G,H} \<union> Wo)"
    using \<open>{G,H} \<union> Wo \<subseteq> {G,H,F} \<union> Wo\<close> by (simp only: sat_mono)
qed
      
lemma pcp_colecComp_CON:
  assumes "W \<in> (colecComp S)"
  shows "\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> (colecComp S)"
proof (rule allI)+
  fix F G H
  show "Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> (colecComp S)"
  proof (rule impI)+
    assume "Con F G H"
    assume "F \<in> W"
    show "{G,H} \<union> W \<in> (colecComp S)"
      unfolding colecComp fin_sat_def
    proof (rule CollectI)
      show "\<forall>S' \<subseteq> {G,H} \<union> W. finite S' \<longrightarrow> sat S'"
      proof (rule sallI)
        fix S'
        assume "S' \<subseteq> {G,H} \<union> W"
        then have "S' \<subseteq> {G} \<union> ({H} \<union> W)"
          by blast (*Pendiente*)
        show "finite S' \<longrightarrow> sat S'"
        proof (rule impI)
          assume "finite S'" 
          have Ex:"\<exists>Wo \<subseteq> W. finite Wo \<and> (S' = {G,H} \<union> Wo \<or> S' = {G} \<union> Wo \<or> S' = {H} \<union> Wo \<or> S' = Wo)"
            using \<open>finite S'\<close> \<open>S' \<subseteq> {G,H} \<union> W\<close> by (rule finite_subset_insert2)
          obtain Wo' where "Wo' \<subseteq> W" and 1:"finite Wo' \<and> (S' = {G,H} \<union> Wo' \<or> S' = {G} \<union> Wo' \<or> S' = {H} \<union> Wo' \<or> S' = Wo')"
            using Ex by blast (*Pendiente*)
          have "finite Wo'"
            using 1 by (rule conjunct1)
            have "sat ({G,H} \<union> Wo')" 
              using \<open>W \<in> (colecComp S)\<close> \<open>Con F G H\<close> \<open>F \<in> W\<close> \<open>finite Wo'\<close> \<open>Wo' \<subseteq> W\<close> by (rule pcp_colecComp_CON_sat)
          have "S' = {G,H} \<union> Wo' \<or> S' = {G} \<union> Wo' \<or> S' = {H} \<union> Wo' \<or> S' = Wo'"
            using 1 by (rule conjunct2)
          thus "sat S'"
          proof (rule disjE)
            assume "S' = {G,H} \<union> Wo'"
            show "sat S'"
              using \<open>sat({G,H} \<union> Wo')\<close> by (simp only: \<open>S' = {G,H} \<union> Wo'\<close>)
          next
            assume "S' = {G} \<union> Wo' \<or> S' = {H} \<union> Wo' \<or> S' = Wo'"
            thus "sat S'"
            proof (rule disjE)
              assume "S' = {G} \<union> Wo'"
              then have "S' \<subseteq> {G,H} \<union> Wo'"
                by blast (*Pendiente*)
              thus "sat S'"
                using \<open>sat({G,H} \<union> Wo')\<close> by (rule sat_mono)
            next
              assume "S' = {H} \<union> Wo' \<or> S' = Wo'"
              thus "sat S'"
              proof (rule disjE)
                assume "S' = {H} \<union> Wo'"
                then have "S' \<subseteq> {G,H} \<union> Wo'"
                  by blast (*Pendiente*)
                thus "sat S'"
                  using \<open>sat({G,H} \<union> Wo')\<close> by (rule sat_mono)
              next
                assume "S' = Wo'"
                then have "S' \<subseteq> {G,H} \<union> Wo'"
                  by blast (*Pendiente*)
                thus "sat S'"
                  using \<open>sat({G,H} \<union> Wo')\<close> by (rule sat_mono)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma pcp_colecComp_DIS_sat1:
  assumes "W \<in> (colecComp S)"
          "F = G \<^bold>\<or> H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp (*Pendiente*)
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
    have "\<forall>F \<in> {G,F} \<union> Wo. \<A> \<Turnstile> F"
      using Forall1 \<open>\<A> \<Turnstile> G\<close> by blast (*Pendiente*)
    then have "\<exists>\<A>. \<forall>F \<in> ({G,F} \<union> Wo). \<A> \<Turnstile> F"
      by blast (*Pendiente*)
    then have "sat ({G,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI1)
  next
    assume "\<A> \<Turnstile> H"
    have "\<forall>F \<in> {H,F} \<union> Wo. \<A> \<Turnstile> F"
      using Forall1 \<open>\<A> \<Turnstile>H\<close> by blast (*Pendiente*)
    then have "\<exists>\<A>. \<forall>F \<in> ({H,F} \<union> Wo). \<A> \<Turnstile> F"
      by blast (*Pendiente*)
    then have "sat ({H,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI2)
  qed
qed

lemma pcp_colecComp_DIS_sat2:
  assumes "W \<in> (colecComp S)"
          "F = G \<^bold>\<rightarrow> H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({\<^bold>\<not> G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp (*Pendiente*)
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
    by blast (*Pendiente*)
  then have "(\<not> \<A> \<Turnstile> G) \<or> \<A> \<Turnstile> H"
    by blast (*Pendiente*)
  thus ?thesis
  proof (rule disjE)
    assume "\<not> \<A> \<Turnstile> G"
    then have "\<A> \<Turnstile> (\<^bold>\<not> G)"
      by (simp add: formula_semantics.simps(3)) (*Pendiente*)
    have "\<forall>F \<in> {\<^bold>\<not> G,F} \<union> Wo. \<A> \<Turnstile> F"
      using Forall1 \<open>\<A> \<Turnstile> (\<^bold>\<not> G)\<close> by blast (*Pendiente*)
    then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> G,F} \<union> Wo). \<A> \<Turnstile> F"
      by blast (*Pendiente*)
    then have "sat ({\<^bold>\<not> G,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI1)
  next
    assume "\<A> \<Turnstile> H"
    have "\<forall>F \<in> {H,F} \<union> Wo. \<A> \<Turnstile> F"
      using Forall1 \<open>\<A> \<Turnstile>H\<close> by blast (*Pendiente*)
    then have "\<exists>\<A>. \<forall>F \<in> ({H,F} \<union> Wo). \<A> \<Turnstile> F"
      by blast (*Pendiente*)
    then have "sat ({H,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI2)
  qed
qed

lemma pcp_colecComp_DIS_sat3:
  assumes "W \<in> (colecComp S)"
          "F = \<^bold>\<not> (G \<^bold>\<and> H)"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({\<^bold>\<not> G,F} \<union> Wo) \<or> sat ({\<^bold>\<not> H,F} \<union> Wo)"
proof -
  have "sat ({F} \<union> Wo)"
    using assms(1,3,4,5) by (rule pcp_colecComp_elem_sat)
  have "F \<in> {F} \<union> Wo"
    by simp (*Pendiente*)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not> (G \<^bold>\<and> H)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not> (\<A> \<Turnstile> (G \<^bold>\<and> H))"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*)
  then have "\<not>(\<A> \<Turnstile> G \<and> \<A> \<Turnstile> H)"
    by (simp add: formula_semantics.simps(4)) (*Pendiente*)
  then have "\<not> (\<A> \<Turnstile> G) \<or> \<not> (\<A> \<Turnstile> H)"
    by blast (*Pendiente*)
  thus ?thesis
  proof (rule disjE)
    assume "\<not> (\<A> \<Turnstile> G)"
    then have "\<A> \<Turnstile> \<^bold>\<not> G"
      by (simp add: formula_semantics.simps(3))
    have "\<forall>F \<in> {\<^bold>\<not> G,F} \<union> Wo. \<A> \<Turnstile> F"
      using Forall1 \<open>\<A> \<Turnstile> \<^bold>\<not> G\<close> by blast (*Pendiente*)
    then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> G,F} \<union> Wo). \<A> \<Turnstile> F"
      by blast (*Pendiente*)
    then have "sat ({\<^bold>\<not> G,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI1)
  next
    assume "\<not> (\<A> \<Turnstile> H)"
    then have "\<A> \<Turnstile> \<^bold>\<not> H"
      by (simp add: formula_semantics.simps(3)) (*Pendiente*)
    have "\<forall>F \<in> {\<^bold>\<not> H,F} \<union> Wo. \<A> \<Turnstile> F"
      using Forall1 \<open>\<A> \<Turnstile> \<^bold>\<not> H\<close> by blast (*Pendiente*)
    then have "\<exists>\<A>. \<forall>F \<in> ({\<^bold>\<not> H,F} \<union> Wo). \<A> \<Turnstile> F"
      by blast (*Pendiente*)
    then have "sat ({\<^bold>\<not> H,F} \<union> Wo)"
      by (simp only: sat_def)
    thus ?thesis
      by (rule disjI2)
  qed
qed

lemma pcp_colecComp_DIS_sat4:
  assumes "W \<in> (colecComp S)"
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
    by simp (*Pendiente*)
  have Ex1:"\<exists>\<A>. \<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using \<open>sat ({F} \<union> Wo)\<close> by (simp only: sat_def)
  obtain \<A> where Forall1:"\<forall>F \<in> ({F} \<union> Wo). \<A> \<Turnstile> F"
    using Ex1 by (rule exE)
  have "\<A> \<Turnstile> F"
    using Forall1 \<open>F \<in> {F} \<union> Wo\<close> by (rule bspec)
  then have "\<A> \<Turnstile> \<^bold>\<not>(\<^bold>\<not> G)"
    using assms(2) by (simp only: \<open>\<A> \<Turnstile> F\<close>)
  then have "\<not> \<A> \<Turnstile> \<^bold>\<not> G"
    by (simp add: formula_semantics.simps(3)) (*Pendiente*)
  then have "\<not> \<not>\<A> \<Turnstile> G"
    by (simp add: formula_semantics.simps(3))
  then have "\<A> \<Turnstile> G"
    by (rule notnotD)
  have "\<forall>F \<in> {G,F} \<union> Wo. \<A> \<Turnstile> F"
    using Forall1 \<open>\<A> \<Turnstile> G\<close> by blast (*Pendiente*)
  then have "\<exists>\<A>. \<forall>F \<in> ({G,F} \<union> Wo). \<A> \<Turnstile> F"
    by blast (*Pendiente*)
  then have "sat ({G,F} \<union> Wo)"
    by (simp only: sat_def)
  thus ?thesis
    by (rule disjI1)
qed

lemma pcp_colecComp_DIS_sat:
  assumes "W \<in> (colecComp S)"
          "Dis F G H"
          "F \<in> W"
          "finite Wo"
          "Wo \<subseteq> W"
        shows "sat ({G} \<union> Wo) \<or> sat ({H} \<union> Wo)"
proof -
  have "(F = G \<^bold>\<or> H \<or> 
        (\<exists>G1 H1. F = G1 \<^bold>\<rightarrow> H1 \<and> G = \<^bold>\<not> G1 \<and> H = H1) \<or> 
        (\<exists>G1 H1. F = \<^bold>\<not> (G1 \<^bold>\<and> H1) \<and> G = \<^bold>\<not> G1 \<and> H = \<^bold>\<not> H1) \<or> 
        F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G)"
    using assms(2) by (simp only: con_dis_simps(2))
  thus ?thesis
  proof (rule disjE)
    assume "F = G \<^bold>\<or> H"
    have "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
      using assms(1) \<open>F = G \<^bold>\<or> H\<close> assms(3,4,5) by (rule pcp_colecComp_DIS_sat1)
    thus ?thesis
    proof (rule disjE)
      assume "sat ({G,F} \<union> Wo)"
      have "{G} \<union> Wo \<subseteq> {G,F} \<union> Wo"
        by blast (*Pendiente*)
      then have "sat({G} \<union> Wo)"
        using \<open>sat({G,F} \<union> Wo)\<close> by (rule sat_mono)
      thus ?thesis
        by (rule disjI1)
    next
      assume "sat ({H,F} \<union> Wo)"
      have "{H} \<union> Wo \<subseteq> {H,F} \<union> Wo"
        by blast (*Pendiente*)
      then have "sat({H} \<union> Wo)"
        using \<open>sat({H,F} \<union> Wo)\<close> by (rule sat_mono)
      thus ?thesis
        by (rule disjI2)
    qed
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
      thus ?thesis
      proof (rule disjE)
        assume "sat ({\<^bold>\<not> G1,F} \<union> Wo)"
        have "{\<^bold>\<not> G1} \<union> Wo \<subseteq> {\<^bold>\<not> G1,F} \<union> Wo"
          by blast (*Pendiente*)
        then have "sat({\<^bold>\<not> G1} \<union> Wo)"
          using \<open>sat({\<^bold>\<not> G1,F} \<union> Wo)\<close> by (rule sat_mono)
        then have "sat({G} \<union> Wo)"
          by (simp only: \<open>G = \<^bold>\<not> G1\<close>)
        thus ?thesis
          by (rule disjI1)
    next
        assume "sat ({H1,F} \<union> Wo)"
        have "{H1} \<union> Wo \<subseteq> {H1,F} \<union> Wo"
          by blast (*Pendiente*)
        then have "sat({H1} \<union> Wo)"
          using \<open>sat({H1,F} \<union> Wo)\<close> by (rule sat_mono)
        then have "sat({H} \<union> Wo)"
          by (simp only: \<open>H = H1\<close>)
        thus ?thesis
          by (rule disjI2)
      qed
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
        thus ?thesis
        proof (rule disjE)
          assume "sat ({\<^bold>\<not> G1,F} \<union> Wo)"
          have "{\<^bold>\<not> G1} \<union> Wo \<subseteq> {\<^bold>\<not> G1,F} \<union> Wo"
            by blast (*Pendiente*)
          then have "sat({\<^bold>\<not> G1} \<union> Wo)"
            using \<open>sat({\<^bold>\<not> G1,F} \<union> Wo)\<close> by (rule sat_mono)
          then have "sat({G} \<union> Wo)"
            by (simp only: \<open>G = \<^bold>\<not> G1\<close>)
          thus ?thesis
            by (rule disjI1)
        next
          assume "sat ({\<^bold>\<not> H1,F} \<union> Wo)"
          have "{\<^bold>\<not> H1} \<union> Wo \<subseteq> {\<^bold>\<not> H1,F} \<union> Wo"
            by blast (*Pendiente*)
          then have "sat({\<^bold>\<not> H1} \<union> Wo)"
            using \<open>sat({\<^bold>\<not> H1,F} \<union> Wo)\<close> by (rule sat_mono)
          then have "sat({H} \<union> Wo)"
            by (simp only: \<open>H = \<^bold>\<not> H1\<close>)
          thus ?thesis
            by (rule disjI2)
        qed
      next
        assume "F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G"
        then have "F = \<^bold>\<not> (\<^bold>\<not> G)"
          by (rule conjunct1)
        have "H = G"
          using \<open>F = \<^bold>\<not> (\<^bold>\<not> G) \<and> H = G\<close> by (rule conjunct2)
        have "sat ({G,F} \<union> Wo) \<or> sat ({H,F} \<union> Wo)"
          using assms(1) \<open>F = \<^bold>\<not> (\<^bold>\<not> G)\<close> \<open>H = G\<close> assms(3,4,5) by (rule pcp_colecComp_DIS_sat4)
        thus ?thesis
        proof (rule disjE)
          assume "sat ({G,F} \<union> Wo)"
          have "{G} \<union> Wo \<subseteq> {G,F} \<union> Wo"
            by blast (*Pendiente*)
          then have "sat({G} \<union> Wo)"
            using \<open>sat({G,F} \<union> Wo)\<close> by (rule sat_mono)
          thus ?thesis
            by (rule disjI1)
        next
          assume "sat ({H,F} \<union> Wo)"
          have "{H} \<union> Wo \<subseteq> {H,F} \<union> Wo"
            by blast (*Pendiente*)
          then have "sat({H} \<union> Wo)"
            using \<open>sat({H,F} \<union> Wo)\<close> by (rule sat_mono)
          thus ?thesis
            by (rule disjI2)
        qed
      qed
    qed
  qed
qed

lemma sat_subset_ccontr:
  assumes "A \<subseteq> B"
          "\<not> sat A"
        shows "\<not> sat B"
  using assms(1) assms(2) sat_mono by blast (*Pendiente*)

lemma not_colecComp:
  assumes "W \<in> (colecComp S)"
          "{x} \<union> W \<notin> (colecComp S)"
        shows "\<exists>Wo \<subseteq> W. finite Wo \<and> \<not>(sat ({x} \<union> Wo))"
proof -
  have WCol:"\<forall>S' \<subseteq> W. finite S' \<longrightarrow> sat S'"
    using assms(1) unfolding colecComp fin_sat_def by (rule CollectD) 
  have "\<not>(\<forall>Wo \<subseteq> {x} \<union> W. finite Wo \<longrightarrow> sat Wo)"
    using assms(2) unfolding colecComp fin_sat_def by blast (*Pendiente*)
  then have "\<exists>Wo \<subseteq> {x} \<union> W. \<not>(finite Wo \<longrightarrow> sat Wo)"
    by blast (*Pendiente*)
  then have Ex1:"\<exists>Wo \<subseteq> {x} \<union> W. finite Wo \<and> \<not>(sat Wo)"
    by blast (*Pendiente*)
  obtain Wo' where "Wo' \<subseteq> {x} \<union> W" and C1:"finite Wo' \<and> \<not>(sat Wo')"
    using Ex1 by blast (*Pendiente*)
  have "finite Wo'"
    using C1 by (rule conjunct1)
  have "\<not>(sat Wo')"
    using C1 by (rule conjunct2)
  have Ex2:"\<exists>Wo \<subseteq> W. finite Wo \<and> (Wo' = {x} \<union> Wo \<or> Wo' = Wo)"
    using \<open>finite Wo'\<close> \<open>Wo' \<subseteq> {x} \<union> W\<close> by (rule finite_subset_insert1)
  obtain Wo where "Wo \<subseteq> W" and C2:"finite Wo \<and> (Wo' = {x} \<union> Wo \<or> Wo' = Wo)"
    using Ex2 by blast
  have "finite Wo"
    using C2 by (rule conjunct1)
  have "Wo' = {x} \<union> Wo \<or> Wo' = Wo"
    using C2 by (rule conjunct2)
  thus ?thesis
  proof (rule disjE)
    assume "Wo' = {x} \<union> Wo"
    then have "\<not>(sat ({x} \<union> Wo))" try
      using \<open>\<not> sat Wo'\<close> by blast (*Pendiente*)
    have "finite Wo \<and> \<not>(sat ({x} \<union> Wo))"
      using \<open>finite Wo\<close> \<open>\<not>(sat ({x} \<union> Wo))\<close> by (rule conjI)
    thus "\<exists>Wo \<subseteq> W. finite Wo \<and> \<not>(sat ({x} \<union> Wo))"
      using \<open>Wo \<subseteq> W\<close> by blast (*Pendiente*)
  next
    assume "Wo' = Wo"
    then have "Wo' \<subseteq> W"
      using \<open>Wo \<subseteq> W\<close> by blast (*Pendiente*)
    have "finite Wo' \<longrightarrow> sat Wo'"
      using WCol \<open>Wo' \<subseteq> W\<close> by blast (*Pendiente*)
    then have "sat Wo'"
      using \<open>finite Wo'\<close> by (rule mp)
    show ?thesis
      using \<open>\<not> sat Wo'\<close> \<open>sat Wo'\<close> by (rule notE)
  qed
qed

lemma pcp_colecComp_DIS:
  assumes "W \<in> (colecComp S)"
  shows "\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S)"
proof (rule allI)+
  fix F G H
  show "Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S)"
  proof (rule impI)+
    assume "Dis F G H"
    assume "F \<in> W"
    show "{G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S)"
    proof (rule ccontr)
      assume "\<not>({G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S))"
      then have C:"{G} \<union> W \<notin> (colecComp S) \<and> {H} \<union> W \<notin> (colecComp S)"
        by blast (*PEndiente*)
      then have "{G} \<union> W \<notin> (colecComp S)"
        by (rule conjunct1)
      have Ex1:"\<exists>Wo \<subseteq> W. finite Wo \<and> \<not>(sat ({G} \<union> Wo))"
        using assms \<open>{G} \<union> W \<notin> (colecComp S)\<close> by (rule not_colecComp)
      obtain W1 where "W1 \<subseteq> W" and C1:"finite W1 \<and> \<not>(sat ({G} \<union> W1))"
        using Ex1 by blast
      have "finite W1"
        using C1 by (rule conjunct1)
      have "\<not>(sat ({G} \<union> W1))"
        using C1 by (rule conjunct2)
      have "{H} \<union> W \<notin> (colecComp S)"
        using C by (rule conjunct2) 
      have Ex2:"\<exists>Wo \<subseteq> W. finite Wo \<and> \<not>(sat ({H} \<union> Wo))"
        using assms \<open>{H} \<union> W \<notin> (colecComp S)\<close> by (rule not_colecComp)
      obtain W2 where "W2 \<subseteq> W" and C2:"finite W2 \<and> \<not>(sat ({H} \<union> W2))"
        using Ex2 by blast
      have "finite W2"
        using C2 by (rule conjunct1)
      have "\<not>(sat ({H} \<union> W2))"
        using C2 by (rule conjunct2)
      let ?Wo = "W1 \<union> W2"
      have "?Wo \<subseteq> W"
        using \<open>W1 \<subseteq> W\<close> \<open>W2 \<subseteq> W\<close> by blast (*Pendiente*)
      have "finite ?Wo"
        using \<open>finite W1\<close> \<open>finite W2\<close> by blast (*Pendiente*)
      have "{G} \<union> W1 \<subseteq> {G} \<union> ?Wo"
        by blast (*Pendiente*)
      have "\<not> sat ({G} \<union> ?Wo)"
        using \<open>{G} \<union> W1 \<subseteq> {G} \<union> ?Wo\<close> \<open>\<not> sat ({G} \<union> W1)\<close> by (rule sat_subset_ccontr)
      have "{H} \<union> W2 \<subseteq> {H} \<union> ?Wo"
        by blast (*Pendiente*)
      have "\<not> sat ({H} \<union> ?Wo)"
        using \<open>{H} \<union> W2 \<subseteq> {H} \<union> ?Wo\<close> \<open>\<not> sat ({H} \<union> W2)\<close> by (rule sat_subset_ccontr)
      have "\<not> sat ({G} \<union> ?Wo) \<and> \<not> sat ({H} \<union> ?Wo)"
        using \<open>\<not> sat ({G} \<union> ?Wo)\<close> \<open>\<not> sat ({H} \<union> ?Wo)\<close> by (rule conjI)
      have "sat ({G} \<union> ?Wo) \<or> sat ({H} \<union> ?Wo)"
        using assms(1) \<open>Dis F G H\<close> \<open>F \<in> W\<close> \<open>finite ?Wo\<close> \<open>?Wo \<subseteq> W\<close> by (rule pcp_colecComp_DIS_sat)
      then have "\<not>\<not>(sat ({G} \<union> ?Wo) \<or> sat ({H} \<union> ?Wo))"
        by blast (*Pendiente*)
      then have "\<not>(\<not>(sat ({G} \<union> ?Wo)) \<and> \<not>(sat ({H} \<union> ?Wo)))"
        by blast (*Pendiente*)
      thus "False"
        using \<open>\<not>(sat ({G} \<union> ?Wo)) \<and> \<not>(sat ({H} \<union> ?Wo))\<close> by (rule notE)
    qed
  qed
qed

lemma pcp_colecComp: "pcp (colecComp S)"
proof (rule pcp_alt2)
  show "\<forall>W \<in> (colecComp S). \<bottom> \<notin> W
        \<and> (\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False)
        \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> (colecComp S))
        \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S))"
  proof (rule ballI)
    fix W
    assume H:"W \<in> (colecComp S)"
    have C1:"\<bottom> \<notin> W"
      using H by (rule pcp_colecComp_bot)
    have C2:"\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False"
      using H by (rule pcp_colecComp_atoms)
    have C3:"\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> (colecComp S)"
      using H by (rule pcp_colecComp_CON)
    have C4:"\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S)"
      using H by (rule pcp_colecComp_DIS)
    show "\<bottom> \<notin> W
          \<and> (\<forall>k. Atom k \<in> W \<longrightarrow> \<^bold>\<not> (Atom k) \<in> W \<longrightarrow> False)
          \<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> W \<longrightarrow> {G,H} \<union> W \<in> (colecComp S))
          \<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> W \<longrightarrow> {G} \<union> W \<in> (colecComp S) \<or> {H} \<union> W \<in> (colecComp S))"
      using C1 C2 C3 C4 by (iprover intro: conjI)
  qed
qed

lemma prop_Compactness:
  assumes "fin_sat S"
  shows "sat S"
  oops

lemma prop_Compactness_aut:"fin_sat S \<Longrightarrow> sat S"
  oops

(*<*)
end
(*>*) 
