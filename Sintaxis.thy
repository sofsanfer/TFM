(*<*) 
theory Sintaxis
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*) 

(* chapter \<open>Sintaxis\<close> *)

section \<open>Fórmulas\<close>

text \<open>En esta sección presentaremos una formalización en Isabelle de la 
  sintaxis de la lógica proposicional, junto con resultados y pruebas 
  sobre la misma. En líneas generales, primero daremos las nociones de 
  forma clásica y, a continuación, su correspondiente formalización.

  En primer lugar, supondremos que disponemos de los siguientes 
  elementos:
  \begin{description}
    \item[Alfabeto:] Es una lista infinita de variables proposicionales. 
      También pueden ser llamadas átomos o símbolos proposicionales.
    \item[Conectivas:] Conjunto finito cuyos elementos interactúan con 
      las variables. Pueden ser monarias que afectan a un único elemento 
      o binarias que afectan a dos. En el primer grupo se encuentra la 
      negación (\<open>\<not>\<close>) y en el segundo la conjunción (\<open>\<and>\<close>), la disyunción 
      (\<open>\<or>\<close>) y la implicación (\<open>\<longrightarrow>\<close>).
  \end{description}

  A continuación definiremos la estructura de fórmula sobre los 
  elementos anteriores. Para ello daremos una definición recursiva 
  basada en dos elementos: un conjunto de fórmulas básicas y una serie 
  de procedimientos de definición de fórmulas a partir de otras. El 
  conjunto de las fórmulas será el menor conjunto de estructuras 
  sintácticas con dicho alfabeto y conectivas que contiene a las básicas 
  y es cerrado mediante los procedimientos de definición que mostraremos 
  a continuación.

  \begin{definicion}
    El conjunto de las fórmulas proposicionales está formado por las 
    siguientes:
    \begin{itemize}
      \item Las fórmulas atómicas, constituidas únicamente por una 
        variable del alfabeto. 
      \item La constante \<open>\<bottom>\<close>.
      \item Dada una fórmula \<open>F\<close>, la negación \<open>\<not> F\<close> es una fórmula.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la conjunción \<open>F \<and> G\<close> es una
        fórmula.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la disyunción \<open>F \<or> G\<close> es una
        fórmula.
      \item Dadas dos fórmulas \<open>F\<close> y \<open>G\<close>, la implicación \<open>F \<longrightarrow> G\<close> es 
        una fórmula.
    \end{itemize}
  \end{definicion}

  Intuitivamente, las fórmulas proposicionales son entendidas como un 
  tipo de árbol sintáctico cuyos nodos son las conectivas y sus hojas
  las fórmulas atómicas. Veamos, por ejemplo, el árbol sintáctico de
  la fórmula \<open>p \<rightarrow> (\<not> q \<or> p)\<close>.

 \begin{forest} for tree = {parent anchor = south, child anchor = north}
        [\<open>p \<rightarrow> (\<not> q \<or> p)\<close>
            [\<open>p\<close>]
            [\<open>\<not> q \<or> p\<close>
                [\<open>\<not> q\<close>
                  [\<open>q\<close>]]
                [\<open>p\<close>]]
        ]
 \end{forest}

  A continuación, veamos la representación en Isabelle de la estructura
  de las fórmulas proposicionales.\<close>

(*notation insert ("_ ▹ _" [56,55] 55)*)

datatype (atoms: 'a) formula = 
  Atom 'a
| Bot                              ("\<bottom>")  
| Not "'a formula"                 ("\<^bold>\<not>")
| And "'a formula" "'a formula"    (infix "\<^bold>\<and>" 68)
| Or "'a formula" "'a formula"     (infix "\<^bold>\<or>" 68)
| Imp "'a formula" "'a formula"    (infixr "\<^bold>\<rightarrow>" 68)

text\<open>Formulas are countable if their atoms are\<close> 
instance formula :: (countable) countable by countable_datatype

text \<open>Como podemos observar representamos las fórmulas proposicionales
  mediante un tipo de dato recursivo, @{term "formula"}, con los 
  siguientes constructores sobre un tipo cualquiera:

  \begin{description}
    \item[Fórmulas básicas]:
      \begin{itemize}
        \item @{const_typ Atom}
        \item @{const_typ Bot}
      \end{itemize}
    \item [Fórmulas compuestas]:
      \begin{itemize}
        \item @{const_typ Not}
        \item @{const_typ And}
        \item @{const_typ Or}
        \item @{const_typ Imp}
      \end{itemize}
  \end{description}

  Cabe señalar que los términos \<open>infix\<close> e \<open>infixr\<close> nos señalan que 
  los constructores que representan a las conectivas se pueden usar de
  forma infija. En particular, \<open>infixr\<close> se trata de un infijo asociado a 
  la derecha.

  Por otro lado, la definición de @{term "formula"} 
  genera automáticamente los siguientes lemas sobre la función 
  @{const_typ atoms}, que obtiene el conjunto de átomos de una fórmula.

  \begin{itemize}
    \item[] @{thm formula.set}
  \end{itemize} 

  A continuación veremos varios ejemplos de fórmulas y el conjunto de 
  sus variables proposicionales obtenido mediante @{term "atoms"}. Se 
  observa que, por ser conjuntos, no contienen elementos repetidos.\<close>

notepad 
begin
  fix p q r :: 'a

  have "atoms (Atom p) = {p}"
    by (simp only: formula.set)

  have "atoms (\<^bold>\<not> (Atom p)) = {p}"
    by (simp only: formula.set)

  have "atoms ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = {p,q,r}"
    by auto

  have "atoms ((Atom p \<^bold>\<rightarrow> Atom p) \<^bold>\<or> Atom r) = {p,r}"
    by auto  
end

text \<open>En particular, el conjunto de símbolos proposicionales de la 
  fórmula \<open>Bot\<close> es vacío. Además, para calcular esta constante es 
  necesario especificar el tipo sobre el que se construye la fórmula.\<close>

notepad 
begin
  fix p :: 'a

  have "atoms \<bottom> = \<emptyset>"
    by (simp only: formula.set)

  have "atoms (Atom p \<^bold>\<or> \<bottom>) = {p}"
  proof -
    have "atoms (Atom p \<^bold>\<or> \<bottom>) = atoms (Atom p) \<union> atoms Bot"
      by (simp only: formula.set(5))
    also have "\<dots> = {p} \<union> atoms Bot"
      by (simp only: formula.set(1))
    also have "\<dots> = {p} \<union> \<emptyset>"
      by (simp only: formula.set(2))
    also have "\<dots> = {p}"
      by (simp only: Un_empty_right)
    finally show "atoms (Atom p \<^bold>\<or> \<bottom>) = {p}"
      by this
  qed

  have "atoms (Atom p \<^bold>\<or> \<bottom>) = {p}"
    by (simp only: formula.set Un_empty_right)
end

value "(Bot::nat formula)"

text \<open>Una vez definida la estructura de las fórmulas, vamos a introducir 
  el método de demostración que seguirán los resultados que aquí 
  presentaremos, tanto en la teoría clásica como en Isabelle. 

  Según la definición recursiva de las fórmulas, dispondremos de un 
  esquema de inducción sobre las mismas:

  \begin{teorema}[Principio de inducción sobre fórmulas
  proposicionales]
    Sea \<open>\<P>\<close> una propiedad sobre fórmulas que verifica las siguientes 
    condiciones:
    \begin{itemize}
      \item Las fórmulas atómicas la cumplen.
      \item La constante \<open>\<bottom>\<close> la cumple.
      \item Dada \<open>F\<close> fórmula que la cumple, entonces \<open>\<not> F\<close> la cumple.
      \item Dadas \<open>F\<close> y \<open>G\<close> fórmulas que la cumplen, entonces \<open>F * G\<close> la 
        cumple, donde \<open>*\<close> simboliza cualquier conectiva binaria.
    \end{itemize}
    Entonces, todas las fórmulas proposicionales tienen la propiedad 
    \<open>\<P>\<close>.
  \end{teorema}

  Análogamente, como las fórmulas proposicionales están definidas 
  mediante un tipo de datos recursivo, Isabelle genera de forma 
  automática el esquema de inducción correspondiente. De este modo, en 
  las pruebas formalizadas utilizaremos la táctica @{term "induction"}, 
  que corresponde al siguiente esquema.

  \<open>\<And>x. P(Atom x)\<close>

  \<open>P \<bottom>\<close>

  \<open>\<And>x. P x \<Longrightarrow> P(\<^bold>\<not> x)\<close>

  \<open>\<And>x1 x2. P x1 \<and> P x2 \<Longrightarrow> P (x1 \<^bold>\<and> x2)\<close>

  \<open>\<And>x1 x2. P x1 \<and> P x2 \<Longrightarrow> P (x1 \<^bold>\<or> x2)\<close>

  \<open>\<And>x1 x2. P x1 \<and> P x2 \<Longrightarrow> P (x1 \<^bold>\<rightarrow> x2)\<close>

  \rule{70mm}{0.1mm}

  \<open>P formula\<close>

  Como hemos señalado, el esquema inductivo genera así seis casos 
  distintos como se muestra anteriormente. Además, todas las 
  demostraciones sobre casos de conectivas binarias son equivalentes en 
  esta sección, pues la construcción sintáctica de fórmulas es idéntica 
  entre ellas. Estas se diferencian esencialmente en la connotación 
  semántica que veremos más adelante.

  A continuación el primer resultado de este apartado:

  \begin{lema}
    El conjunto de los átomos de una fórmula proposicional es finito.
  \end{lema}

  Para proceder a la demostración, consideremos la siguiente
  definición inductiva de conjunto finito. Cabe añadir que la 
  demostración seguirá el esquema inductivo relativo a la estructura de 
  fórmula, y no el que induce esta última definición.

  \begin{definicion}
    Los conjuntos finitos son:
      \begin{itemize}
        \item El vacío.
        \item Dado un conjunto finito \<open>A\<close> y un elemento cualquiera \<open>a\<close>, 
          entonces \<open>{a} \<union> A\<close> es finito.
      \end{itemize}
  \end{definicion}

  La formalización en Isabelle de la definición anterior es precisamente 
  @{term "finite"} perteneciente a la teoría 
  \href{https://n9.cl/x86r}{FiniteSet.thy}. Dicha definición inductiva
  genera dos reglas análogas a las anteriores que definen a los 
  conjuntos finitos y que emplearemos en la demostración del resultado.

  \begin{itemize}
    \item[] @{thm[mode=Rule] emptyI[no_vars]} 
      \hfill (@{text emptyI})
  \end{itemize}

  \begin{itemize}
    \item[] @{thm[mode=Rule] insertI[no_vars]} 
      \hfill (@{text insertI})
  \end{itemize}

  De este modo, en Isabelle podemos especificar el lema como sigue.\<close>

lemma "finite (atoms F)"
  oops

text \<open>A continuación, veamos la demostración clásica del lema. 

  \begin{demostracion}
  La prueba es por inducción sobre el tipo recursivo de las fórmulas. 
  Veamos cada caso.
  
  Consideremos una fórmula atómica \<open>p\<close> cualquiera. Entonces, 
  su conjunto de variables proposicionales es \<open>{p}\<close>, finito.

  Sea la fórmula \<open>\<bottom>\<close>. Entonces, su conjunto de átomos es vacío y, por 
  lo tanto, finito.
  
  Sea \<open>F\<close> una fórmula cuyo conjunto de variables proposicionales sea 
  finito. Entonces, por definición, \<open>\<not> F\<close> y \<open>F\<close> tienen igual conjunto de
  átomos y, por hipótesis de inducción, es finito.

  Consideremos las fórmulas \<open>F\<close> y \<open>G\<close> cuyos conjuntos de átomos son 
  finitos. Por\\ construcción, el conjunto de variables de \<open>F*G\<close> es la 
  unión de sus respectivos conjuntos de átomos para cualquier \<open>*\<close> 
  conectiva binaria. Por lo tanto, usando la hipótesis de inducción, 
  dicho conjunto es finito. 
  \end{demostracion} 

  Veamos ahora la prueba detallada en Isabelle. Mostraremos con detalle 
  todos los casos de conectivas binarias, aunque se puede observar que 
  son completamente análogos. Para facilitar la lectura, primero 
  demostraremos por separado cada uno de los casos según el esquema 
  inductivo de fórmulas, y finalmente añadiremos la prueba para una 
  fórmula cualquiera a partir de los anteriores.\<close>

lemma atoms_finite_atom:
  "finite (atoms (Atom x))"
proof -
  have "finite \<emptyset>"
    by (simp only: finite.emptyI)
  then have "finite {x}"
    by (simp only: finite_insert)
  then show "finite (atoms (Atom x))"
    by (simp only: formula.set(1)) 
qed

lemma atoms_finite_bot:
  "finite (atoms \<bottom>)"
proof -
  have "finite \<emptyset>"
    by (simp only: finite.emptyI)
  then show "finite (atoms \<bottom>)"
    by (simp only: formula.set(2)) 
qed

lemma atoms_finite_not:
  assumes "finite (atoms F)" 
  shows   "finite (atoms (\<^bold>\<not> F))"
  using assms
  by (simp only: formula.set(3)) 

lemma atoms_finite_and:
  assumes "finite (atoms F1)"
          "finite (atoms F2)"
  shows   "finite (atoms (F1 \<^bold>\<and> F2))"
proof -
  have "finite (atoms F1 \<union> atoms F2)"
    using assms
    by (simp only: finite_UnI)
  then show "finite (atoms (F1 \<^bold>\<and> F2))"  
    by (simp only: formula.set(4))
qed

lemma atoms_finite_or:
  assumes "finite (atoms F1)"
          "finite (atoms F2)"
  shows   "finite (atoms (F1 \<^bold>\<or> F2))"
proof -
  have "finite (atoms F1 \<union> atoms F2)"
    using assms
    by (simp only: finite_UnI)
  then show "finite (atoms (F1 \<^bold>\<or> F2))"  
    by (simp only: formula.set(5))
qed

lemma atoms_finite_imp:
  assumes "finite (atoms F1)"
          "finite (atoms F2)"
  shows   "finite (atoms (F1 \<^bold>\<rightarrow> F2))"
proof -
  have "finite (atoms F1 \<union> atoms F2)"
    using assms
    by (simp only: finite_UnI)
  then show "finite (atoms (F1 \<^bold>\<rightarrow> F2))"  
    by (simp only: formula.set(6))
qed

lemma atoms_finite: "finite (atoms F)"
proof (induction F)
  case (Atom x)
  then show ?case by (simp only: atoms_finite_atom)
next
  case Bot
  then show ?case by (simp only: atoms_finite_bot)
next
  case (Not F)
  then show ?case by (simp only: atoms_finite_not)
next
  case (And F1 F2)
  then show ?case by (simp only: atoms_finite_and)
next
  case (Or F1 F2)
  then show ?case by (simp only: atoms_finite_or)
next
  case (Imp F1 F2)
  then show ?case by (simp only: atoms_finite_imp)
qed

text \<open>Su demostración automática es la siguiente.\<close>

lemma "finite (atoms F)" 
  by (induction F) simp_all 

section \<open>Subfórmulas\<close>

text \<open>Veamos la noción de subfórmulas.

  \begin{definicion}
  El conjunto de subfórmulas de una fórmula \<open>F\<close>, notada \<open>Subf(F)\<close>, se 
  define recursivamente como:
    \begin{itemize}
      \item \<open>{F}\<close> si \<open>F\<close> es una fórmula atómica.
      \item \<open>{\<bottom>}\<close> si \<open>F\<close> es \<open>\<bottom>\<close>.
      \item \<open>{F} \<union> Subf(G)\<close> si \<open>F\<close> es \<open>\<not>G\<close>.
      \item \<open>{F} \<union> Subf(G) \<union> Subf(H)\<close> si \<open>F\<close> es \<open>G*H\<close> donde \<open>*\<close> es 
        cualquier conectiva binaria.
    \end{itemize}
  \end{definicion}

  Para proceder a la formalización de Isabelle, seguiremos dos etapas. 
  En primer lugar, definimos la función primitiva recursiva 
  @{term "subformulae"}. Esta nos devolverá la lista de todas las 
  subfórmulas de una fórmula original obtenidas recursivamente.\<close>
 
primrec subformulae :: "'a formula \<Rightarrow> 'a formula list" where
  "subformulae (Atom k) = [Atom k]" 
| "subformulae \<bottom>        = [\<bottom>]" 
| "subformulae (\<^bold>\<not> F)    = (\<^bold>\<not> F) # subformulae F" 
| "subformulae (F \<^bold>\<and> G)  = (F \<^bold>\<and> G) # subformulae F @ subformulae G" 
| "subformulae (F \<^bold>\<or> G)  = (F \<^bold>\<or> G) # subformulae F @ subformulae G"
| "subformulae (F \<^bold>\<rightarrow> G) = (F \<^bold>\<rightarrow> G) # subformulae F @ subformulae G"
 
text \<open>Observemos que, en la definición anterior, \<open>#\<close> es el operador que 
  añade un elemento al comienzo de una lista y \<open>@\<close> concatena varias 
  listas. 

  Siguiendo con los ejemplos, apliquemos @{term subformulae} en
  las distintas fórmulas. En particular, al tratarse de una lista pueden 
  aparecer elementos repetidos como se muestra a continuación.
\<close>

notepad
begin
  fix p :: 'a

  have "subformulae (Atom p) = [Atom p]"
    by simp

  have "subformulae (\<^bold>\<not> (Atom p)) = [\<^bold>\<not> (Atom p), Atom p]"
    by simp

  have "subformulae ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = 
       [(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, 
        Atom q, Atom r]"
    by simp

  have "subformulae (Atom p \<^bold>\<and> \<bottom>) = [Atom p \<^bold>\<and> \<bottom>, Atom p, \<bottom>]"
    by simp

  have "subformulae (Atom p \<^bold>\<or> Atom p) = 
       [Atom p \<^bold>\<or> Atom p, Atom p, Atom p]"
    by simp
end

text \<open>En la segunda etapa de formalización, definimos 
  @{term "setSubformulae"}, que convierte al tipo conjunto la lista de 
  subfórmulas anterior.\<close>

abbreviation setSubformulae :: "'a formula \<Rightarrow> 'a formula set" where
  "setSubformulae F \<equiv> set (subformulae F)"

text \<open>De este modo, la función \<open>setSubformulae\<close> es la formalización
  en Isabelle de \<open>Subf(·)\<close>. En Isabelle, primero hemos definido la lista 
  de subfórmulas pues, en algunos casos, es más sencilla la prueba de 
  resultados sobre este tipo. 
  Algunas de las ventajas del tipo conjuntos son la eliminación de 
  elementos repetidos o las operaciones propias de teoría de conjuntos. 
  Observemos los siguientes ejemplos con el tipo de conjuntos.
\<close>

notepad
begin
  fix p q r :: 'a

  have "setSubformulae (Atom p \<^bold>\<or> Atom p) = {Atom p \<^bold>\<or> Atom p, Atom p}"
    by simp
  
  have "setSubformulae ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) =
        {(Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r, Atom p \<^bold>\<rightarrow> Atom q, Atom p, 
         Atom q, Atom r}"
  by auto   
end

text \<open>Por otro lado, debemos señalar que el uso de 
  @{term "abbreviation"} para definir @{term "setSubformulae"} no es 
  arbitrario. No es una definición propiamente dicha, sino 
  una forma de nombrar la composición de las funciones @{term "set"} y 
  @{term "subformulae"}.


  En primer lugar, veamos que @{term "setSubformulae"} es una
  formalización de @{term "Subf"} en Isabelle. Para ello 
  utilizaremos el siguiente resultado sobre listas, probado como sigue.\<close>

lemma set_insert: "set (x # ys) = {x} \<union> set ys"
  by (simp only: list.set(2) Un_insert_left sup_bot.left_neutral)

text \<open>Por tanto, obtenemos la equivalencia como resultado de los 
  siguientes lemas, que aparecen demostrados de manera detallada.\<close>

lemma setSubformulae_atom:
  "setSubformulae (Atom p) = {Atom p}"
    by (simp only: subformulae.simps(1) list.set)

lemma setSubformulae_bot:
  "setSubformulae (\<bottom>) = {\<bottom>}"
    by (simp only: subformulae.simps(2) list.set)

lemma setSubformulae_not:
  shows "setSubformulae (\<^bold>\<not> F) = {\<^bold>\<not> F} \<union> setSubformulae F"
proof -
  have "setSubformulae (\<^bold>\<not> F) = set (\<^bold>\<not> F # subformulae F)"
    by (simp only: subformulae.simps(3))
  also have "\<dots> = {\<^bold>\<not> F} \<union> set (subformulae F)"
    by (simp only: set_insert)
  finally show ?thesis
    by this
qed

lemma setSubformulae_and: 
  "setSubformulae (F1 \<^bold>\<and> F2) 
   = {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
proof -
  have "setSubformulae (F1 \<^bold>\<and> F2) 
        = set ((F1 \<^bold>\<and> F2) # (subformulae F1 @ subformulae F2))"
    by (simp only: subformulae.simps(4))
  also have "\<dots> = {F1 \<^bold>\<and> F2} \<union> (set (subformulae F1 @ subformulae F2))"
    by (simp only: set_insert)
  also have "\<dots> = {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: set_append)
  finally show ?thesis
    by this
qed

lemma setSubformulae_or: 
  "setSubformulae (F1 \<^bold>\<or> F2) 
   = {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
proof -
  have "setSubformulae (F1 \<^bold>\<or> F2) 
        = set ((F1 \<^bold>\<or> F2) # (subformulae F1 @ subformulae F2))"
    by (simp only: subformulae.simps(5))
  also have "\<dots> = {F1 \<^bold>\<or> F2} \<union> (set (subformulae F1 @ subformulae F2))"
    by (simp only: set_insert)
  also have "\<dots> = {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: set_append)
  finally show ?thesis
    by this
qed

lemma setSubformulae_imp: 
  "setSubformulae (F1 \<^bold>\<rightarrow> F2) 
   = {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
proof -
  have "setSubformulae (F1 \<^bold>\<rightarrow> F2) 
        = set ((F1 \<^bold>\<rightarrow> F2) # (subformulae F1 @ subformulae F2))"
    by (simp only: subformulae.simps(6))
  also have "\<dots> = {F1 \<^bold>\<rightarrow> F2} \<union> (set (subformulae F1 @ subformulae F2))"
    by (simp only: set_insert)
  also have "\<dots> = {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: set_append)
  finally show ?thesis
    by this
qed

text \<open>Una vez probada la equivalencia, comencemos con los resultados 
  correspondientes a las subfórmulas. En primer lugar, tenemos la 
  siguiente propiedad como consecuencia directa de la equivalencia de 
  funciones anterior.

  \begin{lema}
    Toda fórmula es subfórmula de ella misma.
  \end{lema}

  \begin{demostracion}
    La demostración se hace en cada caso de la estructura de las 
    fórmulas.
  
    Sea \<open>p\<close> fórmula atómica cualquiera. Por definición, tenemos que su
    conjunto de subfórmulas es \<open>{p}\<close>, luego se tiene la propiedad.
  
    Sea la fórmula \<open>\<bottom>\<close>. Por definición, su conjunto de subfórmulas es
    \<open>{\<bottom>}\<close>, luego se verifica el resultado.

    Sea la fórmula \<open>\<not> F\<close>. Veamos que pertenece a su conjunto de
    subfórmulas.
    Por definición, tenemos que el conjunto de subfórmulas de \<open>\<not> F\<close> es
    \<open>{\<not> F} \<union> Subf(F)\<close>. Por tanto, \<open>\<not> F\<close> pertence a su propio conjunto
    de subfórmulas como queríamos demostrar.

    Sea \<open>*\<close> una conectiva binaria cualquiera y las fórmulas \<open>F\<close> y \<open>G\<close>
    Veamos que \<open>F*G\<close> pertenece a su conjunto de subfórmulas.
    Por definición, tenemos que el conjunto de subfórmulas de \<open>F*G\<close> es
    \<open>{F*G} \<union> Subf(F) \<union> Subf(G)\<close>. Por tanto, \<open>F*G\<close> pertence a su propio 
    conjunto de subfórmulas como queríamos demostrar.
  \end{demostracion}

  Formalicemos ahora el lema con su correspondiente demostración 
  detallada.\<close>

lemma subformulae_self: "F \<in> setSubformulae F"
proof (cases F)
  case (Atom x1)
  then show ?thesis 
    by (simp only: singletonI setSubformulae_atom)
next
  case Bot
  then show ?thesis
    by (simp only: singletonI setSubformulae_bot)
next
  case (Not F)
  then show ?thesis
    by (simp only: singletonI UnI1 setSubformulae_not)
next
  case (And F1 F2)
  then show ?thesis
   by (simp only: singletonI UnI1 setSubformulae_and)
next
  case (Or F1 F2)
  then show ?thesis
   by (simp only: singletonI UnI1 setSubformulae_or)
next
  case (Imp F1 F2)
  then show ?thesis
   by (simp only: singletonI UnI1 setSubformulae_imp)
qed 

text \<open>La demostración automática es la siguiente.\<close>

lemma "F \<in> setSubformulae F"
  by (cases F) simp_all

text \<open>Procedamos con los demás resultados de la sección. Como hemos 
  señalado con anterioridad, utilizaremos varias propiedades de 
  conjuntos pertenecientes a la teoría 
  \href{https://n9.cl/qatp}{Set.thy} de Isabelle, que apareceran en 
  el glosario final. 

  Además, definiremos dos reglas adicionales que utilizaremos con 
  frecuencia.\<close>

lemma subContUnionRev1: 
  assumes "A \<union> B \<subseteq> C" 
  shows   "A \<subseteq> C"
proof -
  have "A \<subseteq> C \<and> B \<subseteq> C"
    using assms
    by (simp only: sup.bounded_iff)
  then show "A \<subseteq> C"
    by (rule conjunct1)
qed

lemma subContUnionRev2: 
  assumes "A \<union> B \<subseteq> C" 
  shows   "B \<subseteq> C"
proof -
  have "A \<subseteq> C \<and> B \<subseteq> C"
    using assms
    by (simp only: sup.bounded_iff)
  then show "B \<subseteq> C"
    by (rule conjunct2)
qed

text \<open>Sus correspondientes demostraciones automáticas se muestran a 
  continuación.\<close>

lemma "A \<union> B \<subseteq> C \<Longrightarrow> A \<subseteq> C"
  by simp

lemma "A \<union> B \<subseteq> C \<Longrightarrow> B \<subseteq> C"
  by simp

text \<open>Veamos ahora los distintos resultados sobre subfórmulas.

  \begin{lema}
    Todas las fórmulas atómicas de una fórmula son subfórmulas.
  \end{lema}

  \begin{demostracion}
    Aclaremos que el conjunto de las fórmulas atómicas de una fórmula 
    cualquiera está formado a partir de cada elemento de su conjunto de 
    variables proposicionales. 
    Queremos demostrar que este conjunto está contenido en el conjunto 
    de\\ subfórmulas de dicha fórmula.
    De este modo, la prueba seguirá el esquema inductivo para la 
    estructura de fórmulas. Veamos cada caso:
  
    Consideremos la fórmula atómica \<open>p\<close> cualquiera. Como su
    conjunto de átomos es \<open>{p}\<close>, el conjunto de sus fórmulas atómicas
    correspondiente será \<open>{p}\<close>. Por otro lado, su conjunto de
    subfórmulas es también \<open>{p}\<close>, luego el conjunto de sus fórmulas 
    atómicas está contenido en el conjunto de sus subfórmulas como 
    queríamos demostrar.

    Sea la fórmula \<open>\<bottom>\<close>. Como su conjunto de átomos es vacío, es claro 
    que el conjunto de sus fórmulas atómicas es también el vacío y, por
    tanto, está contenido en el conjunto de sus subfórmulas.

    Sea la fórmula \<open>F\<close> tal que el conjunto de sus fórmulas atómicas está
    contenido en el conjunto de sus subfórmulas. Probemos el resultado 
    para \<open>\<not> F\<close>. 
    En primer lugar, sabemos que los 
    conjuntos de variables proposicionales de \<open>F\<close> y \<open>\<not> F\<close> coinciden, 
    luego tendrán igual conjunto de fórmulas atómicas. Por lo tanto,
    por hipótesis de inducción tenemos que el conjunto de fórmulas
    atómicas de \<open>F\<close> está contenido en el conjunto de subfórmulas de 
    \<open>F\<close>. Por otro lado, como el conjunto de subfórmulas de \<open>\<not> F\<close> está 
    definido como\\ \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>, tenemos que el 
    el conjunto de subfórmulas de \<open>F\<close> está contenido en el de \<open>\<not> F\<close>.
    Por tanto, por propiedades de contención, 
    tenemos que el conjunto de fórmulas atómicas de \<open>\<not> F\<close> está 
    contenido en el conjunto de subfórmulas de \<open>\<not> F\<close> como queríamos 
    demostrar.

    Sean las fórmulas \<open>F\<close> y \<open>G\<close> tales que sus conjuntos de fórmulas 
    atómicas están contenidos en sus conjuntos de subfórmulas 
    respectivamente. Probemos ahora el resultado para \<open>F*G\<close>, donde \<open>*\<close>
    simboliza una conectiva binaria cualquiera.
    En primer lugar, sabemos que el conjunto de átomos de \<open>F*G\<close>
    es la unión de sus correspondientes conjuntos de átomos. De este
    modo, el conjunto de fórmulas atómicas de \<open>F*G\<close> será la unión del 
    conjunto de fórmulas atómicas de \<open>F\<close> y el correspondiente de \<open>G\<close>. 
    Por tanto, por hipótesis de inducción tenemos que el conjunto de 
    fórmulas atómicas de \<open>F*G\<close> está contenido en la unión del conjunto
    de subfórmulas de \<open>F\<close> y el conjunto de subfórmulas de \<open>G\<close>. Como el
    conjunto de subfórmulas de \<open>F*G\<close> se define como\\
    \<open>Subf(F*G) = {F*G} \<union> Subf(F) \<union> Subf(G)\<close>, tenemos que la unión
    de los conjuntos de subfórmulas de \<open>F\<close> y \<open>G\<close> está contenida en el
    conjunto de subfórmulas de \<open>F*G\<close>. Por tanto, por propiedades
    de la contención, tenemos que le conjunto de fórmulas atómicas de
    \<open>F*G\<close> está contenido en el conjunto de subfórmulas de \<open>F*G\<close> como 
    queríamos demostrar.  
  \end{demostracion}

  En Isabelle, se especifica como sigue.\<close>

lemma "Atom ` atoms F \<subseteq> setSubformulae F"
  oops

text \<open>Debemos observar que \<open>Atom ` atoms F\<close> construye las fórmulas 
  atómicas a partir de cada uno de los elementos de \<open>atoms F\<close>, creando 
  un conjunto de fórmulas atómicas. Para ello emplea el infijo \<open>`\<close> 
  definido como notación abreviada de @{term "image"} que calcula la 
  imagen de un conjunto en la teoría \href{https://n9.cl/qatp}{Set.thy}.

  \begin{itemize}
    \item[] @{thm[mode=Def] image_def} 
      \hfill (@{text image_def})
  \end{itemize}

  Para aclarar su funcionamiento, veamos ejemplos para distintos casos 
  de fórmulas.\<close>

notepad
begin
  fix p q r :: 'a

  have "Atom `atoms (Atom p \<^bold>\<or> \<bottom>) = {Atom p}"
    by simp

  have "Atom `atoms ((Atom p \<^bold>\<rightarrow> Atom q) \<^bold>\<or> Atom r) = 
       {Atom p, Atom q, Atom r}"
    by auto 

  have "Atom `atoms ((Atom p \<^bold>\<rightarrow> Atom p) \<^bold>\<or> Atom r) = 
       {Atom p, Atom r}"
    by auto
end

text \<open>Además, esta función tiene las siguientes propiedades sobre 
  conjuntos que utilizaremos en la demostración.

  \begin{itemize}
    \item[] @{thm[mode=Rule] image_Un[no_vars]} 
      \hfill (@{text image_Un})
    \item[] @{thm[mode=Rule] image_insert[no_vars]} 
      \hfill (@{text image_insert})
    \item[] @{thm[mode=Rule] image_empty[no_vars]} 
      \hfill (@{text image_empty})
  \end{itemize}

  Una vez hechas las aclaraciones necesarias, comencemos la demostración 
  estructurada. Esta seguirá el esquema inductivo señalado con 
  anterioridad.\<close>

lemma atoms_are_subformulae_atom: 
  "Atom ` atoms (Atom x) \<subseteq> setSubformulae (Atom x)" 
proof -
  have "Atom ` atoms (Atom x) = Atom ` {x}"
    by (simp only: formula.set(1))
  also have "\<dots> = {Atom x}"
    by (simp only: image_insert image_empty)
  also have "\<dots> = set [Atom x]"
    by (simp only: list.set(1) list.set(2))
  also have "\<dots> = set (subformulae (Atom x))"
    by (simp only: subformulae.simps(1))
  finally have "Atom ` atoms (Atom x) = set (subformulae (Atom x))"
    by this
  then show ?thesis 
    by (simp only: subset_refl)
qed

lemma atoms_are_subformulae_bot: 
  "Atom ` atoms \<bottom> \<subseteq> setSubformulae \<bottom>"  
proof -
  have "Atom ` atoms \<bottom> = Atom ` \<emptyset>"
    by (simp only: formula.set(2))
  also have "\<dots> = \<emptyset>"
    by (simp only: image_empty)
  also have "\<dots> \<subseteq> setSubformulae \<bottom>"
    by (simp only: empty_subsetI)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_not: 
  assumes "Atom ` atoms F \<subseteq> setSubformulae F" 
  shows   "Atom ` atoms (\<^bold>\<not> F) \<subseteq> setSubformulae (\<^bold>\<not> F)"
proof -
  have "Atom ` atoms (\<^bold>\<not> F) = Atom ` atoms F"
    by (simp only: formula.set(3))
  also have "\<dots> \<subseteq> setSubformulae F"
    by (simp only: assms)
  also have "\<dots> \<subseteq> {\<^bold>\<not> F} \<union> setSubformulae F"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (\<^bold>\<not> F)"
    by (simp only: setSubformulae_not)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_and: 
  assumes "Atom ` atoms F1 \<subseteq> setSubformulae F1"
          "Atom ` atoms F2 \<subseteq> setSubformulae F2"
  shows   "Atom ` atoms (F1 \<^bold>\<and> F2) \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
proof -
  have "Atom ` atoms (F1 \<^bold>\<and> F2) = Atom ` (atoms F1 \<union> atoms F2)"
    by (simp only: formula.set(4))
  also have "\<dots> = Atom ` atoms F1 \<union> Atom ` atoms F2" 
    by (rule image_Un)
  also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
    using assms
    by (rule Un_mono)
  also have "\<dots> \<subseteq> {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (F1 \<^bold>\<and> F2)"
    by (simp only: setSubformulae_and)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_or: 
  assumes "Atom ` atoms F1 \<subseteq> setSubformulae F1"
          "Atom ` atoms F2 \<subseteq> setSubformulae F2"
  shows   "Atom ` atoms (F1 \<^bold>\<or> F2) \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
proof -
  have "Atom ` atoms (F1 \<^bold>\<or> F2) = Atom ` (atoms F1 \<union> atoms F2)"
    by (simp only: formula.set(5))
  also have "\<dots> = Atom ` atoms F1 \<union> Atom ` atoms F2" 
    by (rule image_Un)
  also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
    using assms
    by (rule Un_mono)
  also have "\<dots> \<subseteq> {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (F1 \<^bold>\<or> F2)"
    by (simp only: setSubformulae_or)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae_imp: 
  assumes "Atom ` atoms F1 \<subseteq> setSubformulae F1"
          "Atom ` atoms F2 \<subseteq> setSubformulae F2"
  shows   "Atom ` atoms (F1 \<^bold>\<rightarrow> F2) \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
proof -
  have "Atom ` atoms (F1 \<^bold>\<rightarrow> F2) = Atom ` (atoms F1 \<union> atoms F2)"
    by (simp only: formula.set(6))
  also have "\<dots> = Atom ` atoms F1 \<union> Atom ` atoms F2" 
    by (rule image_Un)
  also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
    using assms
    by (rule Un_mono)
  also have "\<dots> \<subseteq> {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    by (simp only: Un_upper2)
  also have "\<dots> = setSubformulae (F1 \<^bold>\<rightarrow> F2)"
    by (simp only: setSubformulae_imp)
  finally show ?thesis
    by this
qed

lemma atoms_are_subformulae: 
  "Atom ` atoms F \<subseteq> setSubformulae F"
proof (induction F)
  case (Atom x)
  then show ?case by (simp only: atoms_are_subformulae_atom) 
next
  case Bot
  then show ?case by (simp only: atoms_are_subformulae_bot) 
next
  case (Not F)
  then show ?case by (simp only: atoms_are_subformulae_not) 
next
  case (And F1 F2)
  then show ?case by (simp only: atoms_are_subformulae_and) 
next
  case (Or F1 F2)
  then show ?case by (simp only: atoms_are_subformulae_or)
next
  case (Imp F1 F2)
  then show ?case by (simp only: atoms_are_subformulae_imp)
qed

text \<open>La demostración automática queda igualmente expuesta a 
  continuación.\<close>

lemma "Atom ` atoms F \<subseteq> setSubformulae F"
  by (induction F)  auto

text \<open>La siguiente propiedad declara que el conjunto de átomos de una 
  subfórmula está contenido en el conjunto de átomos de la propia 
  fórmula.

  \begin{lema}
  Dada una fórmula, los átomos de sus subfórmulas son átomos de ella
  misma.
  \end{lema}

  \begin{demostracion}
  Procedemos mediante inducción en la estructura de las fórmulas según 
  los distintos casos:

  Sea \<open>p\<close> una fórmula atómica cualquiera. Por definición de su conjunto
  de subfórmulas, su única subfórmula es ella misma, luego se verifica
  el resultado.

  Sea la fórmula \<open>\<bottom>\<close>. Por definición de su conjunto de subfórmulas, su 
  única subfórmula es ella misma, luego se verifica análogamente la
  propiedad en este caso.

  Sea la fórmula \<open>F\<close> tal que para cualquier subfórmula suya se verifica 
  que el conjunto de sus átomos está contenido en el conjunto de átomos 
  de \<open>F\<close>. Supongamos \<open>G\<close> subfórmula cualquiera de \<open>\<not> F\<close>. Vamos a
  probar que el conjunto de átomos de \<open>G\<close> está contenido en el de 
  \<open>\<not> F\<close>.
  Por definición, tenemos que el conjunto de subfórmulas de \<open>\<not> F\<close> es de
  la forma \\ \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>. De este modo, tenemos dos 
  opciones posibles:\\ \<open>G \<in> {\<not> F}\<close> o \<open>G \<in> Subf(F)\<close>. 
  Del primer caso se deduce \<open>G = \<not> F\<close> 
  y, por tanto, tienen igual conjunto de átomos.
  Observando el segundo caso, por hipótesis de inducción, se tiene que 
  el conjunto de átomos de \<open>G\<close> está contenido en el de \<open>F\<close>. Además, como 
  el conjunto de átomos de \<open>F\<close> y \<open>\<not> F\<close> coinciden, se verifica el 
  resultado.

  Sea \<open>F1\<close> una fórmula proposicional tal que el conjunto de los átomos 
  de cualquier subfórmula suya está contenido en el conjunto de átomos 
  de \<open>F1\<close>. Sea también \<open>F2\<close>\\ cumpliendo dicha hipótesis de inducción 
  para sus correspondientes subfórmulas. Supongamos además que \<open>G\<close> es
  subfórmula de \<open>F1*F2\<close>, donde \<open>*\<close> simboliza una conectiva binaria 
  cualquiera. Vamos a probar que el conjunto de átomos de \<open>G\<close> está 
  contenido en el conjunto de átomos de \<open>F1*F2\<close>.
  En primer lugar, por definición tenemos que el conjunto de
  subfórmulas de \<open>F1*F2\<close> es de la forma\\
  \<open>Subf(F1*F2) = {F1*F2} \<union> (Subf(F1) \<union> Subf(F2))\<close>. De este modo, 
  tenemos dos posibles opciones:
  \<open>G \<in> {F1*F2}\<close> o \<open>G \<in> Subf(F1) \<union> Subf(F2)\<close>.
  Si \<open>G \<in> {F1*F2}\<close>, entonces \<open>G = F1*F2\<close> y tienen igual conjunto de 
  átomos.
  Por otro lado, si \<open>G \<in> Subf(F1) \<union> Subf(F2)\<close> tenemos dos nuevas
  posibilidades: \<open>G\<close> es subfórmula de \<open>F1\<close> o \<open>G\<close> es subfórmula de \<open>F2\<close>.
  Suponiendo que fuese subfórmula de \<open>F1\<close>, aplicando hipótesis de
  inducción tendríamos que el conjunto de átomos de \<open>G\<close> está contenido 
  en el de \<open>F1\<close>. De este modo, como el conjunto de átomos de \<open>F1*F2\<close> se
  define como la unión de los conjuntos de átomos de \<open>F1\<close> y \<open>F2\<close>, por
  propiedades de la contención se verifica que el conjunto de átomos de
  \<open>G\<close> está contenido en el de \<open>F1*F2\<close>. Observemos que si \<open>G\<close> es 
  subfórmula de \<open>F2\<close>, se demuestra análogamente cambiando los
  subíndices correspondientes. Por tanto, se tiene el resultado.      
  \end{demostracion}

  Formalizado en Isabelle:\<close>

lemma "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  oops

text \<open>Veamos su demostración estructurada.\<close>

lemma subformulas_atoms_atom:
  assumes "G \<in> setSubformulae (Atom x)" 
  shows   "atoms G \<subseteq> atoms (Atom x)"
proof -
  have "G \<in> {Atom x}"
    using assms
    by (simp only: setSubformulae_atom)
  then have "G = Atom x"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subformulas_atoms_bot:
  assumes "G \<in> setSubformulae \<bottom>" 
  shows   "atoms G \<subseteq> atoms \<bottom>"
proof -
  have "G \<in> {\<bottom>}"
    using assms
    by (simp only: setSubformulae_bot)
  then have "G = \<bottom>"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subformulas_atoms_not:
  assumes "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
          "G \<in> setSubformulae (\<^bold>\<not> F)"
  shows   "atoms G \<subseteq> atoms (\<^bold>\<not> F)"
proof -
  have "G \<in> {\<^bold>\<not> F} \<union> setSubformulae F"
    using assms(2)
    by (simp only: setSubformulae_not) 
  then have "G \<in> {\<^bold>\<not> F} \<or> G \<in> setSubformulae F"
    by (simp only: Un_iff)
  then show "atoms G \<subseteq> atoms (\<^bold>\<not> F)"
  proof (rule disjE)
    assume "G \<in> {\<^bold>\<not> F}"
    then have "G = \<^bold>\<not> F"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F"
    then have "atoms G \<subseteq> atoms F"
      by (simp only: assms(1))
    also have "\<dots> = atoms (\<^bold>\<not> F)"
      by (simp only: formula.set(3))
    finally show ?thesis
      by this
  qed
qed

lemma subformulas_atoms_and:
  assumes "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
          "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
          "G \<in> setSubformulae (F1 \<^bold>\<and> F2)"
  shows   "atoms G \<subseteq> atoms (F1 \<^bold>\<and> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_and)
  then have "G \<in> {F1 \<^bold>\<and> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<and> F2}"
    then have "G = F1 \<^bold>\<and> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "atoms G \<subseteq> atoms F1"
        by (rule assms(1))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper1)
      also have "\<dots> = atoms (F1 \<^bold>\<and> F2)"
        by (simp only: formula.set(4))
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "atoms G \<subseteq> atoms F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper2)
      also have "\<dots> = atoms (F1 \<^bold>\<and> F2)"
        by (simp only: formula.set(4))
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subformulas_atoms_or:
  assumes "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
          "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
          "G \<in> setSubformulae (F1 \<^bold>\<or> F2)"
  shows   "atoms G \<subseteq> atoms (F1 \<^bold>\<or> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_or)
  then have "G \<in> {F1 \<^bold>\<or> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<or> F2}"
    then have "G = F1 \<^bold>\<or> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "atoms G \<subseteq> atoms F1"
        by (rule assms(1))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper1)
      also have "\<dots> = atoms (F1 \<^bold>\<or> F2)"
        by (simp only: formula.set(5))
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "atoms G \<subseteq> atoms F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper2)
      also have "\<dots> = atoms (F1 \<^bold>\<or> F2)"
        by (simp only: formula.set(5))
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subformulas_atoms_imp:
  assumes "G \<in> setSubformulae F1 \<Longrightarrow> atoms G \<subseteq> atoms F1"
          "G \<in> setSubformulae F2 \<Longrightarrow> atoms G \<subseteq> atoms F2"
          "G \<in> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
  shows   "atoms G \<subseteq> atoms (F1 \<^bold>\<rightarrow> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_imp)
  then have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<rightarrow> F2}"
    then have "G = F1 \<^bold>\<rightarrow> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "atoms G \<subseteq> atoms F1"
        by (rule assms(1))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper1)
      also have "\<dots> = atoms (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula.set(6))
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "atoms G \<subseteq> atoms F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> atoms F1 \<union> atoms F2"
        by (simp only: Un_upper2)
      also have "\<dots> = atoms (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula.set(6))
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subformulae_atoms: 
  "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
proof (induction F)
  case (Atom x)
  then show ?case by (simp only: subformulas_atoms_atom) 
next
  case Bot
  then show ?case by (simp only: subformulas_atoms_bot)
next
  case (Not F)
  then show ?case by (simp only: subformulas_atoms_not)
next
  case (And F1 F2)
  then show ?case by (simp only: subformulas_atoms_and)
next
  case (Or F1 F2)
  then show ?case by (simp only: subformulas_atoms_or)
next
  case (Imp F1 F2)
  then show ?case by (simp only: subformulas_atoms_imp)
qed

text \<open>Por último, su demostración automática.\<close>

lemma "G \<in> setSubformulae F \<Longrightarrow> atoms G \<subseteq> atoms F"
  by (induction F) auto

text \<open>A continuación vamos a introducir un lema para facilitar
   las siguientes demostraciones detalladas mediante contenciones en 
   cadena.

  \begin{lema}
    Sea \<open>G\<close> una subfórmula de \<open>F\<close>, entonces el conjunto de subfórmulas 
    de \<open>G\<close> está contenido en el de \<open>F\<close>.
  \end{lema} 

  \begin{demostracion}
  La prueba es por inducción en la estructura de fórmula.
  
  Sea \<open>p\<close> una fórmula atómica cualquiera. Por definición, el conjunto de
  sus subfórmulas es \<open>{p}\<close>, luego su única subfórmula es ella misma y,
  por tanto, tienen igual conjunto de subfórmulas.

  Sea la fórmula \<open>\<bottom>\<close>. Por definición, el conjunto de
  sus subfórmulas es \<open>{\<bottom>}\<close>, luego su única subfórmula es ella misma y,
  por tanto, tienen igual conjunto de subfórmulas.

  Sea una fórmula \<open>F\<close> tal que para toda subfórmula suya se tiene que el
  conjunto de sus subfórmulas está contenido en el conjunto de 
  subfórmulas de \<open>F\<close>.
  Supongamos \<open>G\<close> subfórmula de \<open>\<not> F\<close>. Vamos a probar que el conjunto de
  subfórmulas de \<open>G\<close> está contenido en el de \<open>\<not> F\<close>.
  En primer lugar, por definición se cumple que el conjunto de
  subfórmulas de \<open>\<not> F\<close> es de la forma \<open>Subf(\<not> F) = {\<not> F} \<union> Subf(F)\<close>.
  Como hemos supuesto \<open>G\<close> subfórmula de \<open>\<not> F\<close>, hay dos opciones 
  posibles: \<open>G \<in> {\<not> F}\<close> o \<open>G \<in> Subf(F)\<close>. 
  Del primer caso se obtiene que \<open>G = \<not> F\<close> y, por tanto, tienen igual 
  conjunto de subfórmulas. 
  Por otro lado si suponemos que \<open>G\<close> es subfórmula de \<open>F\<close>, por hipótesis
  de inducción tenemos que el conjunto de subfórmulas de \<open>G\<close> está 
  contenido en el de \<open>F\<close>. Como, a su vez, el conjunto de subfórmulas
  de \<open>F\<close> está contenido en el de \<open>\<not> F\<close> según la definición anterior, 
  por propiedades de la contención de verifica que el conjunto de 
  subfórmulas de \<open>G\<close> está contenido en el de \<open>\<not> F\<close>, como queríamos 
  demostrar.

  Sean las fórmulas \<open>F1\<close> y \<open>F2\<close> tales que para cualquier subfórmula
  de \<open>F1\<close> el conjunto de sus subfórmulas está contenido en el conjunto 
  de subfórmulas de \<open>F1\<close>, y para cualquier subfórmula de \<open>F2\<close> el 
  conjunto de sus subfórmulas está contenido en el conjunto de 
  subfórmulas de \<open>F2\<close>. Supongamos \<open>G\<close> 
  subfórmula de \<open>F1*F2\<close> donde \<open>*\<close> simboliza una conectiva binaria 
  cualquiera. Vamos a probar que el conjunto de subfórmulas de \<open>G\<close> está
  contenido en el de \<open>F1*F2\<close>. 
  En primer lugar, por definición se cumple que el conjunto de 
  subfórmulas de \<open>F1*F2\<close> es de la forma
  \<open>{F1*F2} \<union> (Subf(F1) \<union> Subf(F2))\<close>. De este modo,
  tenemos dos opciones: \<open>G \<in> {F1*F2}\<close> o \<open>G \<in> Subf(F1) \<union> Subf(F2)\<close>.
  De la primera opción se deduce \<open>G = F1*F2\<close> y, por
  tanto, tienen igual conjunto de subfórmulas. 
  Por otro lado, si \<open>G \<in> Subf(F1) \<union> Subf(F2)\<close>, tenemos a su vez dos 
  opciones: \<open>G\<close> es subfórmula de \<open>F1\<close> o \<open>G\<close> es subfórmula de \<open>F2\<close>.
  Supongamos que fuese subfórmula de \<open>F1\<close>. En este caso, por hipótesis 
  de inducción se tiene que el conjunto de subfórmulas de \<open>G\<close> está 
  contenido en el de \<open>F1\<close>. Por la definición anterior del conjunto de 
  subfórmulas de \<open>F1*F2\<close>, se verifica que el conjunto de subfórmulas de 
  \<open>F1\<close> está contenido en el de \<open>F1*F2\<close>. Por tanto, por propiedades de
  contención se tiene que el conjunto de subfórmulas de \<open>G\<close> está 
  contenido en el conjunto de subfórmulas de \<open>F1*F2\<close>. El caso de \<open>G\<close> 
  subfórmula de \<open>F2\<close> se demuestra análogamente cambiando el 
  índice de la fórmula correspondiente. Por tanto, se verifica el 
  resultado en este caso.  
  \end{demostracion}

Veamos su formalización en Isabelle junto con su demostración 
  estructurada.\<close>

lemma subContsubformulae_atom: 
  assumes "G \<in> setSubformulae (Atom x)" 
  shows "setSubformulae G \<subseteq> setSubformulae (Atom x)"
proof - 
  have "G \<in> {Atom x}" using assms 
    by (simp only: setSubformulae_atom)
  then have "G = Atom x"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subContsubformulae_bot:
  assumes "G \<in> setSubformulae \<bottom>" 
  shows   "setSubformulae G \<subseteq> setSubformulae \<bottom>"
proof -
  have "G \<in> {\<bottom>}"
    using assms
    by (simp only: setSubformulae_bot)
  then have "G = \<bottom>"
    by (simp only: singletonD)
  then show ?thesis
    by (simp only: subset_refl)
qed

lemma subContsubformulae_not:
  assumes "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
          "G \<in> setSubformulae (\<^bold>\<not> F)"
  shows   "setSubformulae G \<subseteq> setSubformulae (\<^bold>\<not> F)"
proof -
  have "G \<in> {\<^bold>\<not> F} \<union> setSubformulae F"
    using assms(2)
    by (simp only: setSubformulae_not) 
  then have "G \<in> {\<^bold>\<not> F} \<or> G \<in> setSubformulae F"
    by (simp only: Un_iff)
  then show "setSubformulae G \<subseteq> setSubformulae (\<^bold>\<not> F)"
  proof
    assume "G \<in> {\<^bold>\<not> F}"
    then have "G = \<^bold>\<not> F"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F"
    then have "setSubformulae G \<subseteq> setSubformulae F"
      by (simp only: assms(1))
    also have "setSubformulae F \<subseteq> setSubformulae (\<^bold>\<not> F)"
      by (simp only: setSubformulae_not Un_upper2)
    finally show ?thesis 
      by this
  qed
qed

lemma subContsubformulae_and:
  assumes "G \<in> setSubformulae F1 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
          "G \<in> setSubformulae F2 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
          "G \<in> setSubformulae (F1 \<^bold>\<and> F2)"
  shows   "setSubformulae G \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<and> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_and)
  then have "G \<in> {F1 \<^bold>\<and> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<and> F2}"
    then have "G = F1 \<^bold>\<and> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof 
      assume "G \<in> setSubformulae F1"
      then have "setSubformulae G \<subseteq> setSubformulae F1"
        by (simp only: assms(1))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper1)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
        by (simp only: setSubformulae_and Un_upper2)
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "setSubformulae G \<subseteq> setSubformulae F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper2)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<and> F2)"
        by (simp only: setSubformulae_and Un_upper2)
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subContsubformulae_or:
  assumes "G \<in> setSubformulae F1 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
          "G \<in> setSubformulae F2 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
          "G \<in> setSubformulae (F1 \<^bold>\<or> F2)"
  shows   "setSubformulae G \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<or> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_or)
  then have "G \<in> {F1 \<^bold>\<or> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<or> F2}"
    then have "G = F1 \<^bold>\<or> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "setSubformulae G \<subseteq> setSubformulae F1"
        by (simp only: assms(1))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper1)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
        by (simp only: setSubformulae_or Un_upper2)
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "setSubformulae G \<subseteq> setSubformulae F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper2)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<or> F2)"
        by (simp only: setSubformulae_or Un_upper2)
      finally show ?thesis
        by this
    qed
  qed
qed

lemma subContsubformulae_imp:
  assumes "G \<in> setSubformulae F1 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F1"
          "G \<in> setSubformulae F2 
            \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F2"
          "G \<in> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
  shows   "setSubformulae G \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
proof -
  have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<union> (setSubformulae F1 \<union> setSubformulae F2)"
    using assms(3) 
    by (simp only: setSubformulae_imp)
  then have "G \<in> {F1 \<^bold>\<rightarrow> F2} \<or> G \<in> setSubformulae F1 \<union> setSubformulae F2"
    by (simp only: Un_iff)
  then show ?thesis
  proof (rule disjE)
    assume "G \<in> {F1 \<^bold>\<rightarrow> F2}"
    then have "G = F1 \<^bold>\<rightarrow> F2"
      by (simp only: singletonD)
    then show ?thesis
      by (simp only: subset_refl)
  next
    assume "G \<in> setSubformulae F1 \<union> setSubformulae F2"
    then have "G \<in> setSubformulae F1 \<or> G \<in> setSubformulae F2"  
      by (simp only: Un_iff)
    then show ?thesis
    proof (rule disjE)
      assume "G \<in> setSubformulae F1"
      then have "setSubformulae G \<subseteq> setSubformulae F1"
        by (simp only: assms(1))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper1)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: setSubformulae_imp Un_upper2)
      finally show ?thesis
        by this
    next
      assume "G \<in> setSubformulae F2"
      then have "setSubformulae G \<subseteq> setSubformulae F2"
        by (rule assms(2))
      also have "\<dots> \<subseteq> setSubformulae F1 \<union> setSubformulae F2"
        by (simp only: Un_upper2)
      also have "\<dots> \<subseteq> setSubformulae (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: setSubformulae_imp Un_upper2)
      finally show ?thesis
        by this
    qed
  qed
qed

lemma
  "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
proof (induction F)
  case (Atom x)
  then show ?case by (rule subContsubformulae_atom)
next
  case Bot
  then show ?case by (rule subContsubformulae_bot)
next
  case (Not F)
  then show ?case by (rule subContsubformulae_not)
next
  case (And F1 F2)
  then show ?case by (rule subContsubformulae_and)
next
  case (Or F1 F2)
  then show ?case by (rule subContsubformulae_or)
next
  case (Imp F1 F2)
  then show ?case by (rule subContsubformulae_imp)
qed

text \<open>Finalmente, su demostración automática se muestra a continuación.\<close>

lemma subContsubformulae:
  "G \<in> setSubformulae F \<Longrightarrow> setSubformulae G \<subseteq> setSubformulae F"
  by (induction F) auto
  
text \<open>El siguiente lema nos da la noción de transitividad de contención 
  en cadena de las subfórmulas, de modo que la subfórmula de una 
  subfórmula es del mismo modo subfórmula de la mayor.

  \begin{lema}
    Sea \<open>H\<close> una subfórmula de \<open>G\<close> que es a su vez subfórmula de \<open>F\<close>, 
    entonces \<open>H\<close> es subfórmula de \<open>F\<close>.
  \end{lema}

  \begin{demostracion}
  La prueba está basada en el lema anterior. Hemos demostrado que si 
  \<open>H\<close> es subfórmula de \<open>G\<close>, entonces el conjunto de subfórmulas de \<open>H\<close> 
  está contenido en el conjunto de subfórmulas de \<open>G\<close>. Del mismo modo, 
  como \<open>G\<close> es subfórmula de \<open>F\<close>, su conjunto de subfórmulas está 
  contenido en el conjunto de subfórmulas de \<open>F\<close>. Por la
  transitividad de la contención, tenemos que el conjunto de subfórmulas
  de \<open>H\<close> está contenido en el de \<open>F\<close>. Por otro lema anterior, 
  como \<open>H\<close> es subfórmula de ella misma, es decir, pertenece a su 
  conjunto de subfórmulas, por la contención anterior se verifica que
  pertenece al conjunto de subfórmulas de \<open>F\<close> como queríamos demostrar. 
  \end{demostracion}

  Veamos su formalización y prueba estructurada en Isabelle.\<close>

lemma
  assumes "G \<in> setSubformulae F" 
          "H \<in> setSubformulae G"
  shows   "H \<in> setSubformulae F"
proof -
  have 1: "setSubformulae G \<subseteq> setSubformulae F" 
    using assms(1) 
    by (rule subContsubformulae)
  have "setSubformulae H \<subseteq> setSubformulae G" 
    using assms(2) 
    by (rule subContsubformulae)
  then have 2: "setSubformulae H \<subseteq> setSubformulae F" 
    using 1 
    by (rule subset_trans)
  have "H \<in> setSubformulae H" 
    by (simp only: subformulae_self)
  then show "H \<in> setSubformulae F" 
    using 2 
    by (rule rev_subsetD)
qed

text\<open>A continuación su demostración automática.\<close>

lemma subsubformulae: 
  "G \<in> setSubformulae F 
   \<Longrightarrow> H \<in> setSubformulae G 
   \<Longrightarrow> H \<in> setSubformulae F"
  by (drule subContsubformulae, erule subsetD)

text \<open>Presentemos ahora otro resultado que relaciona las conectivas
  con los conjuntos de subfórmulas.\<close>

text \<open>Para la demostración en Isabelle, probaremos cada caso de forma
 independiente.\<close>

lemma subformulas_in_subformulas_not:
  assumes "\<^bold>\<not> G \<in> setSubformulae F"
  shows "G \<in> setSubformulae F"
proof -
  have "G \<in> setSubformulae G"
    by (simp only: subformulae_self)
  then have "G \<in> {\<^bold>\<not> G} \<union> setSubformulae G"
    by (simp only: UnI2)
  then have 1:"G \<in> setSubformulae (\<^bold>\<not> G)" 
    by (simp only: setSubformulae_not)
  show "G \<in> setSubformulae F" using assms 1 
    by (rule subsubformulae)
qed

lemma subformulas_in_subformulas_and:
  assumes "G \<^bold>\<and> H \<in> setSubformulae F" 
  shows "G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
proof (rule conjI)
  have "G \<in> setSubformulae (G \<^bold>\<and> H)" 
    by (simp only: subformulae_self UnI2 UnI1 setSubformulae_and)
  with assms show "G \<in> setSubformulae F" 
    by (rule subsubformulae)
next
  have "H \<in> setSubformulae (G \<^bold>\<and> H)"  
    by (simp only: subformulae_self UnI2 UnI1 setSubformulae_and)
  with assms show "H \<in> setSubformulae F" 
    by (rule subsubformulae)
qed

lemma subformulas_in_subformulas_or:
  assumes "G \<^bold>\<or> H \<in> setSubformulae F" 
  shows "G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
proof (rule conjI)
  have "G \<in> setSubformulae (G \<^bold>\<or> H)" 
    by (simp only: subformulae_self UnI2 UnI1 setSubformulae_or)
  with assms show "G \<in> setSubformulae F" 
    by (rule subsubformulae)
next
  have "H \<in> setSubformulae (G \<^bold>\<or> H)"  
    by (simp only: subformulae_self UnI2 UnI1 setSubformulae_or)
  with assms show "H \<in> setSubformulae F" 
    by (rule subsubformulae)
qed

lemma subformulas_in_subformulas_imp:
  assumes "G \<^bold>\<rightarrow> H \<in> setSubformulae F" 
  shows "G \<in> setSubformulae F \<and> H \<in> setSubformulae F"
proof (rule conjI)
  have "G \<in> setSubformulae (G \<^bold>\<rightarrow> H)" 
    by (simp only: subformulae_self UnI2 UnI1 setSubformulae_imp)
  with assms show "G \<in> setSubformulae F" 
    by (rule subsubformulae)
next
  have "H \<in> setSubformulae (G \<^bold>\<rightarrow> H)"  
    by (simp only: subformulae_self UnI2 UnI1 setSubformulae_imp)
  with assms show "H \<in> setSubformulae F" 
    by (rule subsubformulae)
qed

lemmas subformulas_in_subformulas =
  subformulas_in_subformulas_and
  subformulas_in_subformulas_or
  subformulas_in_subformulas_imp
  subformulas_in_subformulas_not

section \<open>Conectivas generalizadas\<close>

text \<open>En esta sección definiremos nuevas conectivas y fórmulas a partir 
  de las ya definidas en el apartado anterior, junto con varios 
  resultados sobre las mismas. Veamos el primero.

  \begin{definicion}
    Se define la fórmula \<open>\<top>\<close> como la implicación \<open>\<bottom> \<longrightarrow> \<bottom>\<close>.
  \end{definicion}

  Se formaliza del siguiente modo.\<close>

definition Top ("\<top>") where
  "\<top> \<equiv> \<bottom> \<^bold>\<rightarrow> \<bottom>"

text \<open>Como podemos observar, se define mediante una relación de 
  equivalencia con otra fórmula ya conocida. El uso de dicha 
  equivalencia justifica el tipo @{term "definition"} empleado en este 
  caso. 

  Por la propia definición, es claro que \<open>\<top>\<close> no contiene ninguna
  variable proposicional, como se verifica a continuación en Isabelle.\<close>

lemma "atoms \<top> = \<emptyset>"
   by (simp only: Top_def formula.set Un_absorb)

text \<open>A continuación vamos a definir dos conectivas que generalizan la 
  conjunción y la disyunción para una lista finita de fórmulas. 

  En Isabelle está predefinido el tipo listas de la siguiente manera:

  \begin{definicion}
    Las listas de un tipo de elemento cualquiera se definen
    recursivamente como sigue.
    \begin{itemize}
      \item[] La lista vacía es una lista.
      \item[] Sea \<open>x\<close> un elemento, y \<open>xs\<close> una lista de elementos de su
      mismo tipo. Entonces, \<open>x#xs\<close> es una lista.
    \end{itemize}
  \end{definicion}

  La conjunción y disyunción generalizadas se definen sobre listas de
  fórmulas de manera recursiva:

  \begin{definicion}
  La conjunción generalizada de una lista de fórmulas se define 
  recursivamente como:
    \begin{itemize}
      \item La conjunción generalizada de la lista vacía es \<open>\<not>\<bottom>\<close>.
      \item Sea \<open>F\<close> una fórmula y \<open>Fs\<close> una lista de fórmulas. Entonces,
  la conjunción generalizada de \<open>F#Fs\<close> es la conjunción de \<open>F\<close> con la 
  conjunción generalizada de \<open>Fs\<close>.
    \end{itemize}
  \end{definicion}

  \begin{definicion}
  La disyunción generalizada de una lista de fórmulas se define 
  recursivamente como:
    \begin{itemize}
      \item La disyunción generalizada de la lista vacía es \<open>\<bottom>\<close>.
      \item Sea \<open>F\<close> una fórmula y \<open>Fs\<close> una lista de fórmulas. Entonces,
  la disyunción generalizada de \<open>F#Fs\<close> es la disyunción de \<open>F\<close> con la 
  disyunción generalizada de \<open>Fs\<close>.
    \end{itemize}
  \end{definicion}

  Notemos que al referirnos simplemente a disyunción o conjunción en las
  siguientes definiciones nos referiremos a la de dos elementos.

  Su formalización en Isabelle es la siguiente: \<close>

primrec BigAnd :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<And>_") where
  "\<^bold>\<And>[] = (\<^bold>\<not>\<bottom>)" 
| "\<^bold>\<And>(F#Fs) = F \<^bold>\<and> \<^bold>\<And>Fs"

primrec BigOr :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<Or>_") where
  "\<^bold>\<Or>[] = \<bottom>" 
| "\<^bold>\<Or>(F#Fs) = F \<^bold>\<or> \<^bold>\<Or>Fs"

text \<open>Ambas nuevas conectivas se definen con el tipo funciones 
  primitivas recursivas. Estas se basan en los dos casos descritos
  anteriormente según la definición recursiva de listas que se genera en
  Isabelle: la lista vacía representada como \<open>[]\<close> y la lista
  construida añadiendo una fórmula a una lista de fórmulas. 
  Además, se observa en cada definición el nuevo símbolo de 
  notación que aparece entre paréntesis.

  Por otro lado, como es habitual, de acuerdo a la definición recursiva
  de listas, Isabelle genera automáticamente un esquema inductivo que 
  emplearemos más adelante.

  Vamos a mostrar una propiedad sobre la conjunción plural.

  \begin{lema}
  El conjunto de átomos de la conjunción generalizada de una lista 
  de fórmulas es la unión de los conjuntos de átomos de cada fórmula de 
  la lista.
  \end{lema}

  \begin{demostracion}
  La prueba se hace por inducción sobre listas, en particular,
  listas de fórmulas. Para ello, demostremos el resultado en los casos
  siguientes. 

  En primer lugar lo probaremos para la lista vacía de fórmulas. Es
  claro por definición que la conjunción generalizada de la lista vacía
  es \<open>\<not> \<bottom>\<close>. De este modo, su conjunto de átomos coincide con los de 
  \<open>\<bottom>\<close>, luego es el vacío. Por tanto, queda demostrado el resultado, 
  pues el vacío es igual a la unión del conjunto de átomos de cada 
  elemento de la lista vacía de fórmulas. 

  Supongamos ahora una lista de fórmulas \<open>Fs\<close> verificando el enunciado.
  Sea la fórmula \<open>F\<close>, vamos a probar que \<open>F#Fs\<close> cumple la propiedad.
  Por definición de la nueva conectiva, el conjunto de átomos de 
  la conjunción generalizada de \<open>F#Fs\<close> es igual al conjunto de átomos de 
  la conjunción de \<open>F\<close> con la conjunción generalizada de \<open>Fs\<close>. De este
  modo, por propiedades del conjunto de átomos de la conjunción, tenemos
  que dicho conjunto es la unión del conjunto de átomos de \<open>F\<close> y el
  conjunto de átomos de la conjunción generalizada de \<open>Fs\<close>. Aplicando 
  ahora la hipótesis de inducción sobre \<open>Fs\<close>, tenemos que lo anterior es 
  igual a la unión del conjunto de átomos de \<open>F\<close> con la unión
 (generalizada) de los conjuntos de átomos de cada fórmula de \<open>Fs\<close>. 
  Luego, por propiedades de la unión, es equivalente a la unión de los 
  conjuntos de átomos de cada elemento de \<open>F#Fs\<close> como queríamos 
  demostrar.
  \end{demostracion}

  En Isabelle se formaliza como sigue.\<close>

lemma atoms_BigAnd: 
  "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
  oops

text \<open>Observemos el lado izquierdo de la igualdad. \<open>Fs\<close> es una 
  lista de fórmulas, luego la conjunción generalizada de dicha lista se 
  trata de una fórmula. Al aplicarle \<open>atoms\<close> a dicha fórmula, obtenemos 
  finalmente el conjunto de sus átomos. Por otro lado, en el lado 
  derecho de la igualdad tenemos el conjunto \<open>set Fs\<close> cuyos elementos 
  son las fórmulas de la lista \<open>Fs\<close>. De este modo, al aplicar \<open>atoms `\<close> 
  a dicho conjunto obtenemos la imagen por \<open>atoms\<close> de cada uno de sus
  elementos, es decir, un conjunto cuyos elementos son los 
  conjuntos de átomos de cada fórmula de \<open>Fs\<close>. Por último, mediante la 
  unión se obtiene el conjunto de los átomos de cada fórmula de la 
  lista inicial.

  Veamos ahora la demostración detallada. Esta seguirá el esquema de 
  inducción sobre listas. Previamente vamos a probar cada caso por
  separado.\<close>

lemma atoms_BigAnd_nil: 
  "atoms (\<^bold>\<And>[]) = \<Union> (atoms ` set Nil)"
proof -
  have "atoms (\<^bold>\<And>[]) = atoms (\<^bold>\<not> \<bottom>)" 
    by (simp only: BigAnd.simps(1))
  also have "\<dots> = atoms \<bottom>" 
    by (simp only: formula.set(3))
  also have "\<dots> = \<emptyset>" 
    by (simp only: formula.set(2))
  also have "\<dots> = \<Union> \<emptyset>"
    by (simp only: Union_empty)
  also have "\<dots> =  \<Union> (atoms ` \<emptyset>)"
    by (simp only: image_empty)
  also have "\<dots> = \<Union> (atoms ` set [])"
    by (simp only: list.set)
  finally show ?thesis
    by this
qed

text \<open>Mostramos el siguiente lema auxiliar que utilizaremos en la
  demostración del último caso de inducción.\<close>

lemma union_imagen: "f a \<union> \<Union> (f ` B) = \<Union> (f ` ({a} \<union> B))"
  by (simp only: Union_image_insert
                 insert_is_Un[THEN sym])

text \<open>Se trata de una modificación del lema \<open>Union_image_insert\<close> en 
  Isabelle para adaptarlo al caso particular. 

  \begin{itemize}
    \item[] @{thm[mode=Rule] Union_image_insert[no_vars]} 
      \hfill (@{text Union_image_insert})
  \end{itemize}

  Para ello empleamos el lema \<open>insert_is_Un\<close>.

  \begin{itemize}
    \item[] \<open>insert a A = {a} \<union> A\<close> \hspace{5cm} \<open>(insert_is_Un)\<close>
  \end{itemize}

  De esta manera, la unión de un conjunto de un solo elemento y otro 
  conjunto cualquiera es equivalente a insertar dicho elemento en el 
  conjunto. Además, aplicamos el lema seguido de \<open>[THEN sym]\<close> para 
  mostrar la equivalencia en el sentido en el que acaba de ser
  enunciada por simetría, pues en Isabelle aparece en sentido opuesto.
  Por tanto, el lema auxiliar \<open>union_imagen\<close> es fundamentalmente el
  lema de Isabelle\\ \<open>Union_image_insert\<close> teniendo en cuenta las
  equivalencias anteriores.

  Procedamos a la demostración del último caso de inducción.\<close>

lemma atoms_BigAnd_cons:
  assumes "atoms (\<^bold>\<And>Fs) = \<Union> (atoms ` set Fs)"
  shows "atoms (\<^bold>\<And>(F#Fs)) = \<Union> (atoms ` set (F#Fs))"
proof -
  have "atoms (\<^bold>\<And>(F#Fs)) = atoms (F \<^bold>\<and> \<^bold>\<And>Fs)"
    by (simp only: BigAnd.simps(2))
  also have "\<dots> = atoms F \<union> atoms (\<^bold>\<And>Fs)"
    by (simp only: formula.set(4))
  also have "\<dots> = atoms F \<union> \<Union>(atoms ` set Fs)"
    by (simp only: assms)
  also have "\<dots> = \<Union>(atoms ` ({F} \<union> set Fs))" 
    by (simp only: union_imagen)
  also have "\<dots> =  \<Union>(atoms ` set (F#Fs))"
    by (simp only: set_insert)
  finally show  "atoms (\<^bold>\<And>(F#Fs)) = \<Union>(atoms ` set (F#Fs))" 
    by this
qed

text \<open>Por tanto, la demostración detallada completa es la siguiente.\<close>

lemma "atoms (\<^bold>\<And>Fs) = \<Union> (atoms ` set Fs)"
proof (induction Fs)
  case Nil
  then show ?case by (rule atoms_BigAnd_nil)
next
  case (Cons a Fs)
  assume "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)" 
  then show ?case 
    by (rule atoms_BigAnd_cons)
qed

text \<open>Por último, su demostración automática.\<close>

lemma atoms_BigAnd: 
  "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
  by (induction Fs) simp_all
(*<*)
end
(*>*) 
