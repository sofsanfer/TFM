(*<*) 
theory Semantica
  imports 
    Sintaxis
begin
(*>*)

section \<open>Semántica\<close>

text \<open>En esta sección presentaremos la semántica de las fórmulas
  proposicionales y su formalización en Isabelle/HOL. 

  \begin{definicion}
  Una interpretación es una aplicación del conjunto de variables
  proposicionales en el conjunto \<open>\<BB>\<close> de los booleanos.
  \end{definicion}

  De este modo, las interpretaciones asignan valores de verdad a las 
  variables proposicionales.

  En Isabelle, se formaliza como sigue.\<close> 

type_synonym 'a valuation = "'a \<Rightarrow> bool"

  text \<open>Como podemos observar, \<open>'a valuation\<close> representa
  una función entre elementos de tipo \<open>'a\<close> cualquiera que conforman los
  átomos de una fórmula proposicional a los que les asigna un booleano. 
  Se define mediante el tipo \<open>type_synonym\<close>, pues consiste en renombrar 
  una construcción ya existente en Isabelle.

  Dada una interpretación, vamos a definir el valor de verdad de una 
  fórmula proposicional en dicha interpretación.

  \begin{definicion}
  Para cada interpretación \<open>\<A>\<close> existe una única aplicación \<open>\<I>\<^sub>\<A>\<close> desde 
  el conjunto de fórmulas al conjunto \<open>\<BB>\<close> de los booleanos definida 
  recursivamente sobre la estructura de las fórmulas como sigue:\\
  Sea \<open>F\<close> una fórmula cualquiera,
    \begin{itemize}
      \item Si \<open>F\<close> es una fórmula atómica de la forma \<open>p\<close>, entonces \\ 
        \<open>\<I>\<^sub>\<A>(F) = \<A>(p)\<close>.
      \item Si \<open>F\<close> es la fórmula \<open>\<bottom>\<close>, entonces \<open>\<I>\<^sub>\<A>(F) = False\<close>.
      \item Si \<open>F\<close> es de la forma \<open>\<not> G\<close> para cierta fórmula \<open>G\<close>, 
        entonces\\ \<open>\<I>\<^sub>\<A>(F) = \<not> \<I>\<^sub>\<A>(G)\<close>.
      \item Si \<open>F\<close> es de la forma \<open>G \<and> H\<close> para ciertas fórmulas \<open>G\<close> y 
        \<open>H\<close>, entonces\\ \<open>\<I>\<^sub>\<A>(F)= \<I>\<^sub>\<A>(G) \<and> \<I>\<^sub>\<A>(H)\<close>.
      \item Si \<open>F\<close> es de la forma \<open>G \<or> H\<close> para ciertas fórmulas \<open>G\<close> y 
        \<open>H\<close>, entonces\\ \<open>\<I>\<^sub>\<A>(F)= \<I>\<^sub>\<A>(G) \<or> \<I>\<^sub>\<A>(H)\<close>.
      \item Si \<open>F\<close> es de la forma \<open>G \<longrightarrow> H\<close> para ciertas fórmulas \<open>G\<close> y 
        \<open>H\<close>, entonces\\ \<open>\<I>\<^sub>\<A>(F)= \<I>\<^sub>\<A>(G) \<longrightarrow> \<I>\<^sub>\<A>(H)\<close>.
    \end{itemize}
  En estas condiciones se dice que \<open>\<I>\<^sub>\<A>(F)\<close> es el valor de la fórmula 
  \<open>F\<close> en la interpretación \<open>\<A>\<close>.
  \end{definicion}

  En Isabelle, dada una interpretación \<open>\<A>\<close> y una fórmula \<open>F\<close>, vamos a 
  definir \<open>\<I>\<^sub>\<A>(F)\<close> mediante la función \<open>formula_semantics \<A> F\<close>, 
  notado como \<open>\<A> \<Turnstile> F\<close>.\<close>

primrec formula_semantics :: 
  "'a valuation \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 51) where
  "\<A> \<Turnstile> Atom k = \<A> k" 
| "\<A> \<Turnstile> \<bottom> = False" 
| "\<A> \<Turnstile> Not F = (\<not> \<A> \<Turnstile> F)" 
| "\<A> \<Turnstile> And F G = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)" 
| "\<A> \<Turnstile> Or F G = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)" 
| "\<A> \<Turnstile> Imp F G = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"

text \<open>Como podemos observar, \<open>formula_semantics\<close> es una función
  primitiva recursiva, como indica el tipo \<open>primrec\<close>, notada con el 
  símbolo infijo \<open>\<Turnstile>\<close>. De este modo, dada una interpretación \<open>\<A>\<close> sobre 
  variables proposicionales de un tipo \<open>'a\<close> cualquiera y una fórmula,
  se define el valor de la fórmula en la interpretación \<open>\<A>\<close> como se 
  muestra. Veamos algunos ejemplos.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

have "(\<A> (1 := True, 2 := False, 3 := True) 
            \<Turnstile> (\<^bold>\<not> ((Atom 1 \<^bold>\<or> Atom 2)) \<^bold>\<rightarrow> Atom 3)) = True" 
  by simp
  
  have "(\<A> (1 := True) \<Turnstile> Atom 1) = True"
    by simp

  have "(\<A> (1 := True) \<Turnstile> \<^bold>\<not> (Atom 1)) = False"
    by simp

  have "(\<A> (1 := True, 2 := False) \<Turnstile> \<^bold>\<not> (Atom 1) \<^bold>\<and> (Atom 2)) = False"
    by simp

  have "(\<A> (1 := True, 2 := False, 3 := False) 
            \<Turnstile> (\<^bold>\<not> ((Atom 1 \<^bold>\<and> Atom 2)) \<^bold>\<rightarrow> Atom 3)) = False" 
    by simp

end

text \<open>En los ejemplos anteriores se ha usado la notación para
  funciones\\ \<open>f (a := b)\<close>. Dicha notación abreviada se corresponde con 
  la definción de \<open>fun_upd f a b\<close>.

  \begin{itemize}
    \item[] @{thm[mode=Def] fun_upd_def} 
      \hfill (@{text fun_upd_def})
  \end{itemize}

  Es decir, \<open>f (a:=b)\<close> es la función que para cualquier valor \<open>x\<close> del 
  dominio, si \<open>x = a\<close>, entonces devuelve \<open>b\<close>. En caso contrario, 
  devuelve el valor \<open>f x\<close>.

  A continuación veamos una serie de definiciones sobre fórmulas e 
  interpretaciones. En primer lugar, la noción de modelo de una 
  fórmula.

  \begin{definicion}
  Una interpretación es modelo de una fórmula si el valor de la
  fórmula dada dicha interpretación es \<open>Verdadero\<close>. 
  \end{definicion}

  En Isabelle se formaliza de la siguiente manera.\<close>

definition "isModel \<A> F \<equiv> \<A> \<Turnstile> F"

text \<open>Veamos cuáles de las interpretaciones de los ejemplos anteriores
  son modelos de las fórmulas dadas.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

  have "isModel (\<A> (1 := True)) (Atom 1)"
    by (simp add: isModel_def)

  have "\<not> isModel (\<A> (1 := True)) (\<^bold>\<not> (Atom 1))"
    by (simp add: isModel_def)

  have "\<not> isModel (\<A> (1 := True, 2 := False)) (\<^bold>\<not> (Atom 1) \<^bold>\<and> (Atom 2))"
    by (simp add: isModel_def)

  have "\<not> isModel (\<A> (1 := True, 2 := False, 3 := False)) 
          (\<^bold>\<not> ((Atom 1 \<^bold>\<and> Atom 2)) \<^bold>\<rightarrow> Atom 3)"
    by (simp add: isModel_def)

  have "isModel (\<A> (1 := True, 2 := False, 3 := True)) 
          (\<^bold>\<not> ((Atom 1 \<^bold>\<or> Atom 2)) \<^bold>\<rightarrow> Atom 3)"
    by (simp add: isModel_def)

end

text \<open>Demos ahora la noción de fórmula satisfacible.

  \begin{definicion}
    Una fórmula es satisfacible si tiene algún modelo.
  \end{definicion}

  Se concreta en Isabelle como sigue.\<close>

definition "satF(F) \<equiv> \<exists>\<A>. \<A> \<Turnstile> F"

text \<open>Mostremos ejemplos de fórmulas satisfacibles y no satisfacibles.
  Estas últimas son también llamadas contradicciones, pues son
  falsas para cualquier interpretación.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

  have "satF (Atom 1)"
    by (meson formula_semantics.simps(1) satF_def)

  have "satF (Atom 1 \<^bold>\<and> Atom 3)" 
    using satF_def by force

  have "\<not> satF (Atom 2 \<^bold>\<and> (\<^bold>\<not> (Atom 2)))"
    using satF_def by force

end

text \<open>Como podemos observar, \<open>isModel\<close> y \<open>satF\<close> se han 
  formalizado usando el tipo \<open>definition\<close> pues, en ambos casos, hemos
  renombrado una construcción no recursiva ya existente en Isabelle/HOL.

  Continuemos con la noción de fórmula válida o tautología.

  \begin{definicion} 
  \<open>F\<close> es una fórmula válida o tautología (\<open>\<Turnstile> F\<close>) si toda interpretación 
  es modelo de \<open>F\<close>. 
  \end{definicion}

  Es decir, una tautología es una fórmula que es verdadera para 
  cualquier interpretación. En otras palabras, toda interpretación es
  modelo de dicha fórmula. En Isabelle se formaliza de la siguiente
  manera.\<close>

abbreviation valid ("\<Turnstile> _" 51) where
  "\<Turnstile> F \<equiv> \<forall>\<A>. \<A> \<Turnstile> F"

text \<open>Por otro lado, podemos observar que se ha definido mediante el 
  tipo \<open>abbreviation\<close>, introduciendo una nueva notación para la 
  construcción formada por un cuantificador universal aplicado 
  al primer argumento de \<open>formula_semantics\<close>.

  Veamos un ejemplo clásico de tautología: el principio del tercio
  excluso.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

  have "\<Turnstile> (Atom 5 \<^bold>\<or> (\<^bold>\<not> (Atom 5)))"
    by simp

end

text \<open>Otro ejemplo de tautología se muestra con el siguiente lema.

  \begin{lema}
    La fórmula \<open>\<top>\<close> es una tautología.
  \end{lema}
 
  Veamos su prueba.

  \begin{demostracion}
    Sea una interpretación cualquiera \<open>\<A>\<close>. Es obvio que, aplicando la\\
    propiedad reflexiva de la implicación, tenemos que \<open>Verdadero\<close> es
    equivalente a suponer que valor de \<open>\<bottom>\<close> en \<open>\<A>\<close> se implica a sí 
    mismo. Por definición, se tiene que la implicación anterior es, a 
    su vez, equivalente al valor de la fórmula \<open>\<bottom> \<rightarrow> \<bottom>\<close> en la 
    interpretación \<open>\<A>\<close>. Según la definición de \<open>\<top>\<close>, tenemos que esto es
    igual al valor de la fórmula \<open>\<top>\<close> en la interpretación \<open>\<A>\<close>.
    Finalmente, mediante esta cadena de equivalencias se observa que
    el valor de \<open>\<top>\<close> en una interpretación \<open>\<A>\<close> cualquiera es 
    \<open>Verdadero\<close> como queríamos probar.    
  \end{demostracion}

  En Isabelle se enuncia y demuestra de manera detallada como sigue.\<close>

lemma  "\<A> \<Turnstile> \<top>" 
proof -
 have "\<A> \<Turnstile> \<bottom> \<longrightarrow> \<A> \<Turnstile> \<bottom>" 
   by (rule imp_refl)
 then have "\<A> \<Turnstile> (\<bottom> \<^bold>\<rightarrow> \<bottom>)"
   by (simp only: formula_semantics.simps(6))
 thus "\<A> \<Turnstile> \<top>" unfolding Top_def by this
qed

text \<open>Se demuestra automáticamente como sigue.\<close>

lemma top_semantics: "\<A> \<Turnstile> \<top>"
  unfolding Top_def by simp

text \<open>Una vez presentados los conceptos y ejemplos anteriores, 
  continuemos con el siguiente resultado de la sección.

  \begin{lema}
  Sea una fórmula \<open>F\<close> de modo que \<open>p\<close> es una variable proposicional que 
  no pertenece a su conjunto de átomos. Entonces, el valor de \<open>F\<close> en 
  una interpretación no depende del valor de la variable \<open>p\<close> en dicha 
  interpretación.
  \end{lema}

  En Isabelle se formaliza de la siguiente manera empleando la notación
  de \<open>fun_upd\<close>.\<close> 

lemma "p \<notin> atoms F \<Longrightarrow> (\<A>(p := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  oops

text\<open>Veamos ahora la prueba del lema.

  \begin{demostracion}
  Vamos a probar el resultado por inducción en la estructura recursiva
  de las fórmulas. Para ello, dada una interpretación cualquier \<open>\<A>\<close> y 
  una variable \<open>p\<close> que no pertenece al conjunto de átomos de una 
  fórmula, definimos la interpretación \<open>\<A>'\<close> como aquella que devuelve
  \<open>\<A>(q)\<close> para cualquier variable \<open>q\<close> distinta de \<open>p\<close>, y un valor 
  cualquiera \<open>V\<close> en caso contrario. Para demostrar que el valor de una 
  fórmula en una interpretación no depende del valor de \<open>p\<close> en dicha 
  interpretación, basta probar que el valor de la fórmula en \<open>\<A>\<close> 
  coincide con su valor en \<open>\<A>'\<close> según la definición dada anteriormente. 
  Demostremos los siguientes casos.

  Sea \<open>q\<close> una fórmula atómica cualquiera tal que \<open>p\<close> no pertenece
  al conjunto de sus átomos \<open>{q}\<close>. De este modo, se tiene \<open>q \<noteq> p\<close>. 
  Por definición, el valor de la fórmula atómica \<open>q\<close> en la 
  interpretación \<open>\<A>'\<close>, es \<open>\<A>'(q)\<close>. Como hemos visto que \<open>q \<noteq> p\<close>, 
  tenemos a su vez\\ \<open>\<A>'(q) = \<A>(q)\<close> según la definición de \<open>\<A>'\<close>. A su
  vez, \<open>\<A>(q)\<close> es el valor de la fórmula atómica \<open>q\<close> en la 
  interpretación \<open>\<A>\<close>, luego se tiene finalmente que ambos valores
  coinciden. 

  Sea la fórmula \<open>\<bottom>\<close>. Por definición, el valor de dicha fórmula es 
  \<open>Falso\<close> en cualquier interpretación, luego se verifica el
  resultado en particular.

  Sea \<open>F\<close> una fórmula tal que para cualquier variable que no pertenezca
  al conjunto de sus átomos, entonces el valor de \<open>F\<close> en la 
  interpretación \<open>\<A>\<close> coincide con su valor en la interpretación \<open>\<A>'\<close> 
  construida como se indica en el enunciado. Vamos a demostrar el 
  resultado para la fórmula \<open>\<not> F\<close> considerando una variable \<open>p\<close> 
  cualquiera que no pertenezca al conjunto de átomos de \<open>\<not> F\<close>. Como 
  los conjuntos de átomos de \<open>F\<close> y \<open>\<not> F\<close> son el mismo, entonces \<open>p\<close> 
  tampoco pertenece al conjunto de átomos de \<open>F\<close>. De este modo, por 
  hipótesis de inducción, el valor de la fórmula \<open>F\<close> en la 
  interpretación \<open>\<A>\<close> coincide con su valor en la interpretación 
  \<open>\<A>'\<close>. Por otro lado, por definición tenemos que el valor de la 
  fórmula \<open>\<not> F\<close> en \<open>\<A>\<close> es la negación del valor de \<open>F\<close> en \<open>\<A>\<close>. 
  Por lo visto anteriormente según la hipótesis de inducción, esto es 
  igual a la negación del valor de \<open>F\<close> en \<open>\<A>'\<close>. Por último, 
  por definición, esto es igual al valor de \<open>\<not> F\<close> en \<open>\<A>'\<close>, como 
  quería demostrar.

  Sean ahora las fórmulas \<open>G\<close> y \<open>H\<close> tales que, para cada una, su valor
  en la interpretación \<open>\<A>\<close> coincide con su valor en la
  interpretación \<open>\<A>'\<close> construida como se indica en el enunciado a 
  partir de una variable que no pertenezca al conjunto de sus átomos. 
  Veamos que se verifica el resultado para la fórmula \<open>G \<and> H\<close>.
  Sea \<open>p\<close> una variable proposicional que no pertenece al conjunto de
  átomos de \<open>G \<and> H\<close>. Por definición, dicho conjunto es igual a la unión
  del conjunto de átomos de \<open>G\<close> y el conjunto de átomos de \<open>H\<close>.
  Por tanto, en particular \<open>p\<close> no pertenece al conjunto de átomos de
  \<open>G\<close> y, por hipótesis de inducción, el valor de \<open>G\<close> en la
  interpretación \<open>\<A>\<close> coincide con su valor en la
  interpretación \<open>\<A>'\<close>. Por el mismo motivo, \<open>p\<close> no pertenece al
  conjunto de átomos de \<open>H\<close> y, por hipótesis de inducción,
  el valor de \<open>H\<close> es el mismo en las interpretaciones \<open>\<A>\<close> y \<open>\<A>'\<close>. 
  Aclaradas estas observaciones, se tiene por definición que el valor 
  de la fórmula \<open>G \<and> H\<close> en la interpretación \<open>\<A>'\<close> es 
  la conjunción del valor de \<open>G\<close> en \<open>\<A>'\<close> y el valor de \<open>H\<close> en \<open>\<A>'\<close>. 
  Por lo demostrado anteriormente según las hipótesis de inducción, 
  esto es igual a la conjunción del valor de \<open>G\<close> en \<open>\<A>\<close> y el valor de 
  \<open>H\<close> en \<open>\<A>\<close>. Aplicando la definición, esto es el valor de \<open>G \<and> H\<close> 
  en la interpretación \<open>\<A>\<close>. Por tanto, queda probada la equivalencia 
  en este caso.

  Sean las fórmulas \<open>G\<close> y \<open>H\<close> cumpliendo las hipótesis supuestas
  para el caso anterior. Veamos que el resultado se verifica para la
  fórmula \<open>G \<or> H\<close>. Sea \<open>p\<close> una variable proposicional que no pertenece
  al conjunto de átomos de \<open>G \<or> H\<close>. Por definición, dicho conjunto es
  la unión de los conjuntos de átomos de \<open>G\<close> y \<open>H\<close>. Por tanto, como se
  ha probado en el caso anterior, tenemos que \<open>p\<close> no pertenece al
  conjunto de átomos de \<open>G\<close>. Por tanto, aplicando la hipótesis de 
  inducción se tiene que el valor de \<open>G\<close> en la interpretación \<open>\<A>\<close> 
  coincide con su valor en la interpretación \<open>\<A>'\<close>. Análogamente 
  ocurre para la fórmula \<open>H\<close> como vimos en el caso anterior, de modo
  que \<open>p\<close> no pertenece al conjunto de átomos de \<open>H\<close>. Por tanto, por 
  hipótesis de inducción, el valor de \<open>H\<close> es el mismo en \<open>\<A>\<close> y \<open>\<A>'\<close>.
  Veamos la equivalencia. 
  Por definición tenemos que el valor de la fórmula \<open>G \<or> H\<close> en la 
  interpretación \<open>\<A>'\<close> es la disyunción entre el valor de \<open>G\<close> en \<open>\<A>'\<close>
  y el valor de \<open>H\<close> en \<open>\<A>'\<close>. Por lo probado anteriormente según las 
  hipótesis de inducicón, esto es igual a la disyunción entre el valor 
  de \<open>G\<close> en \<open>\<A>\<close> y el valor de \<open>H\<close> en \<open>\<A>\<close>. Por definición, se 
  verifica que es igual al valor de \<open>G \<or> H\<close> en la interpretación \<open>\<A>\<close>, 
  como queríamos demostrar.

  Probemos finalmente el último caso considerando las fórmulas \<open>G\<close> y
  \<open>H\<close> bajo las condiciones de los dos casos anteriores. Sea \<open>p\<close> una 
  variable proposicional que no pertenece al conjunto de átomos de 
  \<open>G \<rightarrow> H\<close>. Como dicho conjunto es la unión del conjunto de átomos de
  \<open>G\<close> y el de \<open>H\<close>, \<open>p\<close> no pertenece ni al conjunto de átomos de \<open>G\<close> ni
  al de \<open>H\<close>. Por lo tanto, por hipótesis de inducción, el valor de \<open>G\<close> 
  es el mismo en las interpretaciones \<open>\<A>\<close> y \<open>\<A>'\<close>, y lo mismo ocurre 
  para \<open>H\<close>. Veamos ahora la cadena de equivalencias. Por definición 
  tenemos que el valor de la fórmula \<open>G \<rightarrow> H\<close> en la interpretación 
  \<open>\<A>'\<close> es la implicación del valor de \<open>G\<close> en \<open>\<A>'\<close> y el valor de \<open>H\<close>
  en \<open>\<A>'\<close>. Análogamente a los casos anteriores por las hipótesis de 
  inducción, esto es igual a la implicación del valor de \<open>G\<close> en \<open>\<A>\<close> y 
  el valor de \<open>H\<close> en \<open>\<A>\<close>. Por definición, esto es igual al valor de 
  \<open>G \<rightarrow> H\<close> en la interpretación \<open>\<A>\<close>, probando así el resultado.
  \end{demostracion}

  Veamos a continuación la demostración detallada del lema en
  Isabelle/HOL. Para facilitar la lectura, inicialmente se ha
  probado el resultado para cada caso de la estructura de las fórmulas
  como es habitual. Además, se han empleado los lemas auxiliares 
  \<open>irrelevant_atom_atomic_l1\<close>, \<open>irrelevant_atom_not_l1\<close>,
  \<open>irrelevant_atom_and_l1\<close>,\\ \<open>irrelevant_atom_or_l1\<close> e 
  \<open>irrelevant_atom_imp_l1\<close> para mostrar resultados sobre la no
  pertenencia a los conjuntos de átomos en cada caso. Es fácil observar 
  que no ha sido necesario el uso de lemas auxiliares en el caso de la 
  fórmula \<open>\<bottom>\<close>, pues su conjunto de átomos es el vacío.\<close>

lemma irrelevant_atom_atomic_l1:
  assumes "p \<notin> atoms (Atom x)" 
  shows "x \<noteq> p"
proof (rule notI)
  assume "x = p"
  then have "p \<in> {x}" 
    by (simp only: singleton_iff)
  also have "\<dots> = atoms (Atom x)"
    by (simp only: formula.set(1))
  finally have "p \<in> atoms (Atom x)"
    by this 
  with assms show "False"  
    by (rule notE)
qed

lemma irrelevant_atom_atomic:
  assumes "p \<notin> atoms (Atom x)" 
  shows "(\<A>(p := V)) \<Turnstile> (Atom x) \<longleftrightarrow> \<A> \<Turnstile> (Atom x)"
proof -
  have "x \<noteq> p"
    using assms
    by (rule irrelevant_atom_atomic_l1)
  have "(\<A>(p := V)) \<Turnstile> (Atom x) = (\<A>(p := V)) x"
    by (simp only: formula_semantics.simps(1))
  also have "\<dots> = \<A> x"
    using \<open>x \<noteq> p\<close>
    by (rule fun_upd_other)
  also have "\<dots> = \<A> \<Turnstile> (Atom x)"
    by (simp only: formula_semantics.simps(1))
  finally show ?thesis
    by this
qed

lemma irrelevant_atom_bot:
  assumes "p \<notin> atoms \<bottom>" 
  shows "(\<A>(p := V)) \<Turnstile> \<bottom> \<longleftrightarrow> \<A> \<Turnstile> \<bottom>"
  by (simp only: formula_semantics.simps(2))

lemma irrelevant_atom_not_l1:
  assumes "p \<notin> atoms (\<^bold>\<not> F)"
  shows   "p \<notin> atoms F"
proof
  assume "p \<in> atoms F"
  then have "p \<in> atoms (\<^bold>\<not> F)"
    by (simp only: formula.set(3)) 
  with assms show False
    by (rule notE)
qed

lemma irrelevant_atom_not:
  assumes "p \<notin> atoms F \<Longrightarrow> \<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "p \<notin> atoms (\<^bold>\<not> F)"
 shows "\<A>(p := V) \<Turnstile> \<^bold>\<not> F \<longleftrightarrow> \<A> \<Turnstile> \<^bold>\<not> F"
proof -
  have "p \<notin> atoms F"
    using assms(2) by (rule irrelevant_atom_not_l1)
  then have "\<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "\<A>(p := V) \<Turnstile> \<^bold>\<not> F = (\<not> \<A>(p := V) \<Turnstile> F)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> \<A> \<Turnstile> F)"
    by (simp only: \<open>\<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F\<close>)
  also have "\<dots> = \<A> \<Turnstile> \<^bold>\<not> F"
    by (simp only: formula_semantics.simps(3))
  finally show "\<A>(p := V) \<Turnstile> \<^bold>\<not> F \<longleftrightarrow> \<A> \<Turnstile> \<^bold>\<not> F"
    by this
qed

lemma irrelevant_atom_and_l1:
  assumes "p \<notin> atoms (F \<^bold>\<and> G)"
  shows   "p \<notin> atoms F"
proof 
  assume "p \<in> atoms F"
  then have "p \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "p \<in> atoms (F \<^bold>\<and> G)"
    by (simp only: formula.set(4))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_and_l2:
  assumes "p \<notin> atoms (F \<^bold>\<and> G)"
  shows   "p \<notin> atoms G"
proof 
  assume "p \<in> atoms G"
  then have "p \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "p \<in> atoms (F \<^bold>\<and> G)"
    by (simp only: formula.set(4))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_and:
  assumes "p \<notin> atoms F \<Longrightarrow> \<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "p \<notin> atoms G \<Longrightarrow> \<A>(p := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "p \<notin> atoms (F \<^bold>\<and> G)"
  shows "\<A>(p := V) \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<and> G)"
proof -
  have "p \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_and_l1)
  then have HF: "\<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "p \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_and_l2)
  then have HG: "\<A>(p := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(p := V) \<Turnstile> (F \<^bold>\<and> G) = (\<A>(p := V) \<Turnstile> F \<and> \<A>(p := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<and> G)"
    by (simp only: formula_semantics.simps(4))
  finally show "\<A>(p := V) \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<and> G)"
    by this
qed

lemma irrelevant_atom_or_l1:
  assumes "p \<notin> atoms (F \<^bold>\<or> G)"
  shows   "p \<notin> atoms F"
proof 
  assume "p \<in> atoms F"
  then have "p \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "p \<in> atoms (F \<^bold>\<or> G)"
    by (simp only: formula.set(5))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_or_l2:
  assumes "p \<notin> atoms (F \<^bold>\<or> G)"
  shows   "p \<notin> atoms G"
proof 
  assume "p \<in> atoms G"
  then have "p \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "p \<in> atoms (F \<^bold>\<or> G)"
    by (simp only: formula.set(5))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_or:
  assumes "p \<notin> atoms F \<Longrightarrow> \<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "p \<notin> atoms G \<Longrightarrow> \<A>(p := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "p \<notin> atoms (F \<^bold>\<or> G)"
  shows   "\<A>(p := V) \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<or> G)"
proof -
  have "p \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_or_l1)
  then have HF: "\<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "p \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_or_l2)
  then have HG: "\<A>(p := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(p := V) \<Turnstile> (F \<^bold>\<or> G) = (\<A>(p := V) \<Turnstile> F \<or> \<A>(p := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<or> G)"
    by (simp only: formula_semantics.simps(5))
  finally show "\<A>(p := V) \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<or> G)"
    by this
qed

lemma irrelevant_atom_imp_l1:
  assumes "p \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows   "p \<notin> atoms F"
proof 
  assume "p \<in> atoms F"
  then have "p \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "p \<in> atoms (F \<^bold>\<rightarrow> G)"
    by (simp only: formula.set(6))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_imp_l2:
  assumes "p \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows   "p \<notin> atoms G"
proof 
  assume "p \<in> atoms G"
  then have "p \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "p \<in> atoms (F \<^bold>\<rightarrow> G)"
    by (simp only: formula.set(6))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_imp:
  assumes "p \<notin> atoms F \<Longrightarrow> \<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "p \<notin> atoms G \<Longrightarrow> \<A>(p := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "p \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows "\<A>(p := V) \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
proof -
  have "p \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_imp_l1)
  then have HF: "\<A>(p := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "p \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_imp_l2)
  then have HG: "\<A>(p := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(p := V) \<Turnstile> (F \<^bold>\<rightarrow> G) = (\<A>(p := V) \<Turnstile> F \<longrightarrow> \<A>(p := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(6))
  also have "\<dots> = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
    by (simp only: formula_semantics.simps(6))
  finally show "\<A>(p := V) \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
    by this
qed

lemma "p \<notin> atoms F \<Longrightarrow> (\<A>(p := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
proof (induction F)
  case (Atom x)
  then show ?case by (rule irrelevant_atom_atomic)
next
  case Bot
  then show ?case by (rule irrelevant_atom_bot)
next
  case (Not F)
  then show ?case by (rule irrelevant_atom_not)
next
  case (And F1 F2)
  then show ?case by (rule irrelevant_atom_and)
next
  case (Or F1 F2)
  then show ?case by (rule irrelevant_atom_or)
next
  case (Imp F1 F2)
  then show ?case by (rule irrelevant_atom_imp)
qed

text \<open>Por último, su demostración automática.\<close>

lemma irrelevant_atom: 
  "p \<notin> atoms F \<Longrightarrow> (\<A>(p := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  by (induction F) simp_all

text \<open>Procedamos con el siguiente lema de la sección.

  \begin{lema}
    Si dos interpretaciones coinciden sobre el conjunto de átomos de una 
    fórmula, entonces dicha fórmula tiene el mismo valor en ambas
    interpretaciones. 
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  oops

text \<open>Vamos a probar el resultado.

  \begin{demostracion}
    La prueba sigue el esquema de inducción sobre la estructura de las
    fórmulas. De este modo, procedamos con la demostración de cada
    caso.

    En primer lugar sea una fórmula atómica \<open>p\<close>, donde \<open>p\<close> es una 
    variable proposicional cualquiera. Sean las interpretaciones
    \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> tales que toman los mismos valores sobre el conjunto de
    átomos de \<open>p\<close>. Veamos que el valor de \<open>p\<close> en \<open>\<A>\<^sub>1\<close> coincide con
    su valor en \<open>\<A>\<^sub>2\<close>. Por definición, el valor de \<open>p\<close> en la
    interpretación \<open>\<A>\<^sub>1\<close> es \<open>\<A>\<^sub>1(p)\<close>. Como el conjunto de átomos de
    \<open>p\<close> es \<open>{p}\<close>, se tiene por hipótesis que \<open>\<A>\<^sub>1(p) = \<A>\<^sub>2(p)\<close>.
    Finalmente, aplicando la definición, esto es igual al valor de la 
    fórmula \<open>p\<close> en la interpretación \<open>\<A>\<^sub>2\<close>, como queríamos probar.

    Consideremos ahora la fórmula \<open>\<bottom>\<close> y dos interpretaciones en las 
    condiciones del enunciado. Es fácil observar que, como el valor de 
    \<open>\<bottom>\<close> es \<open>Falso\<close> en cualquier interpretación, se tiene en 
    particular el resultado.

    Sea una fórmula \<open>F\<close> tal que, si dos interpretaciones coinciden sobre
    el conjunto de átomos de \<open>F\<close>, entonces el valor de \<open>F\<close> es el mismo
    en ambas interpretaciones. Sean dos interpretaciones cualesquiera
    \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> que toman los mismos valores sobre el conjunto de
    átomos de \<open>\<not> F\<close>. Vamos a probar que el valor de \<open>\<not> F\<close> en \<open>\<A>\<^sub>1\<close>
    coincide con su valor en \<open>\<A>\<^sub>2\<close>.
    Observemos que, como el conjunto de átomos de \<open>F\<close> y \<open>\<not> F\<close>
    coinciden, se tiene por hipótesis de inducción que el valor de \<open>F\<close>
    en \<open>\<A>\<^sub>1\<close> coincide con su valor en \<open>\<A>\<^sub>2\<close>. Por otro lado, por
    definición, el valor de \<open>\<not> F\<close> en \<open>\<A>\<^sub>1\<close> es la negación del valor
    de \<open>F\<close> en \<open>\<A>\<^sub>1\<close>. Por la observación anterior, esto es igual a la
    negación del valor de \<open>F\<close> en \<open>\<A>\<^sub>2\<close> que, por definición, es el
    valor de \<open>\<not> F\<close> en \<open>\<A>\<^sub>2\<close>, probando así el resultado.

    Consideremos las fórmulas \<open>F\<close> y \<open>G\<close> con las mismas hipótesis que
    la fórmula del caso anterior. Sean las interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> 
    tales que coinciden sobre el conjunto de átomos de \<open>F \<and> G\<close>. Vamos a
    probar que el valor de \<open>F \<and> G\<close> en \<open>\<A>\<^sub>1\<close> es el mismo que en \<open>\<A>\<^sub>2\<close>.
    Como el conjunto de átomos de \<open>F \<and> G\<close> es la unión del conjunto de
    átomos de \<open>F\<close> y el conjunto de átomos de \<open>G\<close>, tenemos que \<open>\<A>\<^sub>1\<close> y 
    \<open>\<A>\<^sub>2\<close> coinciden sobre los elementos de dicha unión. En particular,
    coinciden sobre los elementos del conjunto de átomos de \<open>F\<close> y, por
    hipótesis de inducción, tenemos que el valor de \<open>F\<close> en \<open>\<A>\<^sub>1\<close> 
    coincide con su valor en \<open>\<A>\<^sub>2\<close>. Del mismo modo, las
    interpretaciones anteriores coinciden también sobre los elementos
    del conjunto de átomos de \<open>G\<close> luego, aplicando análogamente la 
    hipótesis de inducción, tenemos que el valor de \<open>G\<close> es el mismo 
    en las interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close>. Veamos ahora que el valor
    de \<open>F \<and> G\<close> también coincide en dichas interpretaciones.
    Por definición, el valor de \<open>F \<and> G\<close> en \<open>\<A>\<^sub>1\<close> es la conjunción
    del valor de \<open>F\<close> en \<open>\<A>\<^sub>1\<close> y el valor de \<open>G\<close> en \<open>\<A>\<^sub>1\<close>. Por lo 
    obtenido anteriormente por las hipótesis de inducción, tenemos que
    esto es igual a la conjunción del valor de \<open>F\<close> en \<open>\<A>\<^sub>2\<close> y el
    valor de \<open>G\<close> en \<open>\<A>\<^sub>2\<close>. Por último se tiene que esto es igual al
    valor de \<open>F \<and> G\<close> en \<open>\<A>\<^sub>2\<close> tras aplicar la definición.

    Volvamos a considerar \<open>F\<close> y \<open>G\<close> en las condiciones anteriores y
    dos interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> que coinciden sobre el
    conjunto de átomos de \<open>F \<or> G\<close>. Vamos a probar que el valor de 
    dicha fórmula es el mismo en ambas interpretaciones.
    De manera análoga al caso anterior, como el conjunto de átomos de
    \<open>F \<or> G\<close> es la unión del conjunto de átomos de \<open>F\<close> y el conjunto de
    átomos de \<open>G\<close>, tenemos que las interpretaciones coinciden sobre los
    elementos de esta unión. En particular, coinciden sobre el conjunto
    de átomos de \<open>F\<close>. Por tanto, por hipótesis de inducción, el valor
    de \<open>F\<close> en \<open>\<A>\<^sub>1\<close> coincide con su valor en \<open>\<A>\<^sub>2\<close>. Igualmente 
    obtenemos que las interpretaciones coinciden sobre el conjunto de
    átomos de \<open>G\<close> y, aplicando de nuevo hipótesis de inducción, el 
    valor de \<open>G\<close> es el mismo en ambas interpretaciones. 
    Por otra parte, por definición tenemos que le valor de \<open>F \<or> G\<close> en
    la interpretación \<open>\<A>\<^sub>1\<close> es la disyunción entre el valor de \<open>F\<close> en
    \<open>\<A>\<^sub>1\<close> y el valor de \<open>G\<close> en \<open>\<A>\<^sub>1\<close>. Por las observaciones
    anteriores derivadas de las hipótesis de inducción, tenemos que
    esto es igual a la disyunción entre el valor de \<open>F\<close> en \<open>\<A>\<^sub>2\<close> y
    el valor de \<open>G\<close> en \<open>\<A>\<^sub>2\<close>. Por definición, esto es el valor de 
    \<open>F \<or> G\<close> en \<open>\<A>\<^sub>2\<close>, como queríamos demostrar.

    Veamos el último caso de las fórmulas. Sean \<open>F\<close> y \<open>G\<close> fórmulas en 
    las condiciones de los casos anteriores. Consideremos las
    interpretaciones \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close> que coinciden sobre los elementos
    del conjunto de átomos de \<open>F \<rightarrow> G\<close>. Probemos que el valor de 
    \<open>F \<rightarrow> G\<close> es el mismo en ambas interpretaciones. Por definición, 
    el conjunto de átomos de\\ \<open>F \<rightarrow> G\<close> es la unión de los
    conjuntos de átomos de \<open>F\<close> y \<open>G\<close>. Por tanto, dichas
    interpretaciones coinciden sobre los elementos de dicha unión. 
    Como hemos visto en casos anteriores, en particular coinciden sobre
    los átomos de \<open>F\<close> luego, por hipótesis de inducción, el valor de 
    \<open>F\<close> en \<open>\<A>\<^sub>1\<close> coincide con su valor en \<open>\<A>\<^sub>2\<close>. Análogamente, las
    interpretaciones coinciden sobre los átomos de \<open>G\<close> y, por hipótesis
    de inducción, el valor de \<open>G\<close> es el mismo en ambas
    interpretaciones. Probemos que también coincide el valor de \<open>F \<rightarrow> G\<close>
    en \<open>\<A>\<^sub>1\<close> y \<open>\<A>\<^sub>2\<close>.
    Por definición, el valor de \<open>F \<rightarrow> G\<close> en \<open>\<A>\<^sub>1\<close> es la implicación
    entre el valor de \<open>F\<close> en \<open>\<A>\<^sub>1\<close> y el valor de \<open>G\<close> en \<open>\<A>\<^sub>1\<close>. De
    esta manera, por las observaciones anteriores tenemos que esto es
    igual a la implicación entre el valor de \<open>F\<close> en \<open>\<A>\<^sub>2\<close> y el valor
    de \<open>G\<close> en \<open>\<A>\<^sub>2\<close>. Finalmente, por definición, esto es el valor de
    \<open>F \<rightarrow> G\<close> en la interpretación \<open>\<A>\<^sub>2\<close>, probando así el resultado.    
  \end{demostracion}

  Probemos ahora el lema de forma detallada en Isabelle, haciendo cada
  caso de la estructura de las fórmulas por separado y empleando lemas
  auxiliares sobre la pertenencia a los conjuntos de átomos cuando sea 
  necesario.\<close>

lemma relevant_atoms_same_semantics_atomic_l1:
  "x \<in> atoms (Atom x)"
proof 
  show "x \<in> {x}"
    by (simp only: singleton_iff)
next
  show "{x} \<subseteq> atoms (Atom x)"
    by (simp only: formula.set(1))
qed

lemma relevant_atoms_same_semantics_atomic: 
  assumes "\<forall>k \<in> atoms (Atom x). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
  shows   "\<A>\<^sub>1 \<Turnstile> Atom x \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> Atom x"
proof -
  have "\<A>\<^sub>1 \<Turnstile> Atom x = \<A>\<^sub>1 x"
    by (simp only: formula_semantics.simps(1))
  also have "\<dots> = \<A>\<^sub>2 x"
    using  assms(1)
    by (simp only: relevant_atoms_same_semantics_atomic_l1)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> Atom x"
    by (simp only: formula_semantics.simps(1))
  finally show ?thesis
    by this
qed

text \<open>Para las fórmulas atómicas, se observa el uso del lema 
  auxiliar\\ \<open>relevant_atoms_same_semantics_atomic_l\<close>. Sigamos con los
  siguientes casos.\<close>

lemma relevant_atoms_same_semantics_bot: 
  assumes "\<forall>k \<in> atoms \<bottom>. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
  shows "\<A>\<^sub>1 \<Turnstile> \<bottom> \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> \<bottom>"
  by (simp only: formula_semantics.simps(2))

lemma relevant_atoms_same_semantics_not: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms (\<^bold>\<not> F). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
        shows "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
proof -
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(2)
    by (simp only: formula.set(3))
  then have H:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F) = (\<not> \<A>\<^sub>1 \<Turnstile> F)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> \<A>\<^sub>2 \<Turnstile> F)"
    using H by (rule arg_cong)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
    by (simp only: formula_semantics.simps(3))
  finally show ?thesis
    by this
qed

text \<open>Para los casos de la fórmula \<open>\<bottom>\<close> y la negación \<open>\<not> F\<close> no han sido
  necesarios los lemas auxiliares pues, en el primer caso, el conjunto
  de átomos es el vacío y, en el segundo caso, el conjunto de átomos de
  \<open>\<not> F\<close> coincide con el de \<open>F\<close>. Finalmente, introducimos los siguientes 
  lemas auxiliares para facilitar las demostraciones detalladas en 
  Isabelle de los casos correspondientes a las conectivas binarias.\<close>

lemma forall_union1: 
  assumes "\<forall>x \<in> A \<union> B. P x"
  shows "\<forall>x \<in> A. P x"
proof (rule ballI)
  fix x
  assume "x \<in> A"
  then have "x \<in> A \<union> B" 
    by (simp only: UnI1)
  then show "P x" 
    by (simp only: assms)
qed

lemma forall_union2:
  assumes "\<forall>x \<in> A \<union> B. P x"
  shows "\<forall>x \<in> B. P x"
proof (rule ballI)
  fix x
  assume "x \<in> B"
  then have "x \<in> A \<union> B" 
    by (simp only: UnI2)
  then show "P x" 
    by (simp only: assms)
qed

text \<open>Empleando dichos resultados, veamos las demostraciones detalladas
  de los tres últimos casos. Después se mostrará la demostración 
  detallada del lema completo en Isabelle.\<close>

lemma relevant_atoms_same_semantics_and: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<and> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
        shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<and> G)"
proof -
  have H:"\<forall>k \<in> atoms F \<union> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by (simp only: formula.set(4))
  then have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    by (rule forall_union1)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    using H by (rule forall_union2)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    by (simp only: assms(2))
  have "\<A>\<^sub>1 \<Turnstile> F \<^bold>\<and> G = (\<A>\<^sub>1 \<Turnstile> F \<and> \<A>\<^sub>1 \<Turnstile> G)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A>\<^sub>2 \<Turnstile> F \<and> \<A>\<^sub>2 \<Turnstile> G)"
    using H1 H2 by (rule arg_cong2)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> F \<^bold>\<and> G"
    by (simp only: formula_semantics.simps(4))
  finally show ?thesis 
    by this
qed

lemma relevant_atoms_same_semantics_or: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<or> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
     shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)"
proof -
  have H:"\<forall>k \<in> atoms F \<union> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by (simp only: formula.set(5))
  then have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    by (rule forall_union1)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    using H by (rule forall_union2)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    by (simp only: assms(2))
  have "\<A>\<^sub>1 \<Turnstile> F \<^bold>\<or> G = (\<A>\<^sub>1 \<Turnstile> F \<or> \<A>\<^sub>1 \<Turnstile> G)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A>\<^sub>2 \<Turnstile> F \<or> \<A>\<^sub>2 \<Turnstile> G)"
    using H1 H2 by (rule arg_cong2)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> F \<^bold>\<or> G"
    by (simp only: formula_semantics.simps(5))
  finally show ?thesis 
    by this
qed

lemma relevant_atoms_same_semantics_imp: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<rightarrow> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
     shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<rightarrow> G)"
proof -
  have H:"\<forall>k \<in> atoms F \<union> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by (simp only: formula.set(6))
  then have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    by (rule forall_union1)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
    using H by (rule forall_union2)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    by (simp only: assms(2))
  have "\<A>\<^sub>1 \<Turnstile> F \<^bold>\<rightarrow> G = (\<A>\<^sub>1 \<Turnstile> F \<longrightarrow> \<A>\<^sub>1 \<Turnstile> G)"
    by (simp only: formula_semantics.simps(6))
  also have "\<dots> = (\<A>\<^sub>2 \<Turnstile> F \<longrightarrow> \<A>\<^sub>2 \<Turnstile> G)"
    using H1 H2 by (rule arg_cong2)
  also have "\<dots> = \<A>\<^sub>2 \<Turnstile> F \<^bold>\<rightarrow> G"
    by (simp only: formula_semantics.simps(6))
  finally show ?thesis 
    by this
qed

lemma "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
proof (induction F)
case (Atom x)
  then show ?case by (rule relevant_atoms_same_semantics_atomic)
next
  case Bot
then show ?case by (rule relevant_atoms_same_semantics_bot)
next
  case (Not F)
then show ?case by (rule relevant_atoms_same_semantics_not)
next
  case (And F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_and)
next
case (Or F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_or)
next
  case (Imp F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_imp)
qed

text \<open>Su demostración automática es la siguiente.\<close>

lemma relevant_atoms_same_semantics: 
   "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  by (induction F) simp_all

section \<open>Semántica de fórmulas con conectivas generalizadas\<close>

text \<open>En este apartado mostraremos varios resultados relativos a la 
  semántica de las fórmulas construidas con conectivas generalizadas.

  \begin{lema}
    Una interpretación es modelo de la conjunción generalizada de una 
    lista de fórmulas si y solo si es modelo de cada fórmula de la
    lista.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "(\<A> \<Turnstile> \<^bold>\<And>Fs) \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
  oops

text \<open>Como podemos observar, en el enunciado de la derecha hemos
  empleado \<open>set\<close> para cambiar al tipo de los conjuntos la lista de 
  fórmulas, pues esto permite emplear el cuantificador universal.

  Procedamos con la prueba del lema.

  \begin{demostracion}
   La prueba se basa en el esquema de inducción sobre listas. Para ello, 
   demostraremos el resultado mediante cadenas de equivalencias en los 
   siguientes casos.

   En primer lugar, lo probamos para la lista vacía de fórmulas. Sea la
   interpretación \<open>\<A>\<close> tal que es modelo de la conjunción generalizada
   de la lista vacía. Por definición de la conjunción generalizada,
   \<open>\<A>\<close> es modelo de \<open>\<not> \<bottom>\<close>. Aplicando la definición del valor de una
   fórmula en una interpretación para el caso de la negación,
   tenemos que esto es equivalente a que \<open>\<A>\<close> no es modelo de \<open>\<bottom>\<close>.
   Análogamente, como sabemos que el valor de \<open>\<bottom>\<close> es \<open>Falso\<close> en 
   cualquier interpretación, se tiene que lo anterior es equivalente a
   \<open>\<not> Falso\<close>, es decir, \<open>Verdadero\<close>. Por otro lado, por propiedades
   del conjunto vacío, se tiene que toda propiedad sobre sus elementos
   es verdadera. Por tanto, lo anterior es equivalente a decir que \<open>\<A>\<close> 
   es modelo de todos los elementos del conjunto vacío. Es decir, \<open>\<A>\<close>
   es modelo de todos los elementos de la lista vacía, como queríamos
   demostrar. 

   Consideramos ahora la interpretación \<open>\<A>\<close> y la lista de fórmulas
   \<open>Fs\<close> de modo que \<open>\<A>\<close> es modelo de la conjunción generalizada de \<open>Fs\<close> 
   si y solo si es modelo de cada fórmula de \<open>Fs\<close>. Veamos ahora que se 
   verifica la propiedad para la lista \<open>F#Fs\<close> formada al añadir la 
   fórmula \<open>F\<close>.
   En primer lugar, si \<open>\<A>\<close> es modelo de la conjunción generalizada de
   \<open>F#Fs\<close>, por definición de dicha conjunción, esto es equivalente a
   que \<open>\<A>\<close> es modelo de la conjunción de \<open>F\<close> y la conjunción
   generalizada de \<open>Fs\<close>. Según el valor de una fórmula en una
   interpretación, esto es a su vez equivalente a la conjunción de
   "\<open>\<A>\<close> es modelo de \<open>F\<close>" y "\<open>\<A>\<close> es modelo de la conjunción 
   generalizada de \<open>Fs\<close>". Aplicando la hipótesis de inducción sobre el 
   segundo término de la conjunción, es equivalente a la conjunción de 
   "\<open>\<A>\<close> es  modelo de \<open>F\<close>" y "\<open>\<A>\<close> es modelo de toda fórmula del 
   conjunto formado por los elementos de \<open>Fs\<close>". Equivalentemente, \<open>\<A>\<close> 
   es modelo de toda fórmula del conjunto formado por la unión de \<open>{F}\<close> 
   y el conjunto de los elementos de \<open>Fs\<close>. Es decir, \<open>\<A>\<close> es modelo de 
   toda fórmula del conjunto formado por los elementos de \<open>F#Fs\<close>, 
   probando así el resultado.
  \end{demostracion}

  Veamos ahora su demostración detallada en Isabelle. Primero se
  probarán los dos casos correspondientes a la estructura de listas por
  separado.\<close>

lemma BigAnd_semantics_nil: "(\<A> \<Turnstile> \<^bold>\<And>[]) \<longleftrightarrow> (\<forall>f \<in> set []. \<A> \<Turnstile> f)"
proof-
  have "(\<A> \<Turnstile> \<^bold>\<And>[]) = \<A> \<Turnstile> (\<^bold>\<not>\<bottom>)"
    by (simp only: BigAnd.simps(1))
  also have "\<dots> = (\<not> \<A> \<Turnstile> \<bottom>)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> False)"
    by (simp only: formula_semantics.simps(2))
  also have "\<dots> = True"
    by (simp only: not_False_eq_True)
  also have "\<dots> = (\<forall>f \<in> \<emptyset>. \<A> \<Turnstile> f)"
    by (simp only: ball_empty) 
  also have "\<dots> = (\<forall>f \<in> set []. \<A> \<Turnstile> f)"
    by (simp only: list.set)
  finally show ?thesis
    by this
qed

text \<open>Para el caso de la lista formada añadiendo un elemento, vamos a
  emplear el siguiente lema auxiliar.\<close>

lemma Bigprop1: "(\<forall>x\<in>({a} \<union> B). P x) = (P a \<and> (\<forall>x\<in>B. P x))"
  by (simp only: ball_simps(7)
                 insert_is_Un[THEN sym])

text \<open>Se trata de una adaptación del séptimo apartado del lema 
  \<open>ball_simps\<close> en Isabelle, para adecuarlo a nuestro caso particular. 

  \begin{itemize}
    \item[] \<open>(\<forall>x\<in>insert a B. P x) \<longleftrightarrow> (P a \<and> (\<forall>x\<in>B. P x))\<close> 
        \hspace{3cm} \<open>(ball_simps(7))\<close>
  \end{itemize}

  Para ello, empleamos el lema \<open>insert_is_Un\<close> seguido de \<open>[THEN sym]\<close>
  como hemos hecho anteriormente.

  Procedamos, así, con la demostración del caso del lema 
  correspondiente. Por último, mostraremos también su demostración
  detallada completa.\<close>

lemma BigAnd_semantics_cons: 
  assumes "(\<A> \<Turnstile> \<^bold>\<And>Fs) \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
  shows "(\<A> \<Turnstile> \<^bold>\<And>(F#Fs)) \<longleftrightarrow> (\<forall>f \<in> set (F#Fs). \<A> \<Turnstile> f)"
proof -
  have "(\<A> \<Turnstile> \<^bold>\<And>(F#Fs)) = \<A> \<Turnstile> F \<^bold>\<and> \<^bold>\<And>Fs"
    by (simp only: BigAnd.simps(2))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> \<^bold>\<And>Fs)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f))"
    by (simp only: assms)
  also have "\<dots> = (\<forall>f \<in> ({F} \<union> set Fs). \<A> \<Turnstile> f)"
    by (simp only: Bigprop1)
  also have "\<dots> = (\<forall>f \<in> set (F#Fs). \<A> \<Turnstile> f)"
    by (simp only: set_insert)
  finally show ?thesis
    by this
qed

lemma "(\<A> \<Turnstile> \<^bold>\<And>Fs) \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
proof (induction Fs)
  case Nil
  then show ?case by (rule BigAnd_semantics_nil)
next
  case (Cons a Fs)
  then show ?case by (rule BigAnd_semantics_cons)
qed

text \<open>Su demostración automática es la siguiente.\<close>

lemma BigAnd_semantics: 
  "(\<A> \<Turnstile> \<^bold>\<And>Fs) \<longleftrightarrow> (\<forall>f \<in> set Fs. \<A> \<Turnstile> f)"
  by (induction Fs) simp_all

text \<open>Finalmente, un resultado sobre la disyunción generalizada.

  \begin{lema}
    Una interpretación es modelo de la disyunción generalizada de una 
    lista de fórmulas si y solo si existe una fórmula en la lista de la
    cual sea modelo.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "(\<A> \<Turnstile> \<^bold>\<Or>Fs) \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
  oops

text \<open>Procedamos con la demostración del resultado.

  \begin{demostracion}
    La prueba sigue el esquema de inducción sobre la estructura de
    listas. Vamos a probar los dos casos mediante cadenas de 
    equivalencias.

    Sea la lista vacía de fórmulas y una interpretación cualquiera
    \<open>\<A>\<close>. Por definición de la disyunción generalizada, si \<open>\<A>\<close> es
    modelo de la disyunción generalizada de la lista vacía,
    equivalentemente tenemos que es modelo de \<open>\<bottom>\<close>, es decir, \<open>Falso\<close>.
    En particular, esto es equivalente a suponer que existe una fórmula 
    en el conjunto vacío tal que \<open>\<A>\<close> es modelo suyo.

    Consideremos ahora la lista de fórmulas \<open>Fs\<close> y una interpretación
    \<open>\<A>\<close> tal que es modelo de \<open>Fs\<close> si y solo si es modelo de cada
    fórmula del conjunto formado por los elementos de \<open>Fs\<close>. Vamos a
    probar el resultado para la lista \<open>F#Fs\<close> dada cualquier fórmula
    \<open>F\<close>. Si \<open>\<A>\<close> es modelo de la disyunción generalizada de \<open>F#Fs\<close>, por
    definición, es equivalente a la disyunción entre "\<open>\<A>\<close> es modelo de
    \<open>F\<close>" y "\<open>\<A>\<close> es modelo de la disyunción generalizada de \<open>Fs\<close>". 
    Aplicando la hipótesis de inducción, tenemos equivalentemente la
    disyunción entre "\<open>\<A>\<close> es modelo de \<open>F\<close>" y "existe una fórmula
    perteneciente al conjunto de elementos de \<open>Fs\<close> tal que \<open>\<A>\<close> es
    modelo suyo". Por tanto, por propiedades de la disyunción, esto es 
    equivalente a que exista una fórmula perteneciente a la unión de
    \<open>{F}\<close> y el conjunto de los elementos de \<open>Fs\<close> que tiene a \<open>\<A>\<close> como 
    modelo. Finalmente, tenemos que esto ocurre si y solo si
    existe una fórmula en el conjunto de los elementos de \<open>F#Fs\<close> de la 
    cual \<open>\<A>\<close> sea modelo, como queríamos demostrar.
  \end{demostracion}

  A continuación lo probamos de manera detallada con Isabelle/HOL, 
  haciendo previamente cada paso por separado.\<close>

lemma BigOr_semantics_nil: "(\<A> \<Turnstile> \<^bold>\<Or>[]) \<longleftrightarrow> (\<exists>f \<in> set []. \<A> \<Turnstile> f)" 
proof -
  have "(\<A> \<Turnstile> \<^bold>\<Or>[]) = \<A> \<Turnstile> \<bottom>"
    by (simp only: BigOr.simps(1))
  also have "\<dots> = False"
    by (simp only: formula_semantics.simps(2))
  also have "\<dots> = (\<exists>f \<in> \<emptyset>. \<A> \<Turnstile> f)"
    by (simp only: bex_empty)
  also have "\<dots> = (\<exists>f \<in> set []. \<A> \<Turnstile> f)"
    by (simp only: list.set)
  finally show ?thesis
    by this
qed

text \<open>Para el segundo caso de las listas emplearemos el siguiente lema
  auxiliar.\<close>

lemma Bigprop2: "(\<exists>x\<in>{a} \<union> B. P x) = (P a \<or> (\<exists>x\<in>B. P x))"
  by (simp only: bex_simps(5)
                 insert_is_Un[THEN sym])

text\<open>De forma similar al resultado sobre conjunción generalizada, se 
  trata de una modificación del quinto apartado del lema \<open>bex_simps\<close> en 
  Isabelle para adaptarlo al caso particular. 

  \begin{itemize}
    \item[] \<open>(\<exists>x\<in>insert a B. P x) \<longleftrightarrow> (P a \<or> (\<exists>x\<in>B. P x))\<close> 
        \hspace{3cm} \<open>(bex_simps(5))\<close>
  \end{itemize}
  
  Para modificarlo, empleamos análogamente el lema \<open>insert_is_Un\<close>
  seguido de \<open>[THEN sym]\<close>, procediendo de manera similar a los casos 
  en los que se ha usado con anterioridad.
  
  Seguimos, así, con la demostración detallada del lema.\<close>

lemma BigOr_semantics_cons: 
  assumes "(\<A> \<Turnstile> \<^bold>\<Or>Fs) \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
  shows "(\<A> \<Turnstile> \<^bold>\<Or>(F#Fs)) \<longleftrightarrow> (\<exists>f \<in> set (F#Fs). \<A> \<Turnstile> f)" 
proof -
  have "(\<A> \<Turnstile> \<^bold>\<Or>(F#Fs)) = \<A> \<Turnstile> F \<^bold>\<or> \<^bold>\<Or>Fs"
    by (simp only: BigOr.simps(2))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> \<^bold>\<Or>Fs)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f))"
    by (simp only: assms)
  also have "\<dots> = (\<exists>f \<in> ({F} \<union> set Fs). \<A> \<Turnstile> f)"
    by (simp only: Bigprop2)
  also have "\<dots> = (\<exists>f \<in> set (F#Fs). \<A> \<Turnstile> f)"
    by (simp only: set_insert)
  finally show ?thesis
    by this
qed

lemma "(\<A> \<Turnstile> \<^bold>\<Or>Fs) \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
proof (induction Fs)
case Nil
  then show ?case by (rule BigOr_semantics_nil)
next
  case (Cons a Fs)
then show ?case by (rule BigOr_semantics_cons)
qed

lemma BigOr_semantics: 
  "(\<A> \<Turnstile> \<^bold>\<Or>Fs) \<longleftrightarrow> (\<exists>f \<in> set Fs. \<A> \<Turnstile> f)" 
  by (induction Fs) simp_all

section \<open>Semántica de conjuntos de fórmulas\<close>
    
text \<open>Veamos definiciones y resultados relativos a la semántica de un
  conjunto de fórmulas.
  
  En primer lugar, extendamos la noción de modelo a un conjunto de 
  fórmulas.

  \begin{definicion}
    Una interpretación es modelo de un conjunto de fórmulas si es 
    modelo de todas las fórmulas del conjunto.
  \end{definicion}

  Su formalización en Isabelle es la siguiente.\<close>

definition "isModelSet \<A> S \<equiv> \<forall>F. (F \<in> S \<longrightarrow> \<A> \<Turnstile> F)"

text \<open>Continuando con los ejemplos anteriores, veamos una interpretación
  que es modelo de un conjunto de fórmulas.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

  have "isModelSet (\<A> (4 := True))
     {Atom 4, (Atom 4 \<^bold>\<and> Atom 4) \<^bold>\<rightarrow> Atom 4}"
    by (simp add: isModelSet_def)

end

text \<open>El siguiente resultado relaciona los conceptos de modelo de 
  una fórmula y modelo de un conjunto de fórmulas en Isabelle.
  La equivalencia se demostrará fácilmente mediante las definiciones
  de \<open>isModel\<close> e \<open>isModelSet\<close>.\<close>

lemma modelSet:
  "isModelSet \<A> S \<equiv> \<forall>F. (F \<in> S \<longrightarrow> isModel \<A> F)" 
  by (simp only: isModelSet_def isModel_def)

text\<open>Veamos la noción de satisfacibilidad para un conjunto de fórmulas.

  \begin{definicion}
    Un conjunto de fórmulas es satisfacible si tiene algún modelo.
  \end{definicion}

  En Isabelle se formaliza de la siguiente manera.\<close>

definition "sat S \<equiv> \<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F"

text \<open>En otras palabras, la satisfacibilidad de un conjunto de fórmulas 
  depende de la existencia de una interpretación que sea modelo de dicho 
  conjunto, es decir, que sea modelo de todas las fórmulas del conjunto.
  
  El siguiente lema muestra una forma alternativa de definir
  un conjunto de fórmulas satisfacible en Isabelle empleando 
  \<open>isModelSet\<close> y \<open>sat\<close>, según la observación anterior.\<close>

lemma "sat S \<equiv> \<exists>\<A>. isModelSet \<A> S"
  oops

text \<open>Veamos sus demostraciones detallada y automática. Para ello, 
  introducimos inicialmente el lema auxiliar \<open>forall_set\<close>.\<close>

lemma forall_set:
  "(\<forall>x. (x \<in> A \<longrightarrow> P x)) = (\<forall>x \<in> A. P x)"
proof (rule iffI)
  assume H1:"\<forall>x. (x \<in> A \<longrightarrow> P x)"
  show "\<forall>x \<in> A. P x"
  proof (rule ballI)
    fix x
    have "x \<in> A \<longrightarrow> P x"
      using H1 by (rule allE)
    thus "x \<in> A \<Longrightarrow> P x"
      by (rule mp)
  qed
next
  assume H2: "\<forall>x \<in> A. P x"
  show "\<forall>x. (x \<in> A \<longrightarrow> P x)"
  proof (rule allI)
    fix x
    show "x \<in> A \<longrightarrow> P x"
    proof (rule impI)
      assume "x \<in> A"
      show "P x" 
        using H2 \<open>x \<in> A\<close> by (rule bspec)
    qed
  qed
qed

lemma "sat S \<equiv> \<exists>\<A>. isModelSet \<A> S"
proof -
  have "sat S = (\<exists>\<A>. isModelSet \<A> S)"
  proof (rule iffI)
    assume H1:"\<exists>\<A>. isModelSet \<A> S"
    obtain "\<A>" where "isModelSet \<A> S"
      using H1 by (rule exE)
    then have "\<forall>F. (F \<in> S \<longrightarrow> \<A> \<Turnstile> F)"
      by (simp only: isModelSet_def)
    then have "\<forall>F \<in> S. \<A> \<Turnstile> F"
      by (simp only: forall_set)
    then have "\<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F" 
      by (simp only: exI)
    thus "sat S"
      by (simp only: sat_def)
  next
    assume "sat S"
    then have H2:"\<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F"
      by (simp only: sat_def)
    obtain "\<A>" where "\<forall>F \<in> S. \<A> \<Turnstile> F"
      using H2 by (rule exE)
    then have "\<forall>F. (F \<in> S \<longrightarrow> \<A> \<Turnstile> F)"
      by (simp only: forall_set)
    then have "isModelSet \<A> S"
      by (simp only: isModelSet_def)
    thus "\<exists>\<A>. isModelSet \<A> S"
      by (simp only: exI)
  qed
  thus "sat S  \<equiv> \<exists>\<A>. isModelSet \<A> S"
    by (simp only: atomize_eq)
qed

lemma satAlt:
 "sat S \<equiv> \<exists>\<A>. isModelSet \<A> S"
  by (smt isModelSet_def sat_def)

text \<open>Mostremos algunos ejemplos de conjuncto satisfacible. Por 
  definición, se observa que el conjunto de fórmulas utilizado 
  en el ejemplo de \<open>modelSet\<close> es satisfacible. Por otro lado, un 
  caso de conjunto de fórmulas no satisfacible es cualquiera que 
  incluya una contradicción entre sus elementos.
  
  Por otra parte, en particular, se puede definir un conjunto de 
  fórmulas finitamente satisfacible.

  \begin{definicion}
    Un conjunto de fórmulas es finitamente satisfacible si todo
    subconjunto finito suyo es satisfacible.
  \end{definicion}

  Su formalización en Isabelle se muestra a continuación.\<close>

definition "fin_sat S \<equiv> (\<forall>s \<subseteq> S. finite s \<longrightarrow> sat s)"

text \<open>Continuemos con la noción de consecuencia lógica.

  \begin{definicion}
    Una fórmula es consecuencia lógica de un conjunto de fórmulas si
    todos los modelos del conjunto son modelos de la fórmula.
  \end{definicion}

  Teniendo en cuenta la definición de modelo de una fórmula y modelo de
  un conjunto de fórmulas, su formalización en Isabelle es la 
  siguiente.\<close>

definition entailment :: 
  "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>/ _)" 
    (* \TTurnstile *) [53,53] 53) where
  "\<Gamma> \<TTurnstile> F \<equiv> (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> F)))"
 
text \<open>Hagamos varias observaciones sobre esta definición. En primer
  lugar, hemos usado el tipo \<open>definition\<close>. Por otro lado, no hemos 
  empleado \<open>isModel\<close> ni \<open>isModelSet\<close> para su\\ definición ya que, de 
  este modo, no tenemos que desplegar dichas definiciones en las 
  demostraciones detalladas y automáticas de los lemas posteriores. 
  Finalmente se puede observar la notación \<open>\<TTurnstile>\<close>. En la teoría clásica no 
  se suele emplear una nueva notación, ya que se diferencia por el 
  contexto. En Isabelle/HOL es imprescindible aclarar la diferencia.

  Mostremos algún ejemplo de fórmula que sea consecuencia lógica de
  un conjunto.\<close>

notepad
begin
  fix \<A> :: "nat valuation"

  have "{Atom 1 \<^bold>\<rightarrow> Atom 2, Atom 2 \<^bold>\<rightarrow> Atom 3} \<TTurnstile> (Atom 1 \<^bold>\<rightarrow> Atom 3)"
    by (simp add: entailment_def)

end

text \<open>Llegamos así al último lema de la sección.

  \begin{lema}
    \<open>\<bottom>\<close> es consecuencia lógica de un conjunto si y solo si el conjunto
    es insatisfacible.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
  oops

text\<open>Comencemos las demostraciones del resultado.

  \begin{demostracion}
    Vamos a probar la doble implicación mediante una cadena de
    equivalencias.

    Sea un conjunto de fórmulas \<open>\<Gamma>\<close> tal que la fórmula \<open>\<bottom>\<close> es
    consecuencia lógica de dicho conjunto. Por definición, esto es
    equivalente a que toda interpretación que sea modelo de
    \<open>\<Gamma>\<close> es, a su vez, modelo de \<open>\<bottom>\<close>. Como el valor de \<open>\<bottom>\<close> es \<open>Falso\<close> 
    en cualquier interpretación, ninguna interpretación es modelo suyo. 
    Por tanto, por la hipótesis inicial, se verifica que ninguna 
    interpretación es modelo del conjunto \<open>\<Gamma>\<close>. Es decir, no existe 
    ninguna interpretación que sea modelo de dicho conjunto. Según la 
    definición, esto es equivalente a que el conjunto \<open>\<Gamma>\<close> es 
    insatisfacible, como queríamos demostrar.
  \end{demostracion}

  Procedamos con las pruebas en Isabelle/HOL.\<close>

lemma "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
proof -
  have "\<Gamma> \<TTurnstile> \<bottom> = (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<bottom>))"
    by (simp only: entailment_def)
  also have "\<dots> = (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> False))"
    by (simp only: formula_semantics.simps(2))
  also have "\<dots> = (\<forall>\<A>. \<not>(\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G))"
    by (simp only: not_def)
  also have "\<dots> =  (\<not>(\<exists>\<A>. \<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G))"
    by (simp only: not_ex) 
  also have "\<dots> = (\<not> sat \<Gamma>)"
    by (simp only: sat_def)
  finally show ?thesis
    by this
qed

text \<open>Finalmente su demostración automática es la siguiente.\<close>

lemma entail_sat: 
  "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
  unfolding sat_def entailment_def 
  by simp

(*<*)
end
(*>*) 
