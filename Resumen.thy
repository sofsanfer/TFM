(*<*)
theory Resumen
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*)

text \<open>
El objetivo de la Lógica es la formalización del conocimiento y su
razonamiento. En este trabajo, estudiaremos elementos de la lógica
proposicional desde la perspectiva teórica de \<open>First−Order Logic and 
Automated Theorem Proving\<close> \<open>[4]\<close> de Melvin Fitting. En particular, nos 
centraremos en la sintaxis y la semántica, concluyendo con la versión 
proposicional del lema de Hintikka sobre la satisfacibilidad de una 
clase determinada de conjuntos de fórmulas. Siguiendo la inspiración de 
\<open>Propositional Proof Systems\<close> \<open>[10]\<close> por Julius Michaelis y Tobias 
Nipkow, los resultados expuestos serán formalizados mediante Isabelle: 
un demostrador interactivo que incluye herramientas de razonamiento 
automático para guiar al usuario en el proceso de formalización, 
verificación y automatización de resultados. Concretamente, Isabelle/HOL 
es una especialización de Isabelle para la lógica de orden superior. 
Las demostraciones de los resultados en Isabelle/HOL se elaborarán 
siguiendo dos tácticas distintas a lo largo del trabajo. En primer 
lugar, cada lema será probado de manera detallada prescindiendo de toda 
herramienta de razonamiento automático, como resultado de una búsqueda 
inversa en cada paso de la prueba. En contraposición, elaboraremos una 
demostración automática alternativa de cada resultado que utilice todas 
las herramientas de razonamiento automático que proporciona el 
demostrador. De este modo, se evidenciará la capacidad de razonamiento 
automático de Isabelle. 
   \<close>

(*section \<open>Abstract \<close>*)

text\<open>Logic’s purpose is about knowledge’s formalisation and its 
reasoning. In this project, we will approach Propositional Logic’s 
elements from the theoretical perspective of \<open>First−Order Logic and 
Automated Theorem Proving\<close> \<open>[4]\<close> by Melvin Fitting. We will focus on the 
study of Syntax and Semantics to reach propositional version of 
Hintikka’s lemma, which determinate the satisfiability of a concrete 
type of formula set. Inspired by \<open>Propositional Proof Systems\<close> \<open>[10]\<close> by 
Julius Michaelis and Tobias Nipkow, these results will be formalised 
using Isabelle: a proof assistant including automatic reasoning tools 
to guide the user on formalising, verifying and automating results. In 
particular, Isabelle/HOL is the specialization of Isabelle for 
High-Order Logic. The processing of the results formalised in 
Isabelle/HOL follows two directions. In the first place, each lemma 
will be proved on detail without any automation, as the result of an 
inverse research on every step of the demonstration until it is only 
completed with deductions based on elementary rules and definitions. 
Conversely, we will alternatively prove the results using all the 
automatic reasoning tools that are provide by the proof assistant. In 
this way,\\ Isabelle’s power of automatic reasoning will be shown as the 
contrast between these two different proving tactics. 
\<close>


(*<*)
end
(*>*)
