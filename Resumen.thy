(*<*)
theory Resumen
imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar" 
begin
(*>*)

text \<open>
El objetivo de la Lógica es la formalización del conocimiento y su
razonamiento. Este trabajo constituye una continuación del Trabajo de Fin de
Grado \<open>Elementos de lógica formalizados en Isabelle/HOL\<close>, donde se estudiaron
la sintaxis, semántica y \<open>Lema de Hintikka\<close> de la Lógica Proposicional
desde la perspectiva teórica de \<open>First−Order Logic and Automated Theorem Proving\<close> 
\<open>[4]\<close> de Melvin Fitting. Manteniendo dicha perspectiva, nos centraremos en la 
demostración del \<open>Teorema de Existencia de Modelo\<close>, concluyendo con 
el \<open>Teorema de Compacidad\<close> como consecuencia del mismo. Siguiendo la 
inspiración de \<open>Propositional Proof Systems\<close> \<open>[10]\<close> por Julius Michaelis y Tobias 
Nipkow, los resultados expuestos serán formalizados mediante Isabelle: un demostrador 
interactivo que incluye herramientas de razonamiento automático para guiar al usuario 
en el proceso de formalización, verificación y automatización de resultados. 
Concretamente, Isabelle/HOL es una especialización de Isabelle para la lógica de orden 
superior. Las demostraciones de los resultados en Isabelle/HOL se elaborarán siguiendo 
dos tácticas distintas a lo largo del trabajo. En primer lugar, cada lema será probado 
de manera detallada prescindiendo de toda herramienta de razonamiento automático, como 
resultado de una búsqueda inversa en cada paso de la prueba. En contraposición, 
elaboraremos una demostración automática alternativa de cada resultado que utilice todas 
las herramientas de razonamiento automático que proporciona el demostrador. De este modo, 
se evidenciará la capacidad de razonamiento automático de Isabelle.\<close>

(*section \<open>Abstract \<close>*)

text\<open>Logic’s purpose is about knowledge’s formalisation and its 
reasoning. This project is a continuation of \<open>Elementos de lógica
formalizados en Isabelle/HOL\<close> in which we studied Syntax, Semantics and
a propositional version of Hintikka's lemma from the theoretical perspective 
of \<open>First−Order Logic and Automated Theorem Proving\<close> \<open>[4]\<close> by Melvin Fitting. 
Following the same perspective, we will focus on the demonstration of 
\<open>Propositional Model Existence\<close> theorem, concluding with the \<open>Propositional 
Compactness\<close> theorem as a consecuence. Inspired by \<open>Propositional Proof Systems\<close> \<open>[10]\<close> by Julius Michaelis and Tobias Nipkow, 
these results will be formalised using Isabelle: a proof assistant including 
automatic reasoning tools to guide the user on formalising, verifying and 
automating results. In particular, Isabelle/HOL is the specialization of 
Isabelle for High-Order Logic. The processing of the results formalised in 
Isabelle/HOL follows two directions. In the first place, each lemma 
will be proved on detail without any automation, as the result of an 
inverse research on every step of the demonstration until it is only 
completed with deductions based on elementary rules and definitions. 
Conversely, we will alternatively prove the results using all the 
automatic reasoning tools that are provide by the proof assistant. In 
this way, Isabelle’s power of automatic reasoning will be shown as the 
contrast between these two different proving tactics. 
\<close>

text \<open>\comentario{Modificar referencia bibliográfica si necesario.}\<close>

(*<*)
end
(*>*)
