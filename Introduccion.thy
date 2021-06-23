(*<*) 
theory Introduccion
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*)

(* chapter \<open>Introducción\<close> *)

text \<open>
  El objetivo de la Lógica es la formalización del conocimiento y el 
  razonamiento sobre el mismo. Tiene su origen en la lógica
  silogística de Aristóteles (384 a.C - 322 a.C) que consistía en la 
  deducción de conclusiones a partir de dos premisas iniciales, recogida 
  en su obra \<open>Organon\<close>. Posteriormente, los estoicos (400-200 a.C) 
  comenzaron a plantearse cuestiones semánticas relacionadas con la 
  naturaleza de la verdad.

  En el siglo XVII el matemático y filósofo Gottfried Wilhelm 
  Leibniz (1646 – 1716) instaura un programa lógico que propone la 
  búsqueda de un sistema simbólico del lenguaje natural junto con la 
  matematización del concepto de validez, lo que motivó el desarrollo 
  de la lógica moderna del siglo XIX por parte de matemáticos y 
  filósofos como Bernard Bolzano (1781 – 1848), George Boole 
  (1815 – 1864), Charles Saunders Pierce (1839 – 1914) y Gottlob Frege 
  (1848 – 1925). Este último introdujo el primer tratamiento sistemático 
  de la lógica proposicional dentro de la escuela del logicismo, cuyo
  objetivo consistía en investigar los fundamentos de las matemáticas 
  para formalizarlos\\ lógicamente con el fin de realizar deducciones y 
  razonamientos válidos.

	En las últimas décadas, el desarrollo de la computación y la 
  inteligencia artificial ha permitido la formalización de las 
  matemáticas y la lógica mediante el lenguaje computacional. 
  Concretamente, el razonamiento automático es un área que investiga los
  distintos aspectos del razonamiento para crear programas y
  algoritmos que permitan realizarlo de manera eficiente y automática.
  Se fundamenta en el programa lógico desarrollado por Leibniz,
  estructurado en base a dos principios: la formalización rigurosa
  de resultados y el desarrollo de algoritmos que permitan manipular
  y razonar a partir de dichas formalizaciones. Entre las principales 
  aplicaciones de este área se encuentra la verificación y síntesis 
  automáticas de programas que permite la validación de razonamientos
  junto con la creación de herramientas de razonamiento automático 
  que permitan el desarrollo de nuevos resultados.

  En este contexto nace Isabelle en 1986, desarrollada por Larry Paulson 
  de la Universidad de Cambridge y Tobias Nipkow del Techniche 
  Universität München. Isabelle es un demostrador interactivo que,
  desde el razonamiento automático, facilita la formalización lógica de 
  resultados y proporciona herramientas para realizar deducciones. En 
  particular, Isabelle/HOL es la especialización de Isabelle para la 
  lógica de orden superior. Junto con Coq, ACL2 y PVS, entre
  otros, constituye uno de los demostradores interactivos más 
  influyentes.

  Como demostrador interactivo, Isabelle permite automatizar 
  razonamientos guiados por el usuario, verificando cada paso de una 
  deducción de manera precisa. Además, incorpora herramientas de 
  razonamiento automático para mejorar la productividad del proceso de 
  demostración. Para ello, cuenta con una extensa librería de resultados 
  lógicos y matemáticos que han sido formalizados y continúan en 
  desarrollo por parte de proyectos como \<open>The Alexandria Project: 
  Large-Scale Formal Proof for the Working Mathematician\<close>. Este proyecto 
  comienza en 2017, dirigido por Lawrence Paulson desde la Universidad 
  de Cambridge. Tiene como finalidad la formalización de distintas 
  teorías para ampliar la librería de Isabelle, junto con la creación de 
  herramientas interactivas que asistan a los matemáticos en el proceso 
  de formalización, demostración y búsqueda de nuevos resultados. 

  Este trabajo constituye una continuación del Trabajo de Fin de Grado
  \<open>Elementos de lógica formalizados en Isabelle/HOL\<close> \<open>[4]\<close> dedicado al estudio
  y formalización de la sintaxis, semántica y lema de Hintikka de la lógica
  proposicional. Inspirado en la primera sección de la publicación 
  \<open>Propositional Proof Systems\<close> \<open>[10]\<close> de Julius Michaelis y Tobias Nipkow, y
  basando su contenido teórico en el libro \<open>First-Order Logic and Automated 
  Theorem Proving\<close> \<open>[5]\<close> de Melvin Fitting, este trabajo tiene como objetivo la
  demostración y formalización del \<open>Teorema de Existencia de Modelo\<close>, concluyendo
  con el \<open>Teorema de Compacidad\<close> como consecuencia del mismo. Para ello, consta
  de cuatro capítulos. En el primero se introduce la notación uniforme para 
  fórmulas proposicionales, en el segundo capítulo se estudia la propiedad de 
  consistencia proposicional para colecciones de conjuntos de fórmulas, el 
  tercero trata sobre las colecciones cerradas bajo subconjuntos y de carácter 
  finito y en el último capítulo se demuestra finalmente \<open>Teorema de Existencia 
  de Modelo\<close>, concluyendo con la prueba del \<open>Teorema de Compacidad\<close>.

  El primer capítulo introduce la notación uniforme para las fórmulas
  proposicionales, lo que permite reducir el número de casos a considerar 
  sobre la estructura de las fórmulas. Para justificar la clasificación del 
  conjunto de fórmulas proposicionales en dos tipos, se introduce la definición de 
  fórmulas semánticamente equivalentes como aquellas que tienen el mismo valor 
  para toda interpretación. De este modo, las fórmulas proposicionales pueden ser 
  de tipo conjuntivo (las fórmulas \<open>\<alpha>\<close>) y de tipo disyuntivo (las fórmulas \<open>\<beta>\<close>),
  asociándose dos componentes a cada fórmula según el tipo al que correspondan. 
  Intuitivamente, una fórmula de tipo \<open>\<alpha>\<close> es semánticamente equivalente a la 
  conjunción de sus componentes conjuntivas, y una fórmula de tipo \<open>\<beta>\<close> es 
  semánticamente equivalente a la disyunción de sus componentes disyuntivas. En 
  Isabelle, se formalizarán sintácticamente los conjuntos de fórmulas de tipo \<open>\<alpha>\<close> 
  y de tipo \<open>\<beta>\<close> como predicados inductivos, prescindiendo de la noción de 
  equivalencia semántica. Finalmente, el capítulo concluye con 
  un lema de caracterización de los conjuntos de Hintikka mediante la notación 
  uniforme.

  En el siguiente capítulo se define la propiedad de consistencia proposicional
  para colecciones de conjuntos de fórmulas. Al final del capítulo se caracteriza 
  dicha propiedad mediante notación uniforme, lo que facilita las demostraciones 
  de los resultados posteriores.

  En el tercer capítulo se estudian las colecciones de conjuntos de fórmulas
  cerradas bajo subconjuntos y de carácter finito. Una colección de conjuntos 
  es cerrada bajo subconjuntos si todo subconjunto de cada conjunto de la 
  colección pertenece a la colección, mientras que una colección es de 
  carácter finito si para todo conjunto son equivalentes que el conjunto
  pertenezca a la colección y que todo subconjunto finito del mismo pertenezca
  a la colección. Por una parte, se probará que toda colección de carácter 
  finito es cerrada bajo subconjuntos. Por otro lado, en este capítulo se
  introducirán dos resultados sobre extensiones de colecciones de conjuntos de
  fórmulas. El primero de ellos permite extender una colección con la propiedad de 
  consistencia proposicional a otra que también la verifique y sea cerrada bajo 
  subconjuntos. Finalmente, se demostrará que una colección cerrada bajo 
  subconjuntos que verifique la propiedad de consistencia proposicional se puede 
  extender a otra que también verifique dicha propiedad y sea de carácter finito. 

  Por último, en el cuarto capítulo se centra en la demostración del \<open>Teorema de 
  Existencia de Modelo\<close>, exponiendo posteriormente la prueba del \<open>Teorema de 
  Compacidad\<close> como consecuencia de éste. El capítulo está dividido en tres apartados: 
  el primero, en el que se definen ciertas sucesiones de conjuntos de fórmulas a partir de 
  una colección y un conjunto, el segundo apartado dedicado a la demostración del 
  \<open>Teorema de Existencia de Modelo\<close> y el tercer apartado donde se demuestra el 
  \<open>Teorema de Compacidad\<close>. 

  Para demostrar el \<open>Teorema de Existencia de Modelo\<close>, dada una colección
  y un conjunto perteneciente a ella, se dedicará el primer apartado del cuarto capítulo 
  a la definición de ciertas sucesiones monótonas de conjuntos de fórmulas y a la 
  demostración de distintos resultados relativos a este tipo de sucesiones. En primer 
  lugar, se demostrará que todo conjunto de la sucesión pertenece a la colección si esta 
  verifica la propiedad de consistencia proposicional. Por otro lado, se caracterizará 
  cada conjunto de la sucesión mediante la unión generalizada de los conjuntos anteriores 
  de la sucesión. Como es habitual, se definirá el límite de este tipo de sucesiones, 
  probándose que cada conjunto de la sucesión está contenido en él. En particular, si una 
  fórmula pertenece al límite se demostrará que pertenece a algún conjunto de la sucesión. 
  Finalmente, se probará que todo subconjunto finito del límite está contenido en algún 
  conjunto de la sucesión.

  Por otro lado, en la segunda parte del cuarto capítulo se desarrolla la demostración del
  \<open>Teorema de Existencia de Modelo\<close> que prueba que todo conjunto de fórmulas
  perteneciente a una colección que verifique la propiedad de consistencia proposicional 
  es satisfacible. Dada una colección \<open>C\<close> en estas condiciones y un conjunto \<open>S \<in> C\<close>, 
  la clave de la demostración consiste en probar que \<open>S\<close> está contenido en un conjunto de 
  Hintikka que, por el \<open>Teorema de Hintikka\<close>, es satisfacible. Para ello, empleando los 
  resultados expuestos en el segundo capítulo, extenderemos la colección \<open>C\<close> a otra \<open>C'\<close> 
  que tenga la propiedad de consistencia proposicional, sea cerrada bajo subconjuntos y 
  sea de carácter finito. De este modo, se considerará la sucesión definida a partir de 
  \<open>S\<close> y \<open>C'\<close> según el primer apartado del cuarto capítulo, probamos que el límite de dicha 
  sucesión es un conjunto de Hintikka que contiene a \<open>S\<close>. Para ello, previamente se 
  demostrará que el límite de este tipo de sucesiones es un elemento maximal de la
  colección que lo define si esta es cerrada bajo subconjuntos y verifica la propiedad de
  consistencia proposicional. Por otro lado se demostrará que, si además la colección es 
  de carácter finito, el límite pertenece a ella.

  Por último, el apartado final del capítulo se dedica a la demostración del 
  \<open>Teorema de Compacidad\<close> que prueba que todo conjunto de fórmulas finitamente 
  satisfacible es satisfacible. Para su demostración consideraremos la 
  colección formada por los conjuntos de fórmulas finitamente satisfacibles. 
  Probaremos que dicha colección verifica la propiedad de consistencia 
  proposicional y, por el \<open>Teorema de Existencia de Modelo\<close>, todo conjunto 
  perteneciente a ella será satisfacible. 

  En lo referente a las demostraciones asistidas por Isabelle/HOL de
  los resultados formalizados a lo largo de las secciones, se elaborarán 
  dos tipos de pruebas correspondientes a dos tácticas distintas. En 
  primer lugar, se probará cada resultado siguiendo un esquema de 
  demostración detallado. En él utilizaremos únicamente y de manera 
  precisa las reglas de simplificación y definiciones incluidas en la 
  librería de Isabelle, prescindiendo de las herramientas de 
  razonamiento automático del demostrador. Para ello, se realiza una 
  búsqueda inversa en cada paso de la demostración automática hasta 
  llegar a un desarrollo de la prueba basado en deducciones a partir de
  resultados elementales que la completen de manera rigurosa. En 
  contraposición, se evidenciará la capacidad de razonamiento 
  automático de Isabelle/HOL mediante la realización de una prueba 
  alternativa siguiendo un esquema de demostración automático. Para 
  ello se utilizarán las herramientas de razonamiento que han sido 
  elaboradas en Isabelle/HOL con el objetivo de realizar deducciones de 
  la manera más eficiente.

  \<open>Este trabajo está disponible en la plataforma\<close> GitHub \<open>mediante el
  siguiente enlace:\<close> 

\href{https://github.com/sofsanfer/TFM}
                  {\url{https://github.com/sofsanfer/TFM}}\<close>
(*<*)
end
(*>*) 