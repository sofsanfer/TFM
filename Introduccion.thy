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
  razonamiento sobre el mismo. Tiene su origen en la Antigua Grecia con 
  Aristóteles y su investigación acerca de los principios del 
  razonamiento válido o correcto, recogidos fundamentalmente en su obra 
  \<open>Organon\<close>. De este modo, dio lugar a la lógica silogística, que 
  consistía en la deducción de conclusiones a partir de dos premisas 
  iniciales. 

	Posteriormente, los estoicos (400-200 a.C) comenzaron a cuestionarse 
  temas relacionados con la semántica, como la naturaleza de la verdad. 
  Formularon la \<open>paradoja del mentiroso\<close>, que plantea una incongruencia 
  acerca de la veracidad del siguiente predicado.

  \<open>Esta oración es falsa.\<close>

  Sin embargo, no fue hasta el siglo XVII que el matemático y filósofo 
  Gottfried Wilhelm Leibniz (1646 – 1716) instaura un programa lógico 
  que propone la búsqueda de un sistema simbólico del lenguaje natural 
  junto con la matematización del concepto de validez. Estas ideas 
  fueron la principal motivación del desarrollo de la lógica moderna del 
  siglo XIX de la mano de matemáticos y filósofos como Bernard Bolzano 
  (1781 – 1848), George Boole (1815 – 1864), Charles Saunders Pierce 
  (1839 – 1914) y Gottlob Frege (1848 – 1925). Fue este último quien 
  introdujo el primer tratamiento sistemático de la lógica 
  proposicional. Frege basó su tesis en el desarrollo de una sintaxis 
  completa que combina el razonamiento de deducción de la silogística 
  aristotélica con la noción estoica de conectivas para relacionar 
  ideas. Paralelamente desarrolló una semántica asociada a dicha 
  sintaxis que permitiese verificar la validez de los procesos 
  deductivos. La lógica proposicional de Frege formó parte de la 
  escuela denominada logicismo. Su objetivo consistía en investigar 
  los fundamentos de las matemáticas con el fin de formalizarlos 
  lógicamente, para así realizar deducciones y razonamientos 
  válidos.

	En las últimas décadas, el desarrollo de la computación y la 
  inteligencia artificial ha permitido la formalización de las 
  matemáticas y la lógica mediante el lenguaje computacional. 
  Concretamente, el razonamiento automático es un área que investiga los
  distintos aspectos del razonamiento con el fin de crear programas y
  algoritmos para razonar de manera prácticamente automática.
  Se fundamenta en el programa lógico desarrollado por Leibniz,
  estructurado en base a dos principios: la formalización rigurosa
  de resultados y el desarrollo de algoritmos que permitan manipular
  y razonar a partir de dichas formalizaciones. Entre las principales 
  aplicaciones de este áres se encuentra la verificación y síntesis 
  automáticas de programas. De este modo, podemos validar distintos 
  razonamientos, así como crear herramientas de razonamiento automático 
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
  fórmulas proposicionales, en el segundo capítulo se define la propiedad de 
  consistencia proposicional para colecciones de conjuntos de fórmulas, en el 
  tercero se definen las colecciones cerradas bajo subconjuntos y de carácter 
  finito y en el último capítulo se demuestra finalmente \<open>Teorema de Existencia 
  de Modelo\<close>, concluyendo con la prueba del \<open>Teorema de Compacidad\<close>.

  El primer capítulo introduce la notación uniforme para las fórmulas
  proposicionales con el fin de reducir el número de casos a considerar sobre 
  la estructura de las fórmulas al clasificarlas en dos categorías. Para 
  justificar la clasificación, se introduce la definición de fórmulas 
  semánticamente equivalentes como aquellas que tienen el mismo 
  valor para toda interpretación. De este modo, las fórmulas proposicionales
  pueden ser de dos tipos: las de tipo conjuntivo (las fórmulas \<open>\<alpha>\<close>) y las 
  de tipo disyuntivo (las fórmulas \<open>\<beta>\<close>). Cada fórmula de tipo \<open>\<alpha>\<close>, o \<open>\<beta>\<close> 
  respectivamente, tiene asociada sus dos componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close>, o \<open>\<beta>\<^sub>1\<close> y 
  \<open>\<beta>\<^sub>2\<close> respectivamente. Intuitivamente, una fórmula es de tipo \<open>\<alpha>\<close> con 
  componentes \<open>\<alpha>\<^sub>1\<close> y \<open>\<alpha>\<^sub>2\<close> si es semánticamente equivalente a la fórmula 
  \<open>\<alpha>\<^sub>1 \<and> \<alpha>\<^sub>2\<close>, y una fórmula será de tipo \<open>\<beta>\<close> con componentes \<open>\<beta>\<^sub>1\<close> y \<open>\<beta>\<^sub>2\<close> si es 
  semánticamente equivalente a la fórmula\\ \<open>\<beta>\<^sub>1 \<or> \<beta>\<^sub>2\<close>. En Isabelle, se formalizarán
  sintácticamente los conjuntos de fórmulas de tipo \<open>\<alpha>\<close> y de tipo \<open>\<beta>\<close> como
  predicados inductivos, simplificando la intuición original al prescindir 
  de la noción de equivalencia semántica que permite clasificar la totalidad 
  de las fórmulas proposicionales. Finalmente, el capítulo concluye con un lema
  de caracterización de los conjuntos de Hintikka mediante la notación uniforme.

  En el siguiente capítulo se define la propiedad de consistencia proposicional
  para colecciones de conjuntos de fórmulas. Al final del capítulo se caracteriza 
  dicha propiedad mediante notación uniforme, lo que 
  facilita las demostraciones de los resultados posteriores.

\comentario{Párrafo ligeramente modificado.}

  En el tercer capítulo se definen las colecciones de conjuntos de fórmulas
  cerradas bajo subconjuntos y de carácter finito. Una colección de conjuntos 
  es cerrada bajo subconjuntos si todo subconjunto de cada conjunto de la 
  colección pertenece a la colección, mientras que una colección es de 
  carácter finito si para todo conjunto son equivalentes que el conjunto
  pertenezca a la colección y que todo subconjunto finito del mismo pertenezca
  a la colección. Posteriormente se muestran tres resultados sobre las mismas. 
  El primero de ellos permite extender una colección con la propiedad de 
  consistencia proposicional a otra que también la verifique y sea cerrada bajo 
  subconjuntos. Seguidamente se probará que toda colección de carácter finito
  es cerrada bajo subconjuntos. En último lugar, se demuestra que una colección
  cerrada bajo subconjuntos que verifique la propiedad de consistencia 
  proposicional se puede extender a otra que también verifique dicha propiedad 
  y sea de carácter finito. 

  Finalmente, en el cuarto capítulo se demuestra el \<open>Teorema de Existencia de 
  Modelo\<close> y el \<open>Teorema de Compacidad\<close> como consecuencia de éste. El capítulo 
  está dividido en tres apartados: el primero donde se definen ciertas 
  sucesiones de conjuntos de fórmulas a partir de una colección y un conjunto, 
  el segundo apartado dedicado a la demostración del \<open>Teorema de Existencia de 
  Modelo\<close> y el tercer apartado donde se demuestra el \<open>Teorema de Compacidad\<close>. 

  En la primera parte del cuarto capítulo se define una sucesión 
  monótona \<open>{S\<^sub>n}\<close> de conjuntos de fórmulas a partir de una colección \<open>C\<close> y un 
  conjunto \<open>S \<in> C\<close>. De este modo, se prueban distintas propiedades sobre dichas 
  sucesiones de conjuntos que permiten la prueba del \<open>Teorema de Existencia de
  Modelo\<close>. En primer lugar, se prueba que si \<open>C\<close> verifica la propiedad de 
  consistencia proposicional, entonces todo elemento de la suceción \<open>{S\<^sub>n}\<close> 
  pertenece a la colección. Igualmente, se dará un resultado que permite 
  caracterizar conjuntos de \<open>{S\<^sub>n}\<close> en función de los anteriores. Por otro lado, 
  definiremos el límite de dichas sucesiones, probando que todo conjunto de 
  \<open>{S\<^sub>n}\<close> está contenido en el límite. Además, se demostrará que si una fórmula 
  pertenece al límite, entonces pertenece a algún conjunto de la sucesión \<open>{S\<^sub>n}\<close>. 
  Finalmente, se mostrará un resultado sobre conjuntos finitos contenidos en el 
  límite.

\comentario{Corregir el párrafo anterior, relativo a la primera parte
del cuarto capítulo.}


  En la segunda parte del capítulo se demuestra el \<open>Teorema de Existencia
  de Modelo\<close>, que prueba que todo conjunto de fórmulas \<open>S\<close> perteneciente a una 
  colección \<open>C\<close> que verifique la propiedad de consistencia proposicional es 
  satisfacible. Para ello, extenderemos la colección \<open>C\<close> a otra \<open>C'\<close> que 
  tenga la propiedad de consistencia proposicional, sea cerrada bajo 
  subconjuntos y sea de carácter finito, de modo que se introducirán
  distintos resultados sobre colecciones con las características anteriores. 
  En primer lugar, probaremos que el límite de la sucesión \<open>{S\<^sub>n}\<close> definida a 
  partir de \<open>C'\<close> y \<open>S\<close> pertenece a \<open>C'\<close>. En particular se probará que dicho 
  límite es un elemento maximal de la colección que lo define si esta es 
  cerrada bajo subconjuntos y verifica la propiedad de consistencia 
  proposicional. Por otra parte se demostrará que el límite de \<open>{S\<^sub>n}\<close> es un 
  conjunto de Hintikka si está definido a partir de una colección \<open>C'\<close> con 
  las propiedades descritas luego, por el \<open>Teorema de Hintikka\<close>, es
  satisfacible. Finalmente, como \<open>S \<in> C\<close> pertenece también a la extensión \<open>C'\<close>, 
  se verifica que está contenido en el límite de la sucesión \<open>{S\<^sub>n}\<close> definida a 
  partir de \<open>C'\<close> y\\ \<open>S \<in> C'\<close>. Por tanto, quedará demostrada la satisfacibilidad 
  del conjunto \<open>S\<close> al heredarla por contención del límite.

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