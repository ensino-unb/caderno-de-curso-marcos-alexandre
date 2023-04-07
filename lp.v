(* Copyright (c) 2023, Flávio L. C. de Moura *)

(** %\chapter{A Lógica Proposicional}% *)

(**

Iniciarebmos nosso estudo a partir da noção de %{\bf proposição}\index{proposição}%, que é uma afirmação que pode ser qualificada como verdadeira ou falsa. Por exemplo, afirmações como "2+2=4", "2 é um número primo", "1+3<0" ou "Jõao tem 20 anos e Maria tem 22 anos" são proposições. Mas nem toda afirmação é uma proposição. De fato, a ordem "Feche a porta!", ou ainda, a pergunta "Qual é o seu nome?" não podem ser qualificadas como verdadeira ou falsa, e portanto não são proposições. Algumas proposições podem ser divididas em proposições menores. Por exemplo, a proposição "João tem 20 anos e Maria tem 22 anos" é composta da proposição "João tem 20 anos" e da proposição "Maria tem 22 anos", que por sua vez não podem mais serem divididas porque os pedaços menores não são mais qualificáveis como verdadeiro ou falso. Uma proposição que não pode ser dividida é um elemento básico utilizado na construção de proposições mais complexas, que chamaremos de fórmula atômica%\index{fórmula!atômica}%. Utilizaremos letras latinas minúsculas para representar fórmulas atômicas. Por exemplo, podemos utilizar a letra $q$ para representar a proposição "Maria tem 22 anos", e a letra $p$ para "João tem 20 anos". A proposição do exemplo acima é construída com a utilização do conectivo "E" (conjunção), que será representado pelo símbolo $\land$. Com esta simbologia, podemos codificar a proposição "João tem 20 anos e Maria tem 22 anos" pela fórmula $p \land q$. E o que é uma fórmula? As fórmulas são os elementos sintáticos que vão compor a teoria com a qual iremos trabalhar, a saber a Lógica Proposicional%\index{lógica!proposicional}%. Além da conjunção, existem outros conectivos que compõem as fórmulas da Lógica Proposicional. Estes conectivos estão na gramática das fórmulas da Lógica Proposicional representada a seguir: 

%\begin{equation}\label{gram:lp}
\varphi ::= p \mid \bot \mid (\varphi \to \varphi) \mid (\neg \varphi) \mid (\varphi \land \varphi) \mid (\varphi \lor \varphi)  
\end{equation}%

A gramática (%\ref{gram:lp}%) possui 6 construtores%\index{gramática!construtor}%:
%\begin{enumerate}
\item O primeiro denota uma variável proposicional\index{variável!proposicional}, e caracteriza uma fórmula atômica\index{fórmula!atômica}, i.e. uma fórmula que não pode ser subdividida em  fórmulas menores.
\item O segundo construtor é uma constante que denota o absurdo\index{absurdo} ($\bot$), que também é uma fórmula atômica. O absurdo será utilizado quando tivermos informações contraditórias em nossas provas. Isto ficará mais claro nos exemplos.
\item O terceiro construtor é a implicação\index{implicação}.
\item O quarto construtor denota a negação\index{negação}.
\item O quinto construtor denota a conjunção\index{conjunção}.
\item O sexto construtor denota a disjunção\index{disjunção}.
\end{enumerate}% 

Uma gramática%\index{lógica!proposicional!gramática}% como (%\ref{gram:lp}%) nos fornece as regras sintáticas para a construção das fórmulas da Lógica Proposicional. São quatro construtores recursivos (negação, conjunção, disjunção e implicação) também chamados de conectivos lógicos, e dois não recursivos. Apesar da gramática apresentada acima não incluir a bi-implicação%\index{bi-implicação}%, este é um conectivo bastante utilizado, e pode ser escrito em função dos outros conectivos: $\varphi \leftrightarrow \psi$ é o mesmo que $(\varphi \to \psi) \land (\psi \to \varphi)$. Na verdade, a gramática apresentada possui redundâncias, isto é, conectivos que podem ser escritos em função de outros, mas veremos isto posteriormente.

A seguir, mostraremos como utilizar os elementos da gramática acima no assistente de provas Coq%\index{Coq}%. As variáveis proposicionais são declaradas como elementos do tipo [Prop]. A declaração abaixo é feita dentro de uma seção para delimitar o escopo da declaração no arquivo: *)

Section aula1.
Variables p q: Prop.
End aula1.

(**
Uma declaração global pode ser feita como a palavra reservada [Parameter]:
 *)

Parameter p q: Prop.

(**
A constante $\bot$ (absurdo) está definida em Coq como [False]. Podemos verificar isto solicitando que o sistema retorne o tipo de [False]:
 *)

Check False.

(**

O retorno do comando acima é:

-----
<<
False
     : Prop
>>
-----

Ou seja, [False] tem tipo [Prop]. A implicação é um conectivo binário que recebe duas fórmulas como argumento:

 *)

Check (p -> q).

(**

O retorno para o comando acima é:

-----  
<<
p -> q
     : Prop
>>
-----

Observe que a forma de representar a implicação no Coq é o hífen seguido do sinal de maior. A fórmula dada como argumento para o comando [Check] é escrito da mesma forma, mas a saída pdf deste arquivo transforma a versão ascii da implicação.

A negação é um conectivo unário que recebe uma fórmula como argumento. Escrevemos [~p] para representar a negação da variável [p] declarada anteriormente. No Coq, a negação é representada pelo símbolo $\sim$ antes da fórmula, mas na saída pdf deste arquivo a negação está aparecendo com outro símbolo. Podemos solicitar o tipo da fórmula [~p]:

*)
 Check (~p).

 (**

 Como esperado, obtemos o tipo [Prop]:

-----
<<
~ p
     : Prop
>>
-----

A notação apresentada acima para a negação é, na verdade, uma abreviação para uma implicação particular. De fato, [~phi] é o mesmo que [phi -> False] como veremos na próxima seção. A conjunção é um conectivo binário escrito como a seguir:

  *)

Check (p /\ q).

(**

-----
<<
p /\ q
     : Prop
>>
-----

E por fim, a disjunção é também um conectivo binário escrito como a seguir:

*)

Check (p \/ q).

(**

-----
<<
p \/ q
     : Prop
>>
-----

O sistema conhecido como dedução natural%\index{dedução natural}% será utilizado para a construção das provas. Este sistema foi criado pelo lógico alemão Gerhard Gentzen (1909-1945)%\index{Gerhard Gentzen}%, e consiste em um sistema lógico composto por um conjunto de regras de inferência que tenta capturar o raciocínio matemático da forma mais natural possível. Como veremos, estas regras nos permitem derivar novos fatos a partir das premissas. Os fatos a serem provados são representados por meio de fórmulas da Lógica Proposicional. Neste contexto, o primeiro conceito importante que aparece é o de sequente%\index{sequente}%. Formalmente, um sequente é um par cujo primeiro elemento é um conjunto finito de fórmulas (hipóteses), e o segundo elemento é uma fórmula (conclusão). Assim, se $\varphi_1, \varphi_2, \ldots, \varphi_n$ são as hipóteses de um dado problema, e se $\psi$ é a sua conclusão, escrevemos  $\varphi_1, \varphi_2, \ldots, \varphi_n \vdash \psi$ para representar o sequente que simboliza que $\psi$ tem uma prova a partir das hipóteses $\varphi_1, \varphi_2, \ldots, \varphi_n$. O conjunto $\{\varphi_1, \varphi_2, \ldots, \varphi_n\}$, isto é, a primeira componente do sequente $\varphi_1, \varphi_2, \ldots, \varphi_n \vdash \psi$ também será chamado de contexto ao longo do texto, e normalmente será escrito sem as chaves que usualmente são usadas para representar conjuntos. Este é um abuso de linguagem usado para não deixar a notação sobrecarregada. Assim, se $\Gamma$ denota um conjunto finito de fórmulas, ao invés de $\Gamma \cup \{\varphi\} \vdash \psi$, escreveremos simplesmente $\Gamma, \varphi \vdash \psi$, onde $\Gamma,\varphi$ deve então ser lido como o conjunto que contém a fórmula $\varphi$ e todas as fórmulas de $\Gamma$. O conceito de prova agora será definido de forma mais precisa. Concretamente, uma prova (ou uma derivação) de um sequente da forma $\Gamma \vdash \psi$ é uma árvore finita onde cada nó corresponde a uma regra válida. A raiz da árvore é anotada com a conclusão, ou seja, o sequente que queremos provar, e as folhas são anotadas com axiomas. As regras são representadas por regras de inferência%\index{regra!inferência}%, onde cada premissa e a conclusão correspondem a um sequente:

%\begin{mathpar}
 \inferrule{\Gamma_1\vdash \gamma_1\ \Gamma_2\vdash \gamma_2 \ldots \Gamma_k \vdash \gamma_k}{\Gamma \vdash \psi} 
\end{mathpar}%

%\noindent% onde $k \geq 0$. Quando $k = 0$ a regra corresponde a um axioma, se $\psi$ é uma das fórmulas em $\Gamma$:

%\begin{mathpar}
 \inferrule*[Right={$\ax$, {\rm se} $\psi \in \Gamma$}]{~}{\Gamma \vdash \psi} 
\end{mathpar}%

Uma prova (sequência de passos dedutivos) pode ser representada por meio de uma estrutura de árvore, onde os nós são anotados com fórmulas. A raiz da árvore é anotada com a fórmula que queremos provar, isto é, uma prova do sequente $\Gamma \vdash \psi$, será representado por uma árvore que terá a fórmula $\psi$ como raiz, e as folhas da árvore são fórmulas de $\Gamma$.

Como veremos, a construção desta árvore deve obedecer alguns critérios que detalharemos ao longo deste capítulo, mas em linhas gerais, o principal critério consiste em obedecer um conjunto de regras que definem o sistema de dedução natural. Estas regras são divididas em dois tipos: regras de introdução%\index{regra!introdução}% e regras de eliminação%\index{regra!eliminação}% dos conectivos. Na próxima seção veremos as duas primeiras regras que nos permitirão resolver diversos problemas. Para isto, ficaremos restritos inicialmente a fórmulas que contêm apenas a implicação como conectivo. Esta parte da Lógica proposicional é conhecida como %{\it fragmento implicacional da lógica proposicional}\index{lógica!proposicional!fragmento implicacional}%.

*)

(** * O Fragmento Implicacional da Lógica Proposicional *)

(**

O fragmento implicacional da lógica proposicional é formado pelas fórmulas da lógica proposicional que contêm apenas a implicação como conectivo lógico, ou seja, consiste nas fórmulas construídas a partir da seguinte gramática:

%\begin{equation}\label{gram:lp:impl}
\varphi ::= p \mid \bot \mid (\varphi \to \varphi) 
\end{equation}%

Este fragmento possui duas regras de derivação: uma regra de %{\it introdução}\index{regra!introdução!implicação}% e outra de %{\it eliminação}% da implicação%\index{regra!eliminação!implicação}%. A regra de eliminação da implicação é bastante conhecida e também chamada de %{\it modus ponens}\index{modus ponens}%:

%\begin{mathpar}
 \inferrule*[Right={$\toe$}]{\Gamma \vdash \varphi\to \psi \and \Gamma \vdash \varphi}{\Gamma \vdash \psi}
\end{mathpar}%

A regra $\toe$ nos diz que a partir de uma prova de $\Gamma \vdash \varphi\to \psi$ e de outra prova de $\Gamma \vdash \varphi$ podemos concluir que $\Gamma \vdash \psi$. As regras de introdução são bastante intuitivas e, em certo sentido, podem ser vistas como uma definição do conectivo que estão introduzindo: a regra de %{\it introdução da implicação}\index{regra!introdução!implicação}%, denotada por $\toisa$, possui alguns detalhes importantes. Para construirmos uma prova de uma implicação, digamos do sequente $\Gamma \vdash \varphi \to \psi$, precisamos construir uma prova de $\psi$ tendo $\varphi$ como hipótese adicional ao contexto $\Gamma$. Em outras palavras, na leitura de baixo para cima, reduzimos o problema de provar $\Gamma \vdash \varphi \to \psi$ ao novo problema (possivelmente mais simples) de provar $\Gamma, \varphi \vdash \psi$:

%\begin{mathpar}
 \inferrule*[Right={$\toi{}$}]{\Gamma,\varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}
\end{mathpar}%

Também podemos observar esta regra de cima para baixo. Neste caso, ela nos permite passar uma fórmula do conjunto de hipóteses para o consequente como antecedente de uma implicação. Assim, a fórmula $\varphi$ que era uma das hipóteses necessárias para provar $\psi$, deixa de ser hipótese, e passa a ser antecedente de uma implicação no consequente. Considerando o subconjunto das fórmulas da lógica proposicional construídas apenas com a implicação (variáveis e a constante $\bot$) e as regras $\toe$ e $\toisa$ temos o chamado %{\it fragmento implicacional da lógica proposicional}\index{lógica!proposicional!fragmento implicacional}%. O interesse computacional deste fragmento está diretamente relacionado ao algoritmo de inferência de tipos em linguagens funcionais%\cite{hindleyBasicSimpleType1997}%. O fundamento teórico destas linguagens é o cálculo $\lambda$%\index{cálculo $\lambda$}\cite{barendregtLambdaCalculusIts1984}% desenvolvido por Alonzo Church em 1936%\cite{churchUnsolvableProblemElementary1936,churchFormulationSimpleTheory1940}%. Para mais detalhes veja o Capítulo 1 de %\cite{ayala-rinconAppliedLogicComputer2017}%. Como primeiro exemplo, vamos considerar o sequente $\vdash (p \to q) \to (q \to r) \to p \to r$. A primeira observação a ser feita aqui é que a implicação é associativa à direita, ou seja, $\varphi \to \psi \to \gamma$ deve ser lido como $\varphi \to (\psi \to \gamma)$, e não como $(\varphi \to \psi) \to \gamma$. Portanto, o sequente que queremos provar deve ser lido como $\vdash (p \to q) \to ((q \to r) \to (p \to r))$. Utilizando inicialmente a regra $\toisa$, temos a seguinte situação:

%\begin{mathpar}
 \inferrule*[Right={$\toisa$}]{p \to q \vdash (q \to r) \to (p \to r)}{\vdash (p \to q) \to ((q \to r) \to (p \to r))}
\end{mathpar}%

Agora podemos aplicar novamente a regra $\toisa$:

%\begin{mathpar}
 \inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{p \to q,q \to r \vdash p \to r}{p \to q \vdash (q \to r) \to (p \to r)}}{\vdash (p \to q) \to (q \to r) \to (p \to r)}
\end{mathpar}%

E mais uma vez, já que a conclusão do sequente é ainda uma implicação:

%\begin{mathpar}
 \inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{p \to q,q \to r, p \vdash r}{p \to q,q \to r \vdash p \to r}}{p \to q \vdash (q \to r) \to (p \to r)}}{\vdash (p \to q) \to (q \to r) \to (p \to r)}
\end{mathpar}%

Agora não é mais possível utilizar a regra $\toisa$ porque a conclusão $r$ não é uma implicação, mas podemos utilizar a hipótese $q \to r$ para obter $r$, desde que tenhamos uma prova de $q$ para utilizarmos $\toe$. Neste ponto, a árvore é bifurcada em dois ramos e precisamos dividir o contexto de forma adequada em cada um dos ramos.

%\begin{mathpar} \inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toe$}]{p \to q, q \to r, p \vdash q \and \inferrule*[Right={$\ax$}]{~}{p \to q, q \to r, p \vdash q \to r}}{p \to q,q \to r, p \vdash r}}{p \to q,q \to r \vdash p \to r}}{p \to q \vdash (q \to r) \to (p \to r)}}{\vdash (p \to q) \to (q \to r) \to (p \to r)}
\end{mathpar}%

Observe que o ramo da direita consiste em um axioma já que a fórmula $q \to r$ pertence ao conjunto de hipóteses. No ramo da esquerda podemos obter $q$ por meio da regra $\toe$ com as hipóteses $p \to q$ e $p$. A prova completa é dada a seguir:

%\begin{mathpar} \inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\toe$}]{\inferrule*[Right={$\toe$}]{\inferrule*[Right={$\ax$}]{~}{p \to q, q \to r, p \vdash p} \and \inferrule*[Right={$\ax$}]{~}{p \to q, q \to r, p \vdash p \to q}}{p \to q, p \vdash q} \and \inferrule*[Right={$\ax$}]{~}{p \to q, q \to r, p \vdash q \to r}}{p \to q,q \to r, p \vdash r}}{p \to q,q \to r \vdash p \to r}}{p \to q \vdash (q \to r) \to (p \to r)}}{\vdash (p \to q) \to (q \to r) \to (p \to r)}
\end{mathpar}%

Agora vamos refazer este exercício no assistente de provas Coq. Para isto vamos criar uma seção que chamaremos de [exercicio1]:

*)

Section exemplo1.
  Variables p q r: Prop.

  Lemma ex1: (p -> q) -> (q -> r) -> p -> r.

(**

Depois de aberta a seção, declaramos as variáveis [p], [q] e [r], e enunciamos o exercício a ser resolvido como um lema chamado [ex1]. Neste momento, a janela de provas nos apresenta a seguinte configuração:

-----
<<
1 goal (ID 1)
  
  p, q, r : Prop
  ============================
  (p -> q) -> (q -> r) -> p -> r
>>
-----

A linha dupla pontilhada separa a conclusão das hipóteses (ou contexto). Neste caso, temos a fórmula [(p -> q) -> (q -> r) -> p -> r] como conclusão, e o contexto contém apenas a declaração das variáveis [p], [q] e [r]. Por uma questão de organização, as provas serão escritas entre as palavras reservadas [Proof] e [Qed]. Seguindo os passos da prova acima, iniciaremos com uma aplicação da regra $\toisa$ que vai colocar o antecedente [p -> q] da implicação principal no contexto. A regra $\toisa$ em Coq é chamada de [intro]:

*)

  Proof.
    intro.

(**

A janela de provas apresenta agora a seguinte configuração:

-----
<<
1 goal (ID 2)
  
  p, q, r : Prop
  H : p -> q
  ============================
  (q -> r) -> p -> r
>>
-----

Agora a fórmula [p -> q] aparece como hipótese, como esperado. Observe que a hipótese [p -> q] recebe o nome [H]. Isto é importante porque sempre que precisarmos utilizar a fórmula [p -> q] utilizaremos o nome [H] para nos referirmos a ela. Note que o nome [H] foi criado automaticamente pelo Coq, mas podemos escolher outros nomes. Por exemplo, utilizando o comando [intro H1], o nome utilizado para a fórmula [p -> q] seria [H1], ao invés de [H]. O passo seguinte da prova consiste em outra aplicação da regra de introdução da implicação para colocar a fórmula [q -> r] no contexto:

*)    

    intro H'.

(**

O comando acima, corresponde a uma nova aplicação da regra $\toisa$, mas agora a hipótese introduzida deve se chamar [H']. A janela de provas da configuração atual é dada a seguir:

-----
<<
1 goal (ID 3)
  
  p, q, r : Prop
  H : p -> q
  H' : q -> r
  ============================
  p -> r
>>
-----

Por fim, podemos introduzir a fórmula [p] no contexto:

*)

    intro Hp.

(**

A hipótese correspondente a fórmula [p] será chamada de [Hp]:

-----
<<
1 goal (ID 4)
  
  p, q, r : Prop
  H : p -> q
  H' : q -> r
  Hp : p
  ============================
  r
>>
-----

Segundo a prova feita manualmente, o próximo passo corresponde a uma aplicação da regra de eliminação da implicação $\toe$, que em Coq se chama [apply]. Neste caso, faremos a aplicação da hipótese [H'] porque ela tem como conclusão a fórmula [r] que queremos provar:

*)    

    apply H'.

(**

A janela de prova tem a seguinte forma:

-----
<<
1 goal (ID 5)
  
  p, q, r : Prop
  H : p -> q
  H' : q -> r
  Hp : p
  ============================
  q
>>
-----

Ou seja, precisamos provar [q], que é o antecedente da implicação que acabamos de utilizar. Se considerarmos novamente a estrutura da regra $\toe$, fica fácil compreender o que está acontecendo antes da aplicação da hipótese [H']:

%\begin{mathpar}
\inferrule*[Right={$\toe$}]{p \to q, q \to r, p \vdash q \and p \to q, q \to r, p \vdash q \to r}{p \to q, q \to r, p \vdash r}
\end{mathpar}%

Assim, para provarmos [r] utilizando a regra $\toe$ precisamos de duas hipóteses, uma implicação que tenha [r] como conclusão, e o antecedente desta implicação. A implicação que tem [r] como conclusão é a hipótese [H']. Nos resta, então provar o antecedente da implicação que acabamos de usar, ou seja, precisamos provar a fórmula [q]. Agora podemos repetir o mesmo raciocínio utilizando a hipótese [H]:

*)

    apply H.

(**

A janela de provas atual é como a seguir:

-----
<<
1 goal (ID 6)
  
  p, q, r : Prop
  H : p -> q
  H' : q -> r
  Hp : p
  ============================
  p
>>
-----

Agora precisamos provar a fórmula [p], mas ela faz parte do contexto. De fato, a fórmula [p] corresponde à hipótese [Hp]. Ou seja, estamos na situação em que podemos aplicar a regra $\ax$ que, em Coq corresponde ao comando [assumption], e assim, concluímos a prova e fechamos a seção [exemplo1].
*)

    assumption.
Qed.    
End exemplo1.

(**

Agora é a sua vez de construir provas tanto em papel e lápis, quanto em Coq. Antes de apresentarmos os exercícios, vale um comentário sobre os assistentes de provas em geral. Estas ferramentas não foram projetadas com foco no ensino, e portanto veremos nas próximas seções que não teremos uma correspondência direta entre as regras de dedução natural e os comandos em Coq. Uma observação mais importante ainda é que estas ferramentas (e existem diversos assistentes de provas disponíveis no mercado) não foram projetadas para nos ajudar a construir provas, mas sim para que possamos verificar se uma prova feita em papel e lápis está correta. No exemplo apresentado anteriormente foi exatamente isto que fizemos: primeiro construímos uma prova em papel e lápis para, em seguida, reproduzirmos esta prova no Coq. Se a prova manual possuisse algum erro, não conseguiríamos reproduzí-la no Coq. Nos exercícios a seguir, construa inicialmente uma prova em papel e lápis, e posteriormente, reproduza esta prova no Coq.

 *)

(** *** Exercícios *)

(**

%\begin{enumerate}
 \item $\vdash (p \to p \to q) \to p \to q$
 \item $\vdash (p \to q) \to (p \to p \to q)$
 \item $\vdash (q \to r \to t) \to (p \to q) \to p \to r \to t$
 \item $\vdash (p \to q \to r) \to (p \to q) \to p \to r$
 \item $\vdash (p \to q \to r) \to (q \to p \to r)$
\end{enumerate}%

Uma vez finalizdas as provas em papel e lápis, é hora de verificar se as provas estão corretas. Abaixo apresentamos os enunciados dos exercícios, mas sem as provas. O comando [Admitted] nos permite enunciar um exercício/problema e deixar a prova pendente. Nos exercícios a seguir você deve remover a linha com [Admitted] e substituí-la pela sua prova finalizando com [Qed] como fizemos no exemplo.

*)

  Lemma exercicio1: (p -> p -> q) -> p -> q.
  Proof.
  Admitted.

  Lemma exercicio2: (p -> q) -> (p -> p -> q).
  Proof.
  Admitted.

  Variables r t: Prop.
  Lemma exercicio3: (q -> r -> t) -> (p -> q) -> p -> r -> t.
  Proof.
  Admitted.

  Lemma exercicio4: (p -> q -> r) -> (p -> q) -> p -> r.
  Proof.
  Admitted.

  Lemma exercicio5: (p -> q -> r) -> (q -> p -> r).
  Proof.
  Admitted.

(**

Na próxima seção, vamos considerar os outros conectivos apresentados na gramática (%\ref{gram:lp}%), assim como as regras de introdução e eliminação de cada um deles.

*)
  
(** * A Lógica Proposicional Minimal *)

(**
  
  A negação%\index{negação}% pode ser definida como uma implicação particular: $\neg\varphi = \varphi \to \bot$. Neste caso, as regras de introdução e eliminação são adaptações diretas das regras $\toisa$ e $\toe$:

%\begin{mathpar} \inferrule*[Right={$\negisa$}]{\Gamma,\varphi \vdash \bot}{\Gamma \vdash \neg\varphi}
\and\and \inferrule*[Right={$\nege$}]{\Gamma \vdash \neg \varphi \and \Gamma \vdash \varphi}{\Gamma \vdash \bot}
\end{mathpar}%

Como exemplo, mostraremos como provar o sequente $\varphi \vdash \neg\neg\varphi$, qualquer que seja a fórmula $\varphi$.

%\begin{mathpar} \inferrule*[Right={$\negisa$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Right={$\ax$}]{~}{\varphi,\neg\varphi \vdash \neg\varphi} \and \inferrule*[Right={$\ax$}]{~}{\varphi,\neg\varphi \vdash \varphi}}{\varphi,\neg\varphi \vdash \bot}}{\varphi \vdash \neg\neg\varphi}
\end{mathpar}%

Agora vamos reproduzir esta prova no Coq. Note que este sequente tem uma fórmula como hipótese, a saber $\varphi$. Todos os sequentes anteriores não tinham hipóteses. Como, então declarar uma hipótese no Coq? Simples, a hipótese é declarada dentro de uma seção:

 *)

  Section exemplo2.
    Hypothesis H: p.
    Lemma nni: ~~p. 

      (**

A janela de prova é como a seguir:

-----
<<
1 goal (ID 6)
  
  H : p
  ============================
  ~ ~ p
>>
-----

Ou seja, temos a hipótese [H] que corresponde à fórmula [p], e queremos concluir a fórmula [~~p]. O Coq não possui comandos específicos para as regras de introdução e eliminação da negação. De fato, considerando que a negação é uma implicação particular, podemos utilizar os comandos da implicação.

       *)

      Proof.
        intro.

        (**

A janela de prova é:

-----
<<
1 goal (ID 8)
  
  H : p
  H0 : ~ p
  ============================
  False
>>
-----

E considerando que [~p] é o mesmo que [p -> False], podemos aplicar a hipótese [H0], e fechá-la com [assumption].

         *)

        apply H0. assumption.
      Qed.
End exemplo2.

  (**

E quanto à eliminação da dupla negação? Podemos prová-la agora? Infelizmente não, porque o poder de expressividade que temos até agora com as regras $\toe$, $\toisa$, $\negisa$ e $\nege$ não é suficiente para provarmos a eliminação da dupla negação. Mas para deixá-lo um pouco intrigado sobre esta questão provaremos o seguinte sequente: $\neg\neg\neg\varphi \vdash \neg\varphi$.

%\begin{mathpar} \inferrule*[Right={$\negisa$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Left={$\nni$}]{\inferrule*[Right={$\ax$}]{~}{\neg\neg\neg\varphi, \varphi \vdash \varphi}}{\neg\neg\neg\varphi, \varphi \vdash \neg\neg\varphi} \and \inferrule*[Right={$\ax$}]{~}{\neg\neg\neg\varphi, \varphi \vdash \neg\neg\neg\varphi}}{\neg\neg\neg\varphi,\varphi \vdash \bot}}{\neg\neg\neg\varphi \vdash \neg\varphi}
\end{mathpar}%

O sequente anterior é a prova da eliminação da dupla negação de uma fórmula negada, e não de uma fórmula qualquer, e isto faz toda a diferença. Voltaremos a falar da eliminação da dupla negação na seção sobre lógica proposicional clássica%\index{lógica!proposicional!clássica}%.

A seguir, vamos refazer esta prova no Coq.
       *)

      Section exemplo3.
        Hypothesis H: ~~~p.
        Lemma nne_neg: ~p.
        Proof.
          intro H1.
          apply H.
          apply nni.
          assumption.
        Qed.
      End exemplo3.

      
(** *** Exercícios *)

      (**

%\begin{enumerate}
 \item Prove $\varphi \to \psi \vdash (\neg\neg\varphi) \to (\neg\neg\psi)$, onde $\varphi$ e $\psi$ são fórmulas quaisquer;
\item Prove $\neg\neg(\varphi \to \psi) \vdash (\neg\neg\varphi) \to (\neg\neg\psi)$, onde $\varphi$ e $\psi$ são fórmulas quaisquer.
\item Prove $\vdash (((((\varphi \to \psi) \to \varphi) \to \varphi) \to \psi) \to \psi)$, onde $\varphi$ e $\psi$ são fórmulas quaisquer.
\item Prove $\varphi, \neg\varphi \vdash \neg\psi$, onde $\varphi$ e $\psi$ são fórmulas quaisquer.
\end{enumerate}%

Para cada um dos exercícios, reproduza a sua prova no Coq:

       *)

      Section exercicio_nne_imp.
        Hypothesis H: p -> q.
        Lemma nne_imp: (~~p) -> (~~q).
        Proof.
          Admitted.
      End exercicio_nne_imp.

      Section exercicio_nne_to_imp.
        Hypothesis H: ~~(p -> q).
        Lemma nne_to_imp: (~~p) -> (~~q).
          Proof.
            Admitted.
      End exercicio_nne_to_imp.

      Section exercicio_weak_explosion.
        Hypothesis H1: p.
        Hypothesis H2: ~p.
        Lemma weak_explosion: ~q.
        Proof.
        Admitted.
      End exercicio_weak_explosion.        

      Lemma weak_peirce: (((((p -> q) -> p) -> p) -> q) -> q).
      Proof.
      Admitted.

      (**

A conjunção é um conectivo binário cuja %{\it regra de introdução}\index{regra!introdução!conjunção}%, denotada por $\landi$, tem a seguinte forma:

%\begin{eqnarray}\label{rule:landi}
 \inferrule*[Right={$\landi$}]{\Gamma \vdash \varphi_1 \and \Gamma \vdash \varphi_2}{\Gamma \vdash \varphi_1 \land \varphi_2}
\end{eqnarray}%

%\noindent% ou seja, uma prova de $\Gamma \vdash \varphi_1 \land \varphi_2$ é construída a partir de uma prova de $\Gamma \vdash \varphi_1$ e de uma prova de $\Gamma \vdash \varphi_2$. 

Existem duas regras de eliminação para a conjunção já que podemos extrair qualquer uma das componentes de uma conjunção:

%\begin{mathpar}
  \inferrule*{
  \inferrule*[Right={$\landel$}]{\Gamma \vdash\varphi_1 \land \varphi_2}{\Gamma \vdash\varphi_1} \and\and\and\and\and\and
  \inferrule*[Right={$\lander$}]{\Gamma \vdash\varphi_1 \land \varphi_2}{\Gamma \vdash\varphi_2}}{}
 \end{mathpar}%

 Estas duas regras podem ser representadas de forma mais concisa da seguinte forma:

%\begin{eqnarray}\label{rule:lande}
    \inferrule*[Right={$\lande$}]{\Gamma \vdash\varphi_1 \land \varphi_2}{\Gamma \vdash\varphi_{i\in\{1,2\}}}
  \end{eqnarray}%

Usaremos o nome $\lande$ para designar a utilização da regra de eliminação da conjunção quando não quisermos especificar qual das regras $\landel$ ou $\lander$ foi utilizada.

*)

      (** *** Exercícios *)
      (**

%\begin{enumerate}
\item $\varphi \land \psi \vdash \psi \land \varphi$.
\item $(\varphi \land \psi) \land \rho \vdash \varphi \land (\psi \land \rho)$.
\end{enumerate}%

       *)

      Section exercicio_comm_and.
        Hypothesis H: p /\ q.
        Lemma comm_and: q /\ p.
        Proof.
          Admitted.
      End exercicio_comm_and.

      Section exercicio_comm_assoc.
        Hypothesis H: (p /\ q) /\ r.
        Lemma comm_assoc: p /\ (q /\ r).
        Proof.
          Admitted.
      End exercicio_comm_assoc.

(**

Vejamos agora as regras para a disjunção. A %{\it regra de introdução da disjunção}\index{regra!introdução!disjunção}% nos permite construir a prova de uma disjunção a partir da prova de qualquer uma das suas componentes:

%\begin{mathpar}
 \inferrule*[Right={$\lorl$}]{\Gamma \vdash \varphi_1}{\Gamma \vdash \varphi_1 \lor \varphi_2} \and\and
 \inferrule*[Right={$\lorr$}]{\Gamma \vdash \varphi_2}{\Gamma \vdash \varphi_1 \lor \varphi_2}
 \end{mathpar}%
 
Como no caso da regra de eliminação da conjunção podemos representar estas duas regras de forma mais compacta:

%\begin{mathpar}
 \inferrule*[Right={$\lori$}]{\Gamma \vdash \varphi_{i\in\{1,2\}}}{\Gamma \vdash \varphi_1 \lor \varphi_2}
\end{mathpar}%

A %{\it regra de eliminação da disjunção}\index{regra!eliminação!disjunção}% nos permite construir a prova de uma fórmula, digamos $\gamma$, a partir da prova de uma disjunção da seguinte forma:

%\begin{mathpar}
 \inferrule*[Right={$\loresa$}]{\Gamma \vdash \varphi_1 \lor \varphi_2 \and \Gamma, \varphi_1 \vdash \gamma \and \Gamma, \varphi_2 \vdash \gamma}{\Gamma\vdash \gamma}
\end{mathpar}%

Assim, a construção de uma prova de $\gamma$ a partir das fórmulas em $\Gamma$ (sequente $\Gamma \vdash \gamma$) depende de três coisas: uma prova da disjunção (sequente $\Gamma \vdash \varphi_1 \lor \varphi_2$) uma prova de $\gamma$ a partir de $\varphi_1$ e das fórmulas de $\Gamma$ (sequente $\Gamma, \varphi_1 \vdash \gamma$) e de outra prova de $\gamma$ a partir de $\varphi_2$ e das fórmulas de $\Gamma$ (sequente $\Gamma, \varphi_2 \vdash \gamma$). Como exemplo, mostraremos que a disjunção é comutativa, ou seja, queremos construir uma prova para o sequente $\varphi \lor \psi \vdash \psi \lor \varphi$. A ideia aqui é utilizarmos a regra $\loresa$. Para isto podemos instanciar $\Gamma$ com o conjunto unitário contendo a fórmula $\varphi\lor\psi$. Em função da estrutura da regra $\loresa$, precisamos construir duas provas distintas de $\psi\lor\varphi$: uma a partir de $\varphi$, e outra a partir de $\psi$. Podemos fazer isto com a ajuda da regra $\lori$:
%\begin{mathpar}
\inferrule*[Right={$\loresa$}]{\inferrule*[Left={$\ax$}]{~}{\varphi\lor\psi \vdash \varphi\lor\psi} \and \inferrule*[Right={$\lori$}]{\inferrule*[Right={$\ax$}]{~}{\varphi\lor\psi,\varphi \vdash \varphi}}{\varphi\lor\psi,\varphi \vdash \psi\lor\varphi} \and \inferrule*[Right={$\lori$}]{\inferrule*[Right={$\ax$}]{~}{\varphi\lor\psi,\psi \vdash \psi}}{\varphi\lor\psi,\psi \vdash \psi\lor\varphi}}{\varphi\lor\psi \vdash \psi\lor\varphi}
 \end{mathpar}%

Agora vamos fazer uma prova análoga no Coq.

*)

Section exemplo_or_comm.      
  Hypothesis H: p \/ q.
  Lemma or_comm: q \/ p.
  Proof.

(**

-----
<<
1 goal (ID 7)
  
  H : p \/ q
  ============================
  q \/ p
>>
-----

A regra de eliminação da disjunção pode ser simulada pelo comando [destruct H] que vai bifurcar a prova em dois ramos.

*)    

    destruct H.

(**

-----
<<
2 goals (ID 14)
  
  H : p \/ q
  H0 : p
  ============================
  q \/ p

goal 2 (ID 15) is:
 q \/ p
>>
-----

No primeiro ramo precisamos provar [q \/ p] tendo [p \/ q] e [p] como hipóteses, e no segundo caso, precisamos provar [q \/ p] tendo [p \/ q] e [q] como hipóteses. Podemos organizar as provas que têm bifurcação colocando um hífen para cada caso. O hífen, apesar de não ser obrigatório, deixa a prova mais legível. No primeiro caso, temos as fórmulas [p \/ q] e [p] como hipóteses, e portanto podemos concluir este ramo com uma aplicação da regra de introdução da disjunção. Como a componente da disjunção [q \/ p] que temos como hipótese está à direita, o comando Coq a ser utilizado é [right]. O raciocínio para o outro caso é análogo.

*)    

    - right. assumption.
    - left. assumption.
Qed.
End exemplo_or_comm.

  (** *** Exercício *)
  (**
     Sejam $\varphi$, $\psi$ e $\rho$ fórmulas quaisquer da lógica proposicional. Prove que a disjunção é associativa, isto é, prove o sequente $(\varphi \lor \psi) \lor \rho \vdash \varphi \lor (\psi \lor \rho)$.

*)

  Section exercicio_or_assoc.
    Hypothesis H: (p \/ q) \/ r.
    Lemma or_assoc: p \/ (q \/ r).
    Proof.
    Admitted.
    End exercicio_or_assoc.

(**

O conjunto de regras estudado até aqui forma a chamada %{\it Lógica Proposicional Minimal}%. A Tabela (%\ref{regras:minimal}%) contém todas estas regras:

%\begin{table}
\centering
\begin{tabular}{|c|cc|p{8cm}|}\hline
& Regras de introdução && Regras de eliminação \\
\hline\hline
1& $\inferrule*[Right={$\landi$}]{\Gamma \vdash \varphi_1 \and \Gamma \vdash \varphi_2}{\Gamma \vdash \varphi_1 \land \varphi_2}$  && $\inferrule*[Right={$\lande$}]{\Gamma \vdash\varphi_1 \land \varphi_2}{\Gamma \vdash\varphi_{i\in\{1,2\}}}$ \\\hline
2 & $\inferrule*[Right={$\lori$}]{\Gamma \vdash \varphi_{i\in\{1,2\}}}{\Gamma \vdash \varphi_1 \lor \varphi_2}$ && $\inferrule*[Right={$\loresa$}]{\Gamma \vdash \varphi_1 \lor \varphi_2 \and \Gamma, \varphi_1 \vdash \gamma \and \Gamma, \varphi_2 \vdash \gamma}{\Gamma \vdash \gamma}$ \\\hline
3 & $\inferrule*[Right={$\toisa$}]{\Gamma,\varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}$ && $\inferrule*[Right={$\toe$}]{\Gamma \vdash \varphi\to \psi \and \Gamma \vdash \varphi}{\Gamma \vdash \psi}$ \\\hline
4 & $\inferrule*[Right={$\negisa$}]{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg\varphi}$ && $\inferrule*[Right={$\nege$}]{\Gamma \vdash \neg \varphi \and \Gamma \vdash \varphi}{\Gamma \vdash \bot}$ \\\hline
\end{tabular}
\caption{Regras da Lógica Minimal}\label{regras:minimal}
\end{table}%

Agora vamos resolver mais alguns exercícios na lógica minimal. Considere o sequente $\varphi \to \psi, \neg \psi \vdash \neg \varphi$. Como a fórmula do consequente é uma negação, vamos aplicar a regra de introdução da negação na construção de uma prova (raciocinando de baixo para cima, isto é, da raiz para as folhas da árvore):
%\begin{mathpar}
  \inferrule*[Right={$\negisa$}]{\inferrule{?}{\varphi \to \psi, \neg \psi, \varphi \vdash \bot}}{\varphi \to \psi, \neg \psi \vdash \neg \varphi}
 \end{mathpar}%

Agora, precisamos construir uma prova do absurdo, e portanto podemos tentar utilizar a regra $\nege$. Para isto precisamos escolher uma fórmula do contexto para fazer o papel de $\varphi$ na instância que utilizaremos da regra de eliminação da negação (ver Tabela %\ref{regras:minimal}%). A princípio temos três opções para esta instância: $\varphi\to\psi$, $\neg\psi$ e $\varphi$. A boa escolha neste caso é $\neg\psi$ porque podemos facilmente provar $\psi$ a partir do contexto dado:
%\begin{mathpar}   \inferrule*[Right={$\negisa$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Left={$\toe$}]{\inferrule*[Right={$\ax$}]{~}{\varphi \to \psi, \neg \psi, \varphi \vdash \varphi\to\psi} \and \inferrule*[Right={$\ax$}]{~}{\varphi \to \psi, \neg \psi, \varphi \vdash \varphi}}{\varphi \to \psi, \neg \psi, \varphi \vdash \psi} \and \inferrule*[Right={$\ax$}]{~}{\varphi \to \psi, \neg \psi, \varphi \vdash \neg\psi}}{\varphi \to \psi, \neg \psi, \varphi \vdash \bot}}{\varphi \to \psi, \neg \psi \vdash \neg \varphi}
 \end{mathpar}%

Depois de concluída a prova é fácil entender o que queríamos dizer com %{\it boa escolha}% acima: Uma boa escolha é um caminho que vai nos permitir concluir uma prova. Mas como fazer uma boa escolha? Isto depende do problema a ser resolvido. Em alguns casos pode ser simples, mas em outros, bastante complicado. O ponto importante a compreender é que possivelmente existem caminhos distintos na construção de provas, e muito deste processo depende da nossa criatividade.

O sequente que acabamos de provar ocorre com certa frequência em outras provas, assim como a regra derivada $\nni$ vista anteriormente. As regras que são obtidas a partir das regras da Tabela %\ref{regras:minimal}% são chamadas de %{\it regras derivadas}%. Este é o caso da regra conhecida como %{\it modus tollens (MT)}% obtida a partir do sequente do exemplo anterior, onde cada antecedente é generalizado como uma premissa da regra:

%\begin{mathpar}
 \inferrule*[Right={$\mt$}]{\Gamma \vdash \varphi\to\psi \and \Gamma \vdash \neg\psi}{\Gamma \vdash \neg\varphi}
\end{mathpar}%

 *)

  Section exemplo_mt.
    Hypothesis H1: ~q.
    Hypothesis H2: p -> q.
    Lemma mt: ~p.
    Proof.
      intro H3.
      apply H1.
      apply H2.
      assumption.
    Qed.      
  End exemplo_mt.

(**

Considere o sequente $\varphi \to \psi \vdash \neg \psi \to \neg \varphi$. Inicialmente, devemos observar que a fórmula que queremos provar é uma implicação, e portanto, o mais natural é tentar aplicar a regra $\toisa$, e em seguida aplicar $\mt$ (na construção de baixo para cima) para poder completar a prova:

%\begin{mathpar} \inferrule*[Right={$\toisa$}]{\inferrule*[Right={$\mt$}]{\inferrule*[Left={$\ax$}]{~}{\varphi\to\psi \vdash \varphi\to\psi} \and \inferrule*[Right={$\ax$}]{~}{ \neg\psi \vdash \neg\psi}}{\varphi \to \psi, \neg \psi \vdash \neg \varphi}}{\varphi \to \psi \vdash \neg \psi \to \neg \varphi}
\end{mathpar}%

O sequente que acabamos de provar é outro caso que aparece com frequência em provas, e corresponde a uma regra conhecida como %{\it contrapositiva}%:

%\begin{mathpar}
 \inferrule*[Right={$\cp$}]{\Gamma \vdash \varphi \to \psi}{\Gamma \vdash \neg \psi \to \neg \varphi}
\end{mathpar}%

*)

  Section exemplo_cp.
    Hypothesis H: p -> q.
    Lemma cp: ~q -> ~p.
    Proof.
      intro H1. apply mt.
      - assumption.
      - assumption.
    Qed.      
    End exemplo_cp.

  (** *** Exercício *)

  (**

   Sejam $\varphi$ e $\psi$ fórmulas da lógica proposicional. Prove o sequente $\varphi \to \neg\psi \vdash \psi \to \neg\varphi$. Em seguida, reproduza a sua prova no Coq.

   *)

  Section exercicio_cp1.
    Hypothesis H: p -> ~q.
    Lemma cp1: q -> ~p.
    Proof.
      Admitted.
  End exercicio_cp1.

(**

Este é um bom momento para simplificarmos a notação que estamos usando para fazer as provas em papel e lápis. Na notação atual, cada nó na árvore de derivação é anotado com um sequente. Na nova notação, anotaremos cada nó apenas com a fórmula correspondente ao consequente do sequente. Isto vai deixar a estrutura das provas mais simples, e como veremos, nenhuma informação da provar será perdida porque temos como inferir o contexto correspondente em cada nó da árvore de derivação. Vejamos um exemplo onde o contexto é o mesmo ao longo de toda a prova. Vamos retomar o exercício em que provamos que a conjunção é um conectivo que satisfaz a propriedade associativa. Neste ponto acreditamos que você já resolveu este exercício. Em caso negativo, resolva o exercício antes de prosseguir. Em seguida, compare sua solução com a que apresentamos a seguir, ok? Tentar resolver os exercícios antes de olhar qualquer solução é um passo muito importante para a sua evolução nos estudos de lógica.

Considere a prova a seguir:
%{\scriptsize \begin{mathpar}
 \inferrule*[Right={$\landi$}]{
   \inferrule*[Left={$\lande$}]{
     \inferrule*[Left={$\lande$}]{
       \inferrule*[Left={$\ax$}]{~}{(\phi \land \psi)\land \varphi \vdash (\phi \land \psi)\land \varphi}
       }
       {(\phi \land \psi)\land \varphi \vdash \phi \land \psi}
       }
       {(\phi \land \psi)\land \varphi \vdash \phi}
       \and
       \inferrule*[Right={$\landi$}]{
         \inferrule*[Left={$\lande$}]{
           \inferrule*[Left={$\lande$}]{
             \inferrule*[Left={$\ax$}]{~}{(\phi \land \psi)\land \varphi \vdash (\phi \land \psi) \land \varphi}
             }
             {(\phi \land \psi)\land \varphi \vdash \phi \land \psi}
             }
             {(\phi \land \psi)\land \varphi \vdash \psi}
             \and
             \inferrule*[Right={$\lande$}]{
              \inferrule*[Right={$\ax$}]{~}{(\phi \land \psi)\land \varphi \vdash (\phi \land \psi) \land \varphi}
             }
             {(\phi \land \psi)\land \varphi \vdash \varphi}
            }
            {(\phi \land \psi)\land \varphi \vdash (\psi \land \varphi)}
          }
          {(\phi \land \psi)\land \varphi \vdash \phi \land (\psi \land \varphi)}
\end{mathpar}}%

Ao remover os contextos, obtemos a seguinte árvore: 
%\begin{mathpar}
          \inferrule*[Right={$\landi$}]{
            \inferrule*[Left={$\lande$}]{
              \inferrule*[Left={$\lande$}]{
                (\phi \land \psi)\land \varphi
              }
              {(\phi \land \psi)}
            }
            {\phi}
            \and
            \inferrule*[Right={$\landi$}]{
              \inferrule*[Left={$\lande$}]{
                \inferrule*[Left={$\lande$}]{
                  (\phi \land \psi) \land \varphi
                }
                {\phi \land \psi}
              }
              {\psi}
              \and
              \inferrule*[Right={$\lande$}]{
                (\phi \land \psi) \land \varphi
              }
              {\varphi}
            }
            {(\psi \land \varphi)}
          }
          {\phi \land (\psi \land \varphi)}
\end{mathpar}%

A árvore ficou muito mais compacta e limpa, e este é o objetivo da mudança de notação. Como o contexto é o mesmo em toda a árvore neste exemplo, então podemos facilmente recuperá-lo a partir do enunciado do exercício que é o sequente $(\phi \land \psi)\land \varphi \vdash \phi \land (\psi \land \varphi)$. Do ponto de vista prático, esta mudança facilita a escrita de provas maiores, uma vez que uma árvore de derivação pode crescer rapidamente. Como a janela de prova do Coq mostra o sequente correspondente ao nó da árvore de prova no momento da prova, esta mudança de notação não terá nenhum impacto em relação ao Coq. Você verá também que a maioria das bibliografias sobre dedução natural utilizam a nova notação %\cite{huthLogicComputerScience2004,silvaLogicaParaComputacao2006,dalenLogicStructureEd2008,ayala-rinconAppliedLogicComputer2017}%. O que ocorre então com as regras que promovem uma mudança de contexto? Será que é possível sempre remover os contextos das provas de uma forma sistemática? Sim! Ainda considerando o exemplo anterior, se não soubéssemos qual o contexto que foi apagado, seria possível descobrí-lo? Sim, esta informação vem das folhas da árvore, que são as hipóteses do problema. Na notação com o contexto explícito, as folhas da árvore têm que ser axiomas, e portanto o contexto de todas as folhas é a fórmula $(\phi \land \psi) \land \varphi$ já que todas as folhas são iguais. Podemos também consultar a Tabela %\ref{regras:minimal}% e observar que o contexto não muda nas regras $\lande$ e $\landi$. Portanto, o contexto em cada nó da árvore é formado pelo conjunto unitário contendo a fórmula $(\phi \land \psi)\land \varphi$. Assim, as folhas  de uma árvore de derivação têm que ser fórmulas pertencentes ao contexto.

Em um exemplo anterior construímos uma prova do sequente $\varphi\to\psi, \neg\psi \vdash \neg\varphi$ com contextos explícitos, a versão com contextos implícitos é dada pela seguinte árvore de derivação:
%\begin{mathpar} \inferrule*[Right={$\negisa$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Left={$\toe$}]{\varphi\to\psi \and \varphi}{\psi} \and \neg\psi}{\bot}}{\neg \varphi}
\end{mathpar}%

Note que esta árvore possui três folhas, cada uma contendo uma fórmula distinta. O contexto inicial é o conjunto contendo todas as fórmulas que aparecem nas folhas, ou seja, nosso contexto inicial é o conjunto $\{ \varphi\to\psi, \neg\psi, \varphi \}$. As regras $\toe$ e $\nege$ preservam o contexto, e portanto o contexto da linha 3 é, ainda, o conjunto $\{ \varphi\to\psi, \neg\psi, \varphi \}$. De acordo com a Tabela %\ref{regras:minimal}%, a regra $\negisa$ adiciona uma fórmula ao contexto (leitura de baixo para cima), ou remove uma fórmula do contexto, se a leitura for feita de cima para baixo. Neste caso, a fórmula removida é $\varphi$, e portanto o contexto da fórmula $\neg\varphi$ (raiz da árvore) é o conjunto $\{\varphi\to\psi, \neg\psi \}$ como esperado pelo enunciado do exemplo. Na notação sem contexto, as fórmulas que são removidas do contexto ao longo da prova, como a fórmula $\varphi$ deste exemplo são colocadas entre colchetes para enfatizar que são hipóteses temporárias que, em determinado momento serão removidas do contexto:

%\begin{mathpar} \inferrule*[Right={$\negisa$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Left={$\toe$}]{\varphi\to\psi \and [\varphi]}{\psi} \and \neg\psi}{\bot}}{\neg \varphi}
 \end{mathpar}%

%\noindent% e agora fica claro que a fórmula $\varphi$ não faz parte do contexto original do sequente a ser provado. Note que os colchetes são colocados %{\it apenas nas folhas}% que contêm fórmulas que não fazem parte do contexto dado pelo problema. Adicionalmente, como o contexto da raiz tem que ser o contexto dado pelo problema, caso contrário a prova não é uma prova do problema proposto, precisamos de um mecanismo para nos informar quando as fórmulas marcadas com os colchetes são %{\it removidas}% (ou %{\it descartadas})\index{fórmula!descarte de hipóteses}% do contexto. No exemplo acima, isto ocorre ao aplicarmos a regra $\negisa$. Então, utilizaremos uma letra para registrar este fato:

%\begin{mathpar} \inferrule*[Right={$\negi{u}$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Left={$\toe$}]{\varphi\to\psi \and [\varphi]^u}{\psi} \and \neg\psi}{\bot}}{\neg \varphi}
\end{mathpar}%

Agora sabemos em que momento a fórmula $\varphi$ foi introduzida (folha $[\varphi]^u$), e em que momento foi descartada (regra $\negi{u}$) na árvore de derivação.

A seguir, veremos exemplos mais complexos onde, por exemplo, fórmulas idênticas podem exigir marcas distintas, mas antes disto compare as regras de dedução natural para a lógica proposicional minimal com o contexto explícito e com o contexto implícito na Tabela %\ref{regras:contexto}%, e veja como o mecanismo de descarte simula a mudança de contexto antes e depois de uma aplicação das regras $\loresa$, $\toisa$ e $\negisa$. Como a notação com contexto implícito é mais compacta, a partir deste momento não utilizaremos mais contextos explícitos. A intenção de iniciar esta apresentação utilizando contextos explícitos foi de permitir uma explicação mais fácil e natural para o descarte de hipóteses, que sempre gerou muitas dúvidas entre os alunos. Por exemplo, quando a razão do descarte não está clara, é comum aparecerem soluções (erradas!) com árvores de derivação onde o descarte de hipóteses é feito em regras como $\landi$, $\lande$, $\lori$, $\toe$ e $\nege$. Se você acha que está tudo bem uma árvore de derivação conter descarte de hipóteses nas regras citadas na frase anterior, volte para o início deste capítulo e reinicie o estudo do sistema de dedução natural antes de prosseguir :-)

%\begin{table}
\centering
\begin{tabular}{|c|cc|cc|}\hline
& Contexto explícito && Contexto implícito \\
\hline\hline
1 &  $\inferrule*[Right={$\landi$}]{\Gamma \vdash \varphi_1 \and \Gamma \vdash \varphi_2}{\Gamma \vdash \varphi_1 \land \varphi_2}$ &&  $\inferrule*[Right={$\landi$}]{\varphi_1 \and \varphi_2}{\varphi_1 \land \varphi_2}$ & \\\hline
2 & $\inferrule*[Right={$\lande$}]{\Gamma \vdash\varphi_1 \land \varphi_2}{\Gamma \vdash\varphi_{i\in\{1,2\}}}$ && $\inferrule*[Right={$\lande$}]{\varphi_1 \land \varphi_2}{\varphi_{i\in\{1,2\}}}$ & \\\hline
3 & $\inferrule*[Right={$\lori$}]{\Gamma \vdash \varphi_{i\in\{1,2\}}}{\Gamma \vdash \varphi_1 \lor \varphi_2}$ && $\inferrule*[Right={$\lori$}]{\varphi_{i\in\{1,2\}}}{\varphi_1 \lor \varphi_2}$ & \\\hline
4 & $\inferrule*[Right={$\loresa$}]{\Gamma \vdash \varphi_1 \lor \varphi_2 \and \Gamma, \varphi_1 \vdash \gamma \and \Gamma, \varphi_2 \vdash \gamma}{\Gamma \vdash \gamma}$ &&
\infer[\lore{u}{v}]{\mbox{}\hspace{2.5cm}\gamma\hspace{2.5cm}\mbox{}}{\deduce{\varphi_1\vee\varphi_2}{}\hspace{10mm}\deduce{\gamma}{\deduce{\vdots}{[\varphi_1]^u}}\hspace{10mm}\deduce{\gamma}{\deduce{\vdots}{[\varphi_2]^v}}} & \\\hline
5 & $\inferrule*[Right={$\toisa$}]{\Gamma,\varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}$ && \infer[\toi{u}]{\varphi\rightarrow\psi}{\deduce{\psi}{\deduce{\vdots}{[\varphi]^u}}} & \\\hline
6 & $\inferrule*[Right={$\toe$}]{\Gamma \vdash \varphi\to \psi \and \Gamma \vdash \varphi}{\Gamma \vdash \psi}$ && $\inferrule*[Right={$\toe$}]{\varphi\to \psi \and \varphi}{\psi}$ & \\\hline
7 & $\inferrule*[Right={$\negisa$}]{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg\varphi}$ && \infer[\negi{u}]{\neg\varphi}{\deduce{\bot}{\deduce{\vdots}{[\varphi]^u}}} & \\\hline
8 & $\inferrule*[Right={$\nege$}]{\Gamma \vdash \neg \varphi \and \Gamma \vdash \varphi}{\Gamma \vdash \bot}$ && $\inferrule*[Right={$\nege$}]{\neg \varphi \and \varphi}{\bot}$ & \\\hline
\end{tabular}
\caption{Regras da Lógica Proposicional Minimal}\label{regras:contexto}
\end{table}%

No exemplo a seguir, veremos que é possível fazer a introdução de uma implicação sem o descarte de uma hipótese, se tivermos uma prova do consequente da implicação que queremos provar. Ou seja, se temos uma prova de $\psi$ então podemos construir uma prova de $\varphi\to\psi$, qualquer que seja a fórmula $\varphi$. Em outras palavras, queremos construir uma prova para o sequente $\psi \vdash \varphi\to\psi$. Raciocinando de baixo para cima, temos que a aplicação da regra $\toisa$ reduzirá o problema de provar $\varphi \to \psi$ ao problema de provar $\psi$ tendo $\varphi$ como hipótese adicional:

%\begin{mathpar}
  \inferrule*[Right={$\toi{u}$}]{
  \deduce{\psi}{\deduce{\vdots}{[\varphi]^u \and \psi}}}{\varphi\to\psi}
 \end{mathpar}%

Note que temos como hipótese a fórmula $\psi$ que precisamos provar, então o trabalho a ser feita consiste unicamente em organizar a árvore de forma que $[\varphi]^u$ e $\psi$ sejam suas folhas. Uma maneira de fazer isto é introduzindo e eliminando uma conjunção contendo $\psi$:

%\begin{mathpar}
  \inferrule*[Right={$\toi{u}$}]{ \inferrule*[Right={$\lande$}]{\inferrule*[Right={$\landi$}]{[\varphi]^u \and \psi}{\varphi\land\psi}}{\psi}}{\varphi\to\psi}
 \end{mathpar}%

Em Coq não precisamos lidar com a introdução e eliminação da conjunção:

 *)

  Section exemplo_imp_empty.
    Hypothesis H: q.
    Lemma imp_empty: p -> q.
    Proof.
      intro H1. assumption.
    Qed.
  End exemplo_imp_empty.
      
(**

Como este raciocínio aparece com frequência nas provas, vamos colocá-lo como uma regra derivada:

%\begin{mathpar}
   \inferrule*[Right={$\toi{\emptyset}$}]{\psi}{\varphi\to\psi}
\end{mathpar}%

%\begin{table}
\centering
\begin{tabular}{|p{2.7cm}|p{5.2cm}|p{3.3cm}|p{3.5cm}|}\hline
$\inferrule*[Right={$\nni$}]{\Gamma \vdash \varphi}{\Gamma \vdash \neg\neg\varphi}$ & $\inferrule*[Right={$\mt$}]{\Gamma \vdash \varphi\to\psi \and \Gamma \vdash \neg\psi}{\Gamma \vdash \neg\varphi}$ & $\inferrule*[Right={$\toi{\emptyset}$}]{\Gamma \vdash \psi}{\Gamma \vdash \varphi\to\psi}$ &
$\inferrule*[Right={$\cp$}]{\Gamma \vdash \varphi \to \psi}{\Gamma \vdash \neg \psi \to \neg \varphi}$ \\ \hline
\end{tabular}
\caption{Regras derivadas da Lógica Proposicional Minimal}\label{regras:derivadas}
\end{table}%

 *)

(** *** Exercícios *)  

(**

Prove os sequentes a seguir:
%\begin{enumerate}
 \item $\neg(\varphi \lor \psi) \vdash (\neg\varphi) \land (\neg\psi)$
 \item $(\neg\varphi) \land (\neg\psi) \vdash \neg(\varphi \lor \psi)$
 \item $\varphi \to \psi \vdash (\delta \lor \varphi) \to (\delta \lor \psi)$
 \item $\varphi \to \psi \vdash \neg(\varphi \land \neg\psi)$
 \item $\varphi \land \psi \vdash \neg(\neg\varphi \lor \neg\psi)$
 \item $\neg(\varphi\lor\gamma) \vdash (\neg\varphi)\land(\neg\gamma)$
 \item $(\neg\varphi)\land(\neg\gamma) \vdash \neg(\varphi\lor\gamma)$
 \item $(\neg\varphi)\lor(\neg\gamma) \vdash \neg(\varphi\land\gamma)$
 \item $\neg\neg(\varphi\land\gamma) \vdash (\neg\neg\varphi)\land(\neg\neg\gamma)$
 \item $(\neg\neg\varphi)\land(\neg\neg\gamma) \vdash \neg\neg(\varphi\land\gamma)$
 \item $\varphi \lor (\psi \land \gamma) \vdash (\varphi \lor \psi) \land (\varphi \lor \gamma)$
 \item $(\varphi \lor \psi) \land (\varphi \lor \gamma) \vdash \varphi \lor (\psi \land \gamma)$
 \item $\varphi \land (\psi \lor \gamma) \vdash (\varphi \lor \psi) \land (\varphi \lor \gamma)$
 \item $(\varphi \lor \psi) \land (\varphi \lor \gamma) \vdash \varphi \land (\psi \lor \gamma)$
 \item $\vdash \neg\neg(\varphi \lor \neg\varphi)$
 \item $\vdash \neg(\varphi \land \neg\varphi)$ 
\end{enumerate}%

*)

  Section exercicio_min1.
    Hypothesis H: ~(p \/ q).
    Lemma min1: (~p) /\ (~q).
    Proof.
      Admitted.
    End exercicio_min1.

    Section exercicio_min2.
    Hypothesis H: (~p) /\ (~q).
    Lemma min2: ~(p \/ q).
    Proof.
    Admitted.
    End exercicio_min2.

    Section exercicio_min3.
    Hypothesis H: p -> q.
    Lemma min3: (r \/ p) -> (r \/ q).
    Proof.
      Admitted.
    End exercicio_min3.

    Section exercicio_min4.
    Hypothesis H: p -> q.
    Lemma min4: ~(p /\ ~q).
    Proof.
    Admitted.
    End exercicio_min4.

    Section exercicio_min5.
    Hypothesis H: p /\ q.
    Lemma min5: ~(~p \/ ~q).
    Proof.
    Admitted.
    End exercicio_min5.

    Section exercicio_min6.
    Hypothesis H: ~(p \/ q).
    Lemma min6: (~p) /\ (~q).
    Proof.
      Admitted.
    End exercicio_min6.

    Section exercicio_min7.
    Hypothesis H: (~p) /\ (~q).
    Lemma min7: ~(p \/ q).
    Proof.
    Admitted.
    End exercicio_min7.

    Section exercicio_min8.
    Hypothesis H: (~p) \/ (~q).
    Lemma min8: ~(p /\ q).
    Proof.
    Admitted.
    End exercicio_min8.

    Section exercicio_min9.
    Hypothesis H: ~~(p /\ q).
    Lemma min9: (~~p) /\ (~~q).
    Proof.
    Admitted.
    End exercicio_min9.
    
    Section exercicio_min10.
    Hypothesis H: (~~p) /\ (~~q).
    Lemma min10: ~~(p /\ q).
    Proof.
    Admitted.
    End exercicio_min10.

    Section exercicio_min11.
    Hypothesis H: p \/ (q /\ r).
    Lemma min11: (p \/ q) /\ (p \/ r).
    Proof.
    Admitted.
    End exercicio_min11.
    
    Section exercicio_min12.
    Hypothesis H: (p \/ q) /\ (p \/ r).
    Lemma min12: p \/ (q /\ r).
    Proof.
    Admitted.
    End exercicio_min12.

    Section exercicio_min13.
    Hypothesis H: p /\ (q \/ r).
    Lemma min13:  (p /\ q) \/ (p /\ r).
    Proof.
    Admitted.
    End exercicio_min13.

    Section exercicio_min14.
    Hypothesis H: (p /\ q) \/ (p /\ r).
    Lemma min14: p /\ (q \/ r). 
    Proof.
    Admitted.
    End exercicio_min14.

    Lemma min15: ~~(p \/ ~p).
    Proof.
    Admitted.

    Lemma min16: ~(p /\ ~p).
    Proof.
      Admitted.

    
(** * A Lógica Proposicional Intuicionista *)

(**

Agora vamos estender a lógica proposicional minimal com uma nova regra chamada de %{\it regra da explosão}\index{regra da explosão}% ou %{\it regra da eliminação do absurdo intuicionista}\index{regra!eliminação!absurdo intuicionista}%. Esta regra nos permite concluir qualquer fórmula a partir do absurdo:

%\begin{mathpar}
 \inferrule*[Right={$\bote$}]{\bot}{\varphi}
\end{mathpar}%

A lógica obtida adicionando-se a regra da explosão à lógica proposicional minimal é denominada %{\it lógica proposicional intuicionista}\index{lógica!proposicional!intuicionista}%. Observe que a lógica proposicional minimal possui uma versão mais fraca de regra de explosão. De fato, podemos na lógica proposicional minimal%\index{lógica!proposicional!minimal}% concluir qualquer fórmula negada a partir do absurdo. A lógica proposicional intuicionista é conhecida por corresponder à noção de lógica construtiva que é particularmente interessante para a Computação. De forma simplificada, a lógica proposicional intuicionista pode ser vista como a lógica que rejeita a lei do terceiro excluído, ou seja, nesta lógica o sequente $\vdash \varphi\lor\neg\varphi$ não é um axioma e nem uma regra derivada, quando $\varphi$ é uma fórmula arbitrária. Vejamos um exemplo. Considere o seguinte sequente $\neg\varphi \lor \gamma \vdash \varphi\to\gamma$. Iniciando esta prova de baixo para cima, isto é, partindo do consequente, podemos aplicar a regra de introdução da implicação:
 %\begin{mathpar}
  \inferrule*[Right={$\toi{u}$}]{\neg\varphi\lor\gamma \and [\varphi]^u \\\\\\ ? \\\\\\ \gamma}{\varphi\to\gamma}
 \end{mathpar}%

Agora precisamos construir uma prova de $\gamma$ tendo as fórmulas $\neg\varphi\lor\gamma$ e $[\varphi]^u$ como contexto. Uma ideia possível é usar a regra de eliminação da disjunção porque com o lado esquerdo, isto é, com $\neg\varphi$ e com $[\varphi]^u$ temos o absurdo, e com a regra da explosão podemos concluir $\gamma$ como queríamos. O lado direito da disjunção já é igual a $\gamma$, e assim concluímos a prova:

%\begin{mathpar}
  \inferrule*[Right={$\toi{u}$}]{\inferrule*[Right={$\lore{v}{w}$}]{\neg\varphi\lor\gamma \and \inferrule*[Right={$\bote$}]{\inferrule*[Right={$\nege$}]{[\neg\varphi]^v \and [\varphi]^u}{\bot}}{\gamma} \and\and [\gamma]^w}{\gamma}}{\varphi\to\gamma}
\end{mathpar}%

Segue a mesma prova em Coq:

*)

Section exemplo_or_to_imp.
  Hypothesis H: (~p) \/ q.
  Lemma or_to_imp: p -> q.
  Proof.
    intro H1. destruct H.
    - contradiction.
    - assumption.
  Qed.    
End exemplo_or_to_imp.

(** *** Exercícios *)

(**

Prove os sequentes a seguir:
%\begin{enumerate}
 \item $(\neg\neg\varphi) \to (\neg\neg\psi) \vdash \neg\neg(\varphi \to \psi)$
 \item $\vdash \neg\neg(\neg\neg\varphi \to \varphi)$
 \item $\vdash \neg\neg(((\varphi \to \psi) \to \varphi) \to \varphi)$
\end{enumerate}%

A seguir, reproduza as suas soluções em Coq.

 *)

Section exercicio_nnto.
  Hypothesis H: (~~p) -> (~~q).
  Lemma nnto: ~~(p -> q).
  Proof.
    Admitted.
End exercicio_nnto.

Lemma nne_to: ~~(~~p -> p).
Proof.
  Admitted.

(** * A Lógica Proposicional Clássica *)

(**

Vamos caminhar na direção de mais uma extensão, agora da lógica intuicionista para a lógica clássica. Iniciamos com a lógica proposicional minimal, depois a estendemos para a lógica proposicional intuicionista, e agora vamos estendê-la com a lei do terceiro excluído, obtendo assim a lógica proposicional clássica. Na Tabela %\ref{regras:classica}% apresentamos também as regras com contexto explícito para que tenhamos sempre em mente como os contextos mudam de acordo com a aplicação das regras.
                                                                                                                                                                                          %\begin{table}
\centering
\begin{tabular}{|c|cc|cc|}\hline
& Contexto explícito && Contexto implícito \\
\hline\hline
1 &  $\inferrule*[Right={$\landi$}]{\Gamma \vdash \varphi_1 \and \Gamma \vdash \varphi_2}{\Gamma \vdash \varphi_1 \land \varphi_2}$ &&  $\inferrule*[Right={$\landi$}]{\varphi_1 \and \varphi_2}{\varphi_1 \land \varphi_2}$ & \\\hline
2 & $\inferrule*[Right={$\lande$}]{\Gamma \vdash\varphi_1 \land \varphi_2}{\Gamma \vdash\varphi_{i\in\{1,2\}}}$ && $\inferrule*[Right={$\lande$}]{\varphi_1 \land \varphi_2}{\varphi_{i\in\{1,2\}}}$ & \\\hline
3 & $\inferrule*[Right={$\lori$}]{\Gamma \vdash \varphi_{i\in\{1,2\}}}{\Gamma \vdash \varphi_1 \lor \varphi_2}$ && $\inferrule*[Right={$\lori$}]{\varphi_{i\in\{1,2\}}}{\varphi_1 \lor \varphi_2}$ & \\\hline
4 & $\inferrule*[Right={$\loresa$}]{\Gamma \vdash \varphi_1 \lor \varphi_2 \and \Gamma', \varphi_1 \vdash \gamma \and \Gamma'', \varphi_2 \vdash \gamma}{\Gamma, \Gamma', \Gamma'' \vdash \gamma}$ &&
\infer[\lore{u}{v}]{\mbox{}\hspace{2.5cm}\gamma\hspace{2.5cm}\mbox{}}{\deduce{\varphi_1\vee\varphi_2}{}\hspace{10mm}\deduce{\gamma}{\deduce{\vdots}{[\varphi_1]^u}}\hspace{10mm}\deduce{\gamma}{\deduce{\vdots}{[\varphi_2]^v}}} & \\\hline
5 & $\inferrule*[Right={$\toisa$}]{\Gamma,\varphi \vdash \psi}{\Gamma \vdash \varphi \to \psi}$ && \infer[\toi{u}]{\varphi\rightarrow\psi}{\deduce{\psi}{\deduce{\vdots}{[\varphi]^u}}} & \\\hline
6 & $\inferrule*[Right={$\toe$}]{\Gamma \vdash \varphi\to \psi \and \Gamma \vdash \varphi}{\Gamma \vdash \psi}$ && $\inferrule*[Right={$\toe$}]{\varphi\to \psi \and \varphi}{\psi}$ & \\\hline
7 & $\inferrule*[Right={$\negisa$}]{\Gamma, \varphi \vdash \bot}{\Gamma \vdash \neg\varphi}$ && \infer[\negi{u}]{\neg\varphi}{\deduce{\bot}{\deduce{\vdots}{[\varphi]^u}}} & \\\hline
8 & $\inferrule*[Right={$\nege$}]{\Gamma \vdash \neg \varphi \and \Gamma \vdash \varphi}{\Gamma \vdash \bot}$ && $\inferrule*[Right={$\nege$}]{\neg \varphi \and \varphi}{\bot}$ & \\\hline
9 & $\inferrule*[Right={$\bote$}]{\Gamma \vdash \bot}{\Gamma \vdash \varphi}$ && $\inferrule*[Right={$\bote$}]{\bot}{\varphi}$ & \\\hline
10 & $\inferrule*[Right={$\lem$}]{~}{\vdash \varphi \lor \neg\varphi}$ && $\inferrule*[Right={$\lem$}]{~}{\varphi \lor \neg\varphi}$ & \\\hline
\end{tabular}
\caption{Regras da Lógica Clássica}\label{lp:regras:classica}
\end{table}%

Como exemplo, vamos construir uma prova de uma regra conhecida como %{\it prova por contradição} (PBC)\index{prova por contradição}%. A ideia desta regra consiste em assumir a negação do que se quer provar, e a partir daí derivar uma contradição. O sequente a ser provado é o seguinte $(\neg\varphi) \to \bot \vdash \varphi$. Veja que queremos provar $\varphi$, e para isto estamos assumindo que a negação de $\varphi$ nos leva a uma contradição. Vamos então tomar uma instância da $\lem$, e provar $\varphi$ via a eliminação da disjunção:

%\begin{mathpar}
  \inferrule*[Right={$\lore{u}{v}$}]{\inferrule*[Left={$\lem$}]{~}{\varphi \lor \neg\varphi} \and [\varphi]^u \and \inferrule*[Right={$\bote$}]{\inferrule*[Right={$\toe$}]{(\neg\varphi) \to \bot \and [\neg\varphi]^v}{\bot}}{\varphi}}{\varphi}
 \end{mathpar}%

 A regra de prova por contradição é dada a seguir. Observe como o contexto muda por conta do descarte de hipóteses:

%\begin{center}
\begin{tabular}{|ccc|cc|}\hline
Contexto explícito &&& Contexto implícito & \\
\hline\hline
$\inferrule*[Right={$\pbcsa$}]{\Gamma, \neg\varphi \vdash \bot}{\Gamma \vdash \varphi}$ &&&  $\infer[\pbc{u}]{\varphi}{\deduce{\bot}{\deduce{\vdots}{[\neg\varphi]^u}}}$ & \\\hline
\end{tabular}
\end{center}%
                                                                                             *)

Section exemplo_pbc.
  Hypothesis lem: p \/ ~p.
  Hypothesis H: ~p -> False.
  Lemma pbc: p.
  Proof.
    destruct lem.
    - assumption.
    - contradiction.
  Qed.
End exemplo_pbc.

(**

Acabamos de caracterizar a lógica proposicional clássica como sendo a lógica proposicional intuicionista juntamente com a lei do terceiro excluído (ver Tabela %\ref{lp:regras:classica}%), mas será que poderíamos ter, por exemplo, caracterizado a lógica proposicional clássica como sendo a lógica proposicional intuicionista juntamente com a regra $\pbcsa$, e a partir daí construir uma prova para a lei do terceiro excluídos? Sim! Veja a seguir uma prova de $\lem$ utilizando as regras da lógica proposicional intuicionista e $\pbcsa$:

%\begin{mathpar}
 \inferrule*[Right={$\pbc{u}$}]{\inferrule*[Right={$\nege$}]{\inferrule*[Right={$\lori$}]{\inferrule*[Right={$\negi{v}$}]{\inferrule*[Right={$\nege$}]{[\varphi \lor \neg\varphi]^u \and \inferrule*[Right={$\lori$}]{[\varphi]^v}{\varphi \lor \neg\varphi}}{\bot}}{\neg\varphi}}{\varphi \lor \neg\varphi} \and [\varphi \lor \neg\varphi]^u}{\bot}}{\varphi \lor \neg\varphi}
\end{mathpar}%

As duas últimas provas nos mostram que as regras $\lem$ e $\pbcsa$ são equivalentes módulo a lógica proposicional intuicionista. Em outras palavras, podemos provar $\lem$ assumindo $\pbcsa$ e vice-versa, dadas as regras da lógica proposicional intuicionista. Como exercício, refaça a prova anterior no Coq.

*)

(** *** Exercícios *)

Section exercicio_pbc_to_lem.
  Hypothesis pbc: (~(p \/ ~p) -> False) -> p \/ ~p.
  Lemma lem: p \/ ~p.
  Proof.
    Admitted.
End exercicio_pbc_to_lem.

(**

Outras caracterizações para a lógica proposicional clássica também são possíveis. Por exemplo, a regra de eliminação da dupla negação também é equivalente a $\lem$ e $\pbcsa$. O mesmo vale para a lei de Peirce (LP) conforme sugerido nos exercícios a seguir:

%\begin{enumerate}
 \item $\neg\neg\varphi \vdash_{i+\pbcsa} \varphi$, i.e. prove $\nne$ utilizando a regra $\pbcsa$ juntamente com as regras da lógica proposicional intuicionista;
 \item $\neg\varphi \to \bot \vdash_{i+\nne} \varphi$, i.e. prove $\pbcsa$ utilizando a regra $\nne$ juntamente com as regras da lógica proposicional intuicionista;
 \item $\vdash_{i+\nne} ((\varphi \to \psi) \to \varphi) \to \varphi$, i.e. prove $\lp$ utilizando a regra $\nne$ juntamente com as regras da lógica proposicional intuicionista;
 \item $\vdash_{i+\pbcsa} ((\varphi \to \psi) \to \varphi) \to \varphi$, i.e. prove $\lp$ utilizando a regra $\pbcsa$ juntamente com as regras da lógica proposicional intuicionista;
 \item $\vdash_{i+\lem} ((\varphi \to \psi) \to \varphi) \to \varphi$, i.e. prove $\lp$ utilizando a regra $\lem$ juntamente com as regras da lógica proposicional intuicionista;
 \item $\vdash_{i+\lp} \varphi \lor \neg\varphi$, i.e. prove $\lem$ utilizando a regra $\lp$ juntamente com as regras da lógica proposicional intuicionista;
 \item $(\neg\varphi) \to \bot \vdash_{i+\lp} \varphi$, i.e. prove $\pbcsa$ utilizando a regra $\lp$ juntamente com as regras da lógica proposicional intuicionista;
 \item $\neg\neg\varphi \vdash_{i+\lp} \varphi$, i.e. prove $\nne$ utilizando a regra $\lp$ juntamente com as regras da lógica proposicional intuicionista;
\item Os exercícios propostos no itens anteriores são interessantes porque cada um estabelece um desafio diferente a ser provado, no entanto, não precisamos de tantas provas para estabelecer a equivalência entre as regras $\lem$, $\pbcsa$, $\nne$ e $\lp$. Qual é o número mínimo de provas necessárias para estabelecer esta equivalência? Justifique sua resposta e use o Coq para certificar sua resposta.
\item Prove que a regra da explosão $\bote$ pode ser derivada a partir das regras da lógica proposicional intuicionista juntamente com $\pbcsa$.
\end{enumerate}%

 *)

(** ** A semântica da lógica proposicional clássica%\index{lógica!proposicional!semântica}% *)

(**

Iniciamos nosso estudo dizendo que a lógica proposicional é baseada na noção de proposição, e que uma proposição é uma afirmação que pode ser qualificada como verdadeira ou falsa. Nesta seção veremos como atribuir valor de verdade a uma fórmula da lógica proposicional. Temos dois valores de verdade possíveis: verdadeiro (V) ou falso (F). Considerando novamente a gramática (%\ref{gram:lp}%) da lógica proposicional

%\begin{equation}
\varphi ::= p \mid \bot \mid (\neg \varphi) \mid (\varphi \land \varphi) \mid (\varphi \lor \varphi) \mid (\varphi \to \varphi)  
\end{equation}%
 
\noindent vamos detalhar a seguir como atribuir valor de verdade para as fórmulas considerando cada um dos construtores possíveis:

%\begin{enumerate}
 \item O primeiro construtor denota uma variável proposicional, que pode assumir qualquer um dos valores de verdade possível. Assim, para atribuir um valor de verdade específico para uma variável precisaremos de alguma informação adicional que nos permita concluir o seu valor de verdade;
 \item O segundo construtor é uma constante que denota o absurdo, que é utilizado para representar uma fórmula que tem valor de verdade falso (F);
 \item O terceiro construtor denota a negação, cuja semântica consiste em inverter o valor de verdade da fórmula recebida como argumento. Assim, se uma fórmula $\varphi$ é verdadeira (T) então sua negação é falsa (F), e vice-versa. Normalmente, representamos este fato via a seguinte tabela:
\[
 \begin{array}{|l|l|}\hline
 \varphi & \neg\varphi \\\hline
  V & F \\
  F & V \\\hline
 \end{array}
\]
\item O quarto construtor denota a conjunção, cuja semântica é apresentada na seguinte tabela:
\[
 \begin{array}{|l|l|l|}\hline
 \varphi & \psi & \varphi \land \psi \\\hline
  V & V & V \\
  V & F & F \\
  F & V & F \\
  F & F & F \\\hline
 \end{array}
\]
\item O quinto construtor denota a disjunção, cuja semântica é apresentada na seguinte tabela:
\[
 \begin{array}{|l|l|l|}\hline
 \varphi & \psi & \varphi \lor \psi \\\hline
  V & V & V \\
  V & F & V \\
  F & V & V \\
  F & F & F \\\hline
 \end{array}
\]
\item Por fim, o sexto construtor denota a implicação, cuja semântica é apresentada na seguinte tabela:
\[
 \begin{array}{|l|l|l|}\hline
 \varphi & \psi & \varphi \to \psi \\\hline
  V & V & V \\
  V & F & F \\
  F & V & V \\
  F & F & V \\\hline
 \end{array}
\]
O sentido usual (ou popular) da implicação assume implicitamente uma relação de causa e efeito, ou causa e consequência no sentido de que o antecedente $\varphi$ é o que gera o consequente $\psi$ como em "Se eu não beber água então ficarei desidratado". No entanto, o sentido da implicação na lógica proposicional é diferente pois tem como fundamento a {\it preservação da verdade}, que não necessariamente possui uma relação de causa e efeito. Por exemplo, a proposição {\it Se 2+2=4 então o dia tem 24 horas} é verdadeira, mas não existe relação causal entre a igualdade {\it 2+2=4} e o fato de o dia ter {\it 24} horas de duração.
\end{enumerate}%

Apesar da gramática (%\ref{gram:lp}%) não incluir a bi-implicação, este é um conectivo bastante utilizado. No entanto, podemos facilmente expressar a bi-implicação usando a implicação e conjunção. Ao construirmos a tabela verdade de uma fórmula qualquer, teremos três situações possíveis que originam a seguinte nomenclatura:

%\begin{enumerate}
\item {\bf Tautologia}: Fórmula que é sempre verdadeira, independentemente dos valores de verdade associados às suas variáveis;
\item {\bf Contradição}: Fórmula que é sempre falsa, independentemente dos valores de verdade associados às suas variáveis;
\item {\bf Contingência}: Fórmula que pode ser tanto verdadeira quanto falsa dependendo dos valores de verdade associados às suas variáveis.
\end{enumerate}%

As tautologias e as contradições são particularmente importantes, e possuem símbolos especiais para representá-las. Na gramática (%\ref{gram:lp}%) já vimos que a constante $\bot$ é o representante das contradições. As tautologias, por sua vez, podem ser representadas pelo símbolo $\top$.

Agora chegamos em um momento chave do nosso estudo. Considere um sequente arbitrário, digamos $\Gamma \vdash \varphi$, onde $\Gamma$ é um conjunto finito de fórmulas da lógica proposicional. Podemos então perguntar: é possível provar este sequente? Ou em outras palavras, qualquer sequente possui uma prova? A resposta certamente é não. Se tudo pudesse ser provado então não teríamos razão para estudar a lógica proposicional. Como então é possível separar os sequentes que têm prova dos que não têm prova? Para responder a esta pergunta precisamos inicialmente compreender a noção de {\it consequência lógica}%\index{consequência lógica}%. Dizemos que uma fórmula $\varphi$ é consequência lógica da fórmula $\psi$, notação $\psi \models \varphi$, se $\varphi$ for verdadeira sempre que $\psi$ for verdadeira. Este conceito pode ser facilmente estendido para um conjunto $\Gamma$ de fórmulas, de forma que $\Gamma \models \varphi$, isto é, $\varphi$ é consequência lógica do conjunto $\Gamma$ se $\varphi$ for verdadeira sempre que as fórmulas em $\Gamma$ forem verdadeiras. Agora podemos enunciar dois teoremas importantes que nos permitirão responder à questão anterior:

%\begin{teorema}[Correção da LP]
 Sejam $\Gamma$ um conjunto, e $\varphi$ uma fórmula da lógica proposicional. Se $\Gamma \vdash \varphi$ então $\Gamma \models \varphi$.
\end{teorema}%

A prova deste teorema é por indução em $\Gamma \vdash \varphi$. Não detalharemos aqui esta prova, que pode ser encontrada por exemplo em %\cite{ayala-rinconAppliedLogicComputer2017}%.

%\begin{teorema}[Completude da LP]
 Sejam $\Gamma$ um conjunto, e $\varphi$ uma fórmula da lógica proposicional. Se $\Gamma \models \varphi$ então $\Gamma \vdash \varphi$.
\end{teorema}%

A prova do teorema de completude da LP é um pouco mais complexa do que a prova de correção, e também pode ser encontrada em %\cite{ayala-rinconAppliedLogicComputer2017}%. Note que este lema responde a nossa pergunta anterior: um sequente tem prova exatamente quando seu consequente for consequência lógica do seu antecedente.

A lógica proposicional nos permite resolver diversos problemas interessantes, e constitui a base de tudo o que faremos nos próximos capítulos. Apesar de muito importante como ponto de partida no estudo que estamos fazendo, a lógica proposicional possui limitações importantes, como a impossibilidade de quantificar de forma explícita sobre elementos de um conjunto. Por exemplo, podemos representar a sentença %{\it Todo mundo gosta de Matemática}% na lógica proposicional via uma variável, mas esta representação não expressa a quantificação universal %{\it Todo mundo}% de forma explícita. O mesmo vale para uma sentença da forma %{\it Existe um número natural que não é primo}%. O próprio princípio da indução, tão importante em Matemática e Computação, precisa de uma linguagem mais expressiva do que a proposicional. A lógica que nos permitirá expressar este tipo de quantificação (tanto existencial quanto universal) é conhecida como %{\it Lógica de Primeira Ordem}% (LPO)%\index{lógica!de primeira ordem}%, ou %{\it Lógica de Predicados}\index{lógica!de predicados}% que estudaremos no próximo capítulo.

*)

(** *** Exercícios *)

(**

TBD

*)
