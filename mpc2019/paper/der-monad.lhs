\documentclass{llncs}

% build using
%    lhs2TeX der-monad.lhs | pdflatex --jobname=der-monad

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage{amsfonts}
\usepackage{stmaryrd}
%\usepackage{mathptmx}
%\usepackage{amsthm}
\usepackage{hyperref}
\usepackage{scalerel}
\usepackage{bussproofs}
\EnableBpAbbreviations
\usepackage{url}
\usepackage{subfig}
\usepackage{enumitem}
\usepackage{mdframed}
\usepackage{multicol}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{mathtools}

\usepackage{doubleequals}


%\input{Preamble}

\setlength{\mathindent}{15pt}

\newcommand{\todo}[1]{{\bf [To do: #1]}}
\newcommand{\delete}[1]{}

\allowdisplaybreaks

\newcommand{\scm}[1]{\textcolor{teal}{#1}}
\newcommand{\koen}[1]{\textcolor{blue}{#1}}
\newcommand{\tom}[1]{\textcolor{red}{#1}}
\begin{document}


%% Title information
\title{Handling Local State with Global State}
\titlerunning{Handling Local State with Global State}

\institute{%
Department of Computer Science, KU Leuven, Belgium, \email{first.last@@cs.kuleuven.be}
\and
Institute of Information Science, Academia Sinica, Taiwan, \email{scm@@iis.sinica.edu.tw}
}%instutite
\author{Koen Pauwels \inst{1} \and Tom Schrijvers \inst{1} \and Shin-Cheng Mu \inst{2}}

\maketitle

\begin{abstract}
Equational reasoning is one of the most important tools of functional
programming.
To facilitate its application to monadic programs, Gibbons and Hinze have
proposed a simple axiomatic approach using laws that characterise the
computational effects without exposing their implementation details.  At the
same time Plotkin and Pretnar have proposed algebraic effects and handlers, a
mechanism of layered abstractions by which effects can be implemented in terms of
other effects.

This paper performs a case study that connects these two strands of research.
We consider two ways in which the nondeterminism and state effects can
interact: the high-level semantics where every nondeterministic branch has a
local copy of the state, and the low-level semantics where a single sequentially threaded  state is
global to all branches.

We give a monadic account of the folklore technique of handling local state in
terms of global state, provide a novel axiomatic characterisation of global
state and prove that the handler satisfies Gibbons and Hinze's local state
axioms by means of a novel combination of free monads and contextual
equivalence. We also provide a model for global state that is necessarily
non-monadic.
\end{abstract}

\keywords{monads \and effect handlers \and equational reasoning \and nondeterminism \and state \and contextual equivalence}



%include sections/Intro.lhs
%include sections/Background.lhs
%include sections/Motivation.lhs
%include sections/NondetGlobal.lhs
%include sections/Fold.lhs
%include sections/LawTranslate.lhs
%include sections/Conclusion.lhs
\appendix
%include sections/Ap-LocalState.lhs


%% Bibliography
\bibliographystyle{splncs04}
\bibliography{bib}
%\input{der-monad.bbl}


\end{document}
