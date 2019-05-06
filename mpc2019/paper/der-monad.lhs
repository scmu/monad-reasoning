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
\title{Reasoning and Derivation of Monadic Programs}
\titlerunning{Deriving Monadic Programs}
\subtitle{A Case Study of Non-determinism and State}

\institute{Institute of Information Science, Academia Sinica, Taiwan, \email{scm@@iis.sinica.edu.tw}
    \and Department of Computer Science, KU Leuven, Belgium, \email{first.last@@cs.kuleuven.be}
    }
\author{Shin-Cheng Mu \inst{1} \and Tom Schrijvers \inst{2} \and Koen Pauwels \inst{2}}

\maketitle

\begin{abstract}
Equational reasoning is one of the most important tools of functional
programming. Yet, while monadic programs are ubiquitous, relatively little
attention has been paid to reasoning about them. To help address this
situation, we develop new theorems and patterns for the derivation of monadic
programs. We focus specifically on the intricate interaction between state and
non-determinism. 

We first derive a backtracking algorithm for the $n$-queens puzzle where each
non-deterministic branch has its own local state. Then we show how to simulate
local state in terms of a global state shared by all branches. We
propose laws that global state should satisfy along with a model that satisfies
them. Finally, we formally prove the simulation correct using a novel
combination of free monads and contextual equivalence.
\end{abstract}

\keywords{monads \and effects \and program derivation \and equational reasoning \and nondeterminism \and state}



%include sections/Intro.lhs
%include sections/Background.lhs
%include sections/NondetGlobal.lhs
%include sections/LawTranslate.lhs
%include sections/Conclusion.lhs


%% Bibliography
\bibliographystyle{splncs04}
\bibliography{bib}
%\input{der-monad.bbl}


\end{document}
