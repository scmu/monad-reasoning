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
\begin{document}


%% Title information
\title{Reasoning and Derivation of Monadic Programs}
\titlerunning{Deriving Monadic Programs}
\subtitle{A Case Study of Non-determinism and State}

\institute{Institute of Information Science, Academia Sinica, Taiwan, \email{scm@@iis.sinica.edu.tw}
    \and Department of Computer Science, KU Leuven, Belgium, \email{first.last@@cs.kuleuven.be}
    }
\author{Shin-Cheng Mu \inst{1} \and Tom Schrijvers \inst{2} \and Koen Pauwels \inst{2}}

\begin{abstract}
Equational reasoning is among the most important tools that functional programming provides us. Curiously, relatively less attention has been paid to reasoning about monadic programs. In this pearl we aim to develop theorems and patterns useful for the derivation of monadic programs, focusing on the intricate interaction between state and non-determinism. We derive a backtracking algorithm for the $n$-queens puzzle when each non-deterministic branch has its own local state. For the scenario where a global state is shared, we propose laws the monad should satisfy, and develop programming patterns and techniques to simulate local states.
\end{abstract}

\keywords{monads \and effects \and program derivation \and equational reasoning \and nondeterminism \and state}


\maketitle

%include sections/Intro.lhs
%include sections/Monads.lhs
%include sections/Queens.lhs
%include sections/MonadicScanL.lhs
%include sections/StateLocal.lhs
%include sections/NondetGlobal.lhs
%include sections/LawTranslate.lhs
%include sections/Conclusion.lhs


%% Bibliography
\bibliographystyle{splncs04}
\bibliography{bib}
%\input{der-monad.bbl}

%% Appendix
\appendix
%include sections/GSMonad.lhs

%Text of appendix \ldots

\end{document}
