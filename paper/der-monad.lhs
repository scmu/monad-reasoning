%% For double-blind review submission
\documentclass[acmlarge,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
%\documentclass[acmlarge,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission
%\documentclass[acmlarge]{acmart}\settopmatter{}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage{amsmath}
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

% %% Some recommended packages.
% \usepackage{booktabs}   %% For formal tables:
%                         %% http://ctan.org/pkg/booktabs
% \usepackage{subcaption} %% For complex figures with subfigures/subcaptions
%                         %% http://ctan.org/pkg/subcaption

\usepackage{doubleequals}


%\input{Preamble}

\setlength{\mathindent}{15pt}

\newcommand{\todo}[1]{{\bf [To do: #1]}}
\newcommand{\delete}[1]{}

% \makeatletter\if@ACM@journal\makeatother
% %% Journal information (used by PACMPL format)
% %% Supplied to authors by publisher for camera-ready submission
% \acmJournal{PACMPL}
% \acmVolume{1}
% \acmNumber{1}
% \acmArticle{1}
% \acmYear{2017}
% \acmMonth{1}
% \acmDOI{10.1145/nnnnnnn.nnnnnnn}
% \startPage{1}
% \else
\makeatother
%% Conference information (used by SIGPLAN proceedings format)
%% Supplied to authors by publisher for camera-ready submission
\acmConference[ICFP'18]{ACM SIGPLAN International Conference on Functional Programming}{September 23--29, 2018}{St. Louis, Missouri, United States}
\acmYear{2018}
\acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}
% \fi


%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission
\setcopyright{none}             %% For review submission
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear


%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations


\allowdisplaybreaks

\begin{document}


%% Title information
\title[Deriving Monadic Programs]%
{Functional Pearl: Reasoning and Derivation of Monadic Programs}
%% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
%\titlenote{with title note}             %% \titlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'
\subtitle{A Case Study of Non-determinism and States}
%% \subtitle is optional
%\subtitlenote{with subtitle note}       %% \subtitlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Shin-Cheng Mu}
%\authornote{with author1 note}          %% \authornote is optional;
                                        %% can be repeated if necessary
%\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
%  \position{Position1}
  \department{Institute of Information Science}              %% \department is recommended
  \institution{Academia Sinica}            %% \institution is required
%  \streetaddress{Street1 Address1}
%  \city{City1}
%  \state{State1}
%  \postcode{Post-Code1}
  \country{Taiwan}
}
%\email{scm@iis.sinica.edu.tw}          %% \email is recommended

\begin{abstract}
Equational reasoning is among the most important tools that functional programming provides us. Curiously, relatively less attention has been paid to reasoning about monadic programs. In this pearl we aim to develop theorems and patterns useful for the derivation of monadic programs, focusing on the intricate interaction between state and non-determinism, and derive two backtracking algorithms, respectively using local and global states, to solve the $n$-queens and Sudoku puzzles.
\end{abstract}

%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10003752.10010124.10010138</concept_id>
<concept_desc>Theory of computation~Program reasoning</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Theory of computation~Program reasoning}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{monad, effects, program derivation, equational reasoning}  %% \keywords is optional


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

%include sections/Intro.lhs
%include sections/Monads.lhs
%include sections/Queens.lhs
%include sections/MonadicScanL.lhs
%include sections/StateLocal.lhs
%include sections/NondetGlobal.lhs
%%include sections/BacktrackGlobal.lhs
%include sections/Conclusion.lhs


%% Bibliography
%\bibliographystyle{jfp}
\bibliography{bib}
%\input{der-monad.bbl}

%% Appendix
%\appendix
%\section{Appendix}

%Text of appendix \ldots

\end{document}
