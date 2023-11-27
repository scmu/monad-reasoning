%if False
\begin{code}
module BenchmarkTable where
\end{code}
%endif

% \begin{figure}[h]

% The benchmarks are run using GHC 8.10.4 and clang 12.0.5 with |-O2| optimization option turn on.
% on a MacBook Pro with a 2.3 GHz Intel Core i5 processor and 16 GB RAM.


\begin{table}[]
\begin{tabular}{l||lllll}
Benchmark      & n=10  & n=11 & n=12  &  &  \\
\hline
|queensMT|     & 0.059 & 0.39 & 2.17  &  &  \\
|queensLocal|  & 0.059 & 0.38 & 2.15  &  &  \\
|queensModify| & 0.144 & 0.78 & 4.67  &  &  \\
|queensStateR| & 0.133 & 0.78 & 8.63  &  &  \\
|queensStackR| & 0.207 & 1.21 & 11.23 &  &
\end{tabular}
\caption{Results of free monad implementation (using fusion).}
\label{tbl:benchmarks-haskell}
\end{table}

% \end{figure}

% \begin{figure}[h]

\begin{table}[]
\begin{tabular}{l||lllll}
Benchmark      & n=10 & n=11 & n=12  &  &  \\
\hline
|queensLocal|  & 1.27 & 7.87 & 55.00 &  &  \\
|queensGlobal| & 1.19 & 7.61 & 52.60 &  &  \\
|queensModify| & 1.14 & 7.26 & 51.02 &  &  \\
|queensState|  & 1.33 & 8.20 & 55.29 &  &  \\
|queensStateR| & 1.29 & 7.93 & 53.31 &  &  \\
|queensStackR| & 1.14 & 7.22 & 48.92 &  &
\end{tabular}
\caption{Results of C++ implementation.}
\label{tbl:benchmarks-c++}
\end{table}

% \end{figure}
