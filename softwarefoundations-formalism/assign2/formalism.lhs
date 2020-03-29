\documentclass{article}
\usepackage{minted}
\usepackage{amsmath}
\usepackage{amssymb}
\newcommand{\N}{\ensuremath{\mathbb{N}}}
\renewcommand{\choose}{\texttt{choose}}
\newcommand{\sort}{\texttt{sort}}
\newcommand{\matroid}{\texttt{matroid}}
\newcommand{\bool}{\texttt{bool}}
\newcommand{\true}{\texttt{true}}
\newcommand{\false}{\texttt{false}}
\newcommand{\next}{\texttt{next!}}
\begin{document}
\section{Matroids}

A matroid is a general mathematical object, that was originally axiomatized
to provide an abstraction for \emph{greedy algorithms}. Here, we present
the axiomatization and propose a transition system which models the algorithm
for solving problems with greedy solutions.


We first define a matroid: a matroid over a set $S$ is a set of subsets $I$
of $S$ such that:

\begin{itemize}
    \item [1.] \emph{Non-degenerate}: The empty set is a member of $I$
    \item [2.] \emph{Downward closed}: For any set $S \in I$, all subsets of $S$ are in $I$.
    \item [3.] \emph{Exchange}: For any two sets $A, B \in I$ such that $|A| < |B|$,
              there exists an element $e \in B$, $e \not \in A$ (e for \emph{extend})
              such that $A \cup \{ e \} \in I$.
\end{itemize}

We presume there exists a \emph{weight function} $w: S \rightarrow \N$. We extend
this weight function to work on subsets by evaluating the sum of the
individual elements:
\begin{align*}
 w: 2^S \rightarrow \N ; \quad w(ss) = \sum_{s \in ss} w(s).
\end{align*}

Now, the \emph{greedy algorithm for matroids} allows us to solve the following
question: For a matroid $M \equiv (S, I)$ and weight function $w: S \rightarrow \N$,
produce the set:

$$i^\star \equiv \arg \max_{i \in I} w(i).$$

The algorithm is a typical greedy algorithm:

\begin{minted}{py}
def solve_greedy(S, I, w):
  istar = [] # start with empty set
  Ssorted = sort(S, key=lambda i:w(i)) # sort in descending order of weight.
  # greedily pick 'x' as long as it remains independent
  for s in Ssorted: if (istar + [s]) in I: istar.append(s)
  return istar
\end{minted}

We show how to implement the above algorithm as a transition system.

\section{Transition systems}

A transition system is a 5-tuple $(X, X_0, U, \rightarrow, Y, H)$ where:
\begin{itemize}
    \item[1.] $X$ is the state space
    \item[2.] $X_0 \subseteq X$ is the set of potential initial states
    \item[3.] $U$ is the set of inputs to the system
    \item[4.] $\rightarrow: X \times U \rightarrow 2^X$ is a non-deterministic transition relation
    \item[5.] $Y$ is the output space
    \item[6.] $H: X \rightarrow Y$ is the projection / view from the state to the output space.
\end{itemize}


\section{Matroids as a transition system}
We assume that we are given a matroid $M \equiv (S, I)$ and we are attempting
to build a transition system that models the algorithm \texttt{solve\_greedy}
as outlined above.

Clearly, in our problem, we have two transition systems that need to be
composed together: 

\begin{itemize}
\item[1.] \emph{\sort}: Produces the element $a_i$: the $i$th element of the list of elements of $S$ ordered in descending order by $w$.
\item[2.] \emph{\choose}: Decides whether element $a_i$ belongs to $i^\star$.
\end{itemize}

\subsection{\sort ~ as a transition system}

We assume that we already know how to perform sorting as a transition system,
since this has been covered in class. We can use the bubble-sort encoding
of the transition system.

\subsection{\choose ~as a transition system}

\begin{itemize}
\item[1.] The state space is the possible states of $i^\star$,  which is 
          subsets of $S$: $X \equiv 2^S$.
\item [2.] The initial state starts with $i^\star$ as empty: $X_0 \equiv \emptyset$.
\item [3.] The set of inputs to the system are the elements of $S$: $U \equiv S$. 
           This models the current $s \in S$ we are attempting to add into $i^\star$.
\item [4.] The transition relation decides to add $s \in S$ based on whether
           $i^\star \cup \{ s \}  \overset{?}{\in} I$:
           \begin{align*}
           &\rightarrow: X \times U \rightarrow X \quad \rightarrow: 2^S \times S \rightarrow 2^S \\
           &i^\star \xrightarrow{s}
           \begin{cases}
            i^\star \cup \{ s \} & i^\star \cup \{ s\} \in I \\
            i^\star & \text{otherwise}
           \end{cases}
           \end{align*}
\item [5.] The output space is the state as the state space: $ Y \equiv X = 2^S$
\item [6.] The projection function is the identity: $H: X \rightarrow Y; H(i) = i$
\end{itemize}

\subsection{Composition of transition systems: $\matroid \equiv \sort \rtimes \choose$}

Note that we need an adaptor between \sort~ and \choose~: one that feeds
the output list of \sort~ as a sequence of inputs to \choose. We can define
this combined system, \matroid, as a \emph{composition} of transition systems. 
We assume that the output space of $\sort$ is the sequence of sorted elements.
We also assume that we have a predicate $sorted?: X(\sort) \rightarrow \bool$,
which on being fed a state of $\sort$ tells us if it is sorted or not. We assume
that the transition space of $\sort$ is a single word $U(\sort) \equiv \{ \next \}$,
which moves the sorting algorithm forward.


\begin{itemize}
\item [1.] $X \equiv X(\sort) \cup (X(\sort) \times \N \times X(\choose))$. We are either sorting,
          or we are choosing the $i$th element of the sorted list.
\item [2.] $X_0 \equiv X_0(\sort)$. We start from the sorting algorithm.
\item [3.] $U \equiv \{ \next \}$. The algorithm is fully driven: the sorting
  algorithm was already driven by \next. We plug the \sort~automata with the
  \choose~automata to make \choose~automatically driven as well.
\item [4.] The transition relation uses \next~when we are still sorting.
           Once we are done sorting, it feeds the sorted list element-by-element
           to its \choose~state.
           \begin{align*}
           &arr \xrightarrow{\next}
           \begin{cases}
           arr' & arr \xrightarrow{\next} arr' \in \sort \\
           (arr, 0, X_0(\choose)=\emptyset) & sorted?(arr) = \true
           \end{cases} \\
           &((arr, ix, i^\star)) \xrightarrow{\next} (arr, ix+1, i'^\star);  \quad i^\star \xrightarrow{arr[ix]} i'^\star \in \choose
           \end{align*}

\item [5.]  $Y \equiv Y(\choose) = 2^S$.  The output space is the output of the
 \choose~automata since it is the final independent set we are interested in.
\item [6.] The projection returns the empty set if we are still
  sorting. If we are done sorting, it returns the current independent
  set.
  $$H(x) \equiv \begin{cases}
                i^\star & x = (\_, \_, i^\star) \\
                \emptyset & \text{otherwise}
                \end{cases}$$
           
\end{itemize}

\section{A discussion of alternate designs}
note that we don't, in fact, need the fully sorted list. Rather, what we
really want is the \emph{sequence} of elements of $S$ ordered by $w$. It
is possible to consider other \emph{streaming} combinators that combine
two automata in a streaming fashion, where we do not hold the entire
state in memory.

In contrast, the current implementation is a \emph{buffered} implementation,
where we buffer the sorted array into memory and then operate on it
to build the matroid. It would be interesting to formally implement and compare
these systems to each other.
\end{document}
