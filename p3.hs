Seguindo o enunciado aplica-se a lei de Fokkinga às funções \textit{f k} e \textit{l k}.
\begin{eqnarray*}
\start
| (split (f k) (l k)) |
%
\just\equiv{ Fokkinga }
%
    |lcbr(
      (f k) . in = h . (id + (split (f k) (l k)))
    )(
      (l k) . in = y . (id + (split (f k) (l k)))
)|
%
\just\equiv{ Def+ }
%
    |lcbr(
          (f k) . in = h . (either (i1 . id) (i2 . (split (f k) (l k))))
    )(
          (l k) . in = y . (either (i1 . id) (i2 . (split (f k) (l k))))
    )|
%
\just\equiv{ Fusão+, Natural-id }
%
    |lcbr(
          (f k) . in = (either (h . i1) (h . i2 . ((split (f k) (l k)))))
    )(
          (l n) . in = (either (y . i1) (y . i2 . ((split (f k) (l k)))))
    )|
%
\just\equiv{ inNats, Eq+ }
%
    |lcbr(
          (f k) . (const 0) = h . i1
    )(
          (f k) . succ = h . i2 . (split (f k) (l k))
    )|
    |lcbr(
          (l k) . (const 0) = y . i1
    )(
          (l k) . succ = y . i2 . (split (f k) (l k))
    )|
%
\just\equiv{ Cancelamento+, |h = (either h1 h2)|, |k = (either k1 k2)| }
%
    |lcbr(
          (f k) . (const 0) = h1
    )(
          (f k) . succ = h2 . (split (f k) (l k))
    )|
    |lcbr(
          (l k) . (const 0) = y1
    )(
          (l k) . succ = y2 . (split (f k) (l k))
    )|

\qed
\end{eqnarray*}


Derivando \textit{h}:
\begin{eqnarray*}
\start
%
|lcbr ((f k) . (const 0) = h1) ((f k) . succ = h2 . (split (f k) (l k)))|
%
\just\equiv{Como são precedidas por uma injeção}
%
|lcbr( (f k) . (const 0) = (either h1 h2) . i1
)(
(f k) . succ = (either h1 h2) . i2 . (split (f k) (l k))
)|
%
\just\equiv{Comparando com a função do enunciado}
%
|h = (either (const 1) (uncurry (*)))|
%
\qed
\end{eqnarray*}

Derivando \textit{y}:
\begin{eqnarray*}
\start
%
|lcbr(
    (l k) . (const 0) = y1
)(
    (l k) . succ = y2 . (split (f k) (l k))
)|
%
\just\equiv{Como são precedidas por uma injeção}
%
|lcbr(
  (l k) . (const 0) = (either y1 y2) . i1
)(
  (l k) . succ = (either y1 y2) . i2 . (split (f k) (l k))
)|
%
\just\equiv{Comparando com a função do enunciado}
%
|y = (either (succ.(const k)) (succ.p2))|
\qed
\end{eqnarray*}

Conclui-se que:
\begin{eqnarray*}
|split (f k) (l k) = cataNat (split (either (const 1) (uncurry (*))) (either (succ.(const k)) (succ.p2)))|
\qed
\end{eqnarray*}


Aplicando a lei de Fokkinga às funções \textit{g} e \textit{s}.
\begin{eqnarray*}
\start
| (split (g) (s)) |
%
\just\equiv{ Fokkinga }
%
    |lcbr(
      g . in = m . (id + (split g s))
    )(
      s . in = j . (id + (split g s))
)|
%
\just\equiv{ Def+ }
%
    |lcbr(
          g . in = m . (either (i1 . id) (i2 . (split g s)))
    )(
          s . in = j . (either (i1 . id) (i2 . (split g s )))
    )|
%
\just\equiv{ Fusão+, Natural-id }
%
    |lcbr(
          g . in = (either (m . i1) (m . i2 . ((split g s )))
    )(
          s . in = (either (j . i1) (j . i2 . ((split g s)))
    )|
%
\just\equiv{ inNats, Eq+ }
%
    |lcbr(
          g . (const 0) = m . i1
    )(
          g  . succ = m . i2 . (split g s)
    )|
    |lcbr(
          s . (const 0) = j . i1
    )(
          s . succ = j . i2 . (split (f k) (l k))
    )|
%
\just\equiv{ Cancelamento+, |m = (either m1 m2)|, |j = (either j1 j2)| }
%
    |lcbr(
          g . (const 0) = m1
    )(
          g . succ = m2 . (split g s)
    )|
    |lcbr(
          s . (const 0) = j1
    )(
          s . succ = j2 . (split g s)
    )|

\qed
\end{eqnarray*}


Derivando \textit{m}:
\begin{eqnarray*}
\start
%
|lcbr (g . (const 0) = m1) (g . succ = m2 . (split g s))|
%
\just\equiv{Como são precedidas por uma injeção}
%
|lcbr( g . (const 0) = (either m1 m2) . i1
)(
        g . succ = (either m1 m2) . i2 . (split g s )
)|
%
\just\equiv{Comparando com a função do enunciado}
%
|m = (either (const 1) (uncurry (*)))|
%
\qed
\end{eqnarray*}

Derivando \textit{j}:
\begin{eqnarray*}
\start
%
|lcbr(
    s . (const 0) = j1
)(
    s . succ = j2 . (split g s)
)|
%
\just\equiv{Como são precedidas por uma injeção}
%
|lcbr(
   s . (const 0) = (either j1 j2) . i1
)(
   s . succ = (either j1 j2) . i2 . (split g s)
)|
%
\just\equiv{Comparando com a função do enunciado}
%
|j = (either (const 1) (succ.p2))|
\qed
\end{eqnarray*}

Conclui-se que:
\begin{eqnarray*}
|split g s = cataNat (split (either (const 1) (uncurry (*))) (either (const 1) (succ.p2)))|
\qed
\end{eqnarray*}

Aplicando a Lei de \textit{Banana split}
\begin{eqnarray*}
\start
|cataNat ( ((split (either (const 1) (uncurry (*))) (either (succ.(const k)) (succ.p2))) *  (split (either (const 1) (uncurry (*))) (either (const 1) (succ.p2))))
  .  (split (id + p1) (id + p2)) )|
%
\just\equiv{Absorção*, Fusão*, Absorção+, Natural-Id}
|cataNat (split (split (either (const 1) ((uncurry (*)).p1)) (either (succ.(const k)) (succ.p2.p1)))  (split (either (const 1) ((uncurry (*)).p2))  (either (const 1) (succ.p2.p2))))|
%
\just\equiv{Lei da troca (x2)}
|cataNat (either (split (split (const 1) (succ.(const k))) (split (const 1) (const 1)))  (split (split ((uncurry (*)).p1) (succ.p2.p1)) (split (split ((uncurry (*)).p2)) (succ.p2.p2)))  )|
\qed
\end{eqnarray*}

Sabemos pela definição de um ciclo for que:
\begin{eqnarray*}
\start
%
\just\equiv{|for b i = cataNat (either (const i) b)|}
%
|lcbr(
   i = (split (split (const 1) (succ.(const k))) (split (const 1) (const 1)))
)(
   b = (split (split ((uncurry (*)).p1) (succ.p2.p1)) (split (split ((uncurry (*)).p2)) (succ.p2.p2)))
)|
\just\equiv{|i k  =  (1, succ k, 1, 1)| }
\qed
\end{eqnarray*}

\begin{code}
base k = (1, succ k, 1, 1)
loop = uncurr . (split (split (mul.p1) (succ.p2.p1)) (split (mul.p2) (succ.p2.p2))) . curr
uncurr = (\((a,b),(c,d)) -> (a,b,c,d))
curr = (\(a,b,c,d) -> ((a,b),(c,d)))
\end{code}
