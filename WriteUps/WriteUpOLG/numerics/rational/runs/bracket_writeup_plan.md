# Finishing the gamma=3 bracket write-up (resumable procedure)

Run: `derivcert.py 3 0.04 0.06 200 1 fixed` (fine grid, mu 1, lambda 2), results one line per cell in
`runs/bracket_g3_4to6.txt`, log `runs/bracket_g3_4to6.log`, ends with the line
`ALL CELLS CERTIFIED: E' > 0 on the bracket` (or `NOT all cells certified: [...]`).
Resume after any interruption: rerun the same command (finished cells are skipped); watchdog
`runs/keepalive_bracket.sh` does this if its crontab line is in place.

## When the run has ended
1. `python3 runs/bracket_summary.py runs/bracket_g3_4to6.txt 0.04 0.06` → leaves, splits, worst B_d,
   smallest |D'|, worst ratio and its cell, COVERED/NOT covered. Total time: sum the per-cell seconds
   in the log or take wall clock from first to last result.
2. `sections/increment.tex`, paragraph "From rates to a bracket": replace the sentences from
   "Each cell costs half an hour" to "proof terms for every step but the arithmetic." with the text
   below, filling @@...@@.
3. `sections/programme.tex`: replace "and the run over the whole of $[4\%,6\%]$ --- two hundred cells,
   about a day --- was started as this was written." with "and over the whole of $[4\%,6\%]$ every one
   of the @@N@@ cells certifies, with the bound at most @@RATIO@@ of the demand slope: $E'>0$ on the
   bracket, hence at most one equilibrium rate there, at $\gamma=3$ by certificate."
4. `sections/intro.tex`: in the sentence "a rigorous enclosure of the two policies in its place
   certifies ..." add the bracket result (see the end of that sentence first).
5. No appendix_index row (no Lean names). Build: `cd WriteUps/WriteUpOLG && make` (latexmk); check page
   count and that the new theorem environment compiles (`theorem*` may not exist: use
   `\begin{theorem}[...]\label{thm:bracket}`).
6. Commit: increment/programme/intro .tex, `git add -f` runs/bracket_g3_4to6.txt and .log,
   runs/bracket_summary.py, runs/keepalive_bracket.sh, this file. Never push.
7. Memory: olg-programme.md status line + MEMORY.md OLG row: "E'>0 CERTIFIED on [4%,6%] at gamma=3".
8. If some leaf did NOT certify: report the cell(s), keep the honest statement (E'>0 on the certified
   union; the gap cells need narrower splits below ENCL_MINWIDTH or a transported bound).

## Text for increment.tex (fill @@N@@ cells, @@S@@ splits, @@BD@@, @@DP@@, @@RATIO@@, @@HOURS@@)

Each cell costs about an hour on the fine grid (the midpoint enclosure, its derivative pass and the
cell's), so $[4\%,6\%]$ was run as two hundred cells of $0.01$ points on seven cores, split
automatically where they fail (\texttt{derivcert.py}, mode \texttt{fixed}; the run is resumable and
its results are one line per cell in \texttt{runs/bracket\_g3\_4to6.txt}). It took @@HOURS@@ hours.
@@SPLITSENTENCE@@ The largest certified bound on the fall of supply over any cell is $@@BD@@$, against a
demand slope of at least $@@DP@@$ in magnitude; the worst ratio, $@@RATIO@@$, sits at the top of the
bracket where demand is flattest.

\begin{theorem}[$E'>0$ on the bracket, by certificate]\label{thm:bracket}
At $\gamma=3$ and the calibration of Section~\ref{sec:enclcert}, on every cell of a partition of
$[4\%,6\%]$ into @@N@@ cells the certified bound $B_d$ on $-S'$ is strictly below $|D'|$. Hence
excess demand is strictly increasing on $[4\%,6\%]$ and the model has at most one equilibrium
interest rate in that bracket.
\end{theorem}

Its standing is one step below Theorem~\ref{thm:encllean}. The interval Euler step, monotone saving,
the propensity floor and the envelope are proof terms; the derivative form of the increment and the
continuation argument that discharges the frozen transport are paper arguments of this section; and the
arithmetic is exact rational arithmetic in Python, not yet replayed in Lean. Replaying it is the same
shape as Section~\ref{sec:enclcert}: a checker over naturals, one \texttt{native\_decide}, and a bridge
from the checker's inequalities to the theorems behind them. Combined with Theorem~\ref{thm:finite}
the weaker conclusion, finitely many equilibria, needs only that supply is piecewise analytic in the
rate, which the theorem on the bracket makes moot: strict monotonicity of $E$ gives uniqueness
directly.

@@SPLITSENTENCE@@ = "No cell needed splitting: every cell certified at its first width." or
"@@S@@ cells failed at the first width and certified after one halving."
