# Short recovery handoff

Ignore older handoffs saying no example was known.  The counterexample is
over the residue-\(\mathbf F_2\) length-\(10\) ring
\[
R=(\mathbf Z/4)[x,y,z,d]/(2x,2y,2d,x^2-2,z^2-2,y^2,yz,zd,d^2-xd,yd-xz-xy).
\]
Put \(\xi=xz,\eta=xd,\omega=xy,\sigma=2z\ne0\), and
\(q=x(y+z)\).  Let \(A=R\{1,e_1,e_2,e_3\}\), with
\[
\begin{gathered}
e_1^2=xe_1+ye_2,\ e_1e_2=e_3,\ e_1e_3=xe_3,\\
e_2^2=ze_2,\ e_2e_3=ze_3,\ e_3^2=\xi e_3.
\end{gathered}
\]
Copy the coproduct and antipode exactly from
**notes/RANK4_LENGTH10_COUNTEREXAMPLE_AND_CONCEPTUAL_EXPLANATION_2026-07-10.tex**,
labels **eq:Delta1–eq:Delta3** and **eq:antipode**.  They define a finite
locally free rank-\(4\) group \(G=\operatorname{Spec}A\), and contraction gives
\[
[2]^\#(e_1)=\omega e_2+(y+z+\sigma)e_3,\quad
[2]^\#(e_2)=de_3,\quad [4]^\#(e_1)=\omega d\,e_3=\sigma e_3\ne0,\quad [8]=e.
\]
Verify with **scripts/verify_rank4_length10_counterexample_20260710.py**,
**scripts/audit_rank4_descriptions_20260710.py**, and
**scripts/audit_rank4_subgroups_deformations_20260711.py**.

The human explanation is the square-zero tower
\(R_8=R/(\eta,\sigma)\twoheadrightarrow R_6=R/(d)\): over \(R_6\), \(G\)
is a normal rank-\(2\)-by-rank-\(2\) extension; over \(R_8\), normality is
broken but \([4]=e\); the final lift turns on \(\sigma\) and makes
\([4]^\#(e_1)\ne0\).  The master TeX and PDF have the same stem shown
above.  Do not claim global minimality: length \(10\) is only
solver-conditionally minimal inside the audited cubic chart.
