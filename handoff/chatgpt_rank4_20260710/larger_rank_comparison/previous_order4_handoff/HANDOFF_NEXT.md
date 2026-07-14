# Continuation handoff: Grothendieck's question, order 4

> **SESSION-13 BANNER (2026-07-09, ~12:00) — supersedes everything below.**
> Read `scripts/JOBS.md` FIRST after any crash: it + `scripts/relaunch_all.sh`
> are the one-command recovery path (`./relaunch_all.sh`, idempotent; `--dry`
> to preview). Headlines this session:
> 1. **THEOREM M($t^4$) BANKED** (`THEORY` §14.9, hybrid rule (c)):
>    `s4t4gen` deg-5 certified the last scalar $\Lambda + bB^2$ (+
>    $\Lambda C$, $D_4[3,2]$); with the audited 12.6.6(e) assembly all nine
>    $D_4$ components follow at arbitrary-$k'$ strength ⟹ **curvilinear
>    equal-char CLOSED AT DEPTH 4** (S′ over $k'[\epsilon]/\epsilon^4$,
>    killedness over $\epsilon^5$ + all socle-line extensions of
>    $\epsilon^4$, both fibers).
> 2. **FIFTH external note audited** (`order4_fifth_push_relative_defect.md`,
>    bundle at `scripts/fifth_push_bundle/`; audit `THEORY` §15): Lemma 1.1
>    (top defect kills products — also characteristic-free, §15.2.1) +
>    **cotangent reduction** (§15.2.2: every depth's relative content = the
>    cotangent row); Lemma 2.1 (pairwise symbol nilpotence); **THEOREM N**
>    (S′ over every equal-char square-zero base, ANY embdim, §15.4).
>    Machine gates all green (`s5gates.log` battery A ✓✓ both fibers over
>    NEW ringcheck-validated class $\mathbb F_2[u,v]/(u,v)^2$).
> 3. **$D_5(1,3)$ — the note's open s = 5 component — closed at
>    $\mathbb F_2$** (`s5gates.log` battery B, `unsat`); all nine $D_5$
>    components now `unsat` at $\mathbb F_2$. Arbitrary-$k'$ s = 5 jobs
>    IN FLIGHT: `s5t4gen.m2` / `s5xygen.m2` (cotangent rows = the content;
>    "banked boost" pattern — see their headers for the
>    vanishing-on-solutions reading). Landing ⟹ S′ at $\epsilon^5$,
>    killedness at $\epsilon^6$.
> 4. **New mixed-char S′ result** (`s2check_ext.log`, retargeted to
>    mixed-char rings only): $W(\mathbb F_4)/8$ **✓✓ both fibers** — first
>    S′ result beyond residue field $\mathbb F_2$ in mixed characteristic
>    (⟹ via Thm 7.1: killedness over every socle-line extension of
>    $W(\mathbb F_4)/8$). Ramified $W(\mathbb F_4)[\pi]/(\pi^2{-}2,\pi^3)$
>    rows in flight — NO verdict yet, check the log before citing.
> 5. **New uniform-target formulation** (`THEORY` §15.8): divided squaring
>    $\Phi = \varphi/\epsilon$, **Conjecture $\Phi$** ($\Phi^2 = 0$ exactly
>    ⟺ curvilinear equal-char S′-universality), the §15.8.3 recursion, and
>    the **edge/suspension split** §15.8.4 ($D_{N+1} = \{\Psi_1,\Psi_N\} +
>    \Sigma^{\uparrow}_{N-1}$) with `s6probe.py` testing the suspension
>    sums (discovery rows) + the s = 6 cotangent row at $\mathbb F_2$.
> 6. **FatPoint3/$xy$ gap**: np2's --gaponly rerun returned `unknown` at
>    its 2 h timeout; NEW `s2check_np3.py` in flight (cotangent-split
>    encoding justified by §15.5.1, 12 h/query, gateP kernel-certificate
>    gate). This is the ONLY remaining exact-$\mathbb F_2$ unknown.
> 7. **Job triage for crash mitigation** (load was 10× cores — the likely
>    crash cause; now halved): killed as SUBSUMED `s4gen.m2` +
>    `order4sat_beyond.py` (Theorem M/Cor J cover their whole remaining
>    lists); killed as deferred `order4sat_f8ram.py` (heaviest job, lost
>    19 h twice, cannot checkpoint — relaunch only when box is stable) and
>    `s3xygates --f4only` (marginal). Rationale banners in each log.
>    `s2check --ext` retargeted (equal-char F₄ ring removed — subsumed by
>    Thms I+K+L; mixed-char rings kept). `ringcheck` rerun: ALL PASSED.
> 8. Session-13 verdicts still pending at write-up: `s5t4gen` /
>    `s5xygen` cotangent banners; `s6probe` rows after D6(2,1) (`unsat`);
>    `s2check_np3` split queries; `s4cert` F₄ battery tail → `s4xycert`
>    launch (relaunch_all.sh handles the chain); `s3xy2gates --f4only`
>    (Theorem L's F₄ validation — cite L at F₄ only after
>    `ALL S3XY2 GATES PASSED`); ramified-F₄ $t^4$ row. Harvest via
>    `scripts/JOBS.md` table + golden rule 4.

> **SESSION-12 BANNER (2026-07-09, ~10:30) — supersedes everything below.**
> A FOURTH external note (`order4_max_pass_xy_s4.md`, bundle at
> `scripts/xy_s4_bundle/`) reduced the $xy$/$s=4$ endpoint per split model;
> its targeted Gröbner upgrade `scripts/s4xygen.m2` then certified ALL
> targets in ALL FOUR split models (~3 min, `DONE s4xygen`) —
> **THEOREM M($xy$) banked** (`THEORY` §14.8.8; audit §14.8). The same
> pinning trick was launched for $t^4$ (`s4t4gen.m2`, digit-0 pinned to
> the Theorem-I $(c_1,c_4)$ normal form; deg-5 grinding at write-up —
> `==> ALL s4t4gen targets in J` in its log banks Theorem M($t^4$) and
> closes the curvilinear equal-char story at depth 4: S′ over
> $k'[\epsilon]/\epsilon^4$ + killed-by-4 over $k'[\epsilon]/\epsilon^5$,
> both fibers). Also: `s4pred` DONE (ALL PASSED, F₂+F₄); `s4gen` partials
> certify $aB, aC, BC, aB^2C$ (hence $aB^3$) at arbitrary $k'$;
> `s4xycert.py` (dual-number + F₄ batteries of the fourth note) queued
> behind `s4cert`. Job table: `REPORT_order4.md` §4.1 (session 12).

> **SESSION-11 BANNER (2026-07-09, ~09:30).** The machine crashed ~08:05
> and killed every job; everything below referring to "running" jobs is
> stale — the authoritative post-crash job table is `REPORT_order4.md`
> §4.1 (updated session 11) and the memory file. Headlines since this file
> was written: (1) a THIRD external handoff `order4_further_push_s4_t4.md`
> claims closure of $s=4$/$t^4$ — audit in `THEORY_order4.md` §14;
> `s4cert.py` passed ALL 28 gates over $\mathbb F_2[\epsilon]/\epsilon^4$,
> dual-number + $\mathbb F_4$ batteries and the arbitrary-$k'$ M2 run
> `s4gen.m2` in flight; its $aB=0$ input cites a predecessor note
> `order4_sustained_attempt_note.md` NOT present in this folder — obtain it
> from the user. (2) `s4probe` finished ALL-PASSED: the $s=4$ endpoint
> $D_4 = 0$ holds over $\mathbb F_2[\epsilon]/\epsilon^4$ for BOTH fibers.
> (3) `s3gates` finished: Theorem K validation complete. (4) Theorem L
> still awaits `s3xy2gates --f4only` (relaunched). (5) `eps45`/`z8search`/
> `f8`/`s2gen`/`symbolsq`/`len3gen` are dead and deliberately not
> relaunched.

**For the next agent.** This file is written so that the work can be continued in
small, mostly mechanical steps. Read `REPORT_order4.md` first for what is already
proved (Theorems A, B, B′, D, E, Corollary C) and `macaulay2_handoff_order4.md` for
the original problem statement. Progress state is also mirrored in the memory file
`grothendieck-order4-project`.

**Last updated:** 2026-07-09, morning (session 10 — **Theorem L: the
$s = 3$ layer identity for the $xy$ fiber is proved by hand**, per-case
over the 12.4.1 classification, closing $s = 3$ for BOTH fibers; lemma
battery `s3xy2gates.py` all-green over $\mathbb F_2$; the $\mathbb F_4$
half was running at session end — CHECK `s3xy2gates.log` ends in
`ALL S3XY2 GATES PASSED` before citing anything from it).
Read §0-10 first, then §0-9, §0-8, §0-7 (work queue — superseded items are
marked), then §0-6, §0-5, §0-4, §0-3, §0, §A.
**Read `THEORY_order4.md` §12.6.5, §12.6.6 and §13 before doing any more
theory; the next target is the $s \ge 4$ family / relative first-order
lemma (§13.2), starting from the §12.6.6 beachhead formulas.**

**Golden rules (do not skip):**
1. **Never write new equation-generating code without re-running the validation
   points.** The three gates are: handoff §16.1 (α₂⋊μ₂: all Hopf equations vanish,
   fiber2 *fails*, P4 = 0), §16.2 (all equations vanish, fiber2 holds, P4 = 0),
   and μ₄ over ℤ/8 (`scripts/z8validate.m2`: bialgebra equations vanish mod 8,
   φ(t) = 2t + t², P4 = 0). If a gate fails, your code is wrong — stop.
1b. **Never add or edit a base-ring class without re-running
   `scripts/ringcheck.py`** (added 2026-07-08; expects `ALL RING CHECKS PASSED`).
   A wrong multiplication table or `deform` makes every UNSAT over that ring
   vacuous. This gate did not exist before session 2 and it immediately caught a
   mislabelled ring (`Ext3`). See §0.1.
2. **Distinguish three strengths of result.** (i) Z3 UNSAT = no counterexample over
   that *exact finite ring*; (ii) M2 ideal membership = identity over *every*
   parameter ring of that shape (much stronger); (iii) radical membership (weaker
   than (ii), still fine for geometric points). Never claim more than the tool gives.
3. **A SAT model is not yet a counterexample.** If any level-2 query ever returns
   `sat`, follow the counterexample protocol in §D below before claiming anything.
   As of 2026-07-08 **no level-2 query has ever returned `sat`**, and every level-1
   sanity query has returned `sat` (so no system is vacuous).
4. **A theorem in `REPORT_order4.md` is not evidence.** Before citing one, open the
   log and check it actually contains the `unsat` / `in J` lines for *every* ring or
   coefficient the theorem names. The report has run ahead of its evidence at least
   once (§0.4). This is the single most important lesson of session 2.
5. Everything runs with `/opt/homebrew/bin/M2 --script <file>` and the Python venv
   `/private/tmp/claude-501/.../scratchpad/z3env/bin/python` (rebuild with
   `python3 -m venv .../z3env && .../pip install z3-solver` if the scratchpad was
   cleaned; any venv with `z3-solver` works). The exact venv in use on 2026-07-08:
   `/private/tmp/claude-501/-Users-akhilmathew-Library-CloudStorage-Dropbox-FiniteFlatGroupSchemes/6ae8162a-c24f-42d0-8e47-04a1ec18e1ec/scratchpad/z3env/bin/python`
   (note: the *session-2* scratchpad is a different directory; this venv survives
   from session 1). Launch long jobs with `nohup nice -n 10 ... &`; the box has 18
   cores and 8 jobs already saturate it.

---

## §0-10. Session-10 record (2026-07-09, morning) — THEOREM L: $s = 3$ closed for the $xy$ fiber (both fibers now done)

User prompt: "think deeply about Grothendieck's conjecture and try to
prove or disprove it; read previous handoffs." Outcome: the **$s = 3$
layer identity is proved BY HAND for the $xy$ fiber** (Theorem 12.6.5.1 in
`THEORY_order4.md` §12.6.5 — report name **Theorem L**), per-case over the
12.4.1 height-one classification, with two new UNIVERSAL lemmas; a
40-gate lemma-level battery (`scripts/s3xy2gates.py` →
`s3xy2gates.log`) passed **100% over $\mathbb F_2[\epsilon]/\epsilon^3$**
(the $\mathbb F_4$ half was mid-run at session end); the $s = 4$
beachhead is written (THEORY §12.6.6).

### 0-10.1 Theorem L and how the proof works (read THEORY §12.6.5)

Setting: $\kappa$ perfect, $\Delta_0$ killed-by-2 on
$\kappa[x,y]/(x^2,y^2)$, $k' \supseteq \kappa$, $A$ free rank-4 bialgebra
over $k'[\epsilon]/\epsilon^3$ with fiber $H_\kappa\otimes k'$, fiber2, no
liftability. Then $\Psi_1\Psi_2 + \Psi_2\Psi_1 = 0$. Key new tools:
* **Lemma X1 (12.6.5.2):** $\Psi_1(\mu_1(a,a)) = 0$ for every $a \in I$ —
  layer-2 multiplicativity at $(a,a)$ plus "every element of $I$ squares
  to zero" ($(\Psi_1a)^2 = 0$). Gives the universal composite formula
  $\Psi_1\Psi_2(g) = c_g\Psi_1(\mu_1(x,y)) + \Psi_1(\mu_2(w_0g))$.
* **Lemma X2 (12.6.5.3):** layer-2 diagonal identity
  $w_0(\mu_2(a,a)) = w_1(\mu_1(a,a)) + S_2(a) + T_{11}(a)$; the quadratic
  carry $(w_1a)^2$ dies because ALL basis squares vanish (the $xy$
  analogue of Theorem K's $Y^2 = 0$).
* Per case: $\alpha_2^2$ and $\mu_2^2$ collapse to "both composites equal
  $c_g\Psi_1\mu_1(x,y)$" (in $\mu_2^2$, X2 + $\operatorname{Prim} = 0$
  forces $\mu_2(x,x) = \mu_2(y,y) = 0$). In $W_2[F]$ and
  $\mu_2{\times}\alpha_2$ the surviving obstruction is
  $\lambda\nu(w_1\cdot)_{22}$, killed by the TWO X2 instances at $x$ and
  $y$ jointly (e.g. $\lambda(w_1y)_{22} = \lambda^2$ from X2-at-$x$,
  $\nu(w_1y)_{22} = 0$ from X2-at-$y$ ⟹ $\nu\lambda^2 = 0$); order-2
  coassociativity extraction at the SAME monomials as layer 1 gives
  $c^{(2)}_x = 0$ resp. $c^{(2)}_y = 0$ (the quadratic $(w_1,w_1)$-carries
  cancel via the layer-1 relations).
* **Layer-1 sharpenings found en route (Remark 12.6.5.7):** in $W_2[F]$,
  $\psi(y) = \lambda x$ EXACTLY (its $I^2$-part $c_y$ vanishes — new); in
  $\mu_2{\times}\alpha_2$, $\psi(x) = \lambda y$ exactly ($c_x = 0$). So
  $\psi(I) \subseteq \operatorname{Prim}$ in cases (2)(3)(4) and
  $\psi(I) \subseteq I^2$ in case (1).

### 0-10.2 Consequences (Corollaries 12.6.5.4-6) — THE $\epsilon^3$/$\epsilon^4$ STORY IS NOW CLOSED BY HAND

* **S′ over $k'[\epsilon]/\epsilon^3$, BOTH fibers, arbitrary $k'$** ($xy$:
  fiber defined over a perfect subfield — always true in the group-scheme
  application). This is the FULL target of `s2gen.m2` (whose gate value
  never printed): **`s2gen` is now fully audit-only, safe to kill.**
* **Killed-by-4 over $k'[\epsilon]/\epsilon^4$, BOTH fibers, arbitrary
  $k'$** — the FULL $\epsilon^4$ target of `search_eps45.m2` (its $xy$
  branch stood at 24/30 coefficients at `DegreeLimit` 4). eps45's
  $\epsilon^4$ stages (xy current + t⁴ next) are now audit-only; its
  $\epsilon^5$ stages (queued in the same script, lines 170-171) still
  carry the OPEN $s = 4$ content — let it run into them.
* Via Thm 7.1: killed-by-4 for every socle-line lift over every socle-line
  extension of $k'[\epsilon]/\epsilon^3$, non-curvilinear included,
  arbitrary $k'$.
* Curvilinear equal-char S′-universality is now proved for $N \le 3$ at
  arbitrary-$k'$ strength and the remaining family is exactly $s \ge 4$.

### 0-10.3 Validation (golden rules 1, 1b)

NEW `scripts/s3xy2gates.py` → `s3xy2gates.log`: 4 universal gates (H1-H4:
12.1.1 layers, Hochschild-into-$I^2$, X1, Step-1-at-$z$) + per-split-case
lemma batteries (A: a2a2, B: W2F, C: mu2mu2, E: mu2a2) with pin-sanity
`sat` probes, full-matrix X2 gates, order-1/2 coassociativity extraction
gates, endpoints, and non-vacuity probes. **$\mathbb F_2$: ALL PASSED**
(every gate `unsat`, every expected-`sat` probe `sat`; verified in-session).
Notable probes: BN3 `lam*nu != 0 realizable` → `sat` (the B4/B5
cancellations are load-bearing); EN3 `lam*(w1y)11 != 0` → `sat`
($\mu_2(x,x)$ GENUINELY escapes $I^2$ — the layer-1 case mechanism does
not persist verbatim, consistent with probe Q3). $\mathbb F_4$ half:
H0-H2 passed at session end, rest pending — **harvest before citing**.
No new ring class (F2eps3/Ext already ringcheck-validated; KF2/KF4 reused
from s3gates) ⟹ no ringcheck rerun needed. Builder = the gate-validated
`s2check.build_blocks`, unchanged.

### 0-10.3b Golden-rule-4 near-miss caught in-session

THEORY §12.6.4.5 (session 9) recorded discovery gate G9nc as "both rings"
when only the $\mathbb F_2$ line existed; the $\mathbb F_4$ G9nc line
landed `unsat` DURING session 10 (now true, evidence in `s3gates.log`).
Same failure mode as §0.4 — a claim that lands anyway is the failure mode
you don't notice. When recording per-ring gate tables, count the lines.

### 0-10.4 Jobs (state at session end)

* NEW `s3xy2gates.py` (pid 99019): $\mathbb F_4$ half running.
* NEW `s4probe.py` (written + py_compile-checked, chain-queued behind
  s3xy2gates via a kill-0 waiter, pid 4049 → `s4probe.log`):
  $\mathbb F_2[\epsilon]/\epsilon^4$, both fibers — gates the §12.6.6(e)
  layer-3 computation (T1), the $s{=}4$ endpoints (T2/X2g — cross-validate
  s2check's $\epsilon^4$ rows), the $aB^3 = aB^2C = 0$ scalars (T5/T6),
  discovery on $aB$, $aB^2$ (T3/T4 — Frobenius-collapse caveat in
  §12.6.6(e): F₂ can't separate $aB$ from $aB^3$), the $\Gamma$-vanishing
  lemma (X1g), and the layer-3 X1-analogue (X3).
* `s3gates.py` (pid 80003) STILL on its $\mathbb F_4$ discovery tail
  (G9nc/N1-N5 over $\mathbb F_4$); all substantive gates G0-G10 passed
  both rings (Theorem K fully validated). `s3xygates.py` still
  chain-queued behind it (waiter pid 89780).
* `s2check_np2.py` (pid 81846): **ALL GATES PASSED mid-session** (gate3
  landed; `===== ALL GATES PASSED =====` in log) — main table started
  (first S1 sanity `sat`); rows = BiDual xy/t⁴ + FatPoint3 t⁴
  cross-validation (must reproduce `unsat`), then **FatPoint3/xy = the
  gap**.
* Inherited, no new verdicts: beyond ($\mathbb F_4[\epsilon]/\epsilon^4$
  xy level 2), f8 (cross-validation only, safe to kill), f8ram (first
  query), s2check --ext ($\mathbb F_4[\epsilon]/\epsilon^3$ xy),
  eps45 ($\epsilon^4$/xy `DegreeLimit` 5 — now audit-only until it reaches
  $\epsilon^5$), z8search (`DegreeLimit` 5, 0/9 — kill-after-a-day advice
  in force), s2gen (NOW FULLY AUDIT-ONLY — safe to kill), symbolsq/len3gen
  (audit-only). A log monitor for the four gate/probe logs runs in this
  session only (not persistent across sessions).
* `order4sat_f8nofib.py`: still written-not-launched (box saturated).

### 0-10.5 Next session, in order

1. **Harvest `s3xy2gates.log`** — must end `ALL S3XY2 GATES PASSED`
   ($\mathbb F_4$ half). If any $\mathbb F_4$ gate failed: semilinearity
   slip in the hand proof — fix THEORY §12.6.5 and re-gate BEFORE citing
   Theorem L anywhere. Then harvest `s3xygates.log` (endpoint battery,
   auto-launches after s3gates) and `s2check_np2.log` (FatPoint3/xy gap:
   `unsat` closes Theorem G′'s caveat).
2. **The $s \ge 4$ family / relative first-order lemma** (THEORY §13.2)
   with the §12.6.6 beachhead: layer-3 multiplicativity, layer-$s$
   diagonal identity, $\Gamma$-vanishing (all displayed there; gate the
   $\Gamma$-vanishing lemma before leaning on it). Suggested first move:
   an `s4probe.py`/`s4gates.py` calibration over
   $\mathbb F_2[\epsilon]/\epsilon^4$ (which composite components escape,
   which §12.6.6 shapes hold) once a compute slot frees up. If the
   relative lemma lands at all depths: equal-char curvilinear
   S′-universality is CLOSED, and with the non-principal rows (G′ + np2)
   the §7 socle induction starts eating equal characteristic wholesale.
3. Standing: harvest the six inherited jobs; launch `order4sat_f8nofib.py`
   when a slot frees; user may `pkill -f s2gen.m2` (and `search_eps45.m2`
   once its $\epsilon^4$ stages end, if $\epsilon^5$ is deemed redundant
   with the coming $s = 4$ work — NOT yet).

---

## §0-9. Session-9 record (2026-07-09, night) — THEOREM K: $s = 3$ closed for the $t^4$ fiber

User prompt: continue, reading the most recent ChatGPT handoff
(`order4_divided4_theory_handoff.md`). Outcome: the **$s = 3$ layer
identity is proved BY HAND for the $t^4$ fiber** (Theorem K in the report;
full six-step proof in `THEORY_order4.md` §12.6.4), machine-gated over BOTH
$\mathbb F_2[\epsilon]/\epsilon^3$ and $\mathbb F_4[\epsilon]/\epsilon^3$;
the external handoff is audited (THEORY §13); the FatPoint3/$xy$ `unknown`
got a new attack (`s2check_np2.py`, running); the $xy$-fiber $s = 3$
calibration battery is queued.

### 0-9.1 Theorem K (read THEORY §12.6.4 for the proof)

For every commutative $\mathbb F_2$-algebra $k'$, every counital
multiplicative coassociative killed-by-2 $\Delta_0$ on $k'[t]/t^4$, every
free rank-4 bialgebra over $k'[\epsilon]/\epsilon^N$ ($N \ge 3$) with that
fiber: $\Psi_1\Psi_2 + \Psi_2\Psi_1 = 0$. Fully axiomatic (no perfectness /
classification, like Thm 12.3.2). Key steps found this session:
* $Y := w_1(t^2) = \lambda\,w_0(t^3) + pc_4\,t^2{\otimes}t^2$ with
  $\lambda = pc_1 + p_3 + ac_1^2$ (first-order $\Delta$-mult at $(t,t)$;
  the $S$-term collapses to $c_1^2(u{\otimes}t^2 + t^2{\otimes}u)$).
* $Y^2 = 0$, so the layer-2 diagonal identity degenerates to
  $w_0(\mu_2(t^2,t^2)) = w_1(\mu_1(t^2,t^2))$, giving
  $c_4v_t = a\beta_{22} + pbc_4$.
* Order-1 coassociativity forces $\beta_{13} = \beta_{31}$ (both equal
  $c_1\lambda + c_1^2\Theta_{11}$) — the load-bearing cancellation.
* Assembly: $(\Psi_2t)_t = pB + qC$ EXACTLY, and layer-2 multiplicativity
  gives $\Psi_2(t^2) = p\Psi_1t$, $\Psi_2(t^3) = q\Psi_1t$; both composites
  equal $g_t(pB{+}qC)\Psi_1t$. Char 2.
Corollaries (12.6.4.2-4): **S′ over $k'[\epsilon]/\epsilon^3$ for the $t^4$
fiber, arbitrary $k'$** (the $t^4$ half of `s2gen`'s target, by hand; via
Thm 7.1, killedness of $t^4$-fiber lifts over every socle-line extension of
$k'[\epsilon]/\epsilon^3$, non-curvilinear included); **killedness over
$k'[\epsilon]/\epsilon^4$, $t^4$ fiber, arbitrary $k'$** (the $t^4$ half of
`search_eps45`'s $\epsilon^4$ target — when eps45 finishes its $xy$ branch
and moves to $t^4$, that part is audit-only).

### 0-9.2 Validation (golden rules 1, 1b)

NEW `scripts/s3gates.py` → `s3gates.log`: every proof step (G1-G8, G10) and
the endpoint (G9) as digit-level Z3 gates, **all `unsat` over both rings**
(verified in-session; the log's final `ALL S3 GATES PASSED` line was still
pending the last discovery probes at session end — re-check it). No ring
class was added or edited (F2eps3 and Ext are ringcheck-validated;
residue-field digit arithmetic in `KF2`/`KF4` mirrors the Ext tables).
Discoveries: **G9nc** — the $s=3$ identity survives with coassociativity
dropped (A+M+F only, both rings): the Theorem-F minimal-axiom pattern
persists at layer 2 (the hand proof DOES use coassoc; a leaner proof
exists in principle). **N5** — $a\beta_{13}B = 0$ identically over
$\mathbb F_2$ though $a\beta_{13} \ne 0$ is realizable (N3): the dangerous
term is doubly protected.

### 0-9.3 Audit of the second external handoff (THEORY §13)

`order4_divided4_theory_handoff.md` (GPT, 2026-07-09): its divided-$[4]$ /
Koszul reformulation = Prop 12.6.1 + the s2check_np encoding (independent
convergence — confirming). **Banked as new:** Prop 13.2.1
(minimal-counterexample reduction: $\varphi^2 = 0$ is already forced on a
length-minimal S′-counterexample — 3-line proof via Thm 7.1) and the
**relative first-order lemma** framing for the $s \ge 4$ induction (§13.2).
**Stale — do not follow:** its §9 priorities predate Theorem I (symbolsq
harvest, $\psi^2$ certificate mining are retired/audit-only).

### 0-9.4 Jobs (state at session end)

* NEW `s2check_np2.py` (running, `s2check_np2.log`): Boolean-syzygy-basis
  re-encoding of the non-principal S′ probe. gateS verified |Syz₁| = 32 =
  2⁵ over BiDual (basis span checked exhaustively); gates 0/1/1b/2 passed
  fast; **gate3 still running** at session end (it was the slow one for
  s2check_np too). Then: BiDual xy/t⁴ + FatPoint3 t⁴ (cross-validation
  rows, must reproduce `unsat`) and finally **FatPoint3 xy = the gap**.
* NEW `s3xygates.py` (chain-queued behind `s3gates.py` via a
  `kill -0 80003` waiter, launcher pid 89780 → `s3xygates.log`): $xy$-fiber
  $s = 3$ calibration — endpoint + layer-2-multiplicativity gates, per-case
  pinned batteries over the four 12.4.1 split models, escape-discovery
  rows, over $\mathbb F_2$ AND $\mathbb F_4$. Read it before starting the
  $xy$ hand proof.
* Session-6/7 results are NOW WRITTEN INTO THE REPORT (was work-queue item
  2): Theorem G extended to length 5 (`s2check_deeper.log` re-verified),
  NEW Theorem G′ (non-principal S′, `s2check_np.log` re-verified), Theorem
  E extended (all 16 beyond `unsat` lines + 2 f8 lines re-verified
  in-session), Corollary H gains ℤ/64 and the $\epsilon^5$ socle
  extensions. Theorem K added. Harvest table refreshed.
* Inherited jobs all still alive, no new verdicts this session: beyond
  ($\mathbb F_4[\epsilon]/\epsilon^4$ xy level 2), f8 ($\mathbb
  F_8[\epsilon]/\epsilon^3$ xy — cross-validation only, safe to kill), f8ram
  (first query, ~2461 CPU-min), s2check --ext ($\mathbb F_4[\epsilon]/
  \epsilon^3$ xy main query; gates all passed), eps45 (DegLimit 5),
  z8search (DegLimit 5 — kill-after-a-day advice now in force), s2gen
  (gate value STILL unprinted — do not cite), symbolsq/len3gen
  (audit-only). Box is at ~16/18 cores with the two new probes.

### 0-9.5 Next session, in order

1. Harvest `s3gates.log` final lines, `s2check_np2.log` (main table — if
   FatPoint3/xy lands `unsat`, S′ is closed over ALL four non-principal
   rows; write it into Theorem G′ and drop the gap caveat), and
   `s3xygates.log`.
2. **$xy$-fiber $s = 3$ hand proof** guided by the calibration rows (the
   per-case toolkit of 12.4.3 + the Step-1/2/4 template of 12.6.4; note
   $\Psi_1(I) \not\subseteq I^2$ in cases W2F/mu2a2, so the composite has
   genuinely more terms — expect the per-case coassociativity extraction
   to do the work again).
3. Then the **relative first-order lemma** ($s \ge 4$, THEORY §13.2) — if
   it lands, equal-char curvilinear S′-universality is closed at ALL
   depths, and with the non-principal rows, the socle induction machine
   (§7) starts eating equal characteristic wholesale.
4. Standing: harvest the six inherited jobs; `order4sat_f8nofib.py` still
   written-not-launched (box saturated).

---

## §0-8. Session-8 record (2026-07-09, later) — THEOREM I: the theory push landed

User prompt: "make a serious push at proving the conjecture." Outcome: the
**first-order symbol theorem is now proved BY HAND** and machine-gated, and
with the banked polarization theorem it **closes equal-characteristic
$\mathfrak m^3 = 0$ in ALL embedding dimensions**. Full proofs: `THEORY_order4.md`
§12 (read §12 before touching anything equal-characteristic). Report: Theorem I
+ Corollary J in §1 of `REPORT_order4.md`.

### 0-8.1 What was proved (hand proofs, all machine-gated)

* **Theorem I.** Fiber bialgebra $H$ (either shape) defined over a perfect
  field $\kappa$, $k' \supseteq \kappa$ arbitrary: every first-order
  deformation over $k'[e]/e^2$ (bialgebra + fiber2, NO liftability) has
  $\psi^2 = 0$. For the $t^4$ fiber: arbitrary $\Delta_0$ over arbitrary
  $k'$, and the stronger $\psi(I) \subseteq I^2$.
  Proof mechanism (reusable at depth): (i) *diagonal primitivity* — the
  $(a,a)$-instance of first-order $\Delta$-multiplicativity forces
  $\mu_1(a,a)$ primitive when $a^2 = 0$ and $S(a) = 0$ (THEORY 12.2.1);
  (ii) *symmetric-pair cancellation* — only diagonal $\mu_1(e_p,e_p)$ values
  reach $\psi$ mod $I^2$ (12.2.2); (iii) for $t^4$: coassociativity of
  $\Delta_0$ pins $w_0t = c_1 t{\circ}t^2 + c_1^2 t^2{\circ}t^3 +
  c_4 t^2{\otimes}t^2$ and the primitives obey $a c_4 = 0$ — exactly killing
  the dangerous $t$-component (12.3.1-2); (iv) for $xy$: height-1
  (Demazure–Gabriel) classification over $\bar\kappa$ + faithfully flat
  descent + per-case first-order-coassociativity extraction (12.4).
* **Corollary J.** Equal-char Artin local, $\mathfrak m^3 = 0$, finite (or
  perfect) residue field, ANY embdim: killed by 4 (bialgebra statement
  unconditional; group-scheme statement carries only the standing Schoof
  flag G.2, like Cor. C). Subsumes Theorems A, F at $\epsilon^3$; retires
  the embdim-3 plan; `len3gen` and `symbolsq` are now **audit-only**.
* **Layer-symbol reformulation (THEORY 12.6.1).** Over
  $k'[\epsilon]/\epsilon^N$: S′ $\iff$ $\sum_{m+n=s}\Psi_m\Psi_n = 0$ for
  $2 \le s \le N$ (killedness: $s \le N{-}1$), where $\Psi_n =
  \sum_{j+l=n}\mu_j w_l$ are the layer symbols. **Theorem I = the $s = 2$
  identity for every tower.** The equal-char curvilinear S′-universality
  conjecture is now the precisely-scoped family $s \ge 3$; the layer-2
  analogues of the two workhorse identities are the next theory target.

### 0-8.2 Validation (golden rules 1, 1b — all green)

* NEW `scripts/firstorder_gates.py` → `firstorder_gates.log`:
  **51/51 PASS, `ALL FIRSTORDER GATES PASSED`** — every lemma of the §12
  proof as a Z3 query over $\mathbb F_2[\epsilon]/\epsilon^2$ AND
  $\mathbb F_4[\epsilon]/\epsilon^2$ (P1-P7 + non-vacuity), plus six
  pinned-fiber batteries checking each case computation (PIN-a2a2, -W2F,
  -mu2mu2, -mu2a2, -aF2, -c4). Equation builder reused verbatim from
  `s2check.build_blocks` (itself gate-validated); only assertions are new.
* `Ext(F2epsN(2))` = $\mathbb F_4[\epsilon]/\epsilon^2$ added to
  `ringcheck.py` CASES; full rerun in `ringcheck_s8.log` (new class OK:
  16 elts, residue $\mathbb F_4$, chain [4,1]).

### 0-8.3 Job status (CORRECTED mid-session — read the trap note)

* **TRAP (new instance of golden rule 4, session-8 vintage): the three Z3
  jobs were never dead.** Early in session 8 the check
  `ps aux | grep -E "M2|z3env"` showed no Z3 processes and "all three Z3
  jobs died" was written into the docs — but the venv's `python` symlink
  resolves to `/opt/homebrew/Cellar/python@3.14/...`, so the command lines
  contain neither `M2` nor `z3env`. A later `ps | grep order4sat` showed
  `order4sat_beyond` (pid 6837), `order4sat_f8` (6843), `order4sat_f8ram`
  (27733) all alive the whole time (their logs are quiet simply because
  these scripts print only at query completion, as §0-7 itself noted).
  **When checking Z3 jobs, grep for the script names.**
* Fallout: a duplicate `order4sat_beyond` was launched (job list edited to
  resume at $\mathbb F_4[\epsilon]/\epsilon^4$, `Ext(FatPoint3)` demoted to
  an audit tail per Cor. J) before the mistake was caught; the duplicate
  was killed ~2 min later. **Log-reading note:** in
  `order4sat_beyond.log`, the banner `== RESTARTED session 8 (Jul 9) ==`
  and the immediately following repeated query header + level-1 `sat` line
  belong to the killed duplicate — ignore them; the next verdict line after
  them belongs to the ORIGINAL process's $\mathbb F_4[\epsilon]/\epsilon^4$
  xy level-2 query (running since 01:57). The edited script file on disk
  does not affect the running process (Python read it at startup); if 6837
  ever exits/dies, a relaunch will pick up the edited (improved) list.
* `order4sat_f8` (alive, ~24+ h on $\mathbb F_8[\epsilon]/\epsilon^3$ xy
  level 2): its remaining queries are instances of **Corollary J** — it is
  now cross-validation only. Safe to kill for RAM
  (`pkill -f order4sat_f8.py`) — needs the user, not started this session.
* `order4sat_f8ram` (alive, on its first level-2 query): still the carrier
  of "Corollary C extends to $\mathbb F_8$" — let it run.
* `s2check.py --ext` **LAUNCHED this session** (`s2check_ext.log`): all
  five encoding gates re-passed; $\mathbb F_4$ curvilinear rows running.
* NEW `scripts/s3probe.py` ran to `DONE` (`s3probe.log`), discovery results:
  **Q1 `sat`** — over $\epsilon^3$, $\varphi(e_1)$ CAN have an
  $e_1$-component, i.e. $\Psi_2(I) \not\subseteq I^2$ in general: the
  layer-1 $t^4$ mechanism does NOT persist verbatim at layer 2; the $s=3$
  identity holds only through cancellation in the symmetrized sum
  $\Psi_1\Psi_2 + \Psi_2\Psi_1$ (which IS true — s2check $\epsilon^3$).
  **Q2 `unsat`** — $\varphi(I^2)$ never has an $e_1$-component: candidate
  lemma $\Psi_n(I^2)\subseteq I^2$. **Q3 `sat`** — same non-persistence in
  the $xy$/$\alpha_2{\times}\alpha_2$ case. These calibrate the $s=3$ hand
  proof (THEORY 12.6.3): work with the full sum, not per-symbol images.
* M2 jobs all alive (`symbolsq`, `s2gen`, `len3gen`, `search_eps45`,
  `z8search`); `symbolsq`/`len3gen` now audit-only (do not prioritize);
  `s2gen`'s gate value is STILL unprinted — do not cite it.
* `ringcheck_s8.log` (full rerun incl. new class
  $\mathbb F_4[\epsilon]/\epsilon^2$): **`ALL RING CHECKS PASSED`**
  (verified in-session).

---

## §0-7. Session-7 record (2026-07-09, daytime) — state + work queue (superseded in part by §0-8)

Harvest session. Every claim below was checked against the named log during this
session (golden rule 4). Still **zero** level-2 `sat` anywhere, ever; the only
non-unsat verdict in the whole project is one `unknown` (see 0-7.1).

### 0-7.1 s2check_np is DONE — S′ holds at the non-principal bases (one gap)

`s2check_np.log` ends in `DONE s2check_np`. All gates passed (incl. gate3, which
was still running at the end of session 5). Main table:

| base | fiber xy | fiber t⁴ |
|---|---|---|
| BiDual = 𝔽₂[x,y]/(x²,y²) | **unsat** | **unsat** |
| FatPoint3 = 𝔽₂[x,y]/(x,y)³ | **`unknown`** | **unsat** |

Reading (THEORY Thm 7.1): S′-universality holds over BiDual (both fibers) and
over FatPoint3 (t⁴ fiber) ⟹ **every free rank-4 bialgebra with killed-by-2
local fiber over every socle-line extension of these rings is killed by 4** —
the first socle-extension results over non-curvilinear bases. The `unknown` is
MBQI giving up on the quantified query, NOT a `sat` — no S′-violation was found.
**Gap-closing task:** re-run FatPoint3/xy with the quantifier-free syzygy-coset
encoding (design option (ii) in §0-4.2's design note) instead of ForAll+MBQI;
32³ shifts per pair-witness needs the symmetry reduction described there.

### 0-7.2 s2check --deeper is DONE — Theorem G extends to length 5

`s2check_deeper.log` ends in `DONE s2check`: **𝔽₂[ε]/ε⁵ unsat ✓✓ and ℤ/32
unsat ✓✓** (all four S1 sanity gates `sat`, all gates passed). With Thm 7.1:
killed-by-4 over **every socle-line extension of 𝔽₂[ε]/ε⁵ and of ℤ/32** —
includes ε⁶ (independently SAT-confirmed, §0-6) and **ℤ/64 (new)**, plus all
non-curvilinear extensions. Process exited — **a compute slot is free**.
`--ext` mode (𝔽₄ curvilinear variants) still never run.

### 0-7.3 Other verdicts and progress harvested

* `order4sat_f8`: **W(𝔽₈)/8 is now ✓✓** (the t⁴ query landed post-restart; both
  `unsat` lines in the log). Currently grinding 𝔽₈[ε]/ε³ xy level 2 (~40 CPU-h).
* `order4sat_beyond`: everything through ℤ[π]/(π²−2,π⁴) ✓✓ (see §0-6);
  currently on 𝔽₄[ε]/ε⁴ xy level 2 (since ~01:57).
* `order4sat_f8ram`: still on its FIRST level-2 query (W(𝔽₈)[π], xy), ~19 h
  wall. The 512-element rings are the slowest — this is expected, let it run.
* `search_eps45`: ε⁴/xy `DegreeLimit 4` finished (20 220 s): **6/30 nonzero
  remainders ⟹ 24/30 coefficients proved at arbitrary-k strength** (was 12/30
  at limit 3). `DegreeLimit 5` running.
* `z8search`: `DegreeLimit 4` done, still 9/9 nonzero (0 proved). Limit 5
  running. §A's "kill after ~a day of CPU" advice is approaching relevance.
* `search_nofib3.m2` and `certs.m2`: **confirmed no longer running** (kills
  executed). Both were superseded (Theorem F); their §A rows are historical.
* `symbolsq.m2` / `s2gen.m2` / `len3gen.m2`: processes alive, inside big GB
  computations, **no verdict lines yet**. len3gen xy still at `DegreeLimit 4`
  (16/48 nonzero at limit 3 ⟹ 32/48 proved). **CAUTION:** `s2gen.log`'s gate
  line reads `16.2 delta digits nonzero:` with the value never printed (M2
  stdout buffering, §0-4.2) — the gate is **unconfirmed**; do not cite s2gen
  until the value (must be 0) appears. `symbolsq.log` has no gate lines at all
  yet — only elapsed-time markers.

### 0-7.4 Live jobs (8, box no longer saturated — 2 slots freed this session)

| job | state |
|---|---|
| `order4sat_f8` (Z3) | 𝔽₈[ε]/ε³ xy level 2 |
| `order4sat_beyond` (Z3) | 𝔽₄[ε]/ε⁴ xy level 2 |
| `order4sat_f8ram` (Z3) | W(𝔽₈)[π] xy level 2 (first query) |
| `symbolsq.m2` | GB, pre-gate output (decides all-embdim equal-char 𝔪³=0!) |
| `s2gen.m2` | GB, gate value unprinted |
| `len3gen.m2` | xy `DegreeLimit 4` |
| `search_eps45.m2` | ε⁴ `DegreeLimit 5` |
| `z8search.m2` | `DegreeLimit 5`, 0/9 proved |

### 0-7.5 Work queue for the next session, in order

1. **Harvest `symbolsq.log`** the moment it has verdicts — it decides the
   equal-char 𝔪³=0 all-embedding-dimensions theorem (§0-4.2b). If it lands:
   bank the theorem, demote `len3gen` to audit-only, drop the embdim-3 plan.
2. **Write the session-6/7 results into `REPORT_order4.md`** (none are there
   yet): Theorem E extension (ε⁶, ℤ/16, ℤ/32, ℤ[π]/(π²−2,π⁴), BiDual,
   FatPoint3 as bases — all ✓✓, from `order4sat_beyond.log`); Theorem G
   extension (ε⁴→ε⁵, ℤ/16→ℤ/32, π⁴; 16/16 in `s2check.log` + 4/4 in
   `s2check_deeper.log`); the NEW non-curvilinear S′ corollaries (0-7.1);
   the socle-extension corollaries ℤ/64, ℤ[π]/(π²−2,π⁵). Golden rule 4:
   re-check each log line as you write.
3. **Launch `order4sat_f8nofib.py`** (written session 5, never launched) —
   two slots are now free.
4. **Close the FatPoint3/xy `unknown`** (0-7.1) via the QF syzygy-coset
   encoding. Optionally also launch `s2check.py --ext` (𝔽₄ variants).
5. Then the standing items: harvest s2gen/len3gen/eps45/z8search/f8/f8ram/
   beyond as they finish; highest-value THEORY target unchanged — prove
   S′-universality (Conjecture 7.5.4) or find its obstruction; embdim-3
   analogue of len3gen (unless step 1 retires it).

---

## §0-6. Session-6 record (2026-07-09, early) — beyond batch + s2check complete

* **`order4sat_beyond` fast batch, all UNSAT ✓✓** (fiber2=True, both fibers,
  all verified in the log this session): **𝔽₂[ε]/ε⁶** (Theorem-E family now
  reaches length 6); **𝔽₂[x,y]/(x²,y²)** and **𝔽₂[x,y]/(x,y)³ as BASES**
  (first direct non-curvilinear confirmations — exact-k=𝔽₂ companions to
  len3gen and to s2check_np); **ℤ/16, ℤ/32, ℤ[π]/(π²−2,π⁴)** (previously only
  s2check socle-extension corollaries, now directly SAT-confirmed).
* **`s2check.py` (main run) reached `DONE`: all 8 curvilinear rings of length
  ≤ 4, 16/16 UNSAT** — ε², ε³, ε⁴, ℤ/4, ℤ/8, ℤ/16, ℤ[π]/(π²−2,π³),
  ℤ[π]/(π²−2,π⁴), both fibers each (verified: 16 ring-level `unsat` lines +
  `DONE s2check` in `s2check.log`). Immediate corollaries then: ℤ/32 and
  ℤ[π]/(π²−2,π⁵) killed by 4 (socle exts). `--deeper` (ε⁵, ℤ/32) was launched
  → finished in session 7 (§0-7.2).
* The GPT-5.5-Pro theory-handoff audit and the `symbolsq.m2` launch are
  recorded in §0-4.2b (they straddled sessions 4–6).

---

## §0-5. Session-5 record (2026-07-08, late night — short session after an accidental /clear)

* **NEW `scripts/s2check_np.py`** (running, `s2check_np.log`): the REQUIRED
  non-principal-𝔪 S′ probe of §0-4.2, bases BiDual = 𝔽₂[x,y]/(x²,y²) and
  FatPoint3 = 𝔽₂[x,y]/(x,y)³. Encoding = design option (i): S′-FAIL as a genuine
  Z3 bitvector ForAll (MBQI), sound with or without fiber2 since 𝔪K = xK + yK.
  Gates: gateR_np passed (|Syz₁| = 32 over BiDual — matches §0-4.2's predicted
  32; 128 over FatPoint3), gate0/1/1b/2 passed in ~1 min (pinned point = 16.2
  with ε² ↦ base-socle xy, S′-holds hand-checked). gate3 (first quantified
  UNSAT obligation) still running at session end — **harvest this log first**;
  the script aborts before the main table if any gate fails.
* **`scripts/order4sat_f8nofib.py` written, NOT launched** (box saturated): 𝔽₈
  analogue of Theorem B′, nofiber2 over Ext3(Z8) + Ext3(F2eps3) only — the
  ramified ring's nofiber2 pass is already inside `order4sat_f8ram.py`
  (verified by reading it). Launch when a big SAT job finishes.
* Theorem G audited per golden rule 4: `s2check.log` contains all 16 unsat
  lines + `DONE s2check` for exactly the eight rings named — claim sound.
* Kill of `search_nofib3`/`certs` blocked by the permission system again;
  still needs the user: `pkill -f search_nofib3.m2; pkill -f certs.m2`.
* No other job finished; §0-4.5's live-job table still accurate (plus
  s2check_np). Nothing new banked in the report this session.

---

## §0-4. Session-4 record (2026-07-08, night)

### 0-4.1 Harvest: Theorem F (minassoc) — the Target Lemma is proved

`minassoc.m2` reached `DONE` with **full success on both fibers**: all $[4]^\#$
coefficients (21 xy, 24 t⁴) lie in the ideal generated by **associativity +
Δ-multiplicativity equations alone** (no coassociativity, no fiber2), over every
𝔽₂-algebra k at ε³. Gates 16.1/16.2 printed 0 violations (top of `minassoc.log`);
xy closed at `DegreeLimit` 5, t⁴ at 6. Recorded as **Theorem F** in the report.
Consequences:
* THEORY §8's Target Lemma is now a theorem at arbitrary-k strength.
* Theorem D is complete (its hypotheses are strictly stronger than F's), for
  BOTH fibers — `search_nofib3.m2` is superseded; safe to kill (it was still
  running at session end; the auto-permission system declined a kill from this
  session, so it and `certs.m2` are still burning ~2 cores — **user may want to
  kill them by hand**: `pkill -f search_nofib3.m2; pkill -f certs.m2`).
* Theorem A at ε³ is also subsumed.

### 0-4.2 NEW: `scripts/s2check.py` — the S′ probe (Open Lemma 7.4 evidence)

Probes whether **S′** (THEORY §7: φ(I) ⊆ 𝔪(ker φ ∩ I)) holds for *every* rank-4
bialgebra with killed-by-2 local fiber over the curvilinear rings — i.e. whether
the invariant that Open Lemma 7.4 needs is simply **universal**, no liftability
hypothesis required. Quantifier-free encoding: for 𝔪 = (t) and under fiber2, the
solution set of t·k = φ(e_i), k ∈ I, is exactly one coset k₀ + ann(t)·I (this is
why gateR checks m = tR and computes ann(t) by enumeration — without fiber2 the
encoding would be unsound); "S′ fails at e_i" = one symbolic k₀ + a conjunction
over the 8 concrete coset shifts, all missing ker φ. Five gates, all passed
(`s2check.log`): gateR (m = tR by enumeration), gate0 (level-1 sat), gate1
(16.2 point: S′-FAIL unsat — S′ holds there by hand), gate1b (witness sat),
gate2 (Δ-mult dropped: S′-FAIL sat, matching ablate's [4]≠0 models), gate3
(S′-HOLDS ∧ S′-FAIL unsat — machine-checks coset completeness).

**Reading `[S2] -> unsat` over ring R:** S′ holds for every rank-4 bialgebra
with killed-by-2 local fiber over R ⟹ (THEORY Thm 7.1) **every free rank-4
bialgebra with killed-by-2 local fiber over EVERY socle-line extension R′ of R
is killed by 4** — including all non-curvilinear R′ no direct search has
covered (e.g. the ℤ/4[y]-type rings of §B.2, from the ℤ/4 probe). A `sat`
would be an S′-violating bialgebra (still killed by 4!) — NOT a Grothendieck
counterexample; it would refute universality of S′ and redirect Lemma 7.4.

**Results banked (both fibers each): 𝔽₂[ε]/ε², 𝔽₂[ε]/ε³, ℤ/4, ℤ/8,
ℤ[π]/(π²−2,π³) — all UNSAT** ⟹ **Theorem G + Corollary H** in the report.
The ε² result strengthens THEORY Prop 7.3(ii): ψ² = 0 for ALL first-order
deformations, liftable or not. Still running at session end: ε⁴, then ℤ/16,
ℤ[π]/(π²−2,π⁴); `--ext` flag adds 𝔽₄ variants (not launched). Harvest
`s2check.log`. Also launched: **`s2gen.m2`** (`s2gen.log`) = the M2
arbitrary-k upgrade at ε³ via the defect characterization δ_i = φ(φ(e_i)/ε)
(THEORY Prop 7.5.1); its gate is the 16.2 point (delta digits must evaluate
to 0) — check gate lines before citing. Note M2 buffers stdout when
redirected: `elapsedTime` (stderr) lines appear before the `<<` (stdout)
lines they belong after; the log fills in bursts.

**Design note for the REQUIRED next probe (non-principal 𝔪; see THEORY §7.5
caveat).** Over base 𝔽₂[x,y]/(x²,y²): 𝔪 = xR + yR, so S′ at e_i reads
∃ a,b ∈ ker φ ∩ I with φ(e_i) = x·a + y·b. The solution set of x·a + y·b = v
is a coset of the syzygy module Syz(x,y) ⊆ R³×R³, which is NOT a single
ann-shift: per coordinate, Syz₁ = {(α,β): xα + yβ = 0} has 32 elements
(α₀ = β₀ = 0, α₂ = β₁, rest free), so the brute-force "S′ fails" conjunction
is 32³ per pair-witness — too big to unroll naively. Either (i) use Z3
bitvector quantifiers: FAIL_i = ∀ a,b (24 bits): (xa + yb = φ(e_i)) →
¬(a,b ∈ K'), with MBQI — try this first, it may just work; or (ii) unroll
with symmetry reduction. NOTE: no defect shortcut here — changing the
division (a,b) within the coset CHANGES (φ(a), φ(b)) (the free syzygy
components are not in ann(𝔪)), unlike the curvilinear case of Prop 7.5.1.
Gates: port gate1/gate1b (a concrete pinned point over 𝔽₂[x,y]/(x²,y²) with
hand-checked S′), gate3 (HOLDS ∧ FAIL unsat). Ring class `BiDual` is already
ringcheck-validated.

**If the whole table lands UNSAT**, the natural next theorems to write:
(i) killedness over every length-4 Artin local 𝔽₂-base that is a socle
extension of ε³ (all of them are, in the Gorenstein case relevant by Prop 4.3
— check!); (ii) the mixed-char analogues from ℤ/4, ℤ/8, Rram probes; (iii) an
M2 ideal-membership upgrade of the S′ identity (arbitrary k) — the S′-defect
map δ: I_H → M⊗I_H is polynomial in the structure constants, so "δ-coefficients
∈ J" is a gensearch-style run; success would prove S′ universality per depth
for ALL 𝔽₂-algebras and turn the socle induction into a per-depth machine.
The real prize remains a uniform PROOF of S′-propagation (Lemma 7.4); the probe
tells you whether to attempt proving it or hunting for the obstruction.

### 0-4.2b Audit of the external theory handoff (`order4_theory_push_handoff.md`, GPT-5.5 Pro)

The user supplied an external theory push. Audit outcome (full detail in
THEORY §6.5):
* **Its §2 polarization argument is CORRECT as an implication** — and big:
  unconditional first-order $\psi^2=0$ over arbitrary coefficient algebras
  (+ the graded formula) ⟹ equal-char $\mathfrak m^3=0$ closed in ALL
  embedding dimensions. Also verified: Thm 6.2's proof never used the
  socle-step hypotheses (Remark 6.5.1), so that input is banked.
* **Its hypothesis audit FAILS as of the pre-session state**: it cites
  "Theorem A" for the first-order input, but Theorem A only gives $\psi^2=0$
  for deformations liftable to $\epsilon^3$ (Prop 7.3(ii)); the polarization
  quotients need the UNCONDITIONAL statement. This is exactly the failure
  mode of golden rule 4 — a plausible citation nobody checked. It happens
  to be REPAIRABLE with this session's tools:
  s2check's $\epsilon^2$ rows = the unconditional statement for $k=\mathbb F_2$;
  **`scripts/symbolsq.m2`** (launched, `symbolsq.log`) is the arbitrary-$k$
  ideal-membership upgrade (first-order equations only, M+A+F pass then +C).
  If it lands: **equal-char $\mathfrak m^3=0$, all embdims, killed by 4** —
  bank as a theorem, mark `len3gen` as audit-only, drop the embdim-3 plan.
* Its §5 module-theoretic counterexample (why S′ propagation needs the
  bialgebra axioms) checks out — recorded as THEORY Remark 7.5.5.
* Its "homogeneous-symbol lemma" framing (§3/§6) = equal-char-only
  alternative to Conjecture 7.5.4; its mixed-char symbol $\tau\cdot\mathrm{id}
  + \psi$ matches THEORY §6.2. Its `symbolspace.m2` proposal is subsumed by
  `symbolsq.m2` (membership > basis-listing). Its §10 suggested memory text
  OVERCLAIMS ("conditional only on Theorem A") — do not copy it.

### 0-4.3 ringcheck extended

`F2epsN(2)` (= 𝔽₂[ε]/ε²) and `Z2N(2)` (= ℤ/4) added to `ringcheck.py` CASES for
the probe (golden rule 1b); rerun logged in `ringcheck.log` after the
`RINGCHECK RERUN (session 4)` banner — both pass (chains [2,1], residue 𝔽₂),
all previously validated classes re-pass.

### 0-4.4 Report edits

Theorem F added; Theorem D rewritten as complete-via-F; ablation bullet updated
with the full ablate2 verdict table; harvest table refreshed; files table got
`minassoc` + `s2check` rows. THEORY §8 Target-Lemma paragraph updated to
"proved"; skeleton kept (a HAND proof read off the certificates is still the
route to depth-uniformity).

### 0-4.5 Session-4 live-job status (inherited jobs, at ~19:45 BST)

Same seven as §0.7 minus `order4sat --nofiber2` (done), with: `len3gen` xy at
`DegreeLimit` 4 (running since ~18:24); `search_eps45` ε⁴ at limit 4;
`z8search` at limit 5 (still 0/9); `certs` still silent (kill candidate);
`search_nofib3` superseded (kill candidate); `beyond` on ε⁶ xy level 2; `f8` on
𝔽₈[ε]/ε³ xy level 2; `f8ram` on W(𝔽₈)[π] xy level 2. Plus new: `s2check`.

---

## §0-3. Session-3 record (2026-07-08, evening)

Session 3 was a **theory** session (user prompt: compare square-zero deformation
theory of commutative vs noncommutative group schemes). Deliverable:
**`THEORY_order4.md`** — full proofs. Executive summary:

1. **Reduction theorem (proved):** arbitrary bases ⟶ Artin local rings with
   *finite residue field* (Thm 3.1 there; finite generation + Nullstellensatz
   over ℤ + Krull). Retires standing risk G.4 (imperfect residue fields).
2. **Rigidity (proved):** across a socle-line extension R′ → R′/M with fiber
   killed by 2, the obstruction d = [4]^# − ηε is *independent of the lift* of
   A/R (Thm 5.1). Corollary: a noncommutative deformation is killed by 4 as
   soon as ANY killed-by-4 (e.g. cocommutative, via Deligne) lift of the same
   A exists. This is the precise commutative-vs-noncommutative comparison.
3. **Graded formula (proved):** for 𝔪′³ = 0 the obstruction is
   d = Σ (t_α t_β) ⊗ ψ_β ψ_α in terms of the symbol of the squaring map
   (Thm 6.2). All banked theorems = instances of the polarized identities
   ψ_αψ_β + ψ_βψ_α = 0, ψ_α² = 0. Per nilpotency degree ν the *entire*
   equal-char problem is ONE finite Gröbner computation (Prop 6.3; embdim ≤ 45
   universal bound). The remaining infinite direction is depth ν only.
4. **S′ induction (proved except one lemma):** S′(A/R): φ(I) ⊆ 𝔪(ker φ ∩ I)
   implies every lift over every socle extension is killed by 4 (Thm 7.1).
   S′ ⟺ ψ² = 0 at length 2 (so Theorem A proves it there). **Open Lemma 7.4
   (propagation of S′) is now the single remaining theoretical gap.**
5. **Automatic antipodes (proved):** killed-by-2 fiber ⟹ S = id on the fiber,
   and antipodes lift over Artin local bases (Lemma 2.1). Bialgebra searches
   in this branch ARE group-scheme searches.

### New computations launched (harvest these)

| job | log | status at session end | reading |
|---|---|---|---|
| `ablate.py` | `ablate.log` | ✅ **DONE**, all gates OK | **Coassociativity NOT needed** for [4]^#=0 at ε³ (A+M+F unsat); **associativity NOT needed** (M+C+F unsat); **Δ-multiplicativity IS load-bearing** (A+C+F sat, witnesses in log). Both fibers. |
| `ablate2.py` | `ablate2.log` | ✅ **DONE**, gates OK | Minimal-axiom lattice, both fibers. xy-fiber: M sat, M+F sat, **M+A unsat**, M+C sat. t⁴-fiber: M sat, **M+F unsat, M+A unsat, M+C unsat**. ⟹ **{Δ-mult, associativity} is the common minimal set**; Target Lemma + hand-proof skeleton in THEORY §8. |
| `len3gen.m2` | `len3gen.log` | running; **ALL THREE GATES PASSED** (16.1 ✓, 16.2(s²) ✓ incl. φ(x) = s²·xy digit profile, 16.2′(st) ✓); xy-branch: DegLimit 3 done (147 s) with 16/48 coeffs nonzero ⟹ **32/48 already proved**; DegLimit 4 running | **Universal embdim-2 base k[s,t]/(s,t)³, arbitrary F₂-algebra k.** Full success ⟹ killed-by-4 over EVERY equal-char Artin local base with 𝔪³=0, dim 𝔪/𝔪² ≤ 2 (subsumes Theorem A; proves polarized ψ-identities). Partial GB results are proofs per coefficient, as usual. |
| `minassoc.m2` | `minassoc.log` | launched end of session (gensearch.m2 with J = assoc+compat ONLY — the ablation-minimal axiom set M+A; same gates as gensearch) | ideal-membership (arbitrary k) upgrade of the **Target Lemma** (THEORY §8): commutative associative rank-4 deformation + multiplicative counital Δ (no coassoc, no fiber2) ⟹ [4]^# = 0 at ε³. Success also subsumes Theorem D at ε³. |

### What session 3 changes about priorities

* The **highest-value theory target** is now Open Lemma 7.4 (kernel
  factorization propagates through socle steps). Everything else is finite
  computation. The ablation results say a proof attempt should work with
  Δ-multiplicativity + (co)associativity and may IGNORE the GS-cocycle
  machinery of coassociativity if q4 lands unsat.
* The **highest-value computations** are: (i) finish `len3gen` (closes all
  equal-char 𝔪³=0, embdim ≤ 2); (ii) an embdim-3 analogue
  k[t₁,t₂,t₃]/𝔪³ (10-digit basis — check feasibility; Gorenstein embdim-3
  bases are NOT covered by embdim-2, see THEORY §6.4); (iii) `z8search` +
  ramified analogue for mixed-char length-3 with general residue field;
  (iv) mixed-char depth 4 (ℤ/16) already queued in `order4sat_beyond`.
* `certs.m2` (silent since 15:48, ~15% CPU, no artifacts): its purpose
  (certificate mining for ψ²=0) is partially superseded by the ablation
  results, which localize the mechanism better than raw cofactors would.
  Killing it to free a core for len3gen is a reasonable call for the next
  session if it is still silent.
* Do NOT re-derive the report's Corollary C steps: still `[FLAG]`ed on
  Schoof Thm 1.2's stated generality (G.2), now referenced from THEORY §3.3
  and §11 as well.

---

## §0. Session-2 record (2026-07-08)

### 0.1 New: `scripts/ringcheck.py` — validation gate for the base-ring classes

Every SAT certificate is a statement about a *ring class*: a Python object supplying
`zero/one/var/add/sub/mul/eq0/neq0/lowzero/deform`. If a multiplication table or a
`deform` is wrong, `unsat` is vacuous — it says "no counterexample over a ring that
does not exist". **Nothing checked this before.** `ringcheck.py` now validates all
**18** ring classes actually used, along three independent axes:

1. **Ring axioms** on concrete elements — commutativity, associativity,
   distributivity, `a·1 = a`, `a·0 = 0`, `a−a = 0`, additive associativity.
   Exhaustive below 80 elements; sampled (40 elements, 14³ triples) above.
2. **Reference cross-check** against a wholly independent implementation:
   plain integer arithmetic for ℤ/2ᴺ; polynomial arithmetic reduced modulo the
   defining ideal for ℤ[π]/(π²−2,π³) and ℤ[π]/(π²−2,π⁴); monomial models for
   𝔽₂[x,y]/(x²,y²) and 𝔽₂[x,y]/(x,y)³; truncated polynomials for 𝔽₂[ε]/εᴺ.
3. **Local-ring semantics**: m := {x : `lowzero`(x)} is an ideal; **every element
   outside m is a unit** (this, not the codimension count, is what makes m maximal
   and R local); m is nilpotent, with the computed chain |mᵏ| matching the intended
   length; and `deform(tag)` ranges over **exactly** m — both inclusions decided
   symbolically by Z3 (`Not(lowzero(deform))` is `unsat`; each element of m is
   attained).

**All 18 pass** (`scripts/ringcheck.log`). Selected output, useful as a fingerprint:

| ring | \|R\| | \|m\| | residue | \|mᵏ\| chain |
|---|---|---|---|---|
| 𝔽₂[ε]/ε³ | 8 | 4 | 𝔽₂ | [4, 2, 1] |
| ℤ/8 | 8 | 4 | 𝔽₂ | [4, 2, 1] |
| ℤ[π]/(π²−2,π³) | 8 | 4 | 𝔽₂ | [4, 2, 1] |
| 𝔽₂[x,y]/(x²,y²) | 16 | 8 | 𝔽₂ | [8, 2, 1] |
| ℤ[π]/(π²−2,π⁴) | 16 | 8 | 𝔽₂ | [8, 4, 2, 1] |
| 𝔽₂[x,y]/(x,y)³ | 64 | 32 | 𝔽₂ | [32, 8, 1] |
| 𝔽₂[ε]/ε⁶ | 64 | 32 | 𝔽₂ | [32,16,8,4,2,1] |
| W(𝔽₄)/8 = ℤ/8[w]/(w²+w+1) | 64 | 16 | 𝔽₄ | [16, 4, 1] |
| W(𝔽₈)/8 = ℤ/8[w]/(w³−w−1) | 512 | 64 | 𝔽₈ | [64, 8, 1] |
| W(𝔽₈)[π]/(π²−2,π³) | 512 | 64 | 𝔽₈ | [64, 8, 1] |

For the extension wrappers `Ext`/`Ext3` the check is sharper: it **recomputes the
minimal polynomial of w** from the implemented product and verifies that *its
reduction mod m is irreducible*. Since m_{R[w]} = m_R·R[w] by construction of
`lowzero`, and R[w] is free of the right rank, this certifies the wrapper really is
*the* unramified extension (unique up to isomorphism) with residue field 𝔽₄ / 𝔽₈.

Sizes: locality is exhaustive up to 512 elements (`LOCAL_CAP`); the only class above
that is `Ext(FatPoint3)` (4096 elements), whose locality is **skipped** and reported
as a `NOTE partial coverage` line. Runtime ≈ 15 min under `nice`.

> **Correction it found.** `Ext3` in `order4sat_f8.py` was named and documented as
> R[w]/(w³+w+1), but it reduces using **w³ = w + 1** (it uses `add` throughout, no
> sign), i.e. it implements R[w]/(w³−w−1). Over a characteristic-2 base these
> coincide; over ℤ/8 they do **not** — verified numerically: in `Ext3(Z8())`,
> `w³ = (1,1,0)` so `w³+w+1 = (2,2,0) ≠ 0` while `w³−w−1 = 0`.
> **The mathematics is unaffected**: w³−w−1 reduces mod 2 to the irreducible
> w³+w+1, and any monic lift of an irreducible polynomial presents the same
> unramified extension, so the ring is W(𝔽₈)/8 either way. The name has been
> corrected in `order4sat_f8.py`. Had the intended lift mattered, this would have
> been a silent error underneath the headline 𝔽₈ result.

### 0.2 Results banked this session

All SAT results below are Z3 bitvector UNSAT with exact arithmetic; "✓✓" = UNSAT for
**both** fiber shapes (𝔽_q[x,y]/(x²,y²) and 𝔽_q[t]/t⁴).

* `order4sat_beyond`: **𝔽₂[ε]/ε⁴ ✓✓**, **𝔽₂[ε]/ε⁵ ✓✓** (fiber2 = True).
  ⇒ **Theorem E** in the report. These are the first bases of **length > 3**, i.e.
  outside the reach of Corollary C.
* `order4sat_f8`: **W(𝔽₈)/8 ✓✓** (fiber2 = True) ⇒ Theorem B extended to residue
  field 𝔽₈.
* `order4sat --nofiber2`: ✅ **`DONE order4sat` — all 12 (ring, fiber) queries UNSAT**,
  both fibers for each of 𝔽₂[ε]/ε³, ℤ/8, ℤ[π]/(π²−2,π³), 𝔽₄[ε]/ε³, W(𝔽₄)/8,
  W(𝔽₄)[π]/(π²−2,π³); zero level-2 `sat`. ⇒ **Theorem B′ is complete.** All six ring
  classes are in the `ringcheck.py` validated set, so this rests on verified arithmetic.
  Because `fiber2=False` is the *weaker* hypothesis, B′ subsumes Theorem B over these
  six rings; B retains independent content only for W(𝔽₈)/8, where no no-fiber2 pass
  has been run. (Cheap follow-up: add W(𝔽₈)/8 and W(𝔽₈)[π] to a `--nofiber2` pass.)
* `search_nofib3` (M2, arbitrary 𝔽₂-algebra k, ε³, **no** fiber2, x,y fiber):
  `DegreeLimit 4` completed in **5091.93 s**, leaving **2 of 21** [4]^# coefficients
  unreduced (down from 7/21 at limit 3). `DegreeLimit 5` running.
  ⇒ **Theorem D is now partially proved: 19 of 21 coefficients are in J.**

> **Why 19/21 is a *proof*, not a partial credit.** Reducing a coefficient to 0
> against a *partial* Gröbner basis already exhibits an explicit cofactor
> representation b = Σ qᵢgᵢ. Truncating the GB weakens nothing about the
> coefficients it does kill. So those 19 are settled over **every** 𝔽₂-algebra k at
> once — full Theorem-A strength — regardless of whether the run ever terminates.
> Read every truncated-GB log this way: "n/N nonzero remainders" means **N−n
> coefficients are proved**, not "nothing proved yet".

### 0.3 Determinism of the M2 pipeline — now actually tested

The recovery advice in §A ("just re-run the script, everything is deterministic")
was an assumption the whole crash-recovery plan rests on, and had never been checked
against a real restart. It has now been: after the 15:48 restart, `search_nofib3`
reproduced **exactly** 2/21 nonzero remainders at `DegreeLimit 4`, matching the
pre-restart record. The assumption holds.

### 0.4 Two claims that ran ahead of their evidence

Both are the same failure mode — a load-bearing assertion nobody had checked — and
they are why golden rules 1b and 4 exist:

1. **`Ext3` mislabelling** (§0.1). Benign only by luck.
2. **Theorem B′ over-claim.** It was written asserting all six rings when the log
   contained completed evidence for only three (𝔽₂[ε]/ε³, ℤ/8, ℤ[π]/(π²−2,π³)) plus
   one level-1 line. The post-restart re-run has since terminated and supplied all 12
   queries, so B′ **is now true as stated**. Note what happened, though: it was
   asserted before it was known, and it came out right. That is exactly the failure
   mode that is invisible when it happens to land — the next one need not.

**Still unverified, and no script will close it:** Theorem E's *group-scheme*
conclusion (as opposed to its bialgebra statement) leans on steps 1 and 3 of
Corollary C's proof being pure theory, valid over any Artin local base with perfect
residue field rather than only length ≤ 3. That reading was taken from the report
and **not re-derived**. Specifically, check:
* step 1 (connected-étale sequence over henselian local R; orders (1,4) → Deligne,
  (2,2) → Tate–Oort order 2 twice) — believed base-length-independent;
* step 3 (fiber *not* killed by 2 ⇒ after base change to R ⊗̂ W(𝔽̄₂), Schoof's
  classification gives μ₄ or α₂⋊μ₂; then multiplicative rigidity / Schoof Thm 1.2)
  — Schoof Thm 1.2 is stated for "any local Artin base", so this should be fine,
  **but verify against the paper before the theorem leaves the file.**
Only step 2 consumes the SAT result, and step 2 needs the residue field to be
perfect (𝔽₂ is) and the fiber-shape theorem.

### 0.5 Anomaly worth watching

`certs.m2` has run **1 h 29 m at ~54 % CPU and produced no log output beyond the
restart banner**, and neither `certs_xy.m2out` nor `certs_t4.m2out` exists yet. It
may simply be slow (it extracts explicit cofactors, which is harder than deciding
membership), but it is the one job whose silence is not explained by a visible
`DegreeLimit` ladder. If it is still silent after a few more hours, consider killing
it and re-deriving certificates only for the coefficients you actually need for the
ψ² = 0 story (§E.1).

### 0.6 Process notes / traps in reading the logs

* The four M2 jobs and `order4sat --nofiber2` were restarted at **15:48:59** and
  **re-run from scratch** — they have **no resume logic**. Their pre-restart log
  lines are the only record of the earlier passes, and the logs are append-only, so
  a `RESTARTED DETACHED` banner sits mid-file. Use
  `awk '/RESTARTED/{p=1} p' <log>` to read only the current pass.
* `order4sat_beyond.py` is **different**: its `jobs` list at line ~111 is
  *hand-edited* to skip finished work (`# eps^4 ... already UNSAT -- see log above`).
  That is why its log appears to resume mid-list rather than restart. If you restart
  it, re-check which jobs the list currently contains.
* `pgrep -f <script>` will match your own `until ! pgrep -f <script>` wait-loop and
  never terminate. Match on the interpreter, or exclude `tail`/`grep`.

### 0.7 Live state at 17:17 BST (8 jobs, ~1 h 29 m elapsed; f8ram 18 m)

| job | last line | reading |
|---|---|---|
| `order4sat_beyond` | ε⁶, x,y fiber, level-1 `sat` | level-2 grinding |
| `order4sat_f8` | 𝔽₈[ε]/ε³, x,y fiber, level-1 `sat` | level-2 grinding |
| `order4sat_f8ram` | W(𝔽₈)[π], x,y fiber, level-1 `sat` ✓ | sanity gate passed; level-2 grinding |
| `order4sat --nofiber2` | ✅ **`DONE order4sat`**, 12/12 UNSAT | Theorem B′ complete |
| `search_eps45` | `DegreeLimit 4` | 12/30 coeffs nonzero at limit 3 ⇒ 18/30 proved |
| `search_nofib3` | `DegreeLimit 5` | 2/21 nonzero at limit 4 ⇒ **19/21 proved** |
| `z8search` | `DegreeLimit 5` | 9/9 nonzero at limit 4 ⇒ 0/9 proved so far |
| `certs` | (silent, see §0.5) | no artifacts yet |

---

## A. Harvest the still-running computations (purely mechanical)

> **Status in this table is session-2 vintage — the CURRENT live-job list is
> §0-7.4 and the work queue is §0-7.5.** `search_nofib3` and `certs` are dead
> and superseded (Theorem F); `order4sat --nofiber2`, `s2check`, `s2check_np`,
> `s2check --deeper`, `minassoc`, `ablate`, `ablate2` are DONE and banked. The
> per-log *reading instructions* below remain correct.

Each job ends with a `DONE ...` line when finished. If a process died, just re-run
the script — everything is deterministic and self-contained (now empirically
confirmed, §0.3).

| log (in `scripts/`) | what it decides | how to read the result |
|---|---|---|
| `order4sat_beyond.log` | SAT over ε⁵, ε⁶, ℤ/16, ℤ/32, ℤ[π]/(π²−2,π⁴), 𝔽₂[x,y]/(x²,y²) and 𝔽₂[x,y]/(x,y)³ as **bases**, + 𝔽₄ extensions; then a no-fiber2 pass | every `[2: + [4]^# != 0] -> unsat` line = "no order-4 counterexample over that ring (bialgebra level)". Any `sat` at level 2 → §D protocol. |
| `order4sat_f8.log` | same over W(𝔽₈)/8 and 𝔽₈[ε]/ε³ | same reading. W(𝔽₈)/8 ✓✓ already banked |
| `order4sat_f8ram.log` | **new**: W(𝔽₈)[π]/(π²−2,π³), both fibers, fiber2 on and off | same reading. Completes residue field 𝔽₈ — see §B.0 |
| `search_eps45.log` | M2 ideal membership for ε⁴, ε⁵ (arbitrary base k) | success = `ALL P4 coefficients lie in J`; failure = `NOT all in J` after full gb → check the printed Frobenius-power lines (radical membership still closes the branch for field-valued points). **Partial logs are partial proofs** (§0.2) |
| `search_nofib3.log` (supersedes the truncated `search_deeper.log` run) | M2 ideal membership for ε³ **without** fiber2 | 19/21 coefficients already proved; 2 remain at `DegreeLimit 5`. SAT already confirms k = 𝔽₂, 𝔽₄ (`order4sat_nofib.log`) |
| `z8search.log` | GB over ℤ: upgrades the ℤ/8 SAT result to **all ℤ/8-algebras** (e.g. W(𝔽₂ʳ)/8 for every r at once) | same reading; may run very long. If still stuck after ~a day of CPU, kill it and record "open: unramified mixed char for general residue field 𝔽₂ʳ, r ≥ 4; 𝔽₂, 𝔽₄, 𝔽₈ done by SAT" |
| `certs.log` + `certs_xy.m2out`, `certs_t4.m2out` | explicit cofactor certificates for Theorem A | success = `all N certificates verified by direct multiplication` and the two `.m2out` files exist. See the anomaly note §0.5 |

After harvesting: update the results table and the theorem statements in
`REPORT_order4.md` (§4.1 is the harvest table), and update the memory file. That
alone is a useful session. **Check golden rule 4 while you do it.**

## B. Extend coverage to more base rings (template work, low risk)

The fastest value-per-effort: add rings to the Z3 framework. Copy the pattern of
`scripts/order4sat_beyond.py` (class with `zero/one/var/add/sub/mul/eq0/neq0/
lowzero/deform`, then `run(R, fibname, fib)`). The generic `F2Quot` class handles
**any** finite local 𝔽₂-algebra base: you only supply a basis and multiplication
table. `Ext`/`Ext3` wrap any base to residue field 𝔽₄/𝔽₈. **Add every new class to
`ringcheck.py`'s `CASES` and run it before searching over the ring** (golden rule 1b).

0. **Started this session, harvest first:** `order4sat_f8ram.py` adds
   W(𝔽₈)[π]/(π²−2,π³) = `Ext3(Rram())` (ring pre-validated; level-1 sanity `sat` ✓).
   When it and `𝔽₈[ε]/ε³` (in `order4sat_f8`) both come back UNSAT, all three
   length-3 rings with residue field 𝔽₈ — k[ε]/ε³, W(k)/8, W(k)[π]/(π²−2,π³) — are
   closed and **Corollary C extends to residue field 𝔽₈**. Cheapest remaining theorem.
   (The classification input: for m² ≠ 0 and length 3 the maximal ideal is principal,
   and π² = 2u ∼ 2 after a unit change of π because Frobenius is surjective on 𝔽_{2ʳ}ˣ.)
0b. **Cheap, newly exposed by B′ completing:** the 𝔽₈ rings have only been run with
   `fiber2=True`. Add W(𝔽₈)/8, 𝔽₈[ε]/ε³, W(𝔽₈)[π]/(π²−2,π³) to a `--nofiber2` pass
   (all three classes already validated). That would give the 𝔽₈ analogue of Theorem
   B′ and make the 𝔽₈ case unconditional on the fiber, exactly as for 𝔽₂ and 𝔽₄.
1. Remaining length-4 equal-char bases with non-principal m:
   enumerate the local 𝔽₂-algebras of length 4, 5 — each is a small `F2Quot` table.
   (Length ≤ 3, and 𝔽₂[x,y]/(x²,y²), 𝔽₂[x,y]/(x,y)³, are done or queued.)
   *Caution:* the length-4 classification with dim m/m² = 2 is a classification of
   quadratic forms in char 2 and has genuine subtleties — do not hand-wave it; write
   each candidate as an explicit table and let `ringcheck.py` confirm |mᵏ| and locality.
2. Mixed char, non-principal m: e.g. ℤ/4[y]/(y³, 2y) type rings — these need a new
   small ring class (element = pair (a, b) with the right moduli); *validate against
   μ₄ analogues where possible*, and against a reference model in `ringcheck.py`.
3. Ramified length 5–6: ℤ[π]/(π²−2, π⁵) (element = a + bπ, a ∈ ℤ/8, b ∈ ℤ/4 —
   careful: **mixed moduli**). `ringcheck.py` already has the pattern: see
   `ref_check_Rram` / `ref_check_Rram4`, which compare against
   `_poly_mul_pi(x, y, mod_a, mod_b)`. Add the new class there first.
4. If some level-2 query is slow: that is normal for bigger rings (bit-blast size
   grows with |R|; the 512-element 𝔽₈ rings are by far the slowest). Let it run
   hours. Set `s.set("timeout", ...)` higher if needed.

Each new UNSAT extends the theorem "every finite locally free group scheme of
order 4 over ⟨ring⟩ with local special fiber is killed by 4" (with the fiber2-free
variant it is unconditional on the fiber, given the connected-étale + order-2
reductions in `REPORT_order4.md` §1, Corollary C).

**Sanity check for every new ring class:** level-1 (`bialgebra+fiber2, no extra
condition`) must come back `sat`. If it comes back `unsat`, your ring arithmetic
or the fiber table is wrong (μ₂×μ₂ always exists!). Stop and debug. This is *weaker*
than `ringcheck.py` — run both.

**Fiber tables** (hand-audited session 2, both correct): in `build()`,
`fib` maps (i,j,r) ↦ 1 meaning e_i e_j ∋ e_r. For 𝔽_q[x,y]/(x²,y²) with
e₁=x, e₂=y, e₃=xy: `{(1,2,3):1}`. For 𝔽_q[t]/t⁴ with e₁=t, e₂=t², e₃=t³:
`{(1,1,2):1, (1,2,3):1}`. The e₀-coefficient of e_i e_j (i,j ≥ 1) is forced to 0 —
this is *not* a loss of generality: it says the augmentation ideal I = ⟨e₁,e₂,e₃⟩ is
an ideal, which it is, and A = R·1 ⊕ I as R-modules via the unit and counit.
Likewise Δ(e_i) = e_i⊗1 + 1⊗e_i + Σ c_{ijk} e_j⊗e_k is the fully general counital
comultiplication (apply (ε⊗id)Δ = id to see the other coefficients are forced).

## C. The M2 (all-parameter-rings) upgrades — babysitting GB runs

The M2 scripts prove identities over arbitrary coefficient algebras, which SAT
cannot. If you want to strengthen SAT results to M2-grade:
- Equal char, deeper ε or other fibers: edit the `runAll(NN, useFiber2, fib, name)`
  calls at the bottom of `scripts/search_deeper.m2` (the function is generic in NN).
- If a GB stalls: (i) try smaller `DegreeLimit` first and check whether the
  remainders are already 0 — **a partial GB certificate is still a proof of
  membership** (see §0.2, and note this is how Theorem D got to 19/21);
  (ii) reduce variables by eliminating Δ(e₃) — it is determined by Δ(e₁)Δ(e₂) via
  the compat equation because the e₃-coefficient of e₁e₂ is a unit; this removes
  27·NN of the c-variables (needs careful re-derivation — only do this if you are
  comfortable; otherwise leave GB running overnight).
- Mixed char generalization of `z8search.m2` to ramified rings: replace the base
  ℤ[c,d,w] by ℤ[pi, c, d, w] and add generators (pi^2 - 2, pi^3) — i.e., work in
  ℤ[π]/(π²−2,π³)-algebras; deformations become pi*d. Membership of the P4
  coordinates in J then covers all such algebras. Validate with a μ₄-analogue first.
- `z8search` is the one that would give **all ℤ/8-algebras at once** (hence
  W(𝔽_{2ʳ})/8 for every r simultaneously, superseding the per-r SAT runs). It has
  0/9 coordinates reduced through `DegreeLimit 4` — the least promising of the GB
  jobs so far.

## D. If any query ever returns SAT at level 2 (possible counterexample!)

Do **not** announce a counterexample until every box is checked:
1. Extract the model (the scripts print nonzero assignments). Reconstruct A
   explicitly: write out the 4×4 multiplication table and Δ(e₁), Δ(e₂), Δ(e₃).
2. Verify *independently of Z3* (in M2 or by a fresh Python script with plain
   integer arithmetic): associativity, Δ multiplicativity, coassociativity, counit,
   fiber2 (if claimed), and recompute [2]^# and [4]^# from scratch.
3. Check level 3 (antipode). A bialgebra without antipode is a *monoid scheme*,
   not a group scheme — interesting but NOT a counterexample to Grothendieck.
   (Beware: over mixed-char rings there exist étale idempotent monoid bialgebras
   violating "killed by order" at rank 2 already; local fiber shape excludes them,
   but stay alert.)
4. Check freeness/flatness is manifest (it is, by construction — structure
   constants on a free module — but confirm the fiber really is the intended local
   algebra: reduce the multiplication table mod m).
5. **Re-run `ringcheck.py` on the base ring in question.** A `sat` at level 2 is at
   least as likely to be a broken ring class as a counterexample.
6. Only then: write up R, A, Δ, S, ε explicitly, compute [2]^#(e_i), [4]^#(e_i),
   exhibit the nonzero coefficient, and flag the session for the user. This would
   be a negative answer to a 60-year-old question — triple-check.

## E. Theory tasks (optional, hard — attempt only with spare capacity)

1. **Certificate mining.** Read `certs_xy.m2out` / `certs_t4.m2out` (once they
   exist — see §0.5); try to simplify the cofactors (most b's are ε²-digit
   coefficients; the certificate should reveal which two Hopf identities multiply to
   kill ψ²). Goal: a human-readable proof of "ψ² = 0" where ψ = μ₀Δ₁ + μ₁Δ₀ is the
   ε-divided squaring map of a first-order deformation (a Gerstenhaber–Schack
   2-cocycle of the fiber bialgebra). This would likely give all k[ε]/ε^N at once by
   induction: the top ε-layer of [4]^# is an ε-point-derivation killed on I², cf.
   REPORT §5. **The ε⁴/ε⁵ SAT results (Theorem E) are evidence this induction is
   true** — a proof would supersede them and every future εᴺ run.
2. **General equal-char Artin local base.** Note k[x,y]/(x²,y²) does *not* embed
   in a product of curvilinear rings (functions x·y die on every arc — see report),
   so principal-m results do not formally suffice; the SAT results for
   𝔽₂[x,y]/(x,y)³ and 𝔽₂[x,y]/(x²,y²) bases are the data points. A uniform proof
   probably goes through the deformation-cohomology route of item 1.
3. **Order p², odd p.** All machinery generalizes (rank p², fibers
   k[x,y]/(xᵖ,yᵖ) and k[t]/t^{p²}, base W(k)/p³ etc.); sizes grow but p = 3 SAT
   (𝔽₃ digits / ℤ/27 bitvectors — use integers mod 27 in Z3 via `BitVec(·,5)` with
   explicit mod-27 reduction, or better use Z3 integers with bounded quantifiers —
   or M2 GB over 𝔽₃ exactly as in `gensearch.m2`, which is the safer port) is
   plausibly feasible. The equal-char M2 port is mechanical: change `kk = ZZ/3`,
   fiber tables to the p = 3 shapes, digits 0..2 of ε. **Careful:** the code exploits
   [4] = [2]∘[2]; for p = 3 that identity is unavailable. Use
   [3]^# = mult₁₂₃ ∘ (Δ⊗id) ∘ Δ and [9]^# = [3]^#∘[3]^#. Validate on α₃⋊μ₃.
   Note `ringcheck.py`'s residue-field logic assumes characteristic 2 in
   `_residue_bits`; generalize it before reusing.
4. **Do not** waste time re-searching the fixed-algebra branches (handoff §2/§17):
   they are provably empty (REPORT §2).

## F. Session bookkeeping

- Keep results in `REPORT_order4.md` (tables + theorem statements; §3.1 documents the
  ring-validation gate, §4.1 is the harvest table); keep `scripts/` self-contained and
  deterministic; log files stay next to scripts.
- Update the memory file `grothendieck-order4-project` at the end of each session
  (what finished, what's still open) so the next session starts warm.
- The relevant literature anchors: Schoof, *Compositio* 128 (2001); Torti,
  arXiv:2411.12129; Schoof's survey in *Open Problems in Arithmetic Algebraic
  Geometry* (2019). Anything claiming to settle p² in mixed characteristic beyond
  the above would be new — search arXiv before big pushes.

## G. Standing risks (read before writing anything down as proved)

1. **Report ≠ evidence** (golden rule 4). Two instances already, §0.4.
2. **Theorem E's group-scheme step is un-re-derived** (§0.4). It is the only place
   where a *theory* input silently widens a SAT result from "no bialgebra over this
   exact ring" to "no group scheme over this base". Verify Schoof Thm 1.2's stated
   generality against the paper.
3. **SAT quantifies over exact finite rings only.** Theorem E covers
   𝔽₂[ε]/ε⁴, ε⁵ with residue field *exactly* 𝔽₂ — not k[ε]/εᴺ for general
   𝔽₂-algebras k, which is what Theorem A gives for ε³. `search_eps45.m2` is the
   upgrade and has **not** terminated (18/30 coefficients proved at `DegreeLimit 3`).
4. **Imperfect residue fields are not covered** by the fiber-shape theorem. Theorem
   A's arbitrary-k statement covers non-perfect equal-char cases only *with* the
   fiber-shape assumption imposed by hand.
5. `ringcheck.py` samples (does not exhaust) the axioms for rings above 80 elements,
   and skips locality above 512. `Ext(FatPoint3)` is the only class in the second
   category. Sampling is seeded (`random.seed(20260708)`), so it is reproducible but
   not a proof.
