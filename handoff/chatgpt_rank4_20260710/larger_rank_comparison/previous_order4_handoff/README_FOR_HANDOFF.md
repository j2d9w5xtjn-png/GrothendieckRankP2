# Grothendieck's "killed by order" question, n = 4 — handoff package v4

This archive contains the complete state of a computer-assisted attack on
Grothendieck's question (*is every finite locally free group scheme of order
$n$ killed by $n$?*) in the first genuinely open case, $n = 4$. It is the
fourth package handed back to an external agent; your fifth note
(`order4_fifth_push_relative_defect.md`) is answered below.

## What happened to your fifth note — and the headlines

**All three of your structural results are BANKED** (audit:
`THEORY_order4.md` §15 — read it first):

* **Lemma 1.1 (top defect kills products): CORRECT**, with two supplements:
  the well-definedness bookkeeping for $\Omega$ (uses $\varphi'^2 = 0$
  twice), and the observation that your proof is CHARACTERISTIC-FREE — it
  holds over every curvilinear Artin local socle step, mixed characteristic
  included (§15.2.1). Combined with Proposition 7.5.1 this gives the
  operative **cotangent reduction** (§15.2.2): at every depth, S′ relative
  to an S′-truncation is exactly $\Omega(t) = 0$ (resp.
  $\Omega(x) = \Omega(y) = 0$).
* **Lemma 2.1 (pairwise nilpotence): CORRECT** — and it needs only the
  WEAKER banked shape facts (image in $kx + kz$ etc.), not the sharpened
  session-10 forms (§15.3). Machine gate `unsat` ✓✓ both fibers over the
  NEW ringcheck-validated class $\mathbb F_2[u,v]/(u,v)^2$.
* **Your §3 corollary is now THEOREM N** (§15.4): S′ universal over every
  equal-characteristic square-zero base, in EVERY embedding dimension.
  Machine gate: S′-FAIL `unsat` ✓✓ over $\mathbb F_2[u,v]/(u,v)^2$ — the
  first direct square-zero embdim-2 probe.
* **Bidual calculus (§4): CORRECT** (both boxed lifting equations
  recomputed); sharpened to 15.5.1: over EVERY $\mathfrak m^3 = 0$ base
  (any characteristic, any embdim), product classes have EXPLICIT kernel
  divisions unconditionally — via the basis change
  $\{e_1, e_2, e_3\} \to \{e_1, e_2, e_1e_2\}$. This powers a new attack
  on the FatPoint3/$xy$ gap (`s2check_np3.py`: FAIL restricted to the two
  cotangent generators + split per-generator queries).
* **Your open s = 5 component $D_5(1,3)$ is CLOSED at $k = \mathbb F_2$**
  (`s5gates.log`, `unsat`, no timeout — took ~15 min here) along with the
  four product rows you had no verdicts for. All nine $D_5$ components now
  `unsat` at $\mathbb F_2$.

**Independent headlines from this session:**

* **THEOREM M($t^4$) BANKED** (`THEORY` §14.9): `s4t4gen` certified ALL
  scalars of the audited 12.6.6(e) assembly at arbitrary-$k'$ strength
  (including $\Lambda + bB^2$, the last one). With your M($xy$):
  **the curvilinear equal-char story is closed at depth 4** —
  S′-universality over $k'[\epsilon]/\epsilon^4$, killedness over
  $k'[\epsilon]/\epsilon^5$ + all socle-line extensions of $\epsilon^4$.
* **s = 5 at arbitrary-$k'$ strength is in flight**: `s5t4gen.m2` /
  `s5xygen.m2` — your cotangent reduction cut the targets to the cotangent
  rows, and the banked s ≤ 4 identities are adjoined as generators
  ("banked boost"; results read as vanishing-on-solutions). Check their
  logs for `COTANGENT ROW ... in J_aug`.
* **New MIXED-CHAR S′ result** (`s2check_ext.log`): S′ universal over
  $W(\mathbb F_4)/8$ ✓✓ (both fibers) — the first S′ result with residue
  field $> \mathbb F_2$ in mixed characteristic. The ramified
  $W(\mathbb F_4)[\pi]/(\pi^2{-}2,\pi^3)$ rows are in flight (no S2
  verdict yet at pack time — check the log).
* **The uniform target has a new clean formulation** (`THEORY` §15.8):
  the divided squaring $\Phi := \varphi/\epsilon$ satisfies
  $\Phi(\epsilon x) = \epsilon\Phi(x)$ and $\Phi(xy) =
  \epsilon\,\Phi(x)\Phi(y)$; **Conjecture $\Phi$**: $\Phi^2 = 0$ exactly,
  for every tower — equivalent to curvilinear equal-char S′-universality.
  And an exact **edge/suspension split** (§15.8.4):
  $D_{N+1} = \{\Psi_1, \Psi_N\} + \Sigma^{\uparrow}_{N-1}$ with
  $\Sigma^{\uparrow}$ the index-suspended sum; if suspension sums vanish
  (being probed: `s6probe.py` discovery rows), the whole uniform lemma
  reduces to the scalar-shaped edge family
  $(\Psi_Nt)_t(Bt^2{+}Ct^3) + B\Psi_N(t^2) + C\Psi_N(t^3) = 0$.

## What we ask for this round

1. **Prove the uniform cotangent lemma** — now in its sharpest form ever:
   Conjecture $\Phi$ (§15.8.2) via the §15.8.3 recursion. **The route is
   already decided for you** (§15.8.5): `s6probe`'s suspension discovery
   rows returned `sat`, so the edge/suspension decoupling FAILS — do NOT
   attempt term-by-term splitting; the cancellation is globally coupled,
   and the missing piece is control of $\Phi$-VALUES (not
   $\Phi^2$-values) on kernel lifts — the $D$-map of §15.6, i.e. the
   relative first-order lemma in its 15.2.2 cotangent form. Same-run
   bonus data: all nine $D_6$ components `unsat` at $\mathbb F_2$ (s = 6,
   one depth beyond all previous probes) — the conjecture keeps being
   true.
2. **The bidual boxed equations at arbitrary $k$** (§15.5): show
   $TPg + Pa_g \in \operatorname{im}Q$ and $TQg + Q(Tg{+}a_g) \in
   \operatorname{im}P$ are simultaneously solvable, using the shape theory
   of $P, Q$ (Theorem I) and a $uv$-layer analogue of the $\Psi_2$
   identities that still needs deriving. With Theorem N as base case this
   would give the first non-principal INDUCTION STEP by hand.
3. **Mixed-characteristic layers**: your Lemma 1.1 being characteristic-free
   (§15.2.1) transports the cotangent reduction to $\mathbb Z/2^N$ towers
   for free; the missing piece is only the mixed-char analogue of the
   FIRST-ORDER shape theory (Theorem I with Witt carries). The new
   $W(\mathbb F_4)$ S′ data points say it is all true.
4. *(housekeeping, unchanged)* A leaner route to M($xy$) avoiding the
   split-model classification would remove the perfect-subfield proviso;
   recall coassociativity is load-bearing for $xy$ (GX9nc).

Do NOT re-derive what is banked: Theorems A–N and Corollaries C, H, J
(`REPORT_order4.md` §1), the $s \le 4$ layer identities, the cotangent
reduction, and your own five notes' content (§6.5, §13, §14, §14.8, §15).

## Reading order
1. **`REPORT_order4.md`** — results actually established + the live job
   table (§4.1, updated session 13).
2. **`THEORY_order4.md`** — all hand proofs. Frontier sections: **§15**
   (your fifth note's audit + Theorem N + Conjecture $\Phi$ + the
   edge/suspension split), §14.9 (Theorem M($t^4$)), §13, §12.6.6.
3. **`HANDOFF_NEXT.md`** — golden rules (esp. rule 4: never cite a theorem
   without checking its log) and per-job status; session banners at the
   top supersede stale "running" claims below.
4. **`scripts/JOBS.md`** — canonical job table + `relaunch_all.sh` (the
   machine crashes often; this is the recovery path).
5. **`macaulay2_handoff_order4.md`** — original problem setup + the §16
   validation gates every equation-generating script must pass.
6. Your five earlier notes — kept for provenance; audited in §6.5, §13,
   §14.6, §14.1–14.5/§14.8, §15 respectively.

## `scripts/`
Every computational artifact with its `.log` beside it. Two toolchains:
- **Macaulay2** (`*.m2`, `/opt/homebrew/bin/M2 --script <file>`): Gröbner
  ideal-membership certificates — valid over *every* $\mathbb F_2$-algebra
  at once. A target reduced to 0 against even a *partial* (DegreeLimit)
  basis is a complete proof for that target. (But a partial basis failing
  to reduce a PRODUCT of certified targets means nothing — ideal algebra
  can close it by hand, cf. $aB^3 = B^2(aB)$.) NEW in v4: the "banked
  boost" pattern (`s5t4gen.m2` header) — banked identities adjoined as
  generators; results then read as vanishing-on-solutions, equally good
  for killedness theorems.
- **Z3 / Python** (`*.py`, venv `~/.venvs/z3env/bin/python`): bitvector
  `unsat` certificates over specific finite rings.
- **`ringcheck.py`** validates base-ring classes; rerun after touching any
  (session-13 rerun with the new FatPoint2 class: `ALL RING CHECKS
  PASSED`). (Exception: `ExtD` in `s4cert.py` is deliberately NOT
  Artin-local — self-gated in-script; do not add it to ringcheck.)
- Your bundles are preserved at `scripts/xy_s4_bundle/` and
  `scripts/fifth_push_bundle/`.

## Verification status at pack time
Running: `s5t4gen.m2`, `s5xygen.m2` (THE decisive s = 5 jobs),
`s4t4gen.m2` (belt-and-braces deg-6+), `s4cert.py` (F₄ battery, nearly
done), `s4xycert.py` (queued behind it), `s3xy2gates --f4only` (Theorem
L's F₄ half), `s2check_np3.py` (FatPoint3/$xy$ gap, third encoding),
`s2check.py --ext` (ramified $W(\mathbb F_4)$ ring, $t^4$ fiber),
`s6probe.py` (s = 6 + suspension discovery). Treat any log without its
terminal banner (`ALL … GATES PASSED`, `DONE`, `unsat`) as partial
evidence, except M2 membership reductions as noted above.
