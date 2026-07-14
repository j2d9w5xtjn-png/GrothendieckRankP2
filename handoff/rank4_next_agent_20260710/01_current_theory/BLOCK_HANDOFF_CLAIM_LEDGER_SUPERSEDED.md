# Claim ledger for the 2026-07-10 continuation

The labels below are intentionally conservative.

| ID | Claim | Status | Dependence / caveat |
|---|---|---|---|
| BR1 | A central product decomposition of the closed-fiber algebra of a finite free algebra over an Artin local ring lifts with zero off-diagonal Peirce pieces. | **Proved here** | Idempotent lifting modulo a nilpotent ideal; projectivity of Peirce summands; Nakayama. |
| BR2 | A unital algebra of rank at most two over a commutative local ring is commutative. | **Proved here** | Extend the unit to a basis. |
| BR3 | If `B_k` is a product of blocks of dimensions at most two, then the finite free `R`-algebra `B` is commutative. | **Proved here** | BR1 + BR2. |
| AM1 | If `G_k = alpha_2 x mu_2`, then `O(G)^vee_k = k[u]/u^2 x k[u]/u^2`. | **Proved here / standard duality on the commutative fiber** | Uses `alpha_2^D=alpha_2` and `mu_2^D=(Z/2Z)_k`. |
| AM2 | Every finite locally free degree-four deformation of `alpha_2 x mu_2` over an Artin local ring is commutative. | **Proved here** | BR3 + finite duality. No commutativity of the total deformation is assumed. |
| AM3 | Such a deformation is killed by four. | **Proved here, using a standard theorem** | AM2 + Ferrand norm / Deligne's commutative theorem. A proof is included. |
| AM4 | Such a deformation has a rank-two-by-rank-two filtration. | **Proved here** | The identity component of the lifted two-block Cartier dual is a rank-two subgroup; quotient and dualize. |
| SQ1 | A pointed endomorphism trivial modulo a square-zero ideal becomes trivial after one self-composition. | **Proved here** | Flat affine pointed scheme; augmentation splitting. |
| G4 | The full rank-four Grothendieck conjecture follows from AM3. | **Not established** | The upstream archive does not reduce every remaining branch to `alpha_2 x mu_2`. A separate case-exhaustion theorem is required. |
| RT1 | The universal regular translation matrix satisfies `T^4-(1+delta)T^2+delta I=0`. | **Provisional** | Follows from the displayed derivation once the arbitrary-base Hopf-Frobenius inputs `a chi=eps(a)chi`, `S chi=chi`, and `delta^2=1` are formalized. |
| RT2 | The fourth-power defect is a 4-torsion square-zero augmentation derivation with image in `I^2`. | **Provisional, conditional on RT1** | All subsequent manipulations are recorded in detail. |
| RT3 | Every degree-four finite locally free group scheme is killed by 16. | **Provisional, conditional on RT1** | Derived from `D^2=0`; not banked as a theorem in this package. |
| RT4 | On the open locus where `(delta-1) wedge (chi-4)` is unimodular, the group is killed by four. | **More provisional** | In addition to RT1, uses `Tr([2]^#)=1`; this trace identity is not proved here. |
| CY1 | The cyclic direction satisfies `(1+d) z tensor z=0` and purity forces fourth-power triviality. | **Provisional** | Useful reformulation of RT1 in the finite dual; purity/cancellation is exactly the unresolved issue. |

## Correction to an earlier continuation summary

An earlier note said the handoff had reduced the full rank-four problem to the `alpha_2 x mu_2` locus. The current upstream snapshot instead says:

- no full proof has been found;
- other killed-by-two Hopf structures must not be omitted in a proof-grade exhaustive argument;
- `alpha_2 x mu_2` is the most credible special-fiber locus, not the only logical possibility.

Accordingly, AM2-AM4 are unconditional results on a major locus, while G4 remains open.
