import HarmonicBalls.Draft.Section2

/-!
# Proposition 2.5: the cited Campanato embedding

Proposition 2.5 (prop:lbm-exit-time, paper/lqg_harmonic_ball-corrected.tex:530-:543) states that for a smooth
bounded open set `O`, the expected exit time of Liouville Brownian motion from `O` and, more generally, every Green
potential `q(x) = ∫_O G_O(x,y) f(y) μ_h(dy)` with `f ∈ L^∞(closure O)` are finite and Hölder continuous on
`closure O`. Its proof (:539-:543) reads, as printed:

> Finiteness follows immediately from Lemma 2.4. Hölder continuity uses the embedding of Campanato spaces into
> Hölder spaces together with Lemma 2.4. See, for example, Section 16.2 (or the remark after Proposition 13.5) in
> [Pon16].

[Pon16] = Augusto C. Ponce, *Elliptic PDEs, measures and capacities*, volume 23 of EMS Tracts in Mathematics,
European Mathematical Society (EMS), Zürich, 2016 (bibitem `ponce2016elliptic`).

This module states that literature input, the embedding of Campanato spaces into Hölder spaces, as the Prop
`campanatoHolderEmbeddingCited`: a general statement about functions on planar smooth bounded open sets, not about
the Gaussian free field or the LQG measure. No declaration of the repository states or proves a Campanato embedding
(the two mentions of Campanato, in Steps/Sec2/GreenPotentialGeneral.lean:10 and
Proofs/Potential/GreenPotentialHolder.lean:19, only record that the paper cites it and that the proofs below use
other arguments).

## Status of Proposition 2.5 in the repository

| Declaration | Location | Content |
|---|---|---|
| `greenPotentialHolderStmt_holds` | FirstPass/Phase2/GreenPotentialHolderHolds.lean:24 | Green clause `GreenPotentialHolderStmt`, no hypotheses (COUNTED-MANIFEST row 2.5) |
| `greenPotentialHolderStmt` | Proofs/Potential/LQGGreenPotentialHolderInput.lean:14 | the same theorem, re-exported |
| `greenPotentialHolderStmt_of_volumeGrowth` | Proofs/Sec2/GreenPotentialGeneral.lean:18 | Green clause from `GreenPotentialGeneralStep` and I2 (`LQGVolumeGrowthAllScalesStmt`) |
| `greenPotentialGeneralStep_holds` | Proofs/Potential/GreenGeneralHolder.lean:145 | deterministic general-domain step: Hölder logarithmic potential plus a barrier bound for the harmonic correction (no Campanato embedding) |
| `GreenGeneral.VolumeGrowth.continuousOn_greenPotential` | Proofs/Potential/GreenGeneralIdentification.lean:390 | continuity of the pointwise Green potential on `closure O` |
| `greenPotential_ball_holderOnWith` | Proofs/Potential/GreenPotentialHolder.lean:499 | the disc case `O = B_R(0)`, by a direct kernel estimate |
| `lqgVolumeGrowthAllScalesStmt_of_rows123` | FirstPass/Phase2/DerivedInputs29.lean:66 | I2, the a.s. volume growth at all scales used above |
| `greenPotentialLiouvilleHolderStmt_green` | Draft/Section2.lean:206 | the Green clause from the printed statement |
| `GreenOccupation.occupationMeasure_eq_greenMeasure` | Proofs/Potential/GreenOccupationCharacterization.lean:723 | Brownian occupation measure = Green measure (`2 G_O`) |

The Green clause of Proposition 2.5 is therefore closed in the repository without the cited embedding; the LBM
clause of `GreenPotentialLiouvilleHolderStmt` (Draft/Section2.lean:161) is open (COUNTED-MANIFEST row 2.5). What only
the cited statement supplies is the paper's own route to Hölder continuity: a function on `O` whose mean oscillation
on `O ∩ B_r(x)` is `O(r^{2+α})` has a representative that is `α`-Hölder on `closure O`.

## Why `campanatoHolderEmbeddingCited → LiouvilleVolumeGrowthStmt → GreenPotentialHolderStmt` is not direct

The embedding turns a Campanato bound into Hölder continuity; it does not produce the bound. Applying it to
`u = q` on `O` needs, almost surely, for every smooth bounded open `O` and every `f ∈ L^∞(closure O)`:

1. (missing, the principal step) the Campanato estimate of the Green potential: there are `α ∈ (0, 1]` and `M` with
   `∫_{O ∩ B_r(x)} |q - ⨍_{O ∩ B_r(x)} q| dy ≤ M r^{2+α}` for all `x ∈ O` and `0 < r ≤ diam O`, uniformly up to
   `∂O`. This is a Morrey-type estimate for the Dirichlet problem `-Δq = f μ_h` in `O`, `q = 0` on `∂O`, from the
   upper growth `μ_h(B_r(z)) ≤ r^{β⁺}`. The paper does not write it out and the repository does not state it.
2. (not direct from Lemma 2.4) the volume growth bound at all small scales on a ball containing `closure O`, almost
   surely. `LiouvilleVolumeGrowthStmt` (Lemma 2.4, Draft/Section2.lean:89) is a bound at one scale `ε`, with
   polynomially high probability, for centers in `B_1`; the a.s. bound at all scales and all radii `R` (I2,
   `LQGVolumeGrowthAllScalesStmt`) needs Borel-Cantelli over dyadic scales and the coordinate change of `μ_h`
   (`lqgVolumeGrowthAllScalesStmt_of_ballMass`, Steps/Sec2/VolumeGrowth.lean:164, from `LiouvilleBallMassBoundStep`).
3. (direct once 1 holds) identification of the Hölder representative with the pointwise integral `q` on
   `closure O`, by continuity of `q` (`GreenGeneral.VolumeGrowth.continuousOn_greenPotential`) and positivity of
   Lebesgue measure on nonempty open sets.

Because of step 1 no implication is proved here.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped NNReal

/-- The embedding of Campanato spaces into Hölder spaces, the literature input of the proof of Proposition 2.5
(prop:lbm-exit-time, paper/lqg_harmonic_ball-corrected.tex:539-:543), cited as printed: "Hölder continuity uses the
embedding of Campanato spaces into Hölder spaces together with Lemma 2.4. See, for example, Section 16.2 (or the
remark after Proposition 13.5) in [Pon16]" (A. C. Ponce, *Elliptic PDEs, measures and capacities*, EMS Tracts in
Mathematics 23, EMS, Zürich, 2016). PENDING TRUTH CHECK.

Statement, for the planar domains of Proposition 2.5. Let `O ⊆ ℂ` be a smooth bounded open set
(`IsSmoothBoundedOpen`, Draft/Section2.lean:138) and `0 < α ≤ 1`. There is a constant `K = K(O, α)` such that every
`u ∈ L¹(O)` (Lebesgue measure) in the Campanato space `L^{1,2+α}(O)`, with seminorm bound
`∫_{O ∩ B_r(x)} |u - ⨍_{O ∩ B_r(x)} u| dy ≤ M r^{2+α}` for all centers `x ∈ O` and radii `0 < r ≤ diam O`, agrees
Lebesgue-a.e. on `O` with a function `v` that is `α`-Hölder continuous on `closure O` with Hölder seminorm at most
`K M`.

Reading of the printed citation: the global form (balls `O ∩ B_r(x)` meeting `∂O`, Hölder continuity on `closure O`),
since Proposition 2.5 asserts Hölder continuity on `closure O`; the smoothness of `O` is the domain regularity under
which the embedding holds (it gives Campanato's measure density condition `|O ∩ B_r(x)| ≥ A r²` for `x ∈ O`,
`r ≤ diam O`). Mean oscillation is measured in `L¹`, the case `p = 1` of the Campanato spaces `L^{p,2+pα}(O)`; by
Hölder's inequality a bound in `L^{p,2+pα}(O)` for some `p ≥ 1` implies this one. -/
def campanatoHolderEmbeddingCited : Prop :=
  ∀ O : Set ℂ, IsSmoothBoundedOpen O →
  ∀ α : ℝ≥0, 0 < α → α ≤ 1 →
  ∃ K : ℝ≥0, ∀ (u : ℂ → ℝ) (M : ℝ≥0), IntegrableOn u O →
    (∀ x ∈ O, ∀ r : ℝ, 0 < r → r ≤ diam O →
      (∫ y in O ∩ ball x r, |u y - (⨍ z in O ∩ ball x r, u z)|) ≤ (M : ℝ) * r ^ (2 + (α : ℝ))) →
    ∃ v : ℂ → ℝ, v =ᵐ[volume.restrict O] u ∧ HolderOnWith (K * M) α v (closure O)

end HarmonicBalls
