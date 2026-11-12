import HarmonicBalls.Proofs.GFF.DistMetricPairingAddFun
import LatticeProb.Bonanno.LQGMetric.Statement.Field

/-! # Continuous shifts of the reconstructed distribution, simultaneously

The reconstruction `pairingDistribution` of a pairing functional reads only the countably many
pairings with the test functions `LQGMetric.comb ⊤ c`. Hence, for a whole-plane GFF `h^ℂ` plus a
random continuous function `f`, the per-test almost sure identity between the raw pairings of
`h^ℂ + f` and its distribution-valued version `H` (`shiftedReconstructedGFF`) holds on one event at
all these tests, and on that event the distribution reconstructed from the pairing functional of
`h^ℂ + f + g` is `H + g` for every continuous `g` at once. This is the form in which the Weyl
scaling axiom (Gwynne-Miller 2021, Section 1.2, p. 6, axiom III) is transferred from metrics of
distributions to metrics of pairing functionals. -/

noncomputable section
open MeasureTheory
namespace HarmonicBalls

/-- The reconstructed distribution of a pairing functional `T` is a distribution `S` as soon as `T`
and `S` agree on the countably many test functions `LQGMetric.comb ⊤ c`. -/
theorem pairingDistribution_eq_of_comb (T : (ℂ → ℝ) → ℝ) (S : LQGMetric.DistC)
    (hS : ∀ c : LQGMetric.CoordJ, T (LQGMetric.comb ⊤ c) = S (LQGMetric.comb ⊤ c)) :
    pairingDistribution T = S := by
  have he : (fun c => testRestriction T (LQGMetric.comb ⊤ c)) = LQGMetric.pairJ ⊤ S := by
    funext c
    exact hS c
  change LQGMetric.pairJInv ⊤ (fun c => testRestriction T (LQGMetric.comb ⊤ c)) = S
  rw [he, LQGMetric.pairJInv_pairJ]

/-- For a whole-plane GFF plus a random continuous function, the raw pairings and the shifted
distribution-valued version agree almost surely at all the test functions `LQGMetric.comb ⊤ c`
simultaneously. -/
theorem IsWholePlaneGFF.ae_addFunPairing_comb
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) :
    ∀ᵐ ω ∂P, ∀ c : LQGMetric.CoordJ, addFunPairing (hC ω) (f ω) (LQGMetric.comb ⊤ c) =
      shiftedReconstructedGFF hC f hf ω (LQGMetric.comb ⊤ c) :=
  ae_all_iff.mpr fun c =>
    (hh.ae_shiftedReconstructedGFF_apply f hf (LQGMetric.comb ⊤ c)).mono fun _ hω => hω.symm

/-- If a pairing functional `T` agrees with a distribution `S` at the test functions
`LQGMetric.comb ⊤ c`, then the distribution reconstructed from the pairing functional of `T + g`
is `S + g` for every continuous `g`. -/
theorem pairingDistribution_addFunPairing_of_comb (T : (ℂ → ℝ) → ℝ) (S : LQGMetric.DistC)
    (hS : ∀ c : LQGMetric.CoordJ, T (LQGMetric.comb ⊤ c) = S (LQGMetric.comb ⊤ c))
    (g : C(ℂ, ℝ)) :
    pairingDistribution (addFunPairing T g) = LQGMetric.addFun S g := by
  apply pairingDistribution_eq_of_comb
  intro c
  change T (LQGMetric.comb ⊤ c) + ∫ x, g x * (LQGMetric.comb ⊤ c) x =
    S (LQGMetric.comb ⊤ c) + LQGMetric.ofCont g (LQGMetric.comb ⊤ c)
  rw [LQGMetric.ofCont_apply, hS c]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- For a whole-plane GFF `h^ℂ` plus a random continuous function `f`, almost surely, for every
continuous `g`, the distribution reconstructed from the pairing functional of `h^ℂ + f + g` is
`H + g`, where `H` is the distribution-valued version of `h^ℂ + f`. -/
theorem IsWholePlaneGFF.ae_pairingDistribution_addFunPairing_addFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) :
    ∀ᵐ ω ∂P, ∀ g : C(ℂ, ℝ),
      pairingDistribution (addFunPairing (addFunPairing (hC ω) (f ω)) g) =
        LQGMetric.addFun (shiftedReconstructedGFF hC f hf ω) g := by
  filter_upwards [hh.ae_addFunPairing_comb f hf] with ω hω g
  exact pairingDistribution_addFunPairing_of_comb _ _ hω g

/-- The induced metric of a whole-plane GFF `h^ℂ` plus a random continuous function `f`, shifted by
a further continuous function `g`, is almost surely, for all continuous `g` and all pairs of points
at once, the metric of `H + g`, where `H` is the distribution-valued version of `h^ℂ + f`. -/
theorem IsWholePlaneGFF.ae_pairingMetric_addFunPairing_addFun
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (D : LQGMetric.DistC → LQGMetric.ContMetric)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, ∀ hg : Continuous g, ∀ u v : ℂ,
      pairingMetric D (addFunPairing (addFunPairing (hC ω) (f ω)) g) u v =
        (D (LQGMetric.addFun (shiftedReconstructedGFF hC f hf ω) ⟨g, hg⟩)).1 (u, v) := by
  filter_upwards [hh.ae_pairingDistribution_addFunPairing_addFun f hf] with ω hω g hg u v
  rw [pairingMetric, ← hω ⟨g, hg⟩]
  rfl

end HarmonicBalls
