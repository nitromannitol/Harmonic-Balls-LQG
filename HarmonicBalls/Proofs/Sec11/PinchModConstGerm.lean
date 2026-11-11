import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne
import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import HarmonicBalls.Steps.Sec11.InternalPinchQuantitative
import HarmonicBalls.Proofs.Sec8.BirkhoffPort

/-! # Local comparisons and the field germ modulo constants

The imported Section 8 germ proof uses Leonardo Bonanno's LatticeProb
formalization. The zero-one law here concerns the field modulo constants;
the full field germ used by the current pinch-frequency bridge is distinct.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- Adding deterministic pairing values does not change the local field
sigma algebra modulo constants. No regularity or linearity of the added
values is needed for this sigma-algebra identity. -/
theorem fieldSigmaAlgebraModConst_eq_of_deterministic_pairing_shift
    {Ω : Type*} (α₀ : ℝ) (hC hC' : Ω → (ℂ → ℝ) → ℝ)
    (d : (ℂ → ℝ) → ℝ) (hd : ∀ ω φ, hC' ω φ = hC ω φ + d φ) (U : Set ℂ) :
    Section6.fieldSigmaAlgebraModConst α₀ hC' U =
      Section6.fieldSigmaAlgebraModConst α₀ hC U := by
  unfold Section6.fieldSigmaAlgebraModConst
  congr 1; ext1 φ; congr 1; ext1 _
  have heq : (fun ω => fieldPairing α₀ (hC' ω) φ) =
      (fun t : ℝ => t + d φ) ∘ fun ω => fieldPairing α₀ (hC ω) φ := by
    funext ω
    simp only [Function.comp_apply, fieldPairing, hd]
    ring
  rw [heq, ← MeasurableSpace.comap_comp]
  congr 1
  exact (MeasurableEquiv.addRight (d φ)).measurableEmbedding.comap_eq

/-- A probability law locally absolutely continuous with respect to a
whole-plane GFF has a trivial origin field germ modulo constants. The
comparison is on the full local field sigma algebra at one positive radius;
no global absolute continuity is required. -/
theorem origin_modConst_germ_trivial_of_local_absoluteContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hC hcirc) (α₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (hAC : P.trim (hQ.fieldSigmaAlgebra_le α₀ (ball 0 r)) ≪
      Q.trim (hQ.fieldSigmaAlgebra_le α₀ (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  let : IsProbabilityMeasure Q := hQ.isProbabilityMeasure
  intro A hA
  have hAm : MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 r)] A :=
    (Section6.fieldSigmaAlgebraModConst_le α₀ hC _) A (hA r hr)
  have hAambient : MeasurableSet A := (hQ.fieldSigmaAlgebra_le α₀ _) A hAm
  have hac : ∀ B : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 r)] B → Q B = 0 → P B = 0 := by
    intro B hB hQB
    have hz : Q.trim (hQ.fieldSigmaAlgebra_le α₀ (ball 0 r)) B = 0 := by
      rwa [trim_measurableSet_eq _ hB]
    have hp := hAC hz
    rwa [trim_measurableSet_eq _ hB] at hp
  rcases hQ.origin_germ_trivial α₀ A hA with hzero | hone
  · exact Or.inl (hac A hAm hzero)
  · right
    have hQc : Q Aᶜ = 0 := by
      rw [measure_compl hAambient (measure_ne_top Q A), hone]
      simp
    have hPc := hac Aᶜ hAm.compl hQc
    simpa using measure_of_measure_compl_eq_zero hPc

open Classical in
/-- A stationary local representative measurable modulo constants has the
reference event's block density under a locally absolutely continuous law.
The existence of such representatives, the comparison, and the one-scale
probability bound remain explicit. -/
theorem ae_internal_pinchBlockDensity_of_modConst_germ
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hC hcirc) (α₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (hAC : P.trim (hQ.fieldSigmaAlgebra_le α₀ (ball 0 r)) ≪
      Q.trim (hQ.fieldSigmaAlgebra_le α₀ (ball 0 r)))
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' V : Set ℂ) (M : ℝ) (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hbound : ∀ n ω, X n ω ∈ Icc (0 : ℝ) 1)
    (hX : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  let F : Ω → ℕ → ℝ := fun ω n => X (n + 1) ω
  let : IsFiniteMeasure (P.map F) := P.isFiniteMeasure_map F
  exact ae_eventually_internal_pinch_block_density_of_ae_rep_of_lt_prob P μ D U T Q' V M 0 X
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε))
    (fun ε _ => (Section6.fieldSigmaAlgebraModConst_le α₀ hC _).trans
      (hQ.fieldSigmaAlgebra_le α₀ _)) hXgerm
    (origin_modConst_germ_trivial_of_local_absoluteContinuous P Q hQ α₀ hr hAC)
    hXm hbound hX (pointwiseBirkhoff_of_latticeProb _ _ _) hstat δ hδ



end HarmonicBalls
