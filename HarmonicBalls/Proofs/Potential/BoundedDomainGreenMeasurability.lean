import HarmonicBalls.Proofs.Sec5.GeneralDomainGreenQuadrature

/-!
# Joint measurability of the Green kernel

The balayage construction of Leonardo Bonanno supplies jointly measurable
harmonic corrections on compact sets of poles. This is an analytic leaf, not
a closure claim for a numbered result.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

/-- On a compact set of poles, the Green function has a jointly measurable representative. -/
theorem exists_measurable_greenFunction_of_compact {O L : Set ℂ}
    (hO : IsOpen O) (hL : IsCompact L) (hLO : L ⊆ O) :
    ∃ G : ℂ × ℂ → ℝ, Measurable G ∧
      ∀ x ∈ L, ∀ y, greenFunction O x y = G (x, y) := by
  classical
  by_cases hne : L.Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨δ, hδ, hδO⟩ := hL.exists_cthickening_subset_open hO hLO
    have hε : 0 < δ / 3 := by positivity
    have h3 : cthickening (3 * (δ / 3)) L ⊆ O := by
      rw [show 3 * (δ / 3) = δ by ring]
      exact hδO
    have hbal : ∀ w : ℂ, (∀ x ∈ L, δ / 3 < ‖x - w‖) →
        ∫ x, regularizedNewtonKernel (δ / 3) x w ∂(0 : Measure ℂ) =
          (0 : ℝ) * regularizedNewtonKernel (δ / 3) z w := by
      intros
      simp
    obtain ⟨H, hHm, hHag, -, -⟩ :=
      greenHarmonicCorrectionBalayageStep_holds O L 0 z 0 (δ / 3) hO hL
        inferInstance (by simp) hz hε h3 hbal
    let good : Set (ℂ × ℂ) := {p | p.2 ∈ O ∧ p.1 ≠ p.2}
    have hgood : MeasurableSet good :=
      (measurable_snd hO.measurableSet).inter isClosed_diagonal.isOpen_compl.measurableSet
    refine ⟨fun p => if p ∈ good then newtonKernel p.1 p.2 - H p.1 p.2 else 0,
      Measurable.ite hgood (measurable_uncurry_newtonKernel.sub hHm) measurable_const, ?_⟩
    intro x hx y
    by_cases hy : y ∈ O ∧ x ≠ y
    · simp only [good, mem_ofPred_eq, ite_eq_left hy]
      rw [greenFunction, ite_eq_left ⟨hLO hx, hy.1, hy.2⟩, hHag x hx y hy.1]
    · simp only [good, mem_ofPred_eq, ite_eq_right hy]
      rw [greenFunction, ite_eq_right (fun h => hy ⟨h.2.1, h.2.2⟩)]
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    exact fun x hx => (hne ⟨x, hx⟩).elim

/-- The Green kernel is jointly Borel measurable on every open planar set,
including its prescribed values on the diagonal and outside the set. -/
theorem measurable_greenFunction_uncurry {O : Set ℂ} (hO : IsOpen O) :
    Measurable (fun p : ℂ × ℂ => greenFunction O p.1 p.2) := by
  classical
  let _ : LocallyCompactSpace O := hO.locallyCompactSpace
  have hσ : IsSigmaCompact O := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hσ
  have hKO : ∀ n, K n ⊆ O := fun n => (subset_iUnion K n).trans_eq hcover
  choose G hG hGeq using fun n => exists_measurable_greenFunction_of_compact hO (hK n) (hKO n)
  let T : ℕ → Set (ℂ × ℂ) := fun n => {p | p.1 ∈ K n}
  have hT : ∀ n, MeasurableSet (T n) :=
    fun n => (hK n).isClosed.measurableSet.preimage measurable_fst
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_piecewise T hT G hG (by
    intro i j hij p hp
    exact (hGeq i p.1 hp.1 p.2).symm.trans (hGeq j p.1 hp.2 p.2))
  have hM : Measurable (fun p : ℂ × ℂ => if p.1 ∈ O then F p else 0) :=
    Measurable.ite (hO.measurableSet.preimage measurable_fst) hF measurable_const
  convert hM using 1
  funext p
  by_cases hp : p.1 ∈ O
  · rw [ite_eq_left hp]
    have : p.1 ∈ ⋃ n, K n := hcover.symm ▸ hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp this
    exact (hGeq n p.1 hn p.2).trans (hFeq n (show p ∈ T n from hn)).symm
  · rw [ite_eq_right hp, greenFunction, ite_eq_right (fun h => hp h.1)]

/-- The Green kernel remains jointly measurable after reversing coordinates. -/
theorem measurable_greenFunction_uncurry_swap {O : Set ℂ} (hO : IsOpen O) :
    Measurable (fun p : ℂ × ℂ => greenFunction O p.2 p.1) :=
  (measurable_greenFunction_uncurry hO).comp measurable_swap


end HarmonicBalls
