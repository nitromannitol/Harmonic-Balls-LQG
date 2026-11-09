import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11d.CountableSup
import HarmonicBalls.FirstPass.S11d.ExteriorBound

/-!
# Proposition 11.9, the measurable exterior bound (fp-S11d, owner n3)

FIRST-PASS NEW. The exterior bound of `prop:mass-diam-gen` (corrected paper, lines 3120-3125): with positive probability,
`sup_{u,v ∈ V \ S₂} D_h(u,v; O) ≤ n` for a deterministic `n : ℕ`, with the event measurable. The inputs are the
consequences of Fact 2.2 I and II (`LQGMetricFieldAxioms` in `Proposed/LQG.lean`) for the metric `Dr = (D_h).toReal`:
an a.s. length metric (I) and an a.s. identification of `D_h(·,·; O)` with a function `G` measurable on `O` (II);
the frozen plane-topology input enters only through the hypotheses `IsOpen A`, `IsPreconnected A`.
-/

namespace HarmonicBalls

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- The measurable exterior bound: for `A` open, preconnected, with `closure A ⊆ O` compact, and `A0` measurable with
positive measure, some measurable `B ⊆ A0` with `P B > 0` carries the uniform bound `D(u,v; O) ≤ n` on `A × A`. -/
theorem exists_measurable_exterior_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Dr : Ω → ℂ → ℂ → ℝ} (hDnn : ∀ ω x y, 0 ≤ Dr ω x y)
    (hI : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dr ω))
    {O A : Set ℂ} {A0 : Set Ω} (hO : IsOpen O) (hA : IsOpen A) (hAc : IsPreconnected A) (hclO : closure A ⊆ O)
    (hK : IsCompact (closure A))
    (hG : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ O, ∀ w ∈ O, internalMetric (Dr ω) O z w = G ω z w)
    (hA0 : MeasurableSet A0) (hA0p : 0 < P A0) :
    ∃ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧ B ⊆ A0 ∧ 0 < P B ∧
      ∀ ω ∈ B, ∀ u ∈ A, ∀ v ∈ A, internalMetric (Dr ω) O u v ≤ (n : ℝ≥0∞) := by
  obtain ⟨G, hGm, hGae⟩ := hG
  obtain ⟨Q, hQc, hQA, hAQ⟩ := TopologicalSpace.exists_countable_dense_subset A
  have hAO : A ⊆ O := fun x hx => hclO (subset_closure hx)
  have : Countable Q := hQc.to_subtype
  set M : Ω → ℝ≥0∞ := fun ω => ⨆ q : Q, ⨆ q' : Q, G ω q q' with hMdef
  have hM : Measurable M := Measurable.iSup fun q => Measurable.iSup fun q' => hGm q q'
  -- the good event: a.s. length metric and identification with `G` on `O`
  have hgood : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dr ω) ∧
      ∀ z ∈ O, ∀ w ∈ O, internalMetric (Dr ω) O z w = G ω z w := by
    filter_upwards [hI, hGae] with ω h1 h2
    exact ⟨h1, h2⟩
  -- on a good point, the sup over `A` is the countable sup `M`
  have hsup : ∀ ω, IsEuclideanLengthMetric (Dr ω) →
      (∀ z ∈ O, ∀ w ∈ O, internalMetric (Dr ω) O z w = G ω z w) →
      (⨆ u ∈ A, ⨆ v ∈ A, internalMetric (Dr ω) O u v) = M ω := by
    intro ω h1 h2
    have hcont := h1.continuousOn_internalMetric_pair (hDnn ω) hO
    have hcont' : ContinuousOn (fun p : ℂ × ℂ => internalMetric (Dr ω) O p.1 p.2) (O ×ˢ O) := hcont
    rw [iSup_eq_countable_dense hcont' (hclO) hQA hAQ]
    have hsetG : (⨆ q ∈ Q, ⨆ q' ∈ Q, internalMetric (Dr ω) O q q') = ⨆ q ∈ Q, ⨆ q' ∈ Q, G ω q q' :=
      iSup_congr fun q => iSup_congr fun hq => iSup_congr fun q' =>
        iSup_congr fun hq' => h2 q (hAO (hQA hq)) q' (hAO (hQA hq'))
    rw [hsetG, hMdef]
    simp only [iSup_subtype']
  -- finiteness a.s.
  have hfin : ∀ᵐ ω ∂P, M ω < ⊤ := by
    filter_upwards [hgood] with ω hω
    rw [← hsup ω hω.1 hω.2]
    exact iSup_internalMetric_lt_top hω.1 (hDnn ω) hO hA hAc hclO hK
  obtain ⟨n, hBm, hBp⟩ := exists_nat_measurable_pos_inter_le hA0 hA0p hM hfin
  -- remove a measurable null set containing the bad points
  have hbad : P {ω | ¬ (IsEuclideanLengthMetric (Dr ω) ∧
      ∀ z ∈ O, ∀ w ∈ O, internalMetric (Dr ω) O z w = G ω z w)} = 0 := ae_iff.mp hgood
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null hbad
  refine ⟨n, (A0 ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) \ t, hBm.diff htm, sdiff_subset.trans inter_subset_left,
    by rw [measure_sdiff_null ht0]; exact hBp, ?_⟩
  intro ω hω u hu v hv
  have hgoodω : IsEuclideanLengthMetric (Dr ω) ∧
      ∀ z ∈ O, ∀ w ∈ O, internalMetric (Dr ω) O z w = G ω z w := by
    by_contra hb
    exact hω.2 (hsub hb)
  have hMn : M ω ≤ (n : ℝ≥0∞) := hω.1.2
  calc internalMetric (Dr ω) O u v
      ≤ ⨆ u' ∈ A, ⨆ v' ∈ A, internalMetric (Dr ω) O u' v' :=
        le_iSup₂_of_le u hu (le_iSup₂_of_le v hv le_rfl)
    _ = M ω := hsup ω hgoodω.1 hgoodω.2
    _ ≤ (n : ℝ≥0∞) := hMn

end HarmonicBalls
