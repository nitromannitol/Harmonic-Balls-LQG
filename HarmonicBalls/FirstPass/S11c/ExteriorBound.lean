import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11c.UpperProb
import HarmonicBalls.FirstPass.S11c.Exterior
import HarmonicBalls.FirstPass.S11c.Closed
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Proposition 11.10, the exterior diameter bound with probability

Let `K` be a set and `D ω` the internal metric data
of a realisation `ω`. If the internal diameter `⨆ u ∈ K, ⨆ v ∈ K, internalMetric (D ω) K u v` is an a.e.-measurable random
variable which is almost surely finite, then for every `η > 0` there are an integer `n` and a measurable event `B` with
`1 - η < P B` on which the internal diameter of `K` is at most `n`. This is step S3 of the first-pass proof of Proposition
11.10 (the exterior set `K₁`, paper lines 3127-3137): the bound is chosen from the probability `1 - η`.
The measurable event is obtained by discarding a measurable null set from the a.e. equality with a measurable version.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls

/-- An a.e.-measurable, almost surely finite internal diameter of `K` gives a measurable event of probability greater
than `1 - η`, on which every internal distance of `K` is at most an integer. -/
theorem exists_measurable_diam_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → ℂ → ℂ → ℝ) (K : Set ℂ)
    (hsup : AEMeasurable (fun ω => ⨆ u ∈ K, ⨆ v ∈ K, internalMetric (D ω) K u v) P)
    (hfin : ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ K, ∀ v ∈ K, internalMetric (D ω) K u v ≤ ENNReal.ofReal A)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧ 1 - η < P B ∧
      B ⊆ {ω | ∀ u ∈ K, ∀ v ∈ K, internalMetric (D ω) K u v ≤ ENNReal.ofReal (n : ℝ)} := by
  set X : Ω → ℝ≥0∞ := fun ω => ⨆ u ∈ K, ⨆ v ∈ K, internalMetric (D ω) K u v with hX_def
  set Xm := hsup.mk X with hXm_def
  have hXm : Measurable Xm := hsup.measurable_mk
  have hfinX : ∀ᵐ ω ∂P, X ω < ⊤ := by
    filter_upwards [hfin] with ω hω
    obtain ⟨A, hA⟩ := hω
    exact lt_of_le_of_lt (iSup₂_le fun u hu => iSup₂_le fun v hv => hA u hu v hv) ENNReal.ofReal_lt_top
  have hfinM : ∀ᵐ ω ∂P, Xm ω < ⊤ := by
    filter_upwards [hsup.ae_eq_mk, hfinX] with ω h1 h2
    have h1' : Xm ω = X ω := h1.symm
    rw [h1']
    exact h2
  obtain ⟨n, hn⟩ := exists_nat_bound_prob P hXm hfinM hη
  have h0 : P {ω | ¬ (X ω = Xm ω)} = 0 := ae_iff.1 hsup.ae_eq_mk
  obtain ⟨T, hTsup, hTm, hT0⟩ := exists_measurable_superset_of_null h0
  refine ⟨n, {ω | Xm ω ≤ (n : ℝ≥0∞)} \ T, (measurableSet_le hXm measurable_const).diff hTm, ?_, ?_⟩
  · rw [measure_sdiff_null hT0]
    exact hn
  · intro ω hω u hu v hv
    obtain ⟨hωn, hωT⟩ := hω
    have hXeq : X ω = Xm ω := by
      by_contra hne
      exact hωT (hTsup (show ω ∈ {ω | ¬ (X ω = Xm ω)} from hne))
    have hXn : X ω ≤ (n : ℝ≥0∞) := by
      rw [hXeq]
      exact hωn
    have hle : internalMetric (D ω) K u v ≤ X ω :=
      le_iSup₂_of_le (f := fun u (_ : u ∈ K) => ⨆ v ∈ K, internalMetric (D ω) K u v) u hu
        (le_iSup₂_of_le (f := fun v (_ : v ∈ K) => internalMetric (D ω) K u v) v hv le_rfl)
    rw [ENNReal.ofReal_natCast]
    exact hle.trans hXn

/-- A grid cell of positive side is a closed rectangle in the sense of `IsClosedRectangle`. -/
lemma isClosedRectangle_gridCell {h : ℝ} (hh : 0 < h) (X Y : ℤ) : IsClosedRectangle (gridCell h X Y) := by
  unfold IsClosedRectangle
  exact ⟨(X : ℝ) * h, ((X : ℝ) + 1) * h, (Y : ℝ) * h, ((Y : ℝ) + 1) * h,
    mul_lt_mul_of_pos_right (lt_add_one _) hh, mul_lt_mul_of_pos_right (lt_add_one _) hh, rfl⟩

/-- The exterior set `gridK1` is a finite union of closed rectangles (the hypothesis form of the frozen Props). -/
lemma gridK1_finite_rect_union {h : ℝ} (hh : 0 < h) (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) :
    ∃ F : Finset (Set ℂ), (∀ R ∈ F, IsClosedRectangle R) ∧ gridK1 h Jx Jy A₁ A₂ B₁ B₂ = ⋃ R ∈ F, R := by
  refine ⟨(gridCellFamily_finite Jx Jy A₁ A₂ B₁ B₂).toFinset.image (fun p => gridCell h p.1 p.2), ?_, ?_⟩
  · intro R hR
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hR
    exact isClosedRectangle_gridCell hh p.1 p.2
  · ext x
    simp [gridK1]

/-- The exterior set `gridK1` is connected, given that its core `gridK0` is preconnected and nonempty. -/
lemma isConnected_gridK1 {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ : ℤ} (hA : A₁ + 1 ≤ A₂)
    (hB : B₁ + 1 ≤ B₂) (hK0 : IsPreconnected (gridK0 h Jx Jy A₁ A₂ B₁ B₂)) {x0 : ℂ}
    (hx0 : x0 ∈ gridK0 h Jx Jy A₁ A₂ B₁ B₂) : IsConnected (gridK1 h Jx Jy A₁ A₂ B₁ B₂) := by
  have hsub := gridK0_subset_gridK1 (Jx := Jx) (Jy := Jy) hh hA hB
  unfold IsConnected
  exact ⟨⟨x0, hsub hx0⟩, isPreconnected_gridK1 hh hA hB hK0 hx0⟩

universe u

/-- Step S3 of Proposition 11.10 (paper lines 3127-3137). For a connected finite union `K` of closed rectangles, the
frozen measurability and finiteness inputs give, for every `η > 0`, an integer `n` and a measurable event of
probability greater than `1 - η` on which every internal distance of `K` is at most `n`. -/
theorem exists_measurable_exterior_bound (Hsup : LQGMetricSupMeasurableFrozen.{u})
    (Hfin : ConnectedSquareUnionDiamFiniteFrozen.{u}) {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hW : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    {K : Set ℂ} (hK : ∃ F : Finset (Set ℂ), (∀ R ∈ F, IsClosedRectangle R) ∧ K = ⋃ R ∈ F, R)
    (hconn : IsConnected K) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧ 1 - η < P B ∧
      B ⊆ {ω | ∀ u ∈ K, ∀ v ∈ K, internalMetric (D ω) K u v ≤ ENNReal.ofReal (n : ℝ)} :=
  exists_measurable_diam_bound P D K
    (Hsup γ α₀ ξ hγ hγ2 hα Ω P hC hcirc D hW hD K hK)
    (Hfin γ α₀ ξ hγ hγ2 hα Ω P hC hcirc D hW hD K hK hconn) hη

end HarmonicBalls
