import HarmonicBalls.Proofs.Sec6.GoodAnnulusCollarGrid
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-! # Joint annular counts on finer grids

The fixed-centre estimate uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal
universe u

/-- A quadratic grid union bound remains valid when the mesh is multiplied
by any fixed positive factor; the events retain the original scale. -/
theorem polyHighProb_forall_fine_prevalenceGrid_of_fixed_center
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → ℂ → Set Ω)
    {c C r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (htail : ∀ ε : ℝ, 0 < ε → ε < r₀ → ∀ z : ℂ,
      P (E ε z)ᶜ ≤ ENNReal.ofReal (C * ε ^ (6 : ℝ))) :
    PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid (c*ε), ω ∈ E ε z}) := by
  have hp : PolyHighProb P (fun t => {ω | ∀ z ∈ prevalenceGrid t, ω ∈ E (t/c) z}) := by
    apply polyHighProb_forall_prevalenceGrid_of_fixed_center P _
      (q := 6) (C := C / c ^ (6 : ℝ)) (r₀ := c*r₀) (by norm_num) (mul_pos hc hr₀)
    intro t ht htr z hz
    have ht' : t / c < r₀ := (div_lt_iff₀ hc).2 (by nlinarith)
    have h := htail (t/c) (div_pos ht hc) ht' z
    convert h using 1
    congr 1
    rw [Real.div_rpow ht.le hc.le]
    ring
  have hp' := hp.comp_mul hc
  simpa only [mul_div_cancel_left₀ _ hc.ne'] using hp'

/-- One good-annulus threshold works for every positive collar tolerance and
for every fixed finer-grid factor, all at the original scale window. -/
theorem exists_goodAnnulus_relativeCollar_fineGrid
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (d : ℝ≥0∞), 0 < d → ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      ∀ c : ℝ, 0 < c → ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid (c*ε),
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) z a b ∧
            μ ω (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
              annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
              d * μ ω (annulus z (3*(s*r)) (5*(s*r)))}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hcount⟩ := exists_goodAnnulus_relativeCollar_count_polynomial_tail
    hgrowth h hμ hAff hCC hγ hγ2 hb 6 β (by norm_num) hβ
  refine ⟨a, ha, ?_⟩
  intro d hd
  obtain ⟨η, hη, hη1, C, hC, htail⟩ := hcount d hd
  obtain ⟨ε₀, hε₀, hlog⟩ := exists_radius_logb_inverse_ge (b := 7) (D := 16) (by norm_num)
  refine ⟨η, hη, hη1, ?_⟩
  intro c hc s hs
  apply polyHighProb_forall_fine_prevalenceGrid_of_fixed_center P _ hc hε₀
  intro ε hε hε₀' z
  convert htail z s hs ε hε (hlog ε hε hε₀') using 1
  congr 1
  ext ω
  change ¬ _ ↔ _
  exact not_le (α := ℝ)

end HarmonicBalls.Section6
