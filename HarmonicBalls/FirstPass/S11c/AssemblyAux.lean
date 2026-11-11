import HarmonicBalls.FirstPass.S11c.ShiftedLength
import HarmonicBalls.FirstPass.S11c.ClassFin4
import HarmonicBalls.FirstPass.S11c.Closed
import HarmonicBalls.FirstPass.S11c.Classes
import HarmonicBalls.FirstPass.S11c.ClassClosed

/-!
# Proposition 11.10, auxiliary facts for the shift and the length metric

The assembly of the printed proof of `lemma:mass-diam` (paper lines 3091-3112) needs:
(i) the LQG metric `D ω` is almost surely a Euclidean length metric (`hDl` of `Shifted.shifted_sup_le_of_good`), from item I of
`LQGMetricFieldAxioms` and the representation of `D` in `IsLQGMetricOfField`; (ii) the exterior set `gridK1` is compact (the
support of the shift); (iii) the union of a class cell and the unit circle is closed, and is disjoint from `gridK1` when
`gridK1` lies in the box `S₂` disjoint from the unit circle. The shift of the Cameron-Martin step is zero on that union.
-/

open MeasureTheory Set Metric

namespace HarmonicBalls

universe u

/-- The LQG metric `D ω` of a field is almost surely a Euclidean length metric (item I of the field-level axioms). -/
theorem ae_isEuclideanLengthMetric_of_field {γ ξ α₀ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hI := (haxioms hgff hγ hγ₂ hα 𝔇 h𝔇).1
  filter_upwards [hI, hrepr] with ω hωI hωrep
  have hDfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hωrep u v).2, ENNReal.toReal_ofReal (hωrep u v).1]
  rw [hDfun]
  exact hωI.2

/-- The exterior set `gridK1` of a grid box is compact. -/
lemma isCompact_gridK1 {h : ℝ} (hh : 0 < h) (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) :
    IsCompact (gridK1 h Jx Jy A₁ A₂ B₁ B₂) := by
  have hbox : IsCompact (gridBox h A₁ A₂ B₁ B₂) := by
    unfold gridBox
    exact isCompact_Icc.reProdIm isCompact_Icc
  exact hbox.of_isClosed_subset (gridK1_isClosed h Jx Jy A₁ A₂ B₁ B₂)
    (gridK1_subset_gridBox hh Jx Jy A₁ A₂ B₁ B₂)

/-- A class cell of parity `i` union the unit circle is closed. -/
lemma isClosed_classFin4_union_sphere {h : ℝ} (P₁ P₂ Q₁ Q₂ : ℤ) (i : Fin 4) :
    IsClosed (classFin4 h P₁ P₂ Q₁ Q₂ i ∪ sphere (0 : ℂ) 1) := by
  unfold classFin4
  exact (isClosed_gridClassCells_index _ _ _ _ _ _).union isClosed_sphere

/-- The exterior set of a grid box inside `S₂`, disjoint from the unit circle, is disjoint from a class cell union the
unit circle. -/
lemma disjoint_gridK1_classFin4_union_sphere {h : ℝ} (hh : 0 < h) {S₂ : Set ℂ}
    {P₁ P₂ Q₁ Q₂ A₁ A₂ B₁ B₂ : ℤ} (i : Fin 4)
    (hK : gridK1 h {j : ℤ | j % 2 = (((i : ℕ) / 2 : ℕ) : ℤ) ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
      {k : ℤ | k % 2 = (((i : ℕ) % 2 : ℕ) : ℤ) ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} A₁ A₂ B₁ B₂ ⊆ S₂)
    (hS₂ : Disjoint S₂ (sphere (0 : ℂ) 1)) :
    Disjoint (gridK1 h {j : ℤ | j % 2 = (((i : ℕ) / 2 : ℕ) : ℤ) ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
      {k : ℤ | k % 2 = (((i : ℕ) % 2 : ℕ) : ℤ) ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} A₁ A₂ B₁ B₂)
      (classFin4 h P₁ P₂ Q₁ Q₂ i ∪ sphere (0 : ℂ) 1) := by
  unfold classFin4
  refine Set.disjoint_union_right.2 ⟨gridK1_disjoint_gridClassCells hh, ?_⟩
  exact Set.disjoint_of_subset_left hK hS₂

end HarmonicBalls
