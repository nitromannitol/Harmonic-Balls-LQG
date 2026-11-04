import HarmonicBalls.Steps.Sec11.LogWeylScaleSummability
import HarmonicBalls.Steps.Sec11.PinchDiameterFiniteness
import Mathlib.Analysis.Normed.Module.Connected

/-! # Exponential annular corridors

Explicit open annuli provide the punctured corridors used for logarithmic Weyl
estimates, at arbitrarily small initial scale.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- An open annular corridor around the shell at scale `exp (-(s+n))`. -/
def exponentialAnnulusCorridor (s : ℝ) (n : ℕ) : Set ℂ :=
  {z | Real.exp (-((n : ℝ) + s + 2)) < ‖z‖ ∧
    ‖z‖ < Real.exp (-((n : ℝ) + s - 1))}

/-- Each exponential corridor is open. -/
theorem isOpen_exponentialAnnulusCorridor (s : ℝ) (n : ℕ) :
    IsOpen (exponentialAnnulusCorridor s n) := by
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

/-- Every exponential corridor lies in the punctured initial ball. -/
theorem exponentialAnnulusCorridor_subset (s : ℝ) (n : ℕ) :
    exponentialAnnulusCorridor s n ⊆ ball (0 : ℂ) (Real.exp (1 - s)) \ {0} := by
  intro z hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : Real.exp (-((n : ℝ) + s - 1)) ≤ Real.exp (1 - s) :=
    Real.exp_le_exp.mpr (by linarith)
  refine ⟨?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using hz.2.trans_le hexp
  · have hnz : 0 < ‖z‖ := (Real.exp_pos _).trans hz.1
    simpa only [mem_singleton_iff] using (norm_pos_iff.mp hnz)

/-- Each geometric shell is contained in its exponential corridor. -/
theorem geometricShell_subset_exponentialAnnulusCorridor (s : ℝ) (n : ℕ) :
    geometricShell (Real.exp (-s)) (Real.exp (-1)) n ⊆ exponentialAnnulusCorridor s n := by
  have hs (m : ℕ) : Real.exp (-s) * Real.exp (-1) ^ m =
      Real.exp (-(s + (m : ℝ))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  intro z hz
  have hlo : Real.exp (-(s + ((n + 1 : ℕ) : ℝ))) ≤ ‖z‖ := by
    simpa only [geometricShell, mem_ofPred_eq, hs] using hz.1
  have hhi : ‖z‖ ≤ Real.exp (-(s + (n : ℝ))) := by
    simpa only [geometricShell, mem_ofPred_eq, hs] using hz.2
  refine ⟨(Real.exp_lt_exp.mpr ?_).trans_le hlo, hhi.trans_lt (Real.exp_lt_exp.mpr ?_)⟩ <;>
    push_cast <;> linarith

/-- Exponential corridors are connected. -/
theorem isConnected_exponentialAnnulusCorridor (s : ℝ) (n : ℕ) :
    IsConnected (exponentialAnnulusCorridor s n) := by
  let a := Real.exp (-((n : ℝ) + s + 2))
  let b := Real.exp (-((n : ℝ) + s - 1))
  have ha : 0 < a := Real.exp_pos _
  have hab : a < b := Real.exp_lt_exp.mpr (by linarith)
  let F : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ) * p.2
  have hc : Continuous F := by fun_prop
  have hprod : IsConnected (Ioo a b ×ˢ sphere (0 : ℂ) 1) :=
    (isConnected_Ioo hab).prod (isConnected_sphere (by simp) 0 (by norm_num))
  have himage : F '' (Ioo a b ×ˢ sphere (0 : ℂ) 1) = exponentialAnnulusCorridor s n := by
    ext z
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
      have ht0 : 0 ≤ t := ha.le.trans ht.1.le
      simpa [F, exponentialAnnulusCorridor, a, b, hu', Real.norm_eq_abs,
        abs_of_nonneg ht0] using ht
    · intro hz
      have hnpos : 0 < ‖z‖ := ha.trans hz.1
      let u : ℂ := z / (‖z‖ : ℂ)
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere, dist_zero_right]
        simp [u, ne_of_gt hnpos]
      refine ⟨(‖z‖, u), ⟨⟨hz.1, hz.2⟩, hu⟩, ?_⟩
      dsimp [F, u]
      have hne : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
      field_simp
  rw [← himage]
  exact hprod.image F hc.continuousOn

/-- Every geometric shell is compact. -/
theorem isCompact_geometricShell (R q : ℝ) (n : ℕ) :
    IsCompact (geometricShell R q n) := by
  apply isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · apply (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : ℂ) (R * q ^ n))).subset
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hz.2

/-- The base internal diameter of each geometric shell inside its corridor is
finite. This is a scale-by-scale statement and gives no decay in `n`. -/
theorem IsEuclideanLengthMetric.exponentialAnnulusCorridor_diameter_lt_top
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (s : ℝ) (n : ℕ) :
    (⨆ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ⨆ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        internalMetric D (exponentialAnnulusCorridor s n) x y) < ∞ :=
  hD.iSup_pair_internalMetric_lt_top_of_isCompact hnonneg
    (isOpen_exponentialAnnulusCorridor s n) (isConnected_exponentialAnnulusCorridor s n)
    (isCompact_geometricShell _ _ _) (geometricShell_subset_exponentialAnnulusCorridor s n)

/-- Every neighborhood of the origin contains all corridors at a sufficiently
small initial scale. -/
theorem exists_exponentialAnnulusCorridor_subset {V : Set ℂ} (hV : IsOpen V)
    (hzero : (0 : ℂ) ∈ V) :
    ∃ s : ℝ, ∀ n, exponentialAnnulusCorridor s n ⊆ V \ {0} := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV 0 hzero
  refine ⟨1 - Real.log r, fun n => ?_⟩
  have heq : Real.exp (1 - (1 - Real.log r)) = r := by
    have : 1 - (1 - Real.log r) = Real.log r := by ring
    rw [this, Real.exp_log hr]
  intro z hz
  have hz' := exponentialAnnulusCorridor_subset (1 - Real.log r) n hz
  refine ⟨hball ?_, hz'.2⟩
  simpa only [heq] using hz'.1

/-- A decay estimate on the explicit corridors implies puncture removal for
the logarithmically Weyl-scaled metric. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_exponential_annuli
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ α β s : ℝ} (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) =
      weylScaling D ξ (fun z => -α * Real.log ‖z‖) x y)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbase : ∀ n, ∀ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∀ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      internalMetric D (exponentialAnnulusCorridor s n) x y ≤
        C * ENNReal.ofReal (Real.exp (-β * (n : ℝ))))
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  apply hD.internalMetric_sdiff_zero_eq_of_log_scale_bounds (κ := s + 2) hE hEnonneg hξ hα hgap V
    hzero hscale (Real.exp_pos _) (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by norm_num))
    (exponentialAnnulusCorridor s) hC (isOpen_exponentialAnnulusCorridor s) ?_ ?_ hbase hx hy
  · intro n z hz
    have h := exponentialAnnulusCorridor_subset s n hz
    exact ⟨hball h.1, h.2⟩
  · intro n z hz
    simpa only [add_assoc] using hz.1.le

#print axioms isOpen_exponentialAnnulusCorridor
#print axioms exponentialAnnulusCorridor_subset
#print axioms geometricShell_subset_exponentialAnnulusCorridor
#print axioms isConnected_exponentialAnnulusCorridor
#print axioms isCompact_geometricShell
#print axioms IsEuclideanLengthMetric.exponentialAnnulusCorridor_diameter_lt_top
#print axioms IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_exponential_annuli
#print axioms exists_exponentialAnnulusCorridor_subset

end HarmonicBalls
