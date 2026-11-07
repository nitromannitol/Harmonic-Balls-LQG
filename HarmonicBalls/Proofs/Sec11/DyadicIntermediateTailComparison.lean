import HarmonicBalls.Proofs.Sec11.DyadicIntermediateSquare

/-! # Comparison for dyadic internal-diameter estimates -/

namespace HarmonicBalls
open Set
open scoped ENNReal

/-- The common centre of a dyadic square and its intermediate enlargement. -/
noncomputable def complexGridCenter {N : ℕ} (a : ℂ) (r : ℝ) (i : Fin N × Fin N) : ℂ :=
  ⟨a.re + ((i.1.val : ℝ) + 1 / 2) * r,
    a.im + ((i.2.val : ℝ) + 1 / 2) * r⟩

/-- The centres of all grid tiles lie in the original square. -/
theorem complexGridCenter_mem_closedSquare {N : ℕ} (a : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (i : Fin N × Fin N) :
    complexGridCenter a r i ∈ closedSquare a ((N : ℝ) * r) := by
  have hi : (i.1.val : ℝ) + 1 / 2 ≤ N := by
    have h : (i.1.val : ℝ) < N := by exact_mod_cast i.1.isLt
    have h' : (i.1.val : ℝ) + 1 ≤ N := by exact_mod_cast i.1.isLt
    linarith
  have hj : (i.2.val : ℝ) + 1 / 2 ≤ N := by
    have h : (i.2.val : ℝ) < N := by exact_mod_cast i.2.isLt
    have h' : (i.2.val : ℝ) + 1 ≤ N := by exact_mod_cast i.2.isLt
    linarith
  have hip : 0 ≤ (i.1.val : ℝ) + 1 / 2 := by positivity
  have hjp : 0 ≤ (i.2.val : ℝ) + 1 / 2 := by positivity
  have hix := mul_le_mul_of_nonneg_right hi hr
  have hjx := mul_le_mul_of_nonneg_right hj hr
  have hi0 := mul_nonneg hip hr
  have hj0 := mul_nonneg hjp hr
  simp only [complexGridCenter, closedSquare, Complex.mem_reProdIm, mem_Icc, and_assoc]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The intermediate tile is a closed square of side `3r/2`, with the
same centre as the original dyadic tile. -/
theorem complexIntermediateGridSquare_eq_closedSquare {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) :
    complexIntermediateGridSquare a r i =
      closedSquare ⟨a.re + ((i.1.val : ℝ) - 1 / 4) * r,
        a.im + ((i.2.val : ℝ) - 1 / 4) * r⟩ (3 * r / 2) := by
  ext x
  simp only [complexIntermediateGridSquare, closedSquare, mem_ofPred_eq,
    Complex.mem_reProdIm, mem_Icc, and_assoc]
  constructor <;> intro h <;> rcases h with ⟨h₁, h₂, h₃, h₄⟩ <;>
    exact ⟨by linarith, by nlinarith, by linarith, by nlinarith⟩

/-- The same square is centred at the centre of the dyadic tile. -/
theorem complexIntermediateGridSquare_eq_centered {N : ℕ} (a : ℂ) (r : ℝ)
    (i : Fin N × Fin N) :
    complexIntermediateGridSquare a r i =
      closedSquare (complexGridCenter a r i - ⟨3 * r / 4, 3 * r / 4⟩) (3 * r / 2) := by
  rw [complexIntermediateGridSquare_eq_closedSquare]
  congr 1
  apply Complex.ext <;> simp [complexGridCenter] <;> ring

/-- The centres of every level of the dyadic grid lie in one fixed compact
square, the uniformity set in the diameter estimate. -/
theorem dyadicGridCenter_mem_closedSquare (a : ℂ) {L : ℝ} (hL : 0 ≤ L)
    (n : ℕ) (i : Fin (2 ^ n) × Fin (2 ^ n)) :
    complexGridCenter a (L / (2 : ℝ) ^ n) i ∈ closedSquare a L := by
  have hr : 0 ≤ L / (2 : ℝ) ^ n := by positivity
  have hc := complexGridCenter_mem_closedSquare a hr i
  have hp : ((2 ^ n : ℕ) : ℝ) * (L / (2 : ℝ) ^ n) = L := by
    push_cast
    field_simp
  rwa [hp] at hc

/-- The small-square diameter estimate has exponent greater than two
whenever the Hölder exponent lies below `ξ(Q - 2)`. -/
theorem metricDiameterTailExponent_gt_two {ξ Q s : ℝ} (hξ : 0 < ξ)
    (hs : s < ξ * (Q - 2)) :
    2 < (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) := by
  have hdiff : 2 * ξ < ξ * Q - s := by nlinarith
  have hden : 0 < 2 * ξ ^ 2 := by positivity
  apply (lt_div_iff₀ hden).2
  nlinarith [sq_nonneg (ξ * Q - s - 2 * ξ)]

/-- The internal diameter used for gluing is bounded by the diameter
measured within the closed intermediate square itself. -/
theorem dyadicIntermediateInternalDiameter_le_closedSquareDiameter
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (hL : 0 < L)
    (n : ℕ) (i : Fin (2 ^ n) × Fin (2 ^ n)) (ω : Ω) :
    dyadicIntermediateInternalDiameter D a L n i ω ≤
      ⨆ x ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
        ⨆ y ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          internalMetric (D ω) (complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i) x y := by
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  unfold dyadicIntermediateInternalDiameter
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact (internalMetric_anti (D ω) (complexIntermediateGridSquare_subset_open_enlarged a _ hr i)
    x y).trans (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl))))

#print axioms dyadicIntermediateInternalDiameter_le_closedSquareDiameter
#print axioms complexIntermediateGridSquare_eq_closedSquare
#print axioms complexGridCenter_mem_closedSquare
#print axioms complexIntermediateGridSquare_eq_centered
#print axioms dyadicGridCenter_mem_closedSquare
#print axioms metricDiameterTailExponent_gt_two
end HarmonicBalls
