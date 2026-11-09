import HarmonicBalls.FirstPass.S11c.Identify

/-!
# Proposition 11.10, nested closed dyadic squares on a common grid (fp-S11c, owner n1)

FIRST-PASS NEW (bookkeeping). The first-pass proof of Proposition 11.10 works on the integer grid of mesh `h = 2^{-(N+3)}`
(the cells of `Cover`, `Classes`, `Exterior`). The statement concerns closed dyadic squares `S₁ ⊆ S₂` of levels `m₁`, `m₂`.
For a level `N` deep enough, both squares are integer boxes of this grid, with the corner conditions used by the shifted
bound: the endpoints of `S₁` are divisible by eight and `S₁` has width at least sixteen cells; `S₂` contains `S₁` with width at
least sixteen cells. Ordering of the endpoints follows from the inclusion of corner points.
-/

open Set

namespace HarmonicBalls

/-- The integer endpoints of an inclusion of two grid boxes of mesh `h > 0` are ordered. -/
lemma gridBox_subset_ints {h : ℝ} (hh : 0 < h) {P₁ P₂ Q₁ Q₂ A₁ A₂ B₁ B₂ : ℤ} (hP : P₁ ≤ P₂) (hQ : Q₁ ≤ Q₂)
    (hsub : gridBox h P₁ P₂ Q₁ Q₂ ⊆ gridBox h A₁ A₂ B₁ B₂) :
    A₁ ≤ P₁ ∧ P₂ ≤ A₂ ∧ B₁ ≤ Q₁ ∧ Q₂ ≤ B₂ := by
  unfold gridBox at hsub
  have hP' : (P₁ : ℝ) ≤ P₂ := by exact_mod_cast hP
  have hQ' : (Q₁ : ℝ) ≤ Q₂ := by exact_mod_cast hQ
  have hPh : (P₁ : ℝ) * h ≤ (P₂ : ℝ) * h := mul_le_mul_of_nonneg_right hP' hh.le
  have hQh : (Q₁ : ℝ) * h ≤ (Q₂ : ℝ) * h := mul_le_mul_of_nonneg_right hQ' hh.le
  have c1 : (⟨(P₁ : ℝ) * h, (Q₁ : ℝ) * h⟩ : ℂ) ∈
      Icc ((P₁ : ℝ) * h) ((P₂ : ℝ) * h) ×ℂ Icc ((Q₁ : ℝ) * h) ((Q₂ : ℝ) * h) :=
    Complex.mem_reProdIm.2 ⟨⟨le_refl _, hPh⟩, ⟨le_refl _, hQh⟩⟩
  have c2 : (⟨(P₂ : ℝ) * h, (Q₂ : ℝ) * h⟩ : ℂ) ∈
      Icc ((P₁ : ℝ) * h) ((P₂ : ℝ) * h) ×ℂ Icc ((Q₁ : ℝ) * h) ((Q₂ : ℝ) * h) :=
    Complex.mem_reProdIm.2 ⟨⟨hPh, le_refl _⟩, ⟨hQh, le_refl _⟩⟩
  have d1 := Complex.mem_reProdIm.1 (hsub c1)
  have d2 := Complex.mem_reProdIm.1 (hsub c2)
  have eA1 : (A₁ : ℝ) * h ≤ (P₁ : ℝ) * h := d1.1.1
  have eA2 : (P₂ : ℝ) * h ≤ (A₂ : ℝ) * h := d2.1.2
  have eB1 : (B₁ : ℝ) * h ≤ (Q₁ : ℝ) * h := d1.2.1
  have eB2 : (Q₂ : ℝ) * h ≤ (B₂ : ℝ) * h := d2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast le_of_mul_le_mul_right eA1 hh
  · exact_mod_cast le_of_mul_le_mul_right eA2 hh
  · exact_mod_cast le_of_mul_le_mul_right eB1 hh
  · exact_mod_cast le_of_mul_le_mul_right eB2 hh

/-- The endpoints `J·2^d` and `(J+1)·2^d` of a dyadic interval of level `d ≥ 4` are divisible by eight, and the second
exceeds the first by at least sixteen. -/
lemma dyadic_interval_facts (J : ℤ) {d : ℕ} (hd : 4 ≤ d) :
    J * 2 ^ d % 8 = 0 ∧ (J + 1) * 2 ^ d % 8 = 0 ∧ J * 2 ^ d + 16 ≤ (J + 1) * 2 ^ d := by
  have h8 : (8 : ℤ) ∣ 2 ^ d := by
    have := pow_dvd_pow (2 : ℤ) (show 3 ≤ d by omega)
    norm_num at this
    exact this
  have h16 : (16 : ℤ) ≤ 2 ^ d := by
    have := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by norm_num) hd
    norm_num at this
    exact this
  refine ⟨Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_right h8 J),
    Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_right h8 (J + 1)), ?_⟩
  have e : (J + 1) * 2 ^ d = J * 2 ^ d + 2 ^ d := by ring
  rw [e]
  linarith

/-- Two nested closed dyadic squares of levels `m₁`, `m₂` are integer boxes of the grid of mesh `2^{-(N+3)}`, with the corner
conditions of the shifted bound. -/
theorem exists_grid_of_closedDyadicSquare_subset {m₁ J₁ K₁ m₂ J₂ K₂ N : ℤ} (hN₁ : m₁ + 4 ≤ N + 3)
    (hN₂ : m₂ + 4 ≤ N + 3) (hS : closedDyadicSquare m₁ J₁ K₁ ⊆ closedDyadicSquare m₂ J₂ K₂) :
    ∃ A₁ A₂ B₁ B₂ P₁ P₂ Q₁ Q₂ : ℤ,
      closedDyadicSquare m₂ J₂ K₂ = gridBox ((2 : ℝ) ^ (-(N + 3))) A₁ A₂ B₁ B₂ ∧
      closedDyadicSquare m₁ J₁ K₁ = gridBox ((2 : ℝ) ^ (-(N + 3))) P₁ P₂ Q₁ Q₂ ∧
      P₁ % 8 = 0 ∧ P₂ % 8 = 0 ∧ Q₁ % 8 = 0 ∧ Q₂ % 8 = 0 ∧
      P₁ + 16 ≤ P₂ ∧ Q₁ + 16 ≤ Q₂ ∧ A₁ + 16 ≤ A₂ ∧ B₁ + 16 ≤ B₂ ∧
      A₁ ≤ P₁ ∧ P₂ ≤ A₂ ∧ B₁ ≤ Q₁ ∧ Q₂ ≤ B₂ := by
  obtain ⟨d₁, hd₁⟩ : ∃ d : ℕ, (d : ℤ) = N + 3 - m₁ :=
    ⟨(N + 3 - m₁).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : ℕ, (d : ℤ) = N + 3 - m₂ :=
    ⟨(N + 3 - m₂).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h₁ : 4 ≤ d₁ := by omega
  have h₂ : 4 ≤ d₂ := by omega
  have eS₁ : closedDyadicSquare m₁ J₁ K₁ = gridBox ((2 : ℝ) ^ (-(N + 3))) (J₁ * 2 ^ d₁)
      ((J₁ + 1) * 2 ^ d₁) (K₁ * 2 ^ d₁) ((K₁ + 1) * 2 ^ d₁) := by
    rw [closedDyadicSquare_eq_gridBox m₁ J₁ K₁ d₁, show -(m₁ + (d₁ : ℤ)) = -(N + 3) by omega]
  have eS₂ : closedDyadicSquare m₂ J₂ K₂ = gridBox ((2 : ℝ) ^ (-(N + 3))) (J₂ * 2 ^ d₂)
      ((J₂ + 1) * 2 ^ d₂) (K₂ * 2 ^ d₂) ((K₂ + 1) * 2 ^ d₂) := by
    rw [closedDyadicSquare_eq_gridBox m₂ J₂ K₂ d₂, show -(m₂ + (d₂ : ℤ)) = -(N + 3) by omega]
  have hh : (0 : ℝ) < (2 : ℝ) ^ (-(N + 3)) := by positivity
  have hpos₁ : (0 : ℤ) < 2 ^ d₁ := by positivity
  have hpos₂ : (0 : ℤ) < 2 ^ d₂ := by positivity
  have hP : J₁ * 2 ^ d₁ ≤ (J₁ + 1) * 2 ^ d₁ := by nlinarith
  have hQ : K₁ * 2 ^ d₁ ≤ (K₁ + 1) * 2 ^ d₁ := by nlinarith
  rw [eS₁, eS₂] at hS
  obtain ⟨hA₁, hA₂, hB₁, hB₂⟩ := gridBox_subset_ints hh hP hQ hS
  obtain ⟨p1, p2, p3⟩ := dyadic_interval_facts J₁ h₁
  obtain ⟨q1, q2, q3⟩ := dyadic_interval_facts K₁ h₁
  obtain ⟨a1, a2, a3⟩ := dyadic_interval_facts J₂ h₂
  obtain ⟨b1, b2, b3⟩ := dyadic_interval_facts K₂ h₂
  exact ⟨J₂ * 2 ^ d₂, (J₂ + 1) * 2 ^ d₂, K₂ * 2 ^ d₂, (K₂ + 1) * 2 ^ d₂,
    J₁ * 2 ^ d₁, (J₁ + 1) * 2 ^ d₁, K₁ * 2 ^ d₁, (K₁ + 1) * 2 ^ d₁, eS₂, eS₁,
    p1, p2, q1, q2, p3, q3, a3, b3, hA₁, hA₂, hB₁, hB₂⟩

end HarmonicBalls
