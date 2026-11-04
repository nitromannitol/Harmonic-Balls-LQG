import HarmonicBalls.Proofs.Sec8.PhaseCriterionTranslation

/-! # Periodicity of the shifted lattice criterion

All dyadic lattices used in criterion three contain the coarsest lattice.
Thus a common lattice translation of the phases does not change the event. -/

namespace HarmonicBalls

open MeasureTheory

private theorem scaledLattice_add {δ : ℝ} {z w : ℂ}
    (hz : z ∈ Section6.scaledLattice δ) (hw : w ∈ Section6.scaledLattice δ) :
    z + w ∈ Section6.scaledLattice δ := by
  rcases hz with ⟨j, k, rfl⟩
  rcases hw with ⟨l, m, rfl⟩
  refine ⟨j + l, k + m, ?_⟩
  push_cast
  ring

private theorem scaledLattice_neg {δ : ℝ} {z : ℂ}
    (hz : z ∈ Section6.scaledLattice δ) : -z ∈ Section6.scaledLattice δ := by
  rcases hz with ⟨j, k, rfl⟩
  refine ⟨-j, -k, ?_⟩
  push_cast
  ring

/-- The dyadic lattice at any inner scale contains the outer-scale lattice. -/
theorem scaledLattice_outer_subset_dyadic (ρ : ℝ) (n : ℕ) :
    Section6.scaledLattice (ρ / 100) ⊆
      Section6.scaledLattice (dyadicScale n * ρ / 100) := by
  intro z hz
  rcases hz with ⟨j, k, rfl⟩
  refine ⟨(2 ^ n : ℤ) * j, (2 ^ n : ℤ) * k, ?_⟩
  have hpow : (dyadicScale n : ℂ) * (2 : ℂ) ^ n = 1 := by
    simp only [dyadicScale, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
    rw [← mul_pow]
    norm_num
  push_cast
  calc
    (↑ρ / 100 : ℂ) * (↑j + ↑k * Complex.I) =
        ((↑(dyadicScale n) * (2 : ℂ) ^ n) * ↑ρ / 100) *
          (↑j + ↑k * Complex.I) := by rw [hpow]; ring
    _ = (↑(dyadicScale n) * ↑ρ / 100) *
          ((2 : ℂ) ^ n * ↑j + ((2 : ℂ) ^ n * ↑k) * Complex.I) := by ring

/-- Criterion three only depends on each phase modulo its corresponding lattice. -/
theorem phaseVeryGoodCriterionThree_congr_lattice (μ : Measure ℂ) (ρ : ℝ)
    (x : ℂ) (N : ℕ) (a b c : ℝ) (phase shift : ℕ → ℂ)
    (hshift : ∀ n, N ≤ n → shift n ∈
      Section6.scaledLattice (dyadicScale n * ρ / 100)) :
    PhaseVeryGoodCriterionThree μ ρ x N a b c phase ↔
      PhaseVeryGoodCriterionThree μ ρ x N a b c (fun n => phase n + shift n) := by
  have hmem (n : ℕ) (hn : N ≤ n) (z : ℂ) :
      z - phase n ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) ↔
      z - (phase n + shift n) ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) := by
    constructor
    · intro h
      have h' := scaledLattice_add h (scaledLattice_neg (hshift n hn))
      convert h' using 1; abel
    · intro h
      have h' := scaledLattice_add h (hshift n hn)
      convert h' using 1; abel
  simp only [PhaseVeryGoodCriterionThree]
  constructor <;> intro h n hn z hz hlat
  · exact h n hn z hz ((hmem n hn z).mpr hlat)
  · exact h n hn z hz ((hmem n hn z).mp hlat)

/-- A common outer-scale lattice vector is a period for every inner phase. -/
theorem phaseVeryGoodCriterionThree_outer_period (μ : Measure ℂ) (ρ : ℝ)
    (x : ℂ) (N : ℕ) (a b c : ℝ) (phase : ℕ → ℂ) {t : ℂ}
    (ht : t ∈ Section6.scaledLattice (ρ / 100)) :
    PhaseVeryGoodCriterionThree μ ρ x N a b c phase ↔
      PhaseVeryGoodCriterionThree μ ρ x N a b c (fun n => phase n + t) :=
  phaseVeryGoodCriterionThree_congr_lattice μ ρ x N a b c phase (fun _ => t)
    (fun n _ => scaledLattice_outer_subset_dyadic ρ n ht)

end HarmonicBalls
