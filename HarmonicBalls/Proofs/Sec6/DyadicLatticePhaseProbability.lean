import HarmonicBalls.Proofs.Sec6.GrowingPhaseModuloProbability
import HarmonicBalls.Proofs.Sec6.CriterionThreeLatticeApprox

/-! # Dyadic lattice-valued random phases

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A finer square lattice has at most `m²` classes modulo the lattice whose
mesh is `m` times larger. -/
theorem scaledLattice_finite_representatives (d : ℝ) (m : ℕ) (hm : 0 < m) :
    ∃ F : Finset ℂ, F.card ≤ m ^ 2 ∧
      ∀ z ∈ scaledLattice d, ∃ q ∈ F, z - q ∈ scaledLattice (d * m) := by
  classical
  let square := (Finset.range m) ×ˢ (Finset.range m)
  let f : ℕ × ℕ → ℂ := fun p => (d : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
  refine ⟨square.image f, ?_, ?_⟩
  · calc
      _ ≤ square.card := Finset.card_image_le
      _ = m ^ 2 := by simp [square, pow_two]
  · intro z hz
    obtain ⟨j, k, rfl⟩ := hz
    let M : ℤ := m
    have hM : 0 < M := by dsimp [M]; exact_mod_cast hm
    let r : ℕ := (j % M).toNat
    let t : ℕ := (k % M).toNat
    have hr0 : 0 ≤ j % M := Int.emod_nonneg _ (ne_of_gt hM)
    have ht0 : 0 ≤ k % M := Int.emod_nonneg _ (ne_of_gt hM)
    have hr : (r : ℤ) = j % M := Int.toNat_of_nonneg hr0
    have ht : (t : ℤ) = k % M := Int.toNat_of_nonneg ht0
    have hrm : r < m := by
      have h := hr ▸ Int.emod_lt_of_pos j hM
      dsimp [M] at h
      exact_mod_cast h
    have htm : t < m := by
      have h := ht ▸ Int.emod_lt_of_pos k hM
      dsimp [M] at h
      exact_mod_cast h
    refine ⟨f (r, t), Finset.mem_image.mpr ⟨(r, t), ?_, rfl⟩, ?_⟩
    · simp [square, hrm, htm]
    · refine ⟨j / M, k / M, ?_⟩
      have hj : j = (r : ℤ) + M * (j / M) := by
        rw [hr]
        exact (Int.emod_add_mul_ediv j M).symm
      have hk : k = (t : ℤ) + M * (k / M) := by
        rw [ht]
        exact (Int.emod_add_mul_ediv k M).symm
      have hj' : (j : ℂ) = (r : ℂ) + (m : ℂ) * ((j / M : ℤ) : ℂ) := by exact_mod_cast hj
      have hk' : (k : ℂ) = (t : ℂ) + (m : ℂ) * ((k / M : ℤ) : ℂ) := by exact_mod_cast hk
      simp only [f, Complex.ofReal_mul, Complex.ofReal_natCast]
      rw [hj', hk']
      ring

/-- At each mesh, the lattice at twice the dyadic index has at most
`2^(2*n)` classes modulo the tested lattice. -/
theorem dyadic_lattice_phase_representatives (s : ℝ) :
    ∃ F : ℕ → Finset ℂ, (∀ n, (F n).card ≤ 2 ^ (3 * n)) ∧
      ∀ n z, z ∈ scaledLattice (dyadicScale (2 * n) * s / 100) →
        ∃ q ∈ F n, z - q ∈ scaledLattice (dyadicScale n * s / 100) := by
  classical
  have hrep (n : ℕ) := scaledLattice_finite_representatives
    (dyadicScale (2 * n) * s / 100) (2 ^ n) (by positivity)
  choose F hcard hcover using hrep
  refine ⟨F, ?_, ?_⟩
  · intro n
    calc
      (F n).card ≤ (2 ^ n) ^ 2 := hcard n
      _ = 2 ^ (2 * n) := by rw [← pow_mul]; congr 1; omega
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro n z hz
    obtain ⟨q, hq, hq'⟩ := hcover n z hz
    refine ⟨q, hq, ?_⟩
    have hid : (dyadicScale (2 * n) * s / 100) * ((2 ^ n : ℕ) : ℝ) =
        dyadicScale n * s / 100 := by
      have hp : (dyadicScale n) * ((2 : ℝ) ^ n) = 1 := by
        simp only [dyadicScale, inv_pow, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0)]
      have hd : dyadicScale (2 * n) = dyadicScale n * dyadicScale n := by
        simp only [dyadicScale, mul_comm 2 n, pow_mul, pow_two]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [hd]
      calc
        (dyadicScale n * dyadicScale n * s / 100) * 2 ^ n =
            dyadicScale n * s / 100 * (dyadicScale n * 2 ^ n) := by ring
        _ = _ := by rw [hp, mul_one]
    rwa [hid] at hq'

/-- Every phase is within twice the fine mesh of one of these representatives
plus a vector in the tested lattice. -/
theorem dyadic_lattice_phase_approximation {s : ℝ} (hs : 0 < s) :
    ∃ F : ℕ → Finset ℂ, (∀ n, (F n).card ≤ 2 ^ (3 * n)) ∧
      ∀ n z, ∃ q ∈ F n, ∃ t ∈ scaledLattice (dyadicScale n * s / 100),
        dist z (q + t) < 2 * (dyadicScale (2 * n) * s / 100) := by
  obtain ⟨F, hcard, hcover⟩ := dyadic_lattice_phase_representatives s
  refine ⟨F, hcard, ?_⟩
  intro n z
  obtain ⟨w, hw, hdist⟩ := exists_scaledLattice_dist_lt z (δ := dyadicScale (2 * n) * s / 100)
    (div_pos (mul_pos (dyadicScale_pos _) hs) (by norm_num))
  obtain ⟨q, hq, ht⟩ := hcover n w hw
  refine ⟨q, hq, w - q, ht, ?_⟩
  simpa only [add_sub_cancel] using hdist

/-- The singular third-criterion estimate permits arbitrary field-dependent
phases in the dyadic lattice of index `2*n` at tested index `n`. -/
theorem exists_universal_singular_dyadicLattice_phase_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ x : ℂ,
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (phase : Ω → ℕ → ℂ),
      (∀ ω n, phase ω n ∈ scaledLattice (dyadicScale (2 * n) * s / 100)) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (phase ω)} ≤ δ := by
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_singular_growing_phaseModulo_probability
      (α := α) hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd phase hphase
  obtain ⟨F, hcard, hcover⟩ := dyadic_lattice_phase_representatives s
  exact hbound N hN Ω P hC hcirc μ hgff hμ hE0 s hs x hd F hcard phase
    (fun ω n => hcover n (phase ω n) (hphase ω n))

end HarmonicBalls.Section6
