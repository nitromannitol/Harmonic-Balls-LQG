import HarmonicBalls.Steps.Sec11.ExponentialAnnulusCorridors
import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation
import Mathlib.Topology.MetricSpace.Thickening

/-! # Finite ball covers at exponential annular scales

A compactness argument gives one finite family of balls at unit scale. Its
positive dilations cover all geometric shells, with larger balls still inside
the corresponding open annular corridors.
-/

namespace HarmonicBalls

open Set Metric

/-- Positive dilation carries the unit geometric shell to the shell at the
specified exponential scale. -/
theorem image_smul_unit_geometricShell (s : ℝ) (n : ℕ) :
    (fun x : ℂ => Real.exp (-(s + n)) • x) ''
        geometricShell 1 (Real.exp (-1)) 0 =
      geometricShell (Real.exp (-s)) (Real.exp (-1)) n := by
  let k : ℝ := Real.exp (-(s + n))
  have hk : 0 < k := Real.exp_pos _
  have hk' : Real.exp (-s) * Real.exp (-1) ^ n = k := by
    dsimp [k]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hmem (x : ℂ) : k • x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n ↔
      x ∈ geometricShell 1 (Real.exp (-1)) 0 := by
    simp only [geometricShell, mem_ofPred_eq, pow_succ, pow_zero, mul_one, one_mul,
      norm_smul, Real.norm_eq_abs, abs_of_pos hk, ← mul_assoc, hk']
    have hle : k * ‖x‖ ≤ k ↔ ‖x‖ ≤ 1 := by
      simpa only [mul_one] using
        (mul_le_mul_iff_right₀ hk : k * ‖x‖ ≤ k * 1 ↔ ‖x‖ ≤ 1)
    rw [mul_le_mul_iff_right₀ hk, hle]
  change (fun x : ℂ => k • x) '' _ = _
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hy
    refine ⟨k⁻¹ • y, (hmem _).1 ?_, ?_⟩
    · simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    · simp [hk.ne']

/-- Positive dilation carries the unit corridor to its exponential-scale copy. -/
theorem image_smul_unit_exponentialAnnulusCorridor (s : ℝ) (n : ℕ) :
    (fun x : ℂ => Real.exp (-(s + n)) • x) '' exponentialAnnulusCorridor 0 0 =
      exponentialAnnulusCorridor s n := by
  let k : ℝ := Real.exp (-(s + n))
  have hk : 0 < k := Real.exp_pos _
  have hlo : k * Real.exp (-2) = Real.exp (-((n : ℝ) + s + 2)) := by
    dsimp [k]
    rw [← Real.exp_add]
    congr 1
    ring
  have hhi : k * Real.exp 1 = Real.exp (-((n : ℝ) + s - 1)) := by
    dsimp [k]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmem (x : ℂ) : k • x ∈ exponentialAnnulusCorridor s n ↔
      x ∈ exponentialAnnulusCorridor 0 0 := by
    simp only [exponentialAnnulusCorridor, mem_ofPred_eq, Nat.cast_zero, zero_add,
      zero_sub, neg_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hk, ← hlo, ← hhi,
      mul_lt_mul_iff_right₀ hk]
  change (fun x : ℂ => k • x) '' _ = _
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hy
    refine ⟨k⁻¹ • y, (hmem _).1 ?_, ?_⟩
    · simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    · simp [hk.ne']

/-- The unit closed shell is connected. -/
theorem isConnected_unit_geometricShell :
    IsConnected (geometricShell 1 (Real.exp (-1)) 0) := by
  let a : ℝ := Real.exp (-1)
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by
    simpa only [a, Real.exp_zero] using Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
  let F : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ) * p.2
  have hc : Continuous F := by fun_prop
  have hprod : IsConnected (Icc a 1 ×ˢ sphere (0 : ℂ) 1) :=
    (isConnected_Icc ha1).prod (isConnected_sphere (by simp) 0 (by norm_num))
  have himage : F '' (Icc a 1 ×ˢ sphere (0 : ℂ) 1) =
      geometricShell 1 (Real.exp (-1)) 0 := by
    ext z
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
      have ht0 : 0 ≤ t := ha.le.trans ht.1
      simpa [F, geometricShell, a, hu', Real.norm_eq_abs, abs_of_nonneg ht0] using ht
    · intro hz
      have hz' : a ≤ ‖z‖ ∧ ‖z‖ ≤ 1 := by
        simpa [geometricShell, a] using hz
      have hnpos : 0 < ‖z‖ := ha.trans_le hz'.1
      let u : ℂ := z / (‖z‖ : ℂ)
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere, dist_zero_right]
        simp [u, ne_of_gt hnpos]
      refine ⟨(‖z‖, u), ⟨hz', hu⟩, ?_⟩
      dsimp [F, u]
      have hne : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
      field_simp
  rw [← himage]
  exact hprod.image F hc.continuousOn

/-- Every exponential geometric shell is connected. -/
theorem isConnected_exponential_geometricShell (s : ℝ) (n : ℕ) :
    IsConnected (geometricShell (Real.exp (-s)) (Real.exp (-1)) n) := by
  rw [← image_smul_unit_geometricShell s n]
  exact isConnected_unit_geometricShell.image _ (by fun_prop)

/-- A finite unit-scale set of centers and one positive radius give covers of
all shells, while doubled balls remain in their respective corridors. -/
theorem exists_scaled_finite_ball_cover :
    ∃ (ε : ℝ) (centers : Set ℂ), 0 < ε ∧ centers.Finite ∧
      centers ⊆ geometricShell 1 (Real.exp (-1)) 0 ∧
      ∀ (s : ℝ) (n : ℕ),
        geometricShell (Real.exp (-s)) (Real.exp (-1)) n ⊆
          ⋃ z ∈ centers, ball (Real.exp (-(s + n)) • z) (Real.exp (-(s + n)) * ε) ∧
        ∀ z ∈ centers, ball (Real.exp (-(s + n)) • z)
          (Real.exp (-(s + n)) * (2 * ε)) ⊆ exponentialAnnulusCorridor s n := by
  let K := geometricShell 1 (Real.exp (-1)) 0
  have hK : IsCompact K := isCompact_geometricShell _ _ _
  have hsub : K ⊆ exponentialAnnulusCorridor 0 0 := by
    simpa only [neg_zero, Real.exp_zero] using geometricShell_subset_exponentialAnnulusCorridor 0 0
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_thickening_subset_open
    (isOpen_exponentialAnnulusCorridor 0 0) hsub
  obtain ⟨centers, hcK, hcfin, hcover⟩ := hK.finite_cover_balls (half_pos hδ)
  refine ⟨δ / 2, centers, half_pos hδ, hcfin, hcK, ?_⟩
  intro s n
  let k : ℝ := Real.exp (-(s + n))
  have hk : 0 < k := Real.exp_pos _
  have hshell := image_smul_unit_geometricShell s n
  have hcorr := image_smul_unit_exponentialAnnulusCorridor s n
  change (fun x : ℂ => k • x) '' K = _ at hshell
  change (fun x : ℂ => k • x) '' exponentialAnnulusCorridor 0 0 = _ at hcorr
  constructor
  · intro x hx
    rw [← hshell] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
    refine mem_iUnion₂.mpr ⟨z, hz, ?_⟩
    rw [← image_real_smul_ball hk]
    exact ⟨y, hyz, rfl⟩
  · intro z hz x hx
    have hball : ball z (2 * (δ / 2)) ⊆ exponentialAnnulusCorridor 0 0 := by
      rw [show 2 * (δ / 2) = δ by ring]
      exact (ball_subset_thickening (hcK hz) δ).trans hδsub
    rw [← image_real_smul_ball hk] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← hcorr]
    exact ⟨y, hball hy, rfl⟩

#print axioms image_smul_unit_geometricShell
#print axioms image_smul_unit_exponentialAnnulusCorridor
#print axioms isConnected_exponential_geometricShell
#print axioms isConnected_unit_geometricShell
#print axioms exists_scaled_finite_ball_cover

end HarmonicBalls
