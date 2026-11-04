import HarmonicBalls.Proofs.Sec5.PuncturedMaximumPrinciple

/-! # Comparison of harmonic minorants across a puncture -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace

/-- An upper bound on the outer circle for the difference of a harmonic
minorant and a harmonic comparison function holds throughout the punctured
disc. The logarithmic barrier is removed by letting its coefficient tend to
zero. -/
theorem IsHarmonicMinorant.sub_le_of_boundary_punctured
    {O : Set ℂ} {z a c : ℂ} {r C : ℝ} {h q : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (haz : a ≠ z) (ha : a ∈ closedBall c r)
    (hO : closedBall c r \ {a} ⊆ O) (hq : HarmonicOnNhd q (closedBall c r))
    (hbd : ∀ x ∈ sphere c r, x ≠ a → h x - q x ≤ C) :
    ∀ x ∈ ball c r \ {a}, h x - q x ≤ C := by
  intro x hx
  let M := r + ‖c - a‖
  have hlog : ∀ y ∈ sphere c r, Real.log ‖y - a‖ ≤ M := by
    intro y hy
    have hnorm : ‖y - c‖ = r := by simpa [dist_eq_norm] using mem_sphere.mp hy
    calc
      Real.log ‖y - a‖ ≤ ‖y - a‖ := Real.log_le_self (norm_nonneg _)
      _ ≤ ‖y - c‖ + ‖c - a‖ := by simpa [dist_eq_norm] using dist_triangle y c a
      _ = M := by rw [hnorm]
  have hε : ∀ ε > 0, h x - q x ≤ C + ε * (M - Real.log ‖x - a‖) := by
    intro ε hεpos
    have hbound := hh.add_log_sub_le_of_boundary haz hεpos ha hO hq
      (C := C + ε * M) (fun y hy hya => by
        have := hbd y hy hya
        have := mul_le_mul_of_nonneg_left (hlog y hy) hεpos.le
        linarith) x hx
    linarith
  have hlim : Tendsto (fun ε : ℝ => C + ε * (M - Real.log ‖x - a‖)) (𝓝[>] 0) (𝓝 C) := by
    have hcont : ContinuousAt (fun ε : ℝ => C + ε * (M - Real.log ‖x - a‖)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  exact hε ε hεpos

/-- Removing a point different from the pole does not enlarge any harmonic
minorant beyond the greatest harmonic minorant of the full disc. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_punctured
    {R : ℝ} {z a : ℂ} (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ha : a ∈ ball (0 : ℂ) R) {h : ℂ → ℝ}
    (hh : IsHarmonicMinorant (ball 0 R \ {a}) (newtonKernelEReal z) h)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) R \ {a}) :
    h x ≤ greatestHarmonicMinorantBall R z x := by
  have hza : z ≠ a := by simpa using hz.2
  have hzn : ‖z‖ < R := mem_ball_zero_iff.mp hz.1
  have han : ‖a‖ < R := mem_ball_zero_iff.mp ha
  have hxn : ‖x‖ < R := mem_ball_zero_iff.mp hx.1
  have hR : 0 < R := (norm_nonneg z).trans_lt hzn
  have hr₀ : max ‖a‖ (max ‖z‖ ‖x‖) < R := max_lt han (max_lt hzn hxn)
  let B : ℝ → ℝ := fun ρ =>
    (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖z‖ ^ 2) * (R ^ 2 - ρ ^ 2) / (R ^ 2 * (ρ - ‖z‖) ^ 2))
  have hgB : ∀ ρ ∈ Ioo (max ‖a‖ (max ‖z‖ ‖x‖)) R,
      h x - greatestHarmonicMinorantBall R z x ≤ B ρ := by
    rintro ρ ⟨hρ₀, hρR⟩
    have haρ : ‖a‖ < ρ := (le_max_left _ _).trans_lt hρ₀
    have hzρ : ‖z‖ < ρ := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hρ₀)
    have hxρ : ‖x‖ < ρ := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hρ₀)
    have hq : HarmonicOnNhd (greatestHarmonicMinorantBall R z) (closedBall 0 ρ) :=
      (isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1.mono
        (closedBall_subset_ball hρR)
    have hO : closedBall (0 : ℂ) ρ \ {a} ⊆ ball 0 R \ {a} :=
      fun _ hy => ⟨closedBall_subset_ball hρR hy.1, hy.2⟩
    apply hh.sub_le_of_boundary_punctured (Ne.symm hza) (mem_closedBall_zero_iff.mpr haρ.le)
      hO hq (C := B ρ) _ x ⟨mem_ball_zero_iff.mpr hxρ, hx.2⟩
    intro y hy hya
    have hyn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    have hyz : y ≠ z := by rintro rfl; exact hzρ.ne hyn
    have hyR : ‖y‖ < R := hyn ▸ hρR
    have hpos := norm_sub_conj_mul_pos hR hzn hyR.le
    have h1 : h y ≤ newtonKernel z y := by
      have h := hh.2 y ⟨mem_ball_zero_iff.mpr hyR, by simpa using hya⟩
      simpa [newtonKernelEReal, hyz] using h
    have h2 := newtonKernel_sub_greenBall hR (Ne.symm hyz) hpos.ne'
    have h3 := greenBall_le_of_norm_eq hR hzρ hyn hρR.le
    dsimp only [B]
    linarith
  have hB : Tendsto B (𝓝[<] R) (𝓝 0) := by
    have hden : R ^ 2 * (R - ‖z‖) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (sub_ne_zero.2 hzn.ne'))
    have hc : ContinuousAt B R :=
      continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hden)
    have h0 : B R = 0 := by simp [B]
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hB (eventually_of_mem (Ioo_mem_nhdsLT hr₀) hgB)
  linarith

/-- A point different from the pole is removable for the greatest harmonic
minorant defining the Green function of a disc. -/
theorem greatestHarmonicMinorant_punctured_ball {R : ℝ} {z a x : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (hx : x ∈ ball (0 : ℂ) R \ {a}) :
    greatestHarmonicMinorant (ball 0 R \ {a}) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_punctured hz ha hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ {a}) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- Removing a point different from the pole leaves the Green function of a
disc unchanged at every other point. -/
theorem greenFunction_punctured_ball {R : ℝ} {z a x : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (hx : x ∈ ball (0 : ℂ) R \ {a}) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ {a}) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_punctured_ball ha hz hx, EReal.toReal_coe,
    greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]

/-- The Green function stays above a positive constant at points arbitrarily close
to the removed interior point. -/
theorem frequently_green_pos_punctured_disc {R : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      c ≤ greenFunction (ball (0 : ℂ) R \ {a}) z x :=
  frequently_green_pos_punctured_disc_of_green_eq ha hz
    (fun _ hx hxz => greenFunction_punctured_ball ha hz hx hxz)

/-- Compactly contained compatibility forces the punctured-disc least
supersolution to be inadmissible. This implication does not assert compatibility
or establish an obstacle counterexample. -/
theorem not_admissible_punctured_disc_of_compact_compatibility_proved
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ} {A : Set ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hA : closure A ⊆ ball (0 : ℂ) R \ {a})
    (heq : closure A = closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t)) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t :=
  not_admissible_punctured_disc_of_compact_compatibility ha hz ht
    (fun _ hx hxz => greenFunction_punctured_ball ha hz hx hxz) hA heq

#print axioms frequently_green_pos_punctured_disc
#print axioms not_admissible_punctured_disc_of_compact_compatibility_proved

#print axioms greatestHarmonicMinorant_punctured_ball
#print axioms greenFunction_punctured_ball

#print axioms IsHarmonicMinorant.le_greatestHarmonicMinorantBall_punctured

#print axioms IsHarmonicMinorant.sub_le_of_boundary_punctured

end HarmonicBalls
