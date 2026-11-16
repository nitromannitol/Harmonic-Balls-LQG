import HarmonicBalls.Proposed.PfefferMetricScaling
import HarmonicBalls.FirstPass.S11m.E1Bounds
import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.FirstPass.S11r.RootedFinite

/-! # Annular comparison for a quadratic Weyl shift

A quadratic Weyl shift compares distances across nested annuli to the
original distances across outer and inner annuli.
-/

namespace HarmonicBalls
open Set Metric
open scoped ENNReal

/-- A quadratic Weyl shift compares the distance across the annulus with radii
`r` and `2r` to the original distance across the annulus with radii `1.9r`
and `2r`. -/
theorem pfefferAcross_quadratic_weyl_lower {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ r : ℝ} (hξ : 0 < ξ) (hr : 0 < r)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) =
      weylScaling D ξ (fun z => ‖z‖ ^ 2) x y) :
    ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
      pfefferAcross D 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
      pfefferAcross E 0 r (2 * r) := by
  let a : ℝ := (19 / 10 : ℝ) * r
  let b : ℝ := 2 * r
  have ha : 0 < a := by dsimp [a]; positivity
  have har : r < a := by dsimp [a]; linarith
  have hneA : (sphere (0 : ℂ) a).Nonempty := NormedSpace.sphere_nonempty.mpr ha.le
  have hneB : (sphere (0 : ℂ) b).Nonempty := NormedSpace.sphere_nonempty.mpr (by dsimp [b]; positivity)
  let d := setDist D (sphere (0 : ℂ) a) (sphere (0 : ℂ) b)
  have hd : ∀ x ∈ sphere (0 : ℂ) b, ∀ y ∈ sphere (0 : ℂ) a, d ≤ D x y := by
    intro x hx y hy
    rw [hD.symm x y]
    unfold d setDist
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨u, _, v, _, rfl⟩
      exact S11m.E1Bounds.nonneg_of_isEuclideanLengthMetric hD u v
    · exact ⟨y, hy, x, hx, rfl⟩
  have hcross : pfefferAcross D 0 a b = ENNReal.ofReal d := by
    rw [ofReal_setDist_eq_iInf hneA hneB]
    rfl
  have hweight : ∀ z ∈ closure ((ball (0 : ℂ) a)ᶜ), a ^ 2 ≤ ‖z‖ ^ 2 := by
    intro z hz
    rw [closure_compl, isOpen_ball.interior_eq] at hz
    have hz' : a ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right, not_lt] using hz
    nlinarith [norm_nonneg z]
  have hpoint (x y : ℂ) (hx : x ∈ sphere (0 : ℂ) b) (hy : y ∈ sphere (0 : ℂ) r) :
      ENNReal.ofReal (Real.exp (ξ * a ^ 2) * d) ≤ ENNReal.ofReal (E y x) := by
    rw [hscale]
    have hx' : x ∈ closure ((ball (0 : ℂ) a)ᶜ) := by
      rw [closure_compl, isOpen_ball.interior_eq]
      have hxb : ‖x‖ = b := by simpa [mem_sphere, dist_zero_right] using hx
      simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
      dsimp [a,b] at *
      linarith
    have hy' : y ∉ interior ((ball (0 : ℂ) a)ᶜ) := by
      rw [interior_compl, closure_ball 0 ha.ne']
      have hyr : ‖y‖ = r := by simpa [mem_sphere, dist_zero_right] using hy
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, not_lt]
      linarith
    have h := S11m.E1Bounds.weylScaling_ge_of_exit hD hξ.le hweight hx' hy'
      (fun w hw => by
        rw [frontier_compl, frontier_ball 0 ha.ne'] at hw
        exact hd x hx w hw)
    have hs := hD.weylScaling_symm ξ (fun z : ℂ => ‖z‖ ^ 2) y x
    rw [hs]
    exact h
  change ENNReal.ofReal (Real.exp (ξ * a ^ 2)) * pfefferAcross D 0 a b ≤ pfefferAcross E 0 r b
  rw [hcross, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold pfefferAcross
  exact le_iInf fun y => le_iInf fun hy => le_iInf fun x => le_iInf fun hx => hpoint x y hx hy

/-- A quadratic Weyl shift compares the distance across the annulus with radii
`r` and `1.1r` to the original distance across the annulus with radii `r/2`
and `1.2r`. -/
theorem pfefferAcross_quadratic_weyl_upper {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ r : ℝ} (hξ : 0 < ξ) (hr : 0 < r)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) =
      weylScaling D ξ (fun z => ‖z‖ ^ 2) x y) :
    pfefferAcross E 0 r ((11 / 10 : ℝ) * r) ≤
      ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
      pfefferAcross D 0 (r / 2) ((6 / 5 : ℝ) * r) := by
  let a : ℝ := r / 2
  let b : ℝ := (11 / 10 : ℝ) * r
  let c : ℝ := (6 / 5 : ℝ) * r
  have har : a < r := by dsimp [a]; linarith
  have hrb : r < b := by dsimp [b]; linarith
  have hbc : b < c := by dsimp [b,c]; linarith
  have h0 : ENNReal.ofReal (Real.exp (ξ * b ^ 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hpoint (x y : ℂ) (hx : x ∈ sphere (0 : ℂ) a) (hy : y ∈ sphere (0 : ℂ) c) :
      pfefferAcross E 0 r b ≤ ENNReal.ofReal (Real.exp (ξ * b ^ 2)) * ENNReal.ofReal (D x y) := by
    rw [hD.ofReal_eq_internalMetric]
    unfold internalMetric
    rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
    refine le_iInf fun P => ?_
    rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
    refine le_iInf fun _ => ?_
    by_cases hfin : pathLength D P < ⊤
    · let f : ℝ → ℝ := fun t => ‖P.extend t‖
      have hf : Continuous f := P.continuous_extend.norm
      have hf0 : f 0 = a := by simpa [f, P.extend_zero, mem_sphere, dist_zero_right] using hx
      have hf1 : f 1 = c := by simpa [f, P.extend_one, mem_sphere, dist_zero_right] using hy
      let T : Set ℝ := Icc 0 1 ∩ f ⁻¹' {b}
      have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset
        (isClosed_Icc.inter (isClosed_singleton.preimage hf)) inter_subset_left
      have hTne : T.Nonempty := by
        obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hf.continuousOn
          (show b ∈ Icc (f 0) (f 1) from ⟨by rw [hf0]; linarith, by rw [hf1]; linarith⟩)
        exact ⟨t, ht, hft⟩
      obtain ⟨t, ht⟩ := hTc.exists_isLeast hTne
      have ht0 : 0 ≤ t := ht.1.1.1
      have ht1 : t ≤ 1 := ht.1.1.2
      have hft : f t = b := ht.1.2
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht0 hf.continuousOn
        (show r ∈ Icc (f 0) (f t) from ⟨by rw [hf0]; linarith, by rw [hft]; linarith⟩)
      have hinside : ∀ u ∈ Icc s t, ‖P.extend u‖ ≤ b := by
        intro u hu
        by_contra hn
        have hbu : b < f u := lt_of_not_ge hn
        obtain ⟨v, hv, hvf⟩ := intermediate_value_Icc (hs.1.trans hu.1) hf.continuousOn
          (show b ∈ Icc (f 0) (f u) from ⟨by rw [hf0]; linarith, hbu.le⟩)
        have hvT : v ∈ T := ⟨⟨hv.1, hv.2.trans (hu.2.trans ht1)⟩, hvf⟩
        have htv := ht.2 hvT
        have hvu : v < u := by
          apply lt_of_le_of_ne hv.2
          intro heq
          subst v
          linarith
        exact (not_lt_of_ge (hu.2.trans htv)) hvu
      have hsphere : P.extend s ∈ sphere (0 : ℂ) r := by
        simpa [mem_sphere, dist_zero_right, f] using hfs
      have htsphere : P.extend t ∈ sphere (0 : ℂ) b := by
        simpa [mem_sphere, dist_zero_right, f] using hft
      have hweight : ∀ z ∈ closedBall (0 : ℂ) b,
          Real.exp (ξ * ‖z‖ ^ 2) ≤ Real.exp (ξ * b ^ 2) := by
        intro z hz
        apply Real.exp_le_exp.mpr
        have hz' : ‖z‖ ≤ b := by simpa [mem_closedBall, dist_zero_right] using hz
        have : ‖z‖ ^ 2 ≤ b ^ 2 := by nlinarith [norm_nonneg z]
        exact mul_le_mul_of_nonneg_left this hξ.le
      have hlen : curveLength D P.extend s t ≤ pathLength D P :=
        curveLength_mono_interval D P.extend hs.1 ht1
      have hw := weylScaling_le_mul_curveLength_of_subset hD ξ (Real.exp_pos _) hweight hs.2
        (P.continuous_extend.continuousOn.mono (Icc_subset_Icc hs.1 ht1))
        (fun u hu => by simpa [mem_closedBall, dist_zero_right] using hinside u hu)
        (lt_of_le_of_lt hlen hfin)
      calc
        pfefferAcross E 0 r b ≤ ENNReal.ofReal (E (P.extend s) (P.extend t)) :=
          iInf₂_le_of_le (P.extend s) hsphere (iInf₂_le (P.extend t) htsphere)
        _ = weylScaling D ξ (fun z => ‖z‖ ^ 2) (P.extend s) (P.extend t) := hscale _ _
        _ ≤ ENNReal.ofReal (Real.exp (ξ * b ^ 2)) * curveLength D P.extend s t := hw
        _ ≤ ENNReal.ofReal (Real.exp (ξ * b ^ 2)) * pathLength D P := mul_le_mul_of_nonneg_left hlen zero_le
    · have heq : pathLength D P = ⊤ := top_unique (le_of_not_gt hfin)
      rw [heq, ENNReal.mul_top h0]
      exact le_top
  change pfefferAcross E 0 r b ≤ ENNReal.ofReal (Real.exp (ξ * b ^ 2)) * pfefferAcross D 0 a c
  unfold pfefferAcross at *
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => hpoint x y hx hy
end HarmonicBalls
