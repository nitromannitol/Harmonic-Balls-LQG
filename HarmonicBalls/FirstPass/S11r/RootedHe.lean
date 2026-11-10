import HarmonicBalls.FirstPass.S11r.RootedTriangle

/-!
# First pass, internal-side hypotheses of the rooted gluing for the Weyl-scaled physical metric (fp-S11r, owner n2)

For a length metric `d` and a weight `f`, the physical metric of the rooted field is `e := weylPhysicalE d ξ f`, the
real part of the Weyl scaling `weylScaling d ξ f`. On an open connected `D` where `exp (ξ f) ≤ M`, this file proves the
internal-side hypotheses of `eq_const_mul_internal_of_local_agreement` (RootedRepair.lean) for `internalPhysicalMetric e D`:

* `he_symm` (`weylPhysicalE_internalPhysical_symm`), `he_tri` (`weylPhysicalE_internalPhysical_tri`),
  `he_len` (`weylPhysicalE_internalPhysical_length`), with the finiteness `weylPhysicalE_internal_ne_top` (Steps A, B-C-G, H).

The remaining internal-side hypothesis `he_cont` (root continuity, Steps E-F) is not in this file.
-/

namespace HarmonicBalls

open Set Filter Topology Metric unitInterval
open scoped ENNReal

/-- The real part of the Weyl scaling `weylScaling d ξ f`: the physical metric of the rooted field (on `ℂ × ℂ`). -/
noncomputable def weylPhysicalE (d : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) : ℂ → ℂ → ℝ :=
  fun a b => (weylScaling d ξ f a b).toReal

/-- The Weyl scaling vanishes on the diagonal: the constant curve on `[0, 0]` is length-parametrized of cost `0`. -/
theorem weylScaling_self_eq_zero {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ) (x : ℂ) :
    weylScaling d ξ f x x = 0 := by
  have hcurve : curveLength d (fun _ => x) 0 0 = 0 := by
    unfold curveLength
    refine le_antisymm (iSup_le fun w => ?_) zero_le
    rcases w with ⟨N, u, hu, hmem⟩
    simp [hd.self_eq_zero x]
  have hlp : IsLengthParametrized d (fun _ => x) 0 := by
    refine ⟨le_refl 0, continuousOn_const, fun s t hs hst ht => ?_⟩
    obtain rfl : s = 0 := le_antisymm (hst.trans ht) hs
    obtain rfl : t = 0 := le_antisymm ht (hs.trans hst)
    rw [hcurve]
    simp
  refine le_antisymm ?_ zero_le
  unfold weylScaling
  refine le_trans (iInf_le _ (0 : ℝ)) (le_trans (iInf_le _ (fun _ => x))
    (le_trans (iInf_le _ hlp) (le_trans (iInf_le _ rfl) (le_trans (iInf_le _ rfl) ?_))))
  simp

/-- The Weyl scaling is finite on `D × D` (a path of finite length in `D` gives the bound `M` times its length). -/
theorem weylScaling_ne_top_on {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {M : ℝ} (hM : 0 < M)
    (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M) {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D) :
    weylScaling d ξ f x y ≠ ⊤ := by
  have hlt : internalMetric d D x y < ⊤ :=
    lt_top_iff_ne_top.2 (S11m.internalMetric_ne_top_of_isConnected hd hD hDc hx hy)
  unfold internalMetric at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hPD, hPlt⟩ := iInf_lt_iff.1 hP
  have hfin0 : curveLength d P.extend 0 1 < ⊤ := hPlt
  have hPD' : ∀ t ∈ Icc (0 : ℝ) 1, P.extend t ∈ D := fun t ht => by
    have e1 : P.extend t = P ⟨t, ht⟩ := Path.extend_extends' P ⟨t, ht⟩
    rw [e1]
    exact hPD _
  have h := weylScaling_le_mul_curveLength_of_subset hd ξ hM hfM zero_le_one
    P.continuous_extend.continuousOn hPD' hfin0
  rw [Path.extend_zero, Path.extend_one] at h
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin0.ne) h

/-- The symmetry of the physical metric. -/
theorem weylPhysicalE_symm {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ) :
    ∀ x y, weylPhysicalE d ξ f x y = weylPhysicalE d ξ f y x := by
  intro x y
  unfold weylPhysicalE
  rw [IsEuclideanLengthMetric.weylScaling_symm hd ξ f x y]

/-- The physical metric vanishes on the diagonal of `D`. -/
theorem weylPhysicalE_self {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ) :
    ∀ x, weylPhysicalE d ξ f x x = 0 := by
  intro x
  unfold weylPhysicalE
  rw [weylScaling_self_eq_zero hd ξ f x]
  simp

/-- The triangle inequality of the physical metric on `D`, from the triangle inequality of the Weyl scaling and its
finiteness on `D × D` (`RootedLocal.toReal_triangle_on`). -/
theorem weylPhysicalE_tri {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {M : ℝ} (hM : 0 < M)
    (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      weylPhysicalE d ξ f x z ≤ weylPhysicalE d ξ f x y + weylPhysicalE d ξ f y z := by
  intro x hx y hy z hz
  unfold weylPhysicalE
  exact RootedLocal.toReal_triangle_on hd (weylScaling_ne_top_on hd ξ hD hDc hM hfM hx hy)
    (weylScaling_ne_top_on hd ξ hD hDc hM hfM hy hz)

/-- Finiteness of the internal metric of the physical metric on `D × D`. -/
theorem weylPhysicalE_internal_ne_top {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {M : ℝ} (hM : 0 < M)
    (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M) :
    ∀ x ∈ D, ∀ y ∈ D, internalMetric (weylPhysicalE d ξ f) D x y ≠ ⊤ :=
  fun _ hx _ hy => internalMetric_weylScaling_toReal_ne_top hd ξ hD hDc hM hfM hx hy

/-- **Internal-side hypotheses `he_symm`, `he_tri`, `he_len` for the Weyl-scaled physical metric** (Steps A, C, H of
CHATGPT-n2-R2-rooted-length.md section 3): the internal physical metric of `weylPhysicalE d ξ f` on `D` is symmetric,
satisfies the triangle inequality on `D`, and is a length metric on `D`. -/
theorem weylPhysicalE_internalPhysical_props {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {M : ℝ} (hM : 0 < M)
    (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M) :
    (∀ x y, internalPhysicalMetric (weylPhysicalE d ξ f) D x y =
        internalPhysicalMetric (weylPhysicalE d ξ f) D y x) ∧
    (∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x w ≤
        internalPhysicalMetric (weylPhysicalE d ξ f) D x y + internalPhysicalMetric (weylPhysicalE d ξ f) D y w) ∧
    (∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (internalPhysicalMetric (weylPhysicalE d ξ f) D x y) =
        internalMetric (internalPhysicalMetric (weylPhysicalE d ξ f) D) D x y) := by
  have hs := weylPhysicalE_symm hd ξ f
  have hfin := weylPhysicalE_internal_ne_top hd ξ hD hDc hM hfM
  refine ⟨internalPhysicalMetric_symm_of (internalMetric_symm_of_symm hs D), ?_,
    internalPhysicalMetric_length_eq hs hfin⟩
  exact internalPhysicalMetric_tri_of
    (fun x hx y hy w hw => internalMetric_triangle_on _ hs (fun x hx => weylPhysicalE_self hd ξ f x)
      (fun x hx y hy z hz => weylPhysicalE_tri hd ξ hD hDc hM hfM x hx y hy z hz) ) hfin

end HarmonicBalls
