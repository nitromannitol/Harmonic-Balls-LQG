import HarmonicBalls.Defs.Annuli

/-!
# Translation covariance of the Green function and of the annulus Green potential (B2 sec 5.1 support, deterministic)

`greenFunction O x y` (Defs/Green.lean:70) is `newtonKernel x y` minus the value at `y` of the greatest harmonic
minorant of `newtonKernelEReal x` on `O` (Defs/Green.lean:61). Both ingredients are covariant under the translation
`w ↦ w + c`: `newtonKernel` depends only on differences, and translates of harmonic functions are harmonic. Hence
`G_{τ⁻¹O}(x, y) = G_O(x + c, y + c)` for `τ(w) = w + c` (Armitage-Gardiner, Section 4.1). The annulus Green potential
`annulusGreenPotentialSup` (Defs/Annuli.lean:65) is covariant under the same translation.
-/

open MeasureTheory Filter Metric Set Topology
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- Translation of a `C²` function: `v ↦ g (v + c)` is `C²` at `y` iff `g` is `C²` at `y + c`. -/
lemma contDiffAt_comp_add_right_iff (g : ℂ → ℝ) (c y : ℂ) :
    ContDiffAt ℝ 2 (fun v => g (v + c)) y ↔ ContDiffAt ℝ 2 g (y + c) := by
  constructor
  · intro h
    have h' : ContDiffAt ℝ 2 (fun v => g (v + c)) (y + c - c) := by
      rw [add_sub_cancel_right]; exact h
    have h'' := h'.comp (y + c) (contDiffAt_id.sub contDiffAt_const)
    simpa [Function.comp_def] using h''
  · intro h
    exact h.comp y (contDiffAt_id.add contDiffAt_const)

/-- The Laplacian commutes with translation (Mathlib `iteratedFDeriv_comp_add_right`). -/
lemma laplacian_comp_add_right_eq (f : ℂ → ℝ) (c : ℂ) :
    Laplacian.laplacian (fun v => f (v + c)) = fun x => Laplacian.laplacian f (x + c) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  funext x
  simp only [iteratedFDeriv_comp_add_right]

/-- A translate of a harmonic function is harmonic at `x` iff the function is harmonic at `x + c`. -/
lemma harmonicAt_comp_add_right_iff (f : ℂ → ℝ) (c x : ℂ) :
    InnerProductSpace.HarmonicAt (fun v => f (v + c)) x ↔ InnerProductSpace.HarmonicAt f (x + c) := by
  unfold InnerProductSpace.HarmonicAt
  rw [laplacian_comp_add_right_eq, contDiffAt_comp_add_right_iff]
  have hmap : Filter.map (fun v : ℂ => v + c) (𝓝 x) = 𝓝 (x + c) :=
    (Homeomorph.addRight c).map_nhds_eq x
  have hev : ∀ g : ℂ → ℝ, (∀ᶠ v in 𝓝 x, g (v + c) = 0) ↔ (∀ᶠ w in 𝓝 (x + c), g w = 0) := by
    intro g
    rw [← hmap, Filter.eventually_map]
  simp only [Filter.EventuallyEq, Pi.zero_apply]
  rw [hev (Laplacian.laplacian f)]

/-- Harmonic minorants are transported by translation: `h` is a harmonic minorant of `u` on `O` iff
`w ↦ h (w + c)` is one of `w ↦ u (w + c)` on `τ⁻¹ O`, `τ w = w + c`. -/
lemma isHarmonicMinorant_comp_add_right_iff (O : Set ℂ) (u : ℂ → EReal) (c : ℂ) (h : ℂ → ℝ) :
    IsHarmonicMinorant ((fun w => w + c) ⁻¹' O) (fun w => u (w + c)) (fun w => h (w + c)) ↔
      IsHarmonicMinorant O u h := by
  unfold IsHarmonicMinorant InnerProductSpace.HarmonicOnNhd
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hv' : v - c ∈ (fun w => w + c) ⁻¹' O := by simpa using hv
      have := (harmonicAt_comp_add_right_iff h c (v - c)).mp (h1 (v - c) hv')
      rwa [sub_add_cancel] at this
    · have hv' : v - c ∈ (fun w => w + c) ⁻¹' O := by simpa using hv
      have := h2 (v - c) hv'
      simpa using this
  · rintro ⟨h1, h2⟩
    exact ⟨fun w hw => (harmonicAt_comp_add_right_iff h c w).mpr (h1 (w + c) hw),
      fun w hw => h2 (w + c) hw⟩

/-- The same transport, with the minorant written on the translated side. -/
lemma isHarmonicMinorant_comp_add_right_iff' (O : Set ℂ) (u : ℂ → EReal) (c : ℂ) (h : ℂ → ℝ) :
    IsHarmonicMinorant ((fun w => w + c) ⁻¹' O) (fun w => u (w + c)) h ↔
      IsHarmonicMinorant O u (fun v => h (v - c)) := by
  have e := isHarmonicMinorant_comp_add_right_iff O u c (fun v => h (v - c))
  simpa only [add_sub_cancel_right] using e

/-- The greatest harmonic minorant is translation covariant (the supremum is reindexed by `h ↦ h (· + c)`). -/
lemma greatestHarmonicMinorant_comp_add_right (O : Set ℂ) (u : ℂ → EReal) (c y : ℂ) :
    greatestHarmonicMinorant ((fun w => w + c) ⁻¹' O) (fun w => u (w + c)) y =
      greatestHarmonicMinorant O u (y + c) := by
  unfold greatestHarmonicMinorant
  apply le_antisymm
  · refine iSup₂_le fun h' hh' => ?_
    have hh : IsHarmonicMinorant O u (fun v => h' (v - c)) :=
      (isHarmonicMinorant_comp_add_right_iff' O u c h').mp hh'
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (h : ℂ → ℝ) (_ : IsHarmonicMinorant O u h) =>
      ((h (y + c) : ℝ) : EReal)) (fun v => h' (v - c)) hh)
    simp
  · refine iSup₂_le fun h hh => ?_
    exact le_iSup₂_of_le (fun w => h (w + c))
      ((isHarmonicMinorant_comp_add_right_iff O u c h).mpr hh) le_rfl

/-- **Translation covariance of the Green function.** For `τ w = w + c`,
`G_{τ⁻¹O}(x, y) = G_O(x + c, y + c)` (Defs/Green.lean:70; the kernel `newtonKernel` depends on differences). -/
theorem greenFunction_comp_add_right (O : Set ℂ) (c x y : ℂ) :
    greenFunction ((fun w => w + c) ⁻¹' O) x y = greenFunction O (x + c) (y + c) := by
  have hu : (fun w => newtonKernelEReal (x + c) (w + c)) = newtonKernelEReal x := by
    funext w
    simp [newtonKernelEReal, newtonKernel]
  unfold greenFunction
  rw [← hu, greatestHarmonicMinorant_comp_add_right O (newtonKernelEReal (x + c)) c y]
  have hk : newtonKernel x y = newtonKernel (x + c) (y + c) := by
    simp only [newtonKernel, add_sub_add_right_eq_sub]
  have hc : (x ∈ (fun w => w + c) ⁻¹' O ∧ y ∈ (fun w => w + c) ⁻¹' O ∧ x ≠ y) ↔
      (x + c ∈ O ∧ y + c ∈ O ∧ x + c ≠ y + c) := by
    simp only [Set.mem_preimage, ne_eq, add_left_inj]
  rw [hk]
  split_ifs with h1 h2 <;> simp_all

/-- The ball `B_b(z)` is the translate of `B_b(0)` by `z`. -/
lemma ball_preimage_add_right (z : ℂ) (b : ℝ) : (fun w => w + z) ⁻¹' ball z b = ball 0 b := by
  ext w
  simp [Metric.mem_ball, dist_eq_norm]

/-- Green function of `B_b(0)` at translated points: `G_{B_b(0)}(x, y) = G_{B_b(z)}(x + z, y + z)`. -/
theorem greenFunction_ball_add (z : ℂ) (b : ℝ) (x y : ℂ) :
    greenFunction (ball 0 b) x y = greenFunction (ball z b) (x + z) (y + z) := by
  rw [← ball_preimage_add_right z b, greenFunction_comp_add_right]

/-- Membership in the annulus is translation covariant. -/
lemma mem_annulus_add_right_iff (z : ℂ) (a b : ℝ) (w : ℂ) :
    w + z ∈ annulus z a b ↔ w ∈ annulus 0 a b := by
  simp [annulus, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm]

lemma measurableSet_annulus_centre (z : ℂ) (a b : ℝ) : MeasurableSet (annulus z a b) :=
  measurableSet_ball.diff measurableSet_closedBall

/-- The integrand of the annulus Green potential, after the translation `y ↦ y + z` of the reference measure. -/
lemma lintegral_annulus_map_add_right (ν : Measure ℂ) (z x : ℂ) (a b : ℝ) :
    ∫⁻ y in annulus z a b, (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball z b) x y))
        ∂(ν.map (fun w => w + z)) =
      ∫⁻ y in annulus 0 a b, (if y = x - z then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) (x - z) y)) ∂ν := by
  rw [← lintegral_indicator (measurableSet_annulus_centre z a b),
    ← lintegral_indicator (measurableSet_annulus_centre 0 a b)]
  have hT : ν.map (fun w => w + z) = ν.map (MeasurableEquiv.addRight z) := rfl
  rw [hT, lintegral_map_equiv]
  refine lintegral_congr fun w => ?_
  change (annulus z a b).indicator (fun y => if y = x then ∞ else ENNReal.ofReal (greenFunction (ball z b) x y))
      (w + z) = (annulus 0 a b).indicator
        (fun y => if y = x - z then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) (x - z) y)) w
  classical
  simp only [Set.indicator_apply]
  by_cases hw : w ∈ annulus 0 a b
  · have hw' : w + z ∈ annulus z a b := (mem_annulus_add_right_iff z a b w).mpr hw
    by_cases hx : w = x - z
    · have hx' : w + z = x := by rw [hx, sub_add_cancel]
      simp only [eq_true hw, eq_true hw', eq_true hx, eq_true hx', ↓reduceIte]
    · have hx' : ¬ (w + z = x) := fun h => hx (by rw [← h, add_sub_cancel_right])
      simp only [eq_true hw, eq_true hw', eq_false hx, eq_false hx', ↓reduceIte]
      rw [greenFunction_ball_add z b (x - z) w, sub_add_cancel]
  · have hw' : ¬ (w + z ∈ annulus z a b) := fun h => hw ((mem_annulus_add_right_iff z a b w).mp h)
    simp only [eq_false hw, eq_false hw', ↓reduceIte]

/-- **Translation covariance of the annulus Green potential.** Translating the reference measure by `z` and the
annulus centre from `0` to `z` leaves `annulusGreenPotentialSup` unchanged (Defs/Annuli.lean:65). -/
theorem annulusGreenPotentialSup_map_add_right (ν : Measure ℂ) (z : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (ν.map (fun w => w + z)) z a b = annulusGreenPotentialSup ν 0 a b := by
  unfold annulusGreenPotentialSup
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    rw [lintegral_annulus_map_add_right ν z x a b]
    exact le_iSup₂_of_le (x - z) ((mem_annulus_add_right_iff z a b (x - z)).mp (by rwa [sub_add_cancel])) le_rfl
  · refine iSup₂_le fun x' hx' => ?_
    have hx : x' + z ∈ annulus z a b := (mem_annulus_add_right_iff z a b x').mpr hx'
    refine le_trans (le_of_eq ?_) (le_iSup₂_of_le (x' + z) hx le_rfl)
    rw [lintegral_annulus_map_add_right ν z (x' + z) a b, add_sub_cancel_right]

end HarmonicBalls.S11c
