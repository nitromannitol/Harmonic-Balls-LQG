import HarmonicBalls.FirstPass.S11h.GreenKernel11_17

/-!
# First pass, Lemma 11.17: the annulus Green potential as a supremum over a countable set (fp-S11h, owner n2)

Coordinate 6 of `pinchScalars` is `M * annulusGreenPotentialSup μ 0 3 6` (Defs/Annuli.lean:65). This file reduces the
supremum over `x` in the annulus to a countable dense set of `x`, by lower semicontinuity of
`x ↦ ∫_A κ(x, y) dμ(y)` (Fatou's lemma, `lintegral_liminf_le`, applied to the lower semicontinuous extended kernel
`annulusKernelExt`, GreenKernel11_17.lean). Source: CHATGPT-cm-field-certificate.md section 4 (Green-potential coordinate).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- The extended kernel on `ℂ × ℂ`: `annulusKernel x₀ b` on `B_b(x₀) × B_b(x₀)`, zero elsewhere. -/
noncomputable def annulusKernelExt (x₀ : ℂ) (b : ℝ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  (ball x₀ b ×ˢ ball x₀ b).indicator (fun q => annulusKernel x₀ b q.1 q.2) p

/-- The extended kernel is lower semicontinuous on `ℂ × ℂ` (zero outside the open ball square). -/
theorem annulusKernelExt_lowerSemicontinuous (x₀ : ℂ) {b : ℝ} :
    LowerSemicontinuous (annulusKernelExt x₀ b) := by
  intro p
  by_cases hp : p ∈ ball x₀ b ×ˢ ball x₀ b
  · have hopen : IsOpen (ball x₀ b ×ˢ ball x₀ b) := isOpen_ball.prod isOpen_ball
    have hlsc := annulusKernel_lowerSemicontinuousOn x₀ (b := b) p hp
    intro t ht
    have h1 : t < annulusKernel x₀ b p.1 p.2 := by simpa [annulusKernelExt, hp] using ht
    have h2 := hlsc t h1
    rw [hopen.nhdsWithin_eq hp] at h2
    filter_upwards [h2, hopen.mem_nhds hp] with q hq hqS
    simpa [annulusKernelExt, hqS] using hq
  · intro t ht
    simp [annulusKernelExt, hp] at ht

/-- Composition of a lower semicontinuous (at a point) function with a continuous map. -/
theorem lowerSemicontinuousAt_comp_of_continuous {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : β → ℝ≥0∞} {g : α → β} {x : α} (hf : LowerSemicontinuousAt f (g x)) (hg : Continuous g) :
    LowerSemicontinuousAt (fun a => f (g a)) x := by
  intro t ht
  exact (hg.tendsto x).eventually (hf t ht)

/-- Lower semicontinuity of the integral of a lower semicontinuous kernel in its first variable (Fatou's lemma). -/
theorem lowerSemicontinuous_lintegral_section (μ : Measure ℂ) (A : Set ℂ) (f : ℂ × ℂ → ℝ≥0∞)
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun x => ∫⁻ y in A, f (x, y) ∂μ) := by
  refine fun x0 => lowerSemicontinuousAt_iff_le_liminf.2 ?_
  have hpt : ∀ y, f (x0, y) ≤ liminf (fun x => f (x, y)) (𝓝 x0) := fun y =>
    lowerSemicontinuousAt_iff_le_liminf.1
      (lowerSemicontinuousAt_comp_of_continuous (x := x0) (g := fun x => (x, y)) (hf (x0, y))
        (continuous_id.prodMk continuous_const))
  have hmeas : ∀ x, Measurable (fun y => f (x, y)) := fun x => by
    have hl : LowerSemicontinuous (fun y => f (x, y)) := fun y =>
      lowerSemicontinuousAt_comp_of_continuous (g := fun y => (x, y)) (hf (x, y))
        (continuous_const.prodMk continuous_id)
    exact hl.measurable
  calc ∫⁻ y in A, f (x0, y) ∂μ ≤ ∫⁻ y in A, liminf (fun x => f (x, y)) (𝓝 x0) ∂μ :=
        lintegral_mono fun y => hpt y
    _ ≤ liminf (fun x => ∫⁻ y in A, f (x, y) ∂μ) (𝓝 x0) :=
        lintegral_liminf_le (f := fun x y => f (x, y)) hmeas

/-- A supremum of a lower semicontinuous function over a set is the supremum over any dense countable subset of it
(lower semicontinuity: the sets `{G > t}` are open). -/
theorem iSup_mem_eq_iSup_of_dense_of_lowerSemicontinuous {G : ℂ → ℝ≥0∞} (hG : LowerSemicontinuous G) {A S : Set ℂ}
    (hSA : S ⊆ A) (hAS : A ⊆ closure S) :
    (⨆ x ∈ A, G x) = ⨆ x ∈ S, G x := by
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    refine le_of_forall_lt fun c hc => ?_
    have hev : ∀ᶠ x' in 𝓝 x, c < G x' := hG x c hc
    obtain ⟨s, hs, hsS⟩ := mem_closure_iff_nhds.1 (hAS hx) _ hev
    exact lt_of_lt_of_le (show c < G s from hs) (le_iSup₂ (f := fun x _ => G x) s hsS)
  · exact iSup₂_mono' fun x hx => ⟨x, hSA hx, le_rfl⟩

/-- A countable dense subset of an arbitrary set `A ⊆ ℂ` (subset of `A`). -/
theorem exists_countable_subset_dense_of_set (A : Set ℂ) :
    ∃ S : Set ℂ, S ⊆ A ∧ S.Countable ∧ A ⊆ closure S := by
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense A
  refine ⟨Subtype.val '' s, ?_, hs.image _, ?_⟩
  · rintro _ ⟨p, _, rfl⟩
    exact p.2
  · intro y hy
    have hmem : (⟨y, hy⟩ : A) ∈ closure s := hdense.closure_eq ▸ mem_univ _
    exact (closure_subtype.1 hmem)

/-- The annulus Green potential as the supremum over a countable dense subset of the annulus of the integrated kernel
`x ↦ ∫_A κ(x, ·) dμ` (the open ball `B_b(x₀)` contains the annulus `A = annulus x₀ a b`). -/
theorem annulusGreenPotentialSup_eq_countable (μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ) :
    ∃ S : Set ℂ, S ⊆ annulus x₀ a b ∧ S.Countable ∧
      annulusGreenPotentialSup μ x₀ a b =
        ⨆ x ∈ S, ∫⁻ y in annulus x₀ a b, annulusKernelExt x₀ b (x, y) ∂μ := by
  obtain ⟨S, hSA, hSc, hAS⟩ := exists_countable_subset_dense_of_set (annulus x₀ a b)
  refine ⟨S, hSA, hSc, ?_⟩
  have hAball : annulus x₀ a b ⊆ ball x₀ b := fun z hz => hz.1
  have hmeasA : MeasurableSet (annulus x₀ a b) :=
    isOpen_ball.measurableSet.diff measurableSet_closedBall
  have hG := lowerSemicontinuous_lintegral_section μ (annulus x₀ a b) (annulusKernelExt x₀ b)
    (annulusKernelExt_lowerSemicontinuous x₀)
  have hcongr : ∀ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernelExt x₀ b (x, y) ∂μ =
      ∫⁻ y in annulus x₀ a b, annulusKernel x₀ b x y ∂μ := by
    intro x hx
    refine setLIntegral_congr_fun hmeasA fun y hy => ?_
    simp [annulusKernelExt, hAball hx, hAball hy]
  show ⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernel x₀ b x y ∂μ = _
  have hEq : (⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernel x₀ b x y ∂μ) =
      ⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, annulusKernelExt x₀ b (x, y) ∂μ :=
    iSup_congr fun x => iSup_congr fun hx => (hcongr x hx).symm
  rw [hEq]
  exact iSup_mem_eq_iSup_of_dense_of_lowerSemicontinuous hG hSA hAS

end HarmonicBalls
