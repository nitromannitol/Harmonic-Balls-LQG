import HarmonicBalls.Proofs.Sec5.PuncturedDiscBoundary

/-! # Harmonic minorants near a removed point

Away from the pole, the Newtonian obstacle gives a locally uniform upper bound
for all harmonic minorants. A logarithmic barrier then forces each perturbed
minorant to tend to negative infinity at the removed point. These estimates do
not by themselves prove polar removal or equality of Green functions.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace

/-- The Newtonian obstacle bounds all its harmonic minorants uniformly on a
neighbourhood of any point distinct from the pole. -/
theorem exists_uniform_harmonicMinorant_upper_bound_ne_pole
    {O : Set ℂ} {z a : ℂ} (ha : a ≠ z) :
    ∃ δ C : ℝ, 0 < δ ∧ ∀ h : ℂ → ℝ,
      IsHarmonicMinorant O (newtonKernelEReal z) h →
      ∀ x ∈ O ∩ ball a δ, h x ≤ C := by
  have hc : ContinuousAt (newtonKernel z) a := (harmonicAt_newtonKernel ha).1.continuousAt
  have hnear : ∀ᶠ x in 𝓝 a, newtonKernel z x < newtonKernel z a + 1 :=
    hc.eventually (Iio_mem_nhds (by linarith))
  have hne : ∀ᶠ x in 𝓝 a, x ≠ z :=
    isOpen_compl_singleton.mem_nhds ha
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp (hnear.and hne)
  refine ⟨δ, newtonKernel z a + 1, hδ, ?_⟩
  intro h hh x ⟨hxO, hxδ⟩
  have ⟨hxN, hxz⟩ := hδbound hxδ
  have hle := hh.2 x hxO
  have hle' : h x ≤ newtonKernel z x := by
    simpa [newtonKernelEReal, hxz] using hle
  exact le_of_lt (hle'.trans_lt hxN)

/-- A positive logarithmic barrier dominates a harmonic minorant near a
removed point distinct from the pole. -/
theorem IsHarmonicMinorant.tendsto_add_log_atBot_at_puncture
    {O : Set ℂ} {z a : ℂ} {h : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (ha : a ≠ z) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x => h x + ε * Real.log ‖x - a‖) (𝓝[O \ {a}] a) atBot := by
  obtain ⟨δ, C, hδ, hbound⟩ :=
    exists_uniform_harmonicMinorant_upper_bound_ne_pole (O := O) ha
  have hf : 𝓝[O \ {a}] a ≤ 𝓝[≠] a := nhdsWithin_mono a (fun _ hx => hx.2)
  have hlog : Tendsto (fun x : ℂ => Real.log ‖x - a‖) (𝓝[O \ {a}] a) atBot :=
    (Real.tendsto_log_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE a)).mono_left hf
  have hmajor : Tendsto (fun x : ℂ => C + ε * Real.log ‖x - a‖) (𝓝[O \ {a}] a) atBot := by
    simpa [add_comm] using (hlog.const_mul_atBot hε).atBot_add tendsto_const_nhds
  apply tendsto_atBot_mono' _ _ hmajor
  have hball : ∀ᶠ x in 𝓝[O \ {a}] a, x ∈ ball a δ :=
    (show ∀ᶠ x in 𝓝 a, x ∈ ball a δ from
      isOpen_ball.mem_nhds (mem_ball_self hδ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hball, self_mem_nhdsWithin] with x hx hxO
  linarith [hbound h hh x ⟨hxO.1, hx⟩]

/-- Adding the logarithmic barrier preserves harmonicity away from the
removed point. -/
theorem IsHarmonicMinorant.harmonicOnNhd_add_log_punctured
    {O : Set ℂ} {z a : ℂ} {h : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h) (ε : ℝ) :
    HarmonicOnNhd (fun x => h x + ε * Real.log ‖x - a‖) (O \ {a}) := by
  intro x hx
  have han : AnalyticAt ℂ (fun w : ℂ => w - a) x := by fun_prop
  have hxa : x ≠ a := by simpa using hx.2
  have hlog := (han.harmonicAt_log_norm (sub_ne_zero.mpr hxa)).const_smul (c := ε)
  convert (hh.1 x hx.1).add hlog using 1

#print axioms IsHarmonicMinorant.harmonicOnNhd_add_log_punctured
#print axioms exists_uniform_harmonicMinorant_upper_bound_ne_pole
#print axioms IsHarmonicMinorant.tendsto_add_log_atBot_at_puncture

end HarmonicBalls
