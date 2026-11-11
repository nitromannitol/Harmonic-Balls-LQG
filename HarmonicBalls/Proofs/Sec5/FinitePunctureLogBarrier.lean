import HarmonicBalls.Proofs.Sec5.FinitePunctureMaximum

/-! # Limits of finite logarithmic barriers -/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- A positive finite logarithmic barrier tends to negative infinity at each
of its poles, along the complement of the poles. -/
theorem tendsto_finset_log_barrier_atBot (K : Finset ℂ) {a : ℂ} (ha : a ∈ K)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℂ => ∑ b ∈ K, ε * Real.log ‖x - b‖)
      (𝓝[(K : Set ℂ)ᶜ] a) atBot := by
  classical
  have haK : a ∈ ((K.erase a : Finset ℂ) : Set ℂ)ᶜ := by simp
  have hrest := ((harmonicOnNhd_finset_log_barrier (K.erase a) ε a haK).1.continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds : 𝓝[(K : Set ℂ)ᶜ] a ≤ 𝓝 a)
  have hfilter : 𝓝[(K : Set ℂ)ᶜ] a ≤ 𝓝[≠] a :=
    nhdsWithin_mono a (fun x hx hxa => hx (hxa ▸ ha))
  have hlog := (Real.tendsto_log_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE a)).mono_left hfilter
  have ht := (hlog.const_mul_atBot hε).atBot_add hrest
  convert ht using 1
  funext x
  exact (Finset.add_sum_erase K (fun b => ε * Real.log ‖x - b‖) ha).symm

/-- Adding the finite logarithmic barrier forces a harmonic minorant of the
Newtonian kernel to negative infinity at each deleted point away from the pole. -/
theorem IsHarmonicMinorant.tendsto_add_finset_log_atBot
    {O : Set ℂ} {z a : ℂ} {h : ℂ → ℝ} (K : Finset ℂ) (ha : a ∈ K)
    (haz : a ≠ z) (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℂ => h x + ∑ b ∈ K, ε * Real.log ‖x - b‖)
      (𝓝[O \ (K : Set ℂ)] a) atBot := by
  classical
  have haK : a ∈ ((K.erase a : Finset ℂ) : Set ℂ)ᶜ := by simp
  have hrest := ((harmonicOnNhd_finset_log_barrier (K.erase a) ε a haK).1.continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds : 𝓝[O \ (K : Set ℂ)] a ≤ 𝓝 a)
  have hf : 𝓝[O \ (K : Set ℂ)] a ≤ 𝓝[O \ {a}] a :=
    nhdsWithin_mono a (fun x hx => ⟨hx.1, fun hxa => hx.2 (hxa ▸ ha)⟩)
  have ht := ((hh.tendsto_add_log_atBot_at_puncture haz hε).mono_left hf).atBot_add hrest
  convert ht using 1
  funext x
  rw [← Finset.add_sum_erase K (fun b => ε * Real.log ‖x - b‖) ha]
  ring

/-- A finite logarithmic perturbation of a harmonic minorant satisfies the
maximum principle against a harmonic comparison function. -/
theorem IsHarmonicMinorant.add_finset_log_sub_le_of_boundary
    {O : Set ℂ} {z c : ℂ} {r ε C : ℝ} {h q : ℂ → ℝ} (K : Finset ℂ)
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (hKz : ∀ a ∈ K, a ≠ z) (hε : 0 < ε)
    (hK : (K : Set ℂ) ⊆ closedBall c r)
    (hO : closedBall c r \ (K : Set ℂ) ⊆ O)
    (hq : HarmonicOnNhd q (closedBall c r))
    (hbd : ∀ x ∈ sphere c r, x ∉ K →
      h x + (∑ a ∈ K, ε * Real.log ‖x - a‖) - q x ≤ C) :
    ∀ x ∈ ball c r \ (K : Set ℂ),
      h x + (∑ a ∈ K, ε * Real.log ‖x - a‖) - q x ≤ C := by
  let g : ℂ → ℝ := fun x => h x + (∑ a ∈ K, ε * Real.log ‖x - a‖) - q x
  have hg : HarmonicOnNhd g (closedBall c r \ (K : Set ℂ)) := by
    have h1 := hh.1.mono hO
    have h2 := (harmonicOnNhd_finset_log_barrier K ε).mono
      (show closedBall c r \ (K : Set ℂ) ⊆ (K : Set ℂ)ᶜ from fun _ hx => hx.2)
    convert (h1.add h2).sub (hq.mono sdiff_subset) using 1
  have hlim : ∀ a ∈ K, Tendsto g (𝓝[ball c r \ (K : Set ℂ)] a) atBot := by
    intro a ha
    have hsub : ball c r \ (K : Set ℂ) ⊆ O \ (K : Set ℂ) :=
      fun _ hx => ⟨hO ⟨ball_subset_closedBall hx.1, hx.2⟩, hx.2⟩
    have ht := (hh.tendsto_add_finset_log_atBot K ha (hKz a ha) hε).mono_left
      (nhdsWithin_mono a hsub)
    have hq' : Tendsto (-q) (𝓝[ball c r \ (K : Set ℂ)] a) (𝓝 ((-q) a)) :=
      (hq a (hK ha)).1.continuousAt.neg.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [g, sub_eq_add_neg, Pi.neg_apply] using ht.atBot_add hq'
  exact harmonicOnNhd_finset_punctured_ball_le_of_tendsto_atBot K hg.continuousOn
    (hg.mono (fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩)) hlim hbd

/-- A harmonic minorant minus a harmonic comparison function is bounded by its
outer boundary values on a finitely punctured disc. -/
theorem IsHarmonicMinorant.sub_le_of_boundary_finset_punctured
    {O : Set ℂ} {z c : ℂ} {r C : ℝ} {h q : ℂ → ℝ} (K : Finset ℂ)
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (hKz : ∀ a ∈ K, a ≠ z) (hK : (K : Set ℂ) ⊆ closedBall c r)
    (hO : closedBall c r \ (K : Set ℂ) ⊆ O)
    (hq : HarmonicOnNhd q (closedBall c r))
    (hbd : ∀ x ∈ sphere c r, x ∉ K → h x - q x ≤ C) :
    ∀ x ∈ ball c r \ (K : Set ℂ), h x - q x ≤ C := by
  intro x hx
  let B : ℝ := ∑ a ∈ K, (r + ‖c - a‖)
  have hlog : ∀ y ∈ sphere c r, ∀ a ∈ K, Real.log ‖y - a‖ ≤ r + ‖c - a‖ := by
    intro y hy a ha
    have hnorm : ‖y - c‖ = r := by simpa [dist_eq_norm] using mem_sphere.mp hy
    calc
      Real.log ‖y - a‖ ≤ ‖y - a‖ := Real.log_le_self (norm_nonneg _)
      _ ≤ ‖y - c‖ + ‖c - a‖ := by simpa [dist_eq_norm] using dist_triangle y c a
      _ = r + ‖c - a‖ := by rw [hnorm]
  have hε : ∀ ε > 0, h x - q x ≤
      C + ε * (B - ∑ a ∈ K, Real.log ‖x - a‖) := by
    intro ε hεpos
    have hbound := hh.add_finset_log_sub_le_of_boundary K hKz hεpos hK hO hq
      (C := C + ε * B) (fun y hy hyK => by
        have hs : (∑ a ∈ K, ε * Real.log ‖y - a‖) ≤ ε * B := by
          dsimp [B]
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hlog y hy a ha) hεpos.le
        linarith [hbd y hy hyK]) x hx
    have hs : (∑ a ∈ K, ε * Real.log ‖x - a‖) =
        ε * ∑ a ∈ K, Real.log ‖x - a‖ := (Finset.mul_sum ..).symm
    rw [hs] at hbound
    nlinarith
  have hlim : Tendsto (fun ε : ℝ => C + ε * (B - ∑ a ∈ K, Real.log ‖x - a‖))
      (𝓝[>] 0) (𝓝 C) := by
    have hc : ContinuousAt (fun ε : ℝ => C + ε * (B - ∑ a ∈ K, Real.log ‖x - a‖)) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  exact hε ε hεpos



end HarmonicBalls
