import HarmonicBalls.Proofs.Sec6.InstantHitGerm

/-! # Exit times under spatial maps

Injective continuous spatial transformations preserve exit times and the
corresponding pathwise exit-order events. This is used in affine transfer of
good-annulus estimates.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal Topology

/-- Two paths with identical membership at each time have equal exit times. -/
theorem exitTime_eq_of_membership_iff {U V : Set ℂ}
    (ω η : ContinuousPath ℂ) (h : ∀ t, η t ∈ V ↔ ω t ∈ U) :
    ContinuousPath.exitTime V η = ContinuousPath.exitTime U ω := by
  apply le_antisymm
  · rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    apply ContinuousPath.exitTime_le_of_notMem V η t
    exact fun hV => ht ((h t).mp hV)
  · rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    apply ContinuousPath.exitTime_le_of_notMem U ω t
    exact fun hU => ht ((h t).mpr hU)

/-- Injective continuous spatial maps preserve exit times when the domain is
replaced by its image. -/
theorem exitTime_comp_injective (f : C(ℂ, ℂ)) (hf : Function.Injective f)
    (U : Set ℂ) (ω : ContinuousPath ℂ) :
    ContinuousPath.exitTime (f '' U) (f.comp ω) = ContinuousPath.exitTime U ω := by
  apply exitTime_eq_of_membership_iff
  intro t
  change f (ω t) ∈ f '' U ↔ ω t ∈ U
  exact ⟨fun h => by obtain ⟨x, hx, heq⟩ := h; exact hf heq ▸ hx,
    fun h => ⟨ω t, h, rfl⟩⟩

/-- Exit-order events are preserved pathwise by an injective continuous
spatial transformation. -/
theorem exitTime_le_exitTime_comp_injective_iff (f : C(ℂ, ℂ))
    (hf : Function.Injective f) (U V : Set ℂ) (ω : ContinuousPath ℂ) :
    ContinuousPath.exitTime (f '' U) (f.comp ω) ≤
        ContinuousPath.exitTime (f '' V) (f.comp ω) ↔
      ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω := by
  rw [exitTime_comp_injective f hf U, exitTime_comp_injective f hf V]

/-- Exit times commute with an increasing time reparametrization and its
extension to the extended nonnegative half-line. -/
theorem exitTime_time_orderIso (U : Set ℂ) (ω η : ContinuousPath ℂ)
    (q : NNReal ≃o NNReal) (e : ℝ≥0∞ ≃o ℝ≥0∞)
    (he : ∀ t : NNReal, e (t : ℝ≥0∞) = (q t : ℝ≥0∞))
    (hpath : ∀ t, η t = ω (q t)) :
    e (ContinuousPath.exitTime U η) = ContinuousPath.exitTime U ω := by
  apply le_antisymm
  · rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    have hout : η (q.symm t) ∉ U := by simpa only [hpath, q.apply_symm_apply] using ht
    have hle := e.monotone (ContinuousPath.exitTime_le_of_notMem U η (q.symm t) hout)
    simpa only [he, q.apply_symm_apply] using hle
  · have hle : e.symm (ContinuousPath.exitTime U ω) ≤ ContinuousPath.exitTime U η := by
      rw [ContinuousPath.le_exitTime_iff]
      intro t ht
      have hout : ω (q t) ∉ U := by simpa only [hpath] using ht
      have h := e.symm.monotone (ContinuousPath.exitTime_le_of_notMem U ω (q t) hout)
      rw [← he t, e.symm_apply_apply] at h
      exact h
    have h := e.monotone hle
    simpa only [e.apply_symm_apply] using h

/-- Increasing time reparametrizations preserve the order of exit times. -/
theorem exitTime_le_exitTime_time_orderIso_iff (U V : Set ℂ)
    (ω η : ContinuousPath ℂ) (q : NNReal ≃o NNReal) (e : ℝ≥0∞ ≃o ℝ≥0∞)
    (he : ∀ t : NNReal, e (t : ℝ≥0∞) = (q t : ℝ≥0∞))
    (hpath : ∀ t, η t = ω (q t)) :
    ContinuousPath.exitTime U η ≤ ContinuousPath.exitTime V η ↔
      ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω := by
  rw [← exitTime_time_orderIso U ω η q e he hpath,
    ← exitTime_time_orderIso V ω η q e he hpath]
  exact e.le_iff_le.symm

/-- A positive linear change of time preserves exit-time order. -/
theorem exitTime_le_exitTime_time_scale_iff (U V : Set ℂ)
    (ω η : ContinuousPath ℂ) (c : NNReal) (hc : 0 < c)
    (hpath : ∀ t, η t = ω (c * t)) :
    ContinuousPath.exitTime U η ≤ ContinuousPath.exitTime V η ↔
      ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω := by
  let q : NNReal ≃o NNReal := OrderIso.mulLeft₀ c hc
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hc)
  have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  let e : ℝ≥0∞ ≃o ℝ≥0∞ :=
    (ENNReal.mul_right_strictMono hc0 hct).orderIsoOfSurjective _ fun x =>
      ⟨(c : ℝ≥0∞)⁻¹ * x, ENNReal.mul_inv_cancel_left hc0 hct⟩
  apply exitTime_le_exitTime_time_orderIso_iff U V ω η q e
  · intro t
    change (c : ℝ≥0∞) * (t : ℝ≥0∞) = ((c * t : NNReal) : ℝ≥0∞)
    exact (ENNReal.coe_mul c t).symm
  · exact hpath

/-- Spatial injection and positive linear time change together preserve
exit-order events. -/
theorem exitTime_le_exitTime_spacetime_iff (f : C(ℂ, ℂ))
    (hf : Function.Injective f) (U V : Set ℂ) (ω η : ContinuousPath ℂ)
    (c : NNReal) (hc : 0 < c) (hpath : ∀ t, η t = f (ω (c * t))) :
    ContinuousPath.exitTime (f '' U) η ≤ ContinuousPath.exitTime (f '' V) η ↔
      ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω := by
  calc
    _ ↔ ContinuousPath.exitTime (f '' U) (f.comp ω) ≤
        ContinuousPath.exitTime (f '' V) (f.comp ω) :=
      exitTime_le_exitTime_time_scale_iff (f '' U) (f '' V) (f.comp ω) η c hc hpath
    _ ↔ _ := exitTime_le_exitTime_comp_injective_iff f hf U V ω

/-- A measurable embedding transporting path measures transfers exit-order
probabilities, including when the exit-order event is not measurable. -/
theorem measure_exitTime_order_eq_of_spacetime_map
    (f : C(ℂ, ℂ)) (hf : Function.Injective f) (U V : Set ℂ)
    (c : NNReal) (hc : 0 < c) (T : ContinuousPath ℂ → ContinuousPath ℂ)
    (hT : MeasurableEmbedding T) (hpath : ∀ ω t, T ω t = f (ω (c * t)))
    (μ ν : Measure (ContinuousPath ℂ)) (hmap : μ.map T = ν) :
    ν {ω | ContinuousPath.exitTime (f '' U) ω ≤ ContinuousPath.exitTime (f '' V) ω} =
      μ {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω} := by
  rw [← hmap, hT.map_apply]
  congr 1
  ext ω
  exact exitTime_le_exitTime_spacetime_iff f hf U V ω (T ω) c hc (hpath ω)

end HarmonicBalls.Section6
