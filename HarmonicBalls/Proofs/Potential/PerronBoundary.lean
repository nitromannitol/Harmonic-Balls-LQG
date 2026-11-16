import Mathlib
import HarmonicBalls.Proofs.Potential.PerronHarmonic

/-!
# Boundary behaviour of the Perron function at exterior-sphere points

Let `Ω ⊆ ℂ` be a bounded open set and `φ` bounded on the frontier of `Ω`.  At a frontier point `ξ`
with an exterior disc touching `closure Ω` only at `ξ`, the logarithmic barrier
`x ↦ log ‖x - a‖ - log s` is harmonic in `Ω`, nonnegative on `closure Ω`, vanishes at `ξ` and is
bounded below away from `ξ`.  With such a barrier the Perron function of a datum `φ` that is
continuous at `ξ` tends to `φ ξ` at `ξ` (Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Theorem 2.14, p. 26, with the barrier of (2.34), p. 27).

* `HarmonicBalls.exists_barrier`: the barrier from an exterior disc;
* `HarmonicBalls.perronFun_close`: the Perron function is close to `φ ξ` near `ξ`.
-/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- The logarithmic barrier at `ξ` of an exterior disc `ball w r` of `closure Ω` with `ξ` on its
boundary circle: a function continuous on `closure Ω`, harmonic in `Ω`, nonnegative on
`closure Ω`, zero at `ξ`, and bounded below by a positive constant away from `ξ`. -/
theorem exists_barrier {Ω : Set ℂ} {ξ w : ℂ} {r : ℝ} (hr : 0 < r) (hξ : dist ξ w = r)
    (hext : ball w r ⊆ (closure Ω)ᶜ) :
    ∃ β : ℂ → ℝ, ContinuousOn β (closure Ω) ∧ HarmonicOnNhd β Ω ∧
      (∀ x ∈ closure Ω, 0 ≤ β x) ∧ β ξ = 0 ∧
      ∀ δ : ℝ, 0 < δ → ∃ b : ℝ, 0 < b ∧ ∀ x ∈ closure Ω, δ ≤ dist x ξ → b ≤ β x := by
  set a : ℂ := (ξ + w) / 2 with ha
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by positivity
  have hd : ξ - a = a - w := by rw [ha]; ring
  have hξa : ‖ξ - a‖ = s := by
    have h2 : ξ - a = (ξ - w) / 2 := by rw [ha]; ring
    rw [h2, norm_div, ← dist_eq_norm, hξ]
    simp [hs]
  -- distance estimate on `closure Ω`
  have hkey : ∀ x ∈ closure Ω, s ^ 2 + ‖x - ξ‖ ^ 2 / 2 ≤ ‖x - a‖ ^ 2 := by
    intro x hx
    have hxw : r ≤ ‖x - w‖ := by
      by_contra h
      push Not at h
      exact hext (mem_ball.mpr (by rw [dist_eq_norm]; exact h)) hx
    have hpar := parallelogram_law_with_norm ℝ (x - a) (ξ - a)
    have e1 : x - a + (ξ - a) = x - w := by rw [hd]; ring
    have e2 : x - a - (ξ - a) = x - ξ := by ring
    rw [e1, e2, hξa] at hpar
    have hr2 : r = 2 * s := by rw [hs]; ring
    nlinarith [mul_self_le_mul_self hr.le hxw]
  have hge : ∀ x ∈ closure Ω, s ≤ ‖x - a‖ := by
    intro x hx
    have := hkey x hx
    by_contra h
    push Not at h
    nlinarith [mul_self_lt_mul_self (norm_nonneg _) h, sq_nonneg ‖x - ξ‖]
  refine ⟨fun x => Real.log ‖x - a‖ - Real.log s, ?_, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.sub (ContinuousOn.log (by fun_prop) fun x hx => ?_) continuousOn_const
    exact (hs0.trans_le (hge x hx)).ne'
  · intro x hx
    have hxa : ‖x - a‖ ≠ 0 := (hs0.trans_le (hge x (subset_closure hx))).ne'
    have hne : x - a ≠ 0 := fun h => hxa (by rw [h, norm_zero])
    have h1 : HarmonicAt (fun y : ℂ => Real.log ‖y - a‖) x :=
      AnalyticAt.harmonicAt_log_norm (f := fun y => y - a) (by fun_prop) hne
    exact h1.sub (harmonicAt_const _)
  · intro x hx
    have := Real.log_le_log hs0 (hge x hx)
    simp only
    linarith
  · simp only
    rw [hξa]
    ring
  · intro δ hδ
    set q : ℝ := Real.sqrt (1 + δ ^ 2 / (2 * s ^ 2)) with hq
    have hq1 : 1 < q := by
      rw [hq, Real.lt_sqrt zero_le_one]
      have : 0 < δ ^ 2 / (2 * s ^ 2) := by positivity
      linarith
    have hqq : q ^ 2 = 1 + δ ^ 2 / (2 * s ^ 2) := Real.sq_sqrt (by positivity)
    refine ⟨Real.log q, Real.log_pos hq1, fun x hx hδx => ?_⟩
    have hsq : s * q ≤ ‖x - a‖ := by
      by_contra h
      push Not at h
      have h1 := mul_self_lt_mul_self (by positivity) h
      have h2 := hkey x hx
      have h3 : δ ^ 2 ≤ ‖x - ξ‖ ^ 2 := by
        rw [← dist_eq_norm]
        exact pow_le_pow_left₀ hδ.le hδx 2
      have h4 : (s * q) * (s * q) = s ^ 2 + δ ^ 2 / 2 := by
        have : (s * q) * (s * q) = s ^ 2 * q ^ 2 := by ring
        rw [this, hqq]
        field_simp
      nlinarith
    have hlog := Real.log_le_log (by positivity) hsq
    rw [Real.log_mul hs0.ne' (by positivity)] at hlog
    simp only
    linarith

/-- Near a frontier point `ξ` with a barrier, at which the bounded datum `φ` is continuous
within the frontier, the Perron function is within `ε` of `φ ξ`. -/
theorem perronFun_close {Ω : Set ℂ} {φ : ℂ → ℝ} {B : ℝ} (hΩ : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hB : ∀ z ∈ frontier Ω, |φ z| ≤ B) {ξ : ℂ}
    (hξ : ξ ∈ frontier Ω) (hφξ : ContinuousWithinAt φ (frontier Ω) ξ) {β : ℂ → ℝ}
    (hβc : ContinuousOn β (closure Ω)) (hβh : HarmonicOnNhd β Ω)
    (hβ0 : ∀ x ∈ closure Ω, 0 ≤ β x) (hβξ : β ξ = 0)
    (hβlow : ∀ δ : ℝ, 0 < δ → ∃ b : ℝ, 0 < b ∧ ∀ x ∈ closure Ω, δ ≤ dist x ξ → b ≤ β x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ω, dist x ξ < δ → |perronFun Ω φ x - φ ξ| < ε := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ξ hξ)
  have hfrcl : frontier Ω ⊆ closure Ω := frontier_subset_closure
  obtain ⟨δ₁, hδ₁, hφδ⟩ := Metric.continuousWithinAt_iff.mp hφξ (ε / 2) (by positivity)
  obtain ⟨b, hb, hblow⟩ := hβlow δ₁ hδ₁
  set k : ℝ := 2 * B / b with hk
  have hk0 : 0 ≤ k := by positivity
  have hkb : k * b = 2 * B := by rw [hk]; field_simp
  have hkβ : ∀ x ∈ closure Ω, δ₁ ≤ dist x ξ → 2 * B ≤ k * β x := fun x hx hδx =>
    hkb ▸ mul_le_mul_of_nonneg_left (hblow x hx hδx) hk0
  have hkβ0 : ∀ x ∈ closure Ω, 0 ≤ k * β x := fun x hx => mul_nonneg hk0 (hβ0 x hx)
  -- the frontier comparison for both the lower and the upper function
  have hfr_lo : ∀ x ∈ frontier Ω, φ ξ - ε / 2 - k * β x ≤ φ x := by
    intro x hx
    by_cases hxξ : dist x ξ < δ₁
    · have h1 := hφδ hx hxξ
      rw [Real.dist_eq, abs_lt] at h1
      linarith [hkβ0 x (hfrcl hx)]
    · have h1 := hkβ x (hfrcl hx) (not_lt.mp hxξ)
      linarith [abs_le.mp (hB x hx), abs_le.mp (hB ξ hξ)]
  have hfr_up : ∀ x ∈ frontier Ω, φ x ≤ φ ξ + ε / 2 + k * β x := by
    intro x hx
    by_cases hxξ : dist x ξ < δ₁
    · have h1 := hφδ hx hxξ
      rw [Real.dist_eq, abs_lt] at h1
      linarith [hkβ0 x (hfrcl hx)]
    · have h1 := hkβ x (hfrcl hx) (not_lt.mp hxξ)
      linarith [abs_le.mp (hB x hx), abs_le.mp (hB ξ hξ)]
  have hM : ∀ z ∈ frontier Ω, φ z ≤ B := fun z hz => (abs_le.mp (hB z hz)).2
  have hm : ∀ z ∈ frontier Ω, -B ≤ φ z := fun z hz => (abs_le.mp (hB z hz)).1
  have hbd : ∀ z ∈ Ω, BddAbove {t | ∃ v, IsPerronSub Ω φ v ∧ v z = t} := fun z hz =>
    ⟨B, by rintro t ⟨v, hv, rfl⟩; exact hv.le_bound hΩ hbdd hM z hz⟩
  have hne : ∀ z, {t | ∃ v, IsPerronSub Ω φ v ∧ v z = t}.Nonempty := fun z =>
    ⟨-B, fun _ => -B, IsPerronSub.const hΩ hm, rfl⟩
  have hscale : ∀ k' : ℝ, HarmonicOnNhd (fun x => k' * β x) Ω := fun k' x hx => by
    have h2 : HarmonicAt (k' • β) x := (hβh x hx).const_smul
    exact h2
  have hHh : ∀ c₀ : ℝ, HarmonicOnNhd (fun x => c₀ + k * β x) Ω := fun c₀ =>
    (harmonicOnNhd_const c₀).add (hscale k)
  have hHc : ∀ c₀ : ℝ, ContinuousOn (fun x => c₀ + k * β x) (closure Ω) := fun c₀ =>
    continuousOn_const.add (continuousOn_const.mul hβc)
  have hlow : ∀ x ∈ Ω, φ ξ - ε / 2 - k * β x ≤ perronFun Ω φ x := by
    intro x hx
    have hv : IsPerronSub Ω φ (fun x => (φ ξ - ε / 2) + (-k) * β x) := by
      refine ⟨?_, ?_, fun z hz => ?_⟩
      · exact continuousOn_const.add (continuousOn_const.mul hβc)
      · exact IsLocalSubMean.of_harmonicOnNhd hΩ
          ((harmonicOnNhd_const _).add (hscale (-k)))
      · have := hfr_lo z hz
        linarith
    have h : (φ ξ - ε / 2) + (-k) * β x ≤ perronFun Ω φ x :=
      le_csSup (hbd x hx) ⟨_, hv, rfl⟩
    linarith
  have hup : ∀ x ∈ Ω, perronFun Ω φ x ≤ φ ξ + ε / 2 + k * β x := by
    intro x hx
    refine csSup_le (hne x) ?_
    rintro t ⟨v, hv, rfl⟩
    have := IsLocalSubMean.le_harmonic_of_le_frontier hΩ hbdd hv.1
      (hHc (φ ξ + ε / 2)) (hHh (φ ξ + ε / 2)) hv.2.1
      (fun z hz => (hv.2.2 z hz).trans (by have := hfr_up z hz; linarith)) x hx
    linarith
  obtain ⟨δ₂, hδ₂, hβδ⟩ := Metric.continuousOn_iff.mp hβc ξ (hfrcl hξ)
    (ε / (2 * (k + 1))) (by positivity)
  refine ⟨δ₂, hδ₂, fun x hx hxδ => ?_⟩
  have h1 := hβδ x (subset_closure hx) hxδ
  rw [Real.dist_eq, hβξ, sub_zero, abs_lt] at h1
  have h2 : k * β x < ε / 2 := by
    have hβx := hβ0 x (subset_closure hx)
    have : (k + 1) * β x < ε / 2 := by
      have := mul_lt_mul_of_pos_left h1.2 (by positivity : 0 < k + 1)
      calc (k + 1) * β x < (k + 1) * (ε / (2 * (k + 1))) := this
        _ = ε / 2 := by field_simp
    nlinarith
  rw [abs_sub_lt_iff]
  have := hlow x hx
  have := hup x hx
  constructor <;> linarith

end HarmonicBalls
