import Mathlib

/-!
# Lemma 11.7: local-to-global step

Step S5c of the transfer: the frozen local Campbell statement
(`LocalCampbellMarkedRestrictionFrozen`, Frozen/S11c.lean) is applied to rational discs `U = B(c, s)` with
`closedBall c s ⊆ B(c, t)` and `0 ∉ closedBall c t`. These discs cover `ℂ ∖ {0}`; the point `0` is `μ`-null by
non-atomicity (`LQGMeasureNonatomic`, Proposed/LQG.lean:75). This file proves the countable cover and the passage from
disc-local almost-sure statements to `μ`-almost-every statements.
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- Index of the rational discs: rationals `a, b` (centre `⟨a, b⟩`), `s` (radius of `U`) and `t` (radius of `D`) with
`0 < s < t < ‖⟨a, b⟩‖`, so that `closedBall c s ⊆ ball c t` and `0 ∉ closedBall c t`. -/
abbrev RatDiscIdx : Type :=
  {q : ℚ × ℚ × ℚ × ℚ // 0 < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
    (q.2.2.2 : ℝ) < ‖(⟨(q.1 : ℝ), (q.2.1 : ℝ)⟩ : ℂ)‖}

/-- The centre of the rational disc `k`. -/
def ratDiscCentre (k : RatDiscIdx) : ℂ := ⟨(k.1.1 : ℝ), (k.1.2.1 : ℝ)⟩

/-- The disc `U_k = B(c_k, s_k)` of the index `k`. -/
def ratDiscBall (k : RatDiscIdx) : Set ℂ := ball (ratDiscCentre k) (k.1.2.2.1 : ℝ)

/-- The rational discs cover `ℂ ∖ {0}`: every nonzero `z` lies in some `U_k`, with `s_k < ‖c_k‖`. -/
theorem exists_ratDisc_cover (z : ℂ) (hz : z ≠ 0) : ∃ k : RatDiscIdx, z ∈ ratDiscBall k := by
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ‖z‖ / 16 < z.re + ‖z‖ / 16 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ‖z‖ / 16 < z.im + ‖z‖ / 16 by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show ‖z‖ / 8 < ‖z‖ / 4 by linarith)
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show ‖z‖ / 4 < ‖z‖ / 2 by linarith)
  set c : ℂ := ⟨(a : ℝ), (b : ℝ)⟩ with hc
  have hre : |z.re - (a : ℝ)| < ‖z‖ / 16 := by
    rw [abs_lt]
    constructor <;> linarith
  have him : |z.im - (b : ℝ)| < ‖z‖ / 16 := by
    rw [abs_lt]
    constructor <;> linarith
  have hd : ‖z - c‖ < ‖z‖ / 8 := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - c)
    have hre' : (z - c).re = z.re - (a : ℝ) := rfl
    have him' : (z - c).im = z.im - (b : ℝ) := rfl
    rw [hre', him'] at h
    linarith
  have hnc : ‖z‖ - ‖c‖ ≤ ‖z - c‖ := norm_sub_norm_le z c
  have hct : (t : ℝ) < ‖c‖ := by linarith
  have hk : (0 < (s : ℝ) ∧ (s : ℝ) < (t : ℝ) ∧ (t : ℝ) < ‖(⟨(a : ℝ), (b : ℝ)⟩ : ℂ)‖) :=
    ⟨by linarith, by linarith, hct⟩
  refine ⟨⟨(a, b, s, t), hk⟩, ?_⟩
  show z ∈ ball (ratDiscCentre ⟨(a, b, s, t), hk⟩) (s : ℝ)
  rw [mem_ball, dist_eq_norm]
  have hcentre : ratDiscCentre ⟨(a, b, s, t), hk⟩ = c := rfl
  rw [hcentre]
  linarith

/-- Local-to-global step: if for each rational disc `U_k` the local statement holds almost surely and `μ` has no atom at `0`
almost surely, then almost surely `Good ω z` holds for `μ ω`-almost every `z`. -/
theorem ae_forall_of_ratDiscs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (μ : Ω → Measure ℂ) (Good : Ω → ℂ → Prop)
    (h0 : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (hloc : ∀ k : RatDiscIdx, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ratDiscBall k → Good ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), Good ω z := by
  have h1 : ∀ᵐ ω ∂P, ∀ k : RatDiscIdx, ∀ᵐ z ∂(μ ω), z ∈ ratDiscBall k → Good ω z :=
    ae_all_iff.mpr hloc
  filter_upwards [h1, h0] with ω hω h0ω
  have h2 : ∀ᵐ z ∂(μ ω), ∀ k : RatDiscIdx, z ∈ ratDiscBall k → Good ω z := ae_all_iff.mpr hω
  have h3 : ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    rw [ae_iff]
    simpa using h0ω
  filter_upwards [h2, h3] with z hz hz0
  obtain ⟨k, hk⟩ := exists_ratDisc_cover z hz0
  exact hz k hk

end HarmonicBalls.S11c
