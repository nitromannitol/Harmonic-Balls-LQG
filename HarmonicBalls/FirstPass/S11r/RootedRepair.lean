import HarmonicBalls.FirstPass.S11r.RootedGluing

/-!
# First pass, rooted gluing with the internal physical metric (fp-S11r, owner n2; R2 repair)

Repair of the rooted gluing after the answer to R2 (notes/fp-gaps/CHATGPT-n2-R2-rooted-length.md, sections 4-5; operator
note 04:29 UTC). The ambient Weyl distance `e` of the rooted field is NOT a length metric on the disk `D ∋ z` (it may
be singular at `z`, and its paths may leave `D`), so `eq_const_mul_of_local_agreement` cannot take it as `e` (its
hypothesis `he_len` is false for the ambient distance). The repair applies the same gluing to the internal metric
`internalPhysicalMetric e D x y := (internalMetric e D x y).toReal` on `D`, whose length property is the internalization
(section 4 Step H) and whose root continuity is Steps E-F. This file proves the reduction: the gluing for the internal
physical metric, with its internal-side properties as explicit hypotheses. The Weyl-side proofs of those hypotheses
(Steps A-G of section 3) are the next step; see notes/n2.md.

Conventions: `internalMetric e D x y` is the `ℝ≥0∞`-valued infimum of `pathLength e` over paths from `x` to `y` in `D`
(Defs/LQGMetric.lean:65); `internalPhysicalMetric e D` is its real part, defined on all of `ℂ × ℂ`.
-/

namespace HarmonicBalls

open Set Filter Topology Metric
open scoped ENNReal

/-- The internal physical metric on `D`: the real part of the internal metric of `e` on `D`. Its values are meaningful
(finite) on `D × D` only when `internalMetric e D` is finite there (Steps B-C of CHATGPT-n2-R2-rooted-length.md). -/
noncomputable def internalPhysicalMetric (e : ℂ → ℂ → ℝ) (D : Set ℂ) : ℂ → ℂ → ℝ :=
  fun x y => (internalMetric e D x y).toReal

/-- The symmetry of the internal physical metric follows from the symmetry of the internal metric (path reversal). -/
theorem internalPhysicalMetric_symm_of {e : ℂ → ℂ → ℝ} {D : Set ℂ}
    (hs : ∀ x y, internalMetric e D x y = internalMetric e D y x) :
    ∀ x y, internalPhysicalMetric e D x y = internalPhysicalMetric e D y x := by
  intro x y
  unfold internalPhysicalMetric
  rw [hs x y]

/-- The triangle inequality of the internal physical metric on `D`, from the `ℝ≥0∞` triangle inequality of the internal
metric on `D` and its finiteness there (`ENNReal.toReal` is monotone and additive on finite values). This is the
argument of section 3 Step C (`he_tri`) of CHATGPT-n2-R2-rooted-length.md, where finiteness is essential. -/
theorem internalPhysicalMetric_tri_of {e : ℂ → ℂ → ℝ} {D : Set ℂ}
    (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, internalMetric e D x w ≤ internalMetric e D x y + internalMetric e D y w)
    (hfin : ∀ x ∈ D, ∀ y ∈ D, internalMetric e D x y ≠ ⊤) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D,
      internalPhysicalMetric e D x w ≤ internalPhysicalMetric e D x y + internalPhysicalMetric e D y w := by
  intro x hx y hy w hw
  unfold internalPhysicalMetric
  have hf2 := hfin x hx y hy
  have hf3 := hfin y hy w hw
  rw [← ENNReal.toReal_add hf2 hf3]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf2, hf3⟩) (htri x hx y hy w hw)

/-- **Rooted gluing for the internal physical metric** (CHATGPT-n2-R2-rooted-length.md section 4, the proposed signature,
with its hypotheses proved in the file as the reduction). Let `d` be a symmetric length-type function on an open disk
`D ∋ z` (the decoder output), and `e` the ambient physical metric. If the internal physical metric `internalPhysicalMetric e D`
satisfies the four internal-side properties (symmetry, triangle inequality on `D`, its length property
`ofReal = internalMetric` on `D`, and continuity at `z` within `D`), and `d` tends to `0` at `z`, and the internal metric of
`d` on a neighbourhood of each `q ∈ D ∖ {z}` equals `c` times the internal physical metric there, then
`d = c · internalPhysicalMetric e D` on `D`. Proof: the existing gluing `eq_const_mul_of_local_agreement` with `e` replaced
by the internal physical metric. -/
theorem eq_const_mul_internal_of_local_agreement {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D)
    {d e : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hd_symm : ∀ x y, d x y = d y x)
    (hd_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    (hd_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (d x y) = internalMetric d D x y)
    (hd_cont : Tendsto (fun x => d x z) (𝓝[D] z) (𝓝 0))
    (he_symm : ∀ x y, internalPhysicalMetric e D x y = internalPhysicalMetric e D y x)
    (he_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D,
      internalPhysicalMetric e D x w ≤ internalPhysicalMetric e D x y + internalPhysicalMetric e D y w)
    (he_len : ∀ x ∈ D, ∀ y ∈ D,
      ENNReal.ofReal (internalPhysicalMetric e D x y) = internalMetric (internalPhysicalMetric e D) D x y)
    (he_cont : Tendsto (fun x => internalPhysicalMetric e D x z) (𝓝[D] z) (𝓝 0))
    (hloc : ∀ q ∈ D, q ≠ z → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ D ∧
      ∀ x ∈ V, ∀ y ∈ V,
        internalMetric d V x y = internalMetric (fun a b => c * internalPhysicalMetric e D a b) V x y) :
    ∀ x ∈ D, ∀ y ∈ D, d x y = c * internalPhysicalMetric e D x y :=
  eq_const_mul_of_local_agreement hD hz hc hd_symm he_symm hd_tri he_tri hd_len he_len hd_cont he_cont hloc

end HarmonicBalls
