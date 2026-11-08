import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity

/-!
# L¹ realization of the moving-pole Green row

For a bounded open planar set `U` and a pole `x ∈ ℂ`, the zero-extended Green row
`y ↦ G_U(x, y)` (value `0` off `U`, as in `greenFunction`) is integrable on `ℂ`
(`integrable_greenFunction_pole`). This file gives its class in the Mathlib carrier
`L¹(ℂ, volume; ℝ)` and transfers the scalar continuity theorem of `GreenPoleL1Continuity`
to the moving pole:

* `greenRowL1 hU hUb x` is the class `(integrable_greenFunction_pole hU hUb x).toL1 (greenFunction U x)`;
* `coeFn_greenRowL1`: its coercion agrees almost everywhere with the literal row;
* `eq_greenRowL1_iff`: an element of `L¹` equals `greenRowL1 hU hUb x` exactly when it agrees a.e.
  with the literal row (uniqueness of the representative);
* `norm_greenRowL1_sub` and `dist_greenRowL1`: `‖greenRowL1 x - greenRowL1 z‖` is the integral of
  `|G_U(x, y) - G_U(z, y)|` over `y ∈ ℂ`;
* `continuousOn_greenRowL1`: the pole map is continuous on `U` for the `L¹` norm;
* `uniformContinuousOn_greenRowL1`: it is uniformly continuous on every compact `K ⊆ U`.

Only `IsOpen U`, `Bornology.IsBounded U` and the scalar theorem
`tendsto_integral_abs_greenFunction_sub_nhdsWithin` are used. No kernel-continuity premise, no
representative chosen by choice, and no statement about poles on the boundary of `U`. The junk value
`0` of `greenFunction` on the diagonal `y = x` is a null set and enters no integral.

The local volume estimate and the potential-theoretic infrastructure behind the scalar theorem use
work of Leonardo Bonanno, reached through the pinned Lattice-Probability lean-v4.35 port (module
`LatticeProb.Prob.Birkhoff` in the import closure of `GreenPoleL1Continuity`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric

/-- The zero-extended Green row of the pole `x` as an element of the Lebesgue carrier
`L¹(ℂ, volume; ℝ)`: the class of `y ↦ G_U(x, y)`, integrable by `integrable_greenFunction_pole`. -/
noncomputable def greenRowL1 {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (x : ℂ) :
    Lp ℝ 1 (volume : Measure ℂ) :=
  (integrable_greenFunction_pole hU hUb x).toL1 (greenFunction U x)

/-- The coercion of `greenRowL1 hU hUb x` agrees almost everywhere with the literal Green row. -/
theorem coeFn_greenRowL1 {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (x : ℂ) :
    ⇑(greenRowL1 hU hUb x) =ᵐ[volume] greenFunction U x :=
  (integrable_greenFunction_pole hU hUb x).coeFn_toL1

/-- Uniqueness of the `L¹` representative: an element `φ` of `L¹(ℂ; ℝ)` equals `greenRowL1 hU hUb x`
exactly when `φ` agrees almost everywhere with the literal Green row `y ↦ G_U(x, y)`. -/
theorem eq_greenRowL1_iff {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (x : ℂ)
    (φ : Lp ℝ 1 (volume : Measure ℂ)) :
    φ = greenRowL1 hU hUb x ↔ ⇑φ =ᵐ[volume] greenFunction U x := by
  constructor
  · rintro rfl
    exact coeFn_greenRowL1 hU hUb x
  · intro h
    exact Lp.ext (h.trans (coeFn_greenRowL1 hU hUb x).symm)

/-- The `L¹` norm of a difference of two Green rows is the integral of the absolute difference of the
literal rows: `‖greenRowL1 x - greenRowL1 z‖ = ∫ y, |G_U(x, y) - G_U(z, y)|`. -/
theorem norm_greenRowL1_sub {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (x z : ℂ) :
    ‖greenRowL1 hU hUb x - greenRowL1 hU hUb z‖ =
      ∫ y, |greenFunction U x y - greenFunction U z y| := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (greenRowL1 hU hUb x) (greenRowL1 hU hUb z),
    coeFn_greenRowL1 hU hUb x, coeFn_greenRowL1 hU hUb z] with y h₁ h₂ h₃
  simp only [h₁, Pi.sub_apply, h₂, h₃, Real.norm_eq_abs]

/-- The `L¹` distance of two Green rows is the same integral. -/
theorem dist_greenRowL1 {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (x z : ℂ) :
    dist (greenRowL1 hU hUb x) (greenRowL1 hU hUb z) =
      ∫ y, |greenFunction U x y - greenFunction U z y| := by
  rw [dist_eq_norm, norm_greenRowL1_sub]

/-- The pole map `x ↦ greenRowL1 hU hUb x` is continuous on `U` for the `L¹` norm. -/
theorem continuousOn_greenRowL1 {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ContinuousOn (greenRowL1 hU hUb) U := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  simpa only [dist_greenRowL1 hU hUb] using
    tendsto_integral_abs_greenFunction_sub_nhdsWithin hU hUb hx

/-- On every compact `K ⊆ U` the pole map is uniformly continuous for the `L¹` norm. -/
theorem uniformContinuousOn_greenRowL1 {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K) :
    UniformContinuousOn (greenRowL1 hU hUb) K :=
  hK.uniformContinuousOn_of_continuous ((continuousOn_greenRowL1 hU hUb).mono hKU)

end HarmonicBalls
