import Mathlib
import HarmonicBalls.Defs.Notation

/-! # Planar geometry and topology of Sections 10-11

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Sections 10-11
(lines 2476-3290 of `paper/lqg_harmonic_ball-corrected.tex`). The numbered definitions and the geometric notions used in
the statements of Lemma 10.1 - Lemma 11.17.

## Numbered definitions

* Definition 10.2 (line 2550): `IsLoop`, `IsArc`, `IsSimpleLoop` (simple loop = Jordan curve), `IsSimpleArc`, with the
  parameter arcs `circleArc` of the unit circle `𝕋 = Circle`.
* Definition 10.3 (line 2560): `IsLocallyConnectedSet`; equivalent to Mathlib's `LocallyConnectedSpace` of the subtype
  (`isLocallyConnectedSet_iff_locallyConnectedSpace`).
* Definition 10.4 (line 2566): `IsCutPoint`.
* Definition 11.1 (def:lipschitz, line 2712): `IsLipschitzDomain`.
* Definition 11.3 (line 2730): `openSector`, `IsOpenCone`, `IsCone` (extremal directions `v, w`); `coneAt Q z = 𝒬(z)`
  (line 2735).
* Definition 11.4 (def:cone-condition, line 2737): `SatisfiesInteriorConeCondition`,
  `SatisfiesExteriorConeCondition`, `SatisfiesConeCondition`.

## Further notions used by the statements of Sections 10-11

* `A ⋐ B` (line 329: `closure A ⊆ B`; Lemmas 10.1, 10.5, Proposition 10.6, Section 11.3): written `closure A ⊆ B`
  inline, no definition.
* `∂B_s(z)` (Lemmas 10.1, 10.5, 11.14, eq:pinch-point-event): `Metric.sphere z s`. The annulus `𝔸_{s₁,s₂}(z)`:
  `annulus z s₁ s₂` of `Defs/Notation.lean`.
* Connected components of a set (Lemmas 10.1, 10.5, Propositions 10.6, 10.7): `connectedComponentsIn`, built on
  Mathlib's `connectedComponentIn`.
* A set crosses an annulus (line 2582): `CrossesAnnulus`. The components of a set crossing an annulus:
  `crossingComponents`; "does not cross more than `K` times" (Lemma 10.1, line 2498) is
  `(crossingComponents (Λ ∩ ball w (2ρ)) w (ρ/3) (2ρ)).encard ≤ K`.
* Simply connected set (Lemma 10.5, line 2586; Proposition 10.6, lines 2646, 2661): the Riemann-sphere sense of the
  paper, "connected with connected complement", for a connected open `U ⊆ ℂ` written `IsConnected Uᶜ` (complement in
  `ℂ`) in `Draft/Section10.lean`; not Mathlib's planar `IsSimplyConnected U`, which fails for unbounded components
  `int(U^c)` (proof of Lemma 10.5): `interior Uᶜ`.
* Rescaled sets `A_r(z) := r A + z` (line 3102, Section 11.3): `rescaledSet`.
* Closed dyadic squares (Lemma 11.10, line 2980): `closedDyadicSquare`, `IsClosedDyadicSquare`.
* The deterministic sets `U ⋐ T`, `Q' ⋐ Q` of Section 11.3 (line 3100, Figure fig:pinch-point) entering the pinch-point
  event (eq:pinch-point-event, line 3124) of Lemmas 11.12-11.14: `IsPinchPointConfiguration`.

Not here: the LQG metric `D_h`, its internal metrics and metric balls `𝓑_u(0; D_h)` (Propositions 11.9, 11.11,
Lemma 11.14; `Defs/LQGMetric.lean`), the events `G̃_r(z)`, `Ĝ_r(z)` (they involve `μ_h`, `D_h` and the quantity of
eq:alternate-size-2) and the conformal maps of the proof of Proposition 10.6 (not in any statement).

## Modelling choices

* Definition 10.2. The arc `{φ(ζ) : α ≤ ζ ≤ β}` is `φ '' circleArc α β` with `circleArc α β = {e^{iθ} : α ≤ θ ≤ β}`,
  `α ≤ β < α + 2π` (a closed proper arc of `𝕋`). "φ is also injective" is read on the parameter set: injective on `𝕋`
  for a simple loop, on the arc `circleArc α β` for a simple arc (the values of `φ` off the arc do not enter `Γ`).
  Arcs only appear in proofs (Lemma 10.5), never in a statement.
* Definition 10.4. "`A \ {a}` is no longer connected" is `¬ IsPreconnected (A \ {a})` (the empty set is connected, so
  the point of a singleton is not a cut point). The standing hypothesis "A compact, connected and locally connected"
  is not bundled; statements using cut points carry it.
* Definition 11.1. The printed `U ∩ B_r(x₀)` (line 2717) is read `A ∩ B_r(x₀)` (no `U` in the definition). "Upon
  relabeling and reorienting the coordinate axes" is a linear isometry `e : ℂ ≃ₗᵢ[ℝ] ℂ` (rotations and reflections),
  the new coordinates of `x` being `((e x).re, (e x).im)`. This contains the axis permutations and sign changes of the
  literal reading, so the class of Lipschitz domains is at least as large and "`Λ̂_t` is not a Lipschitz domain"
  (Proposition 11.2) is at least as strong as under the literal reading. Translations are absorbed by `f`.
* Definition 11.3. A cone is an open sector `{c v + d w : c, d > 0}` that is non-empty, open and proper, or the
  complement of one ("we also define complements of cones to be cones", line 2731).
* Definition 11.4. The cone conditions are defined for every `z`; the paper's restriction `z ∈ ∂A` is a hypothesis of
  the statements using them (Lemma 11.5). For an open `A` and `z ∈ ∂A` the interior condition can only hold with an
  open sector (a complement of a sector contains its vertex).
* Section 11.3. "`T` is a keyhole-shaped region, as shown in the figure" is not formalized beyond the requirements
  printed on line 3100; see `IsPinchPointConfiguration`.
-/

namespace HarmonicBalls

open Metric Set Filter Topology Complex

/-! ## Section 10: loops, local connectedness, cut points, crossings -/

/-- The closed arc `{e^{iθ} : α ≤ θ ≤ β}` of the unit circle `𝕋` (Definition 10.2, line 2551). -/
def circleArc (α β : ℝ) : Set Circle :=
  (fun θ : ℝ => Circle.exp θ) '' Icc α β

/-- Definition 10.2 (line 2551). A set `Γ ⊆ ℂ` is a *loop* if `Γ = {φ(ζ) : ζ ∈ 𝕋}` for a continuous
`φ : 𝕋 → ℂ`. -/
def IsLoop (Γ : Set ℂ) : Prop :=
  ∃ φ : Circle → ℂ, Continuous φ ∧ range φ = Γ

/-- Definition 10.2 (line 2552). A set `Γ ⊆ ℂ` is an *arc* if `Γ = {φ(ζ) : α ≤ ζ ≤ β}` for a continuous
`φ : 𝕋 → ℂ` and a closed proper arc `{e^{iθ} : α ≤ θ ≤ β}`, `α ≤ β < α + 2π`, of `𝕋`. -/
def IsArc (Γ : Set ℂ) : Prop :=
  ∃ φ : Circle → ℂ, Continuous φ ∧ ∃ α β : ℝ, α ≤ β ∧ β < α + 2 * Real.pi ∧ φ '' circleArc α β = Γ

/-- Definition 10.2 (line 2553). A *simple loop* (Jordan curve, Jordan loop: line 2632) is the image of a continuous
injective map `φ : 𝕋 → ℂ`. -/
def IsSimpleLoop (Γ : Set ℂ) : Prop :=
  ∃ φ : Circle → ℂ, Continuous φ ∧ Function.Injective φ ∧ range φ = Γ

/-- Definition 10.2 (line 2553). A *simple arc* (Jordan arc) is an arc `φ '' circleArc α β` with `φ` injective on the
parameter arc `circleArc α β`. -/
def IsSimpleArc (Γ : Set ℂ) : Prop :=
  ∃ φ : Circle → ℂ, Continuous φ ∧ ∃ α β : ℝ, α ≤ β ∧ β < α + 2 * Real.pi ∧
    InjOn φ (circleArc α β) ∧ φ '' circleArc α β = Γ

/-- Definition 10.3 (line 2560). A set `X ⊆ ℂ` is *locally connected* if every neighbourhood of each `x ∈ X` with
respect to `X` contains a connected neighbourhood of `x` with respect to `X`. -/
def IsLocallyConnectedSet (X : Set ℂ) : Prop :=
  ∀ x ∈ X, ∀ N ∈ 𝓝[X] x, ∃ V ∈ 𝓝[X] x, V ⊆ N ∩ X ∧ IsConnected V

/-- Definition 10.4 (line 2566). A point `a` of a (compact, connected, locally connected) set `A` is a *cut point* if
`A \ {a}` is not connected. The standing hypotheses on `A` are carried by the statements. -/
def IsCutPoint (A : Set ℂ) (a : ℂ) : Prop :=
  a ∈ A ∧ ¬ IsPreconnected (A \ {a})

/-- The set of connected components of a set `F` (each `connectedComponentIn F x`, `x ∈ F`), as used in
Lemmas 10.1 (line 2499), 10.5 (line 2587) and Propositions 10.6, 10.7 (lines 2624, 2686). -/
def connectedComponentsIn {α : Type*} [TopologicalSpace α] (F : Set α) : Set (Set α) :=
  connectedComponentIn F '' F

/-- A set `X` *crosses* the annulus `𝔸_{s₁,s₂}(z)` if `closure X` meets both `∂B_{s₁}(z)` and `∂B_{s₂}(z)`
(line 2582; Lemma 10.1, line 2499). -/
def CrossesAnnulus (X : Set ℂ) (z : ℂ) (s₁ s₂ : ℝ) : Prop :=
  (closure X ∩ sphere z s₁).Nonempty ∧ (closure X ∩ sphere z s₂).Nonempty

/-- The connected components of `Y` which cross the annulus `𝔸_{s₁,s₂}(z)` (line 2582). Lemma 10.1 (line 2498):
"`Λ` does not cross `𝔸_{ρ/3,2ρ}(w)` more than `K` times" is
`(crossingComponents (Λ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ K`. -/
def crossingComponents (Y : Set ℂ) (z : ℂ) (s₁ s₂ : ℝ) : Set (Set ℂ) :=
  {C ∈ connectedComponentsIn Y | CrossesAnnulus C z s₁ s₂}

/-! ## Section 11: Lipschitz domains, cones, cone conditions, rescaled sets, dyadic squares -/

/-- Definition 11.1 (def:lipschitz, line 2712). A non-empty connected open set `A` is a *Lipschitz domain* if for each
`x₀ ∈ ∂A` there are `r > 0`, orthonormal coordinates (a linear isometry `e`, "relabeling and reorienting the coordinate
axes") and a Lipschitz `f : ℝ → ℝ` with `A ∩ B_r(x₀) = {x ∈ B_r(x₀) : Im(e x) > f(Re(e x))}`. The printed `U ∩ B_r(x₀)`
(line 2717) is read `A ∩ B_r(x₀)`. -/
def IsLipschitzDomain (A : Set ℂ) : Prop :=
  IsOpen A ∧ IsConnected A ∧
    ∀ x₀ ∈ frontier A, ∃ r > 0, ∃ e : ℂ ≃ₗᵢ[ℝ] ℂ, ∃ K : NNReal, ∃ f : ℝ → ℝ, LipschitzWith K f ∧
      A ∩ ball x₀ r = {x ∈ ball x₀ r | f (e x).re < (e x).im}

/-- The open sector `{c v + d w : c, d > 0}` with extremal directions `v, w` (Definition 11.3, line 2730). -/
def openSector (v w : ℂ) : Set ℂ :=
  {x | ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ x = c • v + d • w}

/-- Definition 11.3, first sentence (line 2730): a non-empty open set `𝒬 ⊊ ℂ` of the form `{c v + d w : c, d > 0}`
for extremal directions `v, w ∈ ℂ \ {0}`. -/
def IsOpenCone (Q : Set ℂ) : Prop :=
  Q.Nonempty ∧ IsOpen Q ∧ Q ≠ univ ∧ ∃ v w : ℂ, v ≠ 0 ∧ w ≠ 0 ∧ Q = openSector v w

/-- Definition 11.3 (line 2730). A *cone* is an open cone (`IsOpenCone`) or the complement of one ("we also define
complements of cones to be cones", line 2731). -/
def IsCone (Q : Set ℂ) : Prop :=
  IsOpenCone Q ∨ IsOpenCone Qᶜ

/-- The translate `𝒬(z) := 𝒬 + z` (line 2735). -/
def coneAt (Q : Set ℂ) (z : ℂ) : Set ℂ :=
  (fun x => x + z) '' Q

/-- Definition 11.4 (def:cone-condition, line 2737). `A` satisfies the *interior cone condition* at `z` if
`𝒬(z) ∩ B_R(z) ⊆ A` for some `R > 0` and some cone `𝒬`. (The paper takes `z ∈ ∂A`; statements carry it.) -/
def SatisfiesInteriorConeCondition (A : Set ℂ) (z : ℂ) : Prop :=
  ∃ R > 0, ∃ Q : Set ℂ, IsCone Q ∧ coneAt Q z ∩ ball z R ⊆ A

/-- Definition 11.4 (def:cone-condition, line 2738). `A` satisfies the *exterior cone condition* at `z` if
`𝒬(z) ∩ B_R(z) ⊆ Aᶜ` for some `R > 0` and some cone `𝒬`. -/
def SatisfiesExteriorConeCondition (A : Set ℂ) (z : ℂ) : Prop :=
  ∃ R > 0, ∃ Q : Set ℂ, IsCone Q ∧ coneAt Q z ∩ ball z R ⊆ Aᶜ

/-- Definition 11.4 (def:cone-condition, line 2739). The *cone condition* at `z`: both the interior and the exterior
cone conditions. -/
def SatisfiesConeCondition (A : Set ℂ) (z : ℂ) : Prop :=
  SatisfiesInteriorConeCondition A z ∧ SatisfiesExteriorConeCondition A z

/-- The rescaled translate `A_r(z) := r A + z` (Section 11.3, line 3102). -/
def rescaledSet (A : Set ℂ) (r : ℝ) (z : ℂ) : Set ℂ :=
  (fun x => (r : ℂ) * x + z) '' A

/-- The closed dyadic square `[j 2⁻ⁿ, (j+1) 2⁻ⁿ] × [k 2⁻ⁿ, (k+1) 2⁻ⁿ]` of side length `2⁻ⁿ`, `n ∈ ℤ`
(Lemma 11.10, line 2980; side length `2^{-n₀}`, `n₀ ∈ ℤ`, line 2986). -/
def closedDyadicSquare (n j k : ℤ) : Set ℂ :=
  Icc ((j : ℝ) * 2 ^ (-n)) ((j + 1) * 2 ^ (-n)) ×ℂ Icc ((k : ℝ) * 2 ^ (-n)) ((k + 1) * 2 ^ (-n))

/-- A *closed dyadic square* (Lemma 11.10, line 2980). -/
def IsClosedDyadicSquare (S : Set ℂ) : Prop :=
  ∃ n j k : ℤ, S = closedDyadicSquare n j k

/-- The deterministic sets of Section 11.3 (line 3100, Figure fig:pinch-point, line 3110) entering the pinch-point
event `Ĝ_r(z)` (eq:pinch-point-event, line 3124): connected open sets `U ⋐ T` and `Q' ⋐ Q` with `U` a ball contained
in `𝔸_{1,2}`, `Q', Q ⊆ 𝔸_{4,5} \ closure T`, `T ⊆ 𝔸_{1,5}` and `∂B_5 ⊆ ∂T` (all centred at `0`). The paper further
asks `T` to be "keyhole-shaped, as shown in the figure"; that shape is not formalized, so a statement asserting the
positivity of `P[Ĝ_1(0)]` (Lemma 11.12) for one such configuration should quantify existentially over the
configuration. (`Q' ⊆ 𝔸_{4,5} \ closure T` follows from `closure Q' ⊆ Q`.) -/
structure IsPinchPointConfiguration (U T Q' Q : Set ℂ) : Prop where
  isOpen_U : IsOpen U
  isConnected_U : IsConnected U
  isOpen_T : IsOpen T
  isConnected_T : IsConnected T
  isOpen_Q' : IsOpen Q'
  isConnected_Q' : IsConnected Q'
  isOpen_Q : IsOpen Q
  isConnected_Q : IsConnected Q
  closure_U_subset : closure U ⊆ T
  closure_Q'_subset : closure Q' ⊆ Q
  exists_eq_ball : ∃ c : ℂ, ∃ ρ : ℝ, U = ball c ρ
  U_subset : U ⊆ annulus 0 1 2
  Q_subset : Q ⊆ annulus 0 4 5 \ closure T
  T_subset : T ⊆ annulus 0 1 5
  sphere_subset_frontier : sphere (0 : ℂ) 5 ⊆ frontier T

/-! ## Sanity lemmas -/

/-- The unit circle `𝕋` is a simple loop. -/
theorem isSimpleLoop_sphere_zero_one : IsSimpleLoop (sphere (0 : ℂ) 1) :=
  ⟨(↑), continuous_subtype_val, Circle.coe_injective, by
    ext x
    exact ⟨fun ⟨ζ, hζ⟩ => hζ ▸ ζ.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩

theorem IsSimpleLoop.isLoop {Γ : Set ℂ} (h : IsSimpleLoop Γ) : IsLoop Γ :=
  let ⟨φ, hc, _, hr⟩ := h
  ⟨φ, hc, hr⟩

theorem IsSimpleArc.isArc {Γ : Set ℂ} (h : IsSimpleArc Γ) : IsArc Γ :=
  let ⟨φ, hc, α, β, h₁, h₂, _, h₃⟩ := h
  ⟨φ, hc, α, β, h₁, h₂, h₃⟩

/-- Simple loops are preserved by continuous injective maps of the plane. -/
theorem IsSimpleLoop.image {Γ : Set ℂ} (h : IsSimpleLoop Γ) {g : ℂ → ℂ} (hg : Continuous g)
    (hinj : Function.Injective g) : IsSimpleLoop (g '' Γ) := by
  obtain ⟨φ, hc, hφ, rfl⟩ := h
  exact ⟨g ∘ φ, hg.comp hc, hinj.comp hφ, range_comp g φ⟩

/-- Definition 10.3 agrees with Mathlib's `LocallyConnectedSpace` of the subtype. -/
theorem isLocallyConnectedSet_iff_locallyConnectedSpace {X : Set ℂ} :
    IsLocallyConnectedSet X ↔ LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  constructor
  · intro h y U hU
    rw [mem_nhds_subtype_iff_nhdsWithin] at hU
    obtain ⟨V, hV, hVsub, hVconn⟩ := h y y.2 _ hU
    have hVX : X ∩ V = V := inter_eq_right.2 (hVsub.trans inter_subset_right)
    refine ⟨(↑) ⁻¹' V, ?_, ?_, ?_⟩
    · rw [mem_nhds_subtype_iff_nhdsWithin, Subtype.image_preimage_coe, hVX]
      exact hV
    · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe, hVX]
      exact hVconn.isPreconnected
    · intro u hu
      obtain ⟨u', hu', hu'u⟩ := (hVsub hu).1
      exact Subtype.val_injective hu'u ▸ hu'
  · intro h x hx N hN
    have hN' : ((↑) : X → ℂ) ⁻¹' N ∈ 𝓝 (⟨x, hx⟩ : X) := by
      rw [mem_nhds_subtype_iff_nhdsWithin, Subtype.image_preimage_coe]
      exact inter_mem self_mem_nhdsWithin hN
    obtain ⟨V, hV, hVconn, hVsub⟩ := h ⟨x, hx⟩ _ hN'
    refine ⟨(↑) '' V, mem_nhds_subtype_iff_nhdsWithin.1 hV, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨hVsub hu, u.2⟩
    · exact ⟨⟨x, ⟨x, hx⟩, mem_of_mem_nhds hV, rfl⟩, Topology.IsInducing.subtypeVal.isPreconnected_image.2 hVconn⟩

theorem isConnected_of_mem_connectedComponentsIn {α : Type*} [TopologicalSpace α] {F C : Set α}
    (hC : C ∈ connectedComponentsIn F) : IsConnected C ∧ C ⊆ F := by
  obtain ⟨x, hx, rfl⟩ := hC
  exact ⟨isConnected_connectedComponentIn_iff.2 hx, connectedComponentIn_subset F x⟩

/-- A closed ball crosses every annulus it spans. -/
theorem crossesAnnulus_closedBall {z : ℂ} {s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₁₂ : s₁ ≤ s₂) :
    CrossesAnnulus (closedBall z s₂) z s₁ s₂ := by
  rw [CrossesAnnulus, closure_closedBall]
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (x := z)).2 h₁
  obtain ⟨q, hq⟩ := (NormedSpace.sphere_nonempty (x := z)).2 (h₁.trans h₁₂)
  exact ⟨⟨p, closedBall_subset_closedBall h₁₂ (sphere_subset_closedBall hp), hp⟩,
    ⟨q, sphere_subset_closedBall hq, hq⟩⟩

theorem CrossesAnnulus.mono {X Y : Set ℂ} {z : ℂ} {s₁ s₂ : ℝ} (h : CrossesAnnulus X z s₁ s₂) (hXY : X ⊆ Y) :
    CrossesAnnulus Y z s₁ s₂ :=
  ⟨h.1.mono (inter_subset_inter_left _ (closure_mono hXY)),
    h.2.mono (inter_subset_inter_left _ (closure_mono hXY))⟩

/-- The open upper half-plane is a Lipschitz domain. -/
theorem isLipschitzDomain_upperHalfPlane : IsLipschitzDomain {x : ℂ | 0 < x.im} := by
  refine ⟨isOpen_lt continuous_const continuous_im, (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩, ?_⟩
  intro x₀ _
  refine ⟨1, one_pos, LinearIsometryEquiv.refl ℝ ℂ, 0, fun _ => 0, LipschitzWith.const 0, ?_⟩
  ext x
  simp [and_comm]

theorem openSector_one_I : openSector 1 I = {x : ℂ | 0 < x.re ∧ 0 < x.im} := by
  ext x
  constructor
  · rintro ⟨c, d, hc, hd, rfl⟩
    simp [hc, hd]
  · rintro ⟨h₁, h₂⟩
    exact ⟨x.re, x.im, h₁, h₂, by apply Complex.ext <;> simp⟩

theorem openSector_neg_one_neg_I : openSector (-1) (-I) = {x : ℂ | x.re < 0 ∧ x.im < 0} := by
  ext x
  constructor
  · rintro ⟨c, d, hc, hd, rfl⟩
    simp [hc, hd]
  · rintro ⟨h₁, h₂⟩
    exact ⟨-x.re, -x.im, neg_pos.2 h₁, neg_pos.2 h₂, by apply Complex.ext <;> simp⟩

/-- The open first quadrant is a cone (extremal directions `1, i`). -/
theorem isOpenCone_firstQuadrant : IsOpenCone {x : ℂ | 0 < x.re ∧ 0 < x.im} := by
  refine ⟨⟨1 + I, by simp⟩, ?_, ?_, 1, I, one_ne_zero, I_ne_zero, openSector_one_I.symm⟩
  · exact (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)
  · intro h
    have h0 : (0 : ℂ) ∈ {x : ℂ | 0 < x.re ∧ 0 < x.im} := h ▸ mem_univ 0
    simp at h0

/-- The open third quadrant is a cone (extremal directions `-1, -i`). -/
theorem isOpenCone_thirdQuadrant : IsOpenCone {x : ℂ | x.re < 0 ∧ x.im < 0} := by
  refine ⟨⟨-1 - I, by simp⟩, ?_, ?_, -1, -I, by simp, by simp, openSector_neg_one_neg_I.symm⟩
  · exact (isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_im continuous_const)
  · intro h
    have h0 : (0 : ℂ) ∈ {x : ℂ | x.re < 0 ∧ x.im < 0} := h ▸ mem_univ 0
    simp at h0

/-- The upper half-plane satisfies the cone condition at the boundary point `0`. -/
theorem satisfiesConeCondition_upperHalfPlane_zero : SatisfiesConeCondition {x : ℂ | 0 < x.im} 0 := by
  refine ⟨⟨1, one_pos, _, Or.inl isOpenCone_firstQuadrant, ?_⟩,
    ⟨1, one_pos, _, Or.inl isOpenCone_thirdQuadrant, ?_⟩⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    simpa using hx.2
  · rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    simp only [add_zero, mem_compl_iff, mem_ofPred_eq, not_lt]
    exact hx.2.le

theorem rescaledSet_one (A : Set ℂ) (z : ℂ) : rescaledSet A 1 z = coneAt A z := by
  simp [rescaledSet, coneAt]

theorem isCompact_closedDyadicSquare (n j k : ℤ) : IsCompact (closedDyadicSquare n j k) :=
  isCompact_Icc.reProdIm isCompact_Icc

theorem IsClosedDyadicSquare.isCompact {S : Set ℂ} (h : IsClosedDyadicSquare S) : IsCompact S := by
  obtain ⟨n, j, k, rfl⟩ := h
  exact isCompact_closedDyadicSquare n j k

end HarmonicBalls
