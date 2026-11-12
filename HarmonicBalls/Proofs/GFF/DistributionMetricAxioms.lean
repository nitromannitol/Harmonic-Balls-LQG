import HarmonicBalls.Proofs.GFF.BonannoFieldProjection
import HarmonicBalls.Proofs.GFF.DistributionMetricDecoder
import LatticeProb.LQG.LengthMetric
import LatticeProb.LQG.ContMetricWeyl
import LatticeProb.Bonanno.LQGMetric.Metric.WeylMetric
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import HarmonicBalls.Proofs.GFF.DistMetricPairingCoord
import LatticeProb.LQG.ContMetricLength
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # The metric assignment on distributions: length space, Weyl scaling, coordinate change

Let `𝔇` be a γ-LQG metric on pairing functionals with Weyl exponent `ξ` (`IsLQGMetric γ ξ 𝔇`), and
let `distributionMetric 𝔇 : DistC → ContMetric` be the induced Borel metric assignment on
distributions. For a whole-plane GFF plus a continuous function `h` in the sense of
`LQGMetric.IsGFFPlusCont` (Gwynne-Miller 2021, Section 1.2, p. 6), almost surely:
* Axiom I (length space): `(ℂ, distributionMetric 𝔇 (h ω))` is a length space
  (`ae_isLength_distributionMetric`);
* Axiom III (Weyl scaling): for every continuous `f`,
  `e^{ξ f} · distributionMetric 𝔇 (h ω) = distributionMetric 𝔇 (h ω + f)`
  (`ae_weylScale_distributionMetric`);
* Axiom II (locality): for a deterministic open `U`, the internal metric
  `distributionMetric 𝔇 (h ω)` on `U` is almost surely a fixed measurable function of the
  restriction `h|_U` (`locality_distributionMetric`);
* Axiom IV (coordinate change): for fixed `r > 0` and `z`, `distributionMetric 𝔇 (h ω)` at
  `(r u + z, r v + z)` equals `distributionMetric 𝔇 (h(r · + z) + Q log r)` at `(u, v)`
  (`ae_coord_distributionMetric`).

The field `h` has the same test pairings as `h^ℂ + g` for a project whole-plane GFF `h^ℂ` and a
random continuous function `g` (`exists_projectGFF_of_isGFFPlusCont`), so the axioms of
`IsLQGMetric` apply to it. The deterministic input `hcm` is the fact that a Euclidean length
metric is a continuous length metric (in the sense of `LQGMetric.ContMetric`); it is stated as a
hypothesis in the form of `LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric`.

Weyl scaling determines `𝔇 (h + f)` only through `ENNReal.ofReal`, i.e. through its positive
part; `distributionMetric` samples the positive part, so no sign information is needed off the
almost sure event where axiom I holds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}

/-- The paper's Euclidean length metrics are those of the library. -/
theorem IsEuclideanLengthMetric.toLatticeProb {D : ℂ → ℂ → ℝ} (h : IsEuclideanLengthMetric D) :
    LatticeProb.LQG.IsEuclideanLengthMetric D :=
  ⟨h.self_eq_zero, h.eq_of_eq_zero, h.symm, h.triangle, h.isOpen_iff, h.ofReal_eq_internalMetric⟩

/-- If the distribution `T` has the test pairings of the pairing functional `H`, and the positive
part of `𝔇 H` is the continuous metric `d`, then `distributionMetric 𝔇 T = d`. -/
theorem distributionMetric_eq_of_testPairing
    (h𝔇 : ∀ z w, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    {T : LQGMetric.DistC} {H : (ℂ → ℝ) → ℝ} (hTH : ∀ φ : LQGMetric.TestC, T φ = H φ)
    {d : LQGMetric.ContMetric}
    (hd : ∀ u v, ENNReal.ofReal (𝔇 H u v) = ENNReal.ofReal (d.1 (u, v))) :
    distributionMetric 𝔇 T = d := by
  refine distributionMetric_eq fun u v => ?_
  have e : 𝔇 (distributionPairingExtension T) u v = 𝔇 H u v :=
    eq_of_distribution_measurable_of_testPairing_eq (fun T => 𝔇 T u v) (h𝔇 u v) fun φ hφ => by
      simp only [distributionPairingExtension, hφ, ↓reduceDIte]
      exact hTH _
  rw [e, hd]

/-- **Axiom I for the metric assignment on distributions.** For a γ-LQG metric `𝔇` on pairing
functionals and a whole-plane GFF plus a continuous function `h`, almost surely
`(ℂ, distributionMetric 𝔇 (h ω))` is a length space. -/
theorem ae_isLength_distributionMetric (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, (distributionMetric 𝔇 (h ω)).IsLength := by
  obtain ⟨hC, hcirc, g, hG, hgc, hgm, hpair⟩ := exists_projectGFF_of_isGFFPlusCont hh
  have ax := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc g hG hgc hgm
  filter_upwards [ax.ae_isEuclideanLengthMetric] with ω hω
  obtain ⟨d, hd, hlen⟩ := hcm _ hω.toLatticeProb
  rw [distributionMetric_eq_of_testPairing h𝔇.measurable_apply
    (H := addFunPairing (hC ω) (g ω)) (fun φ => hpair ω φ) fun u v => by rw [hd]]
  exact hlen

/-- **Axiom III for the metric assignment on distributions.** For a γ-LQG metric `𝔇` on pairing
functionals with Weyl exponent `ξ` and a whole-plane GFF plus a continuous function `h`, almost
surely, for every continuous `f`, `e^{ξ f} · distributionMetric 𝔇 (h ω) =
distributionMetric 𝔇 (h ω + f)`. -/
theorem ae_weylScale_distributionMetric (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
      LQGMetric.weylScale ξ f (distributionMetric 𝔇 (h ω)) z w =
        ENNReal.ofReal ((distributionMetric 𝔇 (LQGMetric.addFun (h ω) f)).1 (z, w)) := by
  obtain ⟨hC, hcirc, g, hG, hgc, hgm, hpair⟩ := exists_projectGFF_of_isGFFPlusCont hh
  have ax := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc g hG hgc hgm
  filter_upwards [ax.ae_isEuclideanLengthMetric, ax.ae_weylScaling] with ω hω hW
  intro f z w
  obtain ⟨d, hd, hlen⟩ := hcm _ hω.toLatticeProb
  have hD : distributionMetric 𝔇 (h ω) = d :=
    distributionMetric_eq_of_testPairing h𝔇.measurable_apply
      (H := addFunPairing (hC ω) (g ω)) (fun φ => hpair ω φ) fun u v => by rw [hd]
  have hH : 𝔇 (addFunPairing (hC ω) (g ω)) = fun u v => d.1 (u, v) :=
    funext fun u => funext fun v => (hd u v).symm
  have hDf : distributionMetric 𝔇 (LQGMetric.addFun (h ω) f) = LQGMetric.weylMetric ξ f d hlen := by
    refine distributionMetric_eq_of_testPairing h𝔇.measurable_apply
      (H := addFunPairing (addFunPairing (hC ω) (g ω)) f) (fun φ => ?_) fun u v => ?_
    · show h ω φ + LQGMetric.ofCont f φ = _
      rw [hpair ω φ, ofCont_apply_mul]
      rfl
    · rw [hW f f.continuous u v, LQGMetric.weylMetric_spec, hH]
      exact LatticeProb.LQG.weylScaling_contMetric d ξ f u v
  rw [hD, hDf, LQGMetric.weylMetric_spec]

/-- **Axiom IV for the metric assignment on distributions.** For a γ-LQG metric `𝔇` on pairing
functionals and a whole-plane GFF plus a continuous function `h`, for fixed `r > 0` and `z ∈ ℂ`,
almost surely `D_h(r u + z, r v + z) = D_{h(r · + z) + Q log r}(u, v)` for all `u, v`, where
`D = distributionMetric 𝔇`. -/
theorem ae_coord_distributionMetric (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsGFFPlusCont h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (distributionMetric 𝔇 (h ω)).1 (r * u + z, r * v + z) =
        (distributionMetric 𝔇 (LQGMetric.addConst (LQGMetric.affineComp r z (h ω))
          (LQGMetric.Q γ * Real.log r))).1 (u, v) := by
  obtain ⟨hC, hcirc, g, hG, hgc, hgm, hpair⟩ := exists_projectGFF_of_isGFFPlusCont hh
  have ax := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc g hG hgc hgm
  filter_upwards [ax.ae_isEuclideanLengthMetric, ax.coordChange r hr z] with ω hω hco
  intro u v
  obtain ⟨d, hd, -⟩ := hcm _ hω.toLatticeProb
  have hD : distributionMetric 𝔇 (h ω) = d :=
    distributionMetric_eq_of_testPairing h𝔇.measurable_apply
      (H := addFunPairing (hC ω) (g ω)) (fun φ => hpair ω φ) fun u v => by rw [hd]
  have hD' : distributionMetric 𝔇 (LQGMetric.addConst (LQGMetric.affineComp r z (h ω))
      (LQGMetric.Q γ * Real.log r)) = LQGMetric.ContMetric.affine r hr.ne' z d := by
    refine distributionMetric_eq_of_testPairing h𝔇.measurable_apply
      (H := addFunPairing (affinePullbackPairing (addFunPairing (hC ω) (g ω)) r z)
        fun _ => lqgQ γ * Real.log r) (fun φ => ?_) fun u v => ?_
    · have hψ : (fun y => (φ : ℂ → ℝ) ((y - z) / r)) = ⇑(LQGMetric.testAffinePull r z φ) :=
        funext fun y => by rw [LQGMetric.testAffinePull_apply r z hr.ne']
      show LQGMetric.affineComp r z (h ω) φ +
        LQGMetric.ofCont (ContinuousMap.const ℂ (LQGMetric.Q γ * Real.log r)) φ = _
      rw [← affinePullbackPairing_distributionPairingExtension_test (h ω) hr z φ, ofCont_apply_mul]
      simp only [affinePullbackPairing, addFunPairing]
      rw [hψ, distributionPairingExtension_test, hpair]
      simp only [LQGMetric.testAffinePull_apply r z hr.ne']
      rfl
    · rw [← hco u v, ← hd]
      rfl
  rw [hD, hD']
  rfl

/-- **Axiom II for the metric assignment on distributions.** For a γ-LQG metric `𝔇` on pairing
functionals, a whole-plane GFF plus a continuous function `h` and a deterministic open set `U`,
there is a measurable map `F` on the distributions on `U` such that almost surely the internal
metric of `distributionMetric 𝔇 (h ω)` on `U` is `F (h|_U)` at every pair of points of `U`.
The random internal metric of axiom II of `IsLQGMetric` is measurable for `σ(h|_U)`, which is
generated by the restriction map `h ↦ h|_U`; Doob-Dynkin factorization then gives `F` pair by
pair. -/
theorem locality_distributionMetric (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsGFFPlusCont h P)
    (U : TopologicalSpace.Opens ℂ) :
    ∃ F : LQGMetric.DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
        (distributionMetric 𝔇 (h ω)).internal U z w = F (LQGMetric.restrictTo U (h ω)) z w := by
  obtain ⟨hC, hcirc, g, hG, hgc, hgm, hpair⟩ := exists_projectGFF_of_isGFFPlusCont hh
  have ax := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc g hG hgc hgm
  obtain ⟨G, hGm, hGae⟩ := ax.locality U U.isOpen
  let R : Ω → LQGMetric.DistOn U := fun ω => LQGMetric.restrictTo U (h ω)
  have hle : pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (g ω)) U ≤
      MeasurableSpace.comap R inferInstance := by
    refine iSup₂_le fun φ hφ => ?_
    let ψ : LQGMetric.TestOn U := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
    have hev : Measurable fun T : LQGMetric.DistOn U => T ψ :=
      (measurable_pi_apply ψ).comp (comap_measurable _)
    have he : (fun ω => addFunPairing (hC ω) (g ω) φ) = (fun T : LQGMetric.DistOn U => T ψ) ∘ R :=
      funext fun ω => by
        change addFunPairing (hC ω) (g ω) φ = h ω (TestFunction.monoCLM ℝ ψ)
        rw [hpair, TestFunction.monoCLM_apply]
        simp only [le_refl, le_top, and_self, ↓reduceIte]
        rfl
    rw [he]
    exact (hev.comp (comap_measurable R)).comap_le
  have hfac : ∀ z w, ∃ e : LQGMetric.DistOn U → ℝ≥0∞, Measurable e ∧ (fun ω => G ω z w) = e ∘ R :=
    fun z w => ((hGm z w).mono hle le_rfl).exists_eq_measurable_comp
  choose e he heq using hfac
  refine ⟨fun T z w => e z w T, measurable_pi_iff.mpr fun z => measurable_pi_iff.mpr fun w =>
    he z w, ?_⟩
  filter_upwards [ax.ae_isEuclideanLengthMetric, hGae] with ω hω hGω
  intro z hz w hw
  obtain ⟨d, hd, -⟩ := hcm _ hω.toLatticeProb
  have hD : distributionMetric 𝔇 (h ω) = d :=
    distributionMetric_eq_of_testPairing h𝔇.measurable_apply
      (H := addFunPairing (hC ω) (g ω)) (fun φ => hpair ω φ) fun u v => by rw [hd]
  have hH : (fun u v => d.1 (u, v)) = 𝔇 (addFunPairing (hC ω) (g ω)) :=
    funext fun u => funext fun v => hd u v
  rw [hD, ← LatticeProb.LQG.internalMetric_contMetric d U z w, hH]
  exact (hGω z hz w hw).trans (congrFun (heq z w) ω)

end HarmonicBalls
