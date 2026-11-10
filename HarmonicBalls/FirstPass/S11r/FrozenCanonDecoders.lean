import HarmonicBalls.FirstPass.Frozen.S11n
import HarmonicBalls.FirstPass.S11s.B1Covariance

/-!
# Canonical decoder data from the frozen measurable existence (fp-S11r-G-data, n2)

`CanonDecoderData γ ξ α₀` packages, for one `(γ, ξ, α₀)`, the data that the frozen input
`LQGCanonicalDecodersMeasurableExistStmt` (`FirstPass/Frozen/S11n.lean`, the measurable strengthening of
`LQGCanonicalDecodersExistStmt`; Gwynne-Miller arXiv:1905.00383v3 Thm 1.2, Duplantier-Sheffield arXiv:0808.1560v2 Prop 1.1)
supplies: the measure kernel `K` (s-finite, locally finite values), the metric map `d : CanonSpace → C(ℂ×ℂ, ℝ)`
(Borel), the identification clause, and the measurable set `G` of canonical fields (`alphaCanon α₀ hC ω ∈ G` almost
surely for every whole-plane GFF model) on which `K L` has full support and `d L` is a length metric inducing the
Euclidean topology (`IsEuclideanLengthMetric`).

Consequently, with no further hypothesis:
* `hGm : MeasurableSet G`, `hGa` (for every model), `hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L)`;
* `hDμ`, `hDd` (measurability of `L ↦ Dμ L` and of `L ↦ Dd L x y`);
* `hG0`, `hG0a`, `hinv`, `hstep` for a model, via `B1_covariance` (S11s/B1Covariance.lean), which needs the physical
  measure and metric of that model at the same `α₀` (`canonG0_of_model`).

The α₀ index is the caller's: the identification clause and `alphaCanon α₀` must use the insertion of the physical
measure `μ` and metric `D` of the model that is passed to `canonG0_of_model`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11rFrozenCanonDecoders

/-- The decoder data of one `(γ, ξ, α₀)` given by the frozen measurable existence. -/
structure CanonDecoderData (γ ξ α₀ : ℝ) : Type where
  /-- The measure decoder: a measurable, s-finite kernel from canonical fields to `ℂ`. -/
  K : Kernel S11n.CanonSpace ℂ
  /-- The metric decoder: a Borel map into continuous functions on `ℂ × ℂ`. -/
  d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ
  isSFinite_K : IsSFiniteKernel K
  finiteOnCompacts_K : ∀ L, IsFiniteMeasureOnCompacts (K L)
  measurable_d : Measurable d
  /-- The identification of the LQG measure and metric of every whole-plane model (`LQGCanonicalIdentificationStmt`). -/
  ident : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ α₀ (fun L => K L) (fun L x y => d L (x, y))
  /-- The set of canonical fields on which the decoders are regular. -/
  G : Set S11n.CanonSpace
  measurableSet_G : MeasurableSet G
  /-- The canonical field lies in `G` almost surely, for every whole-plane GFF model. -/
  ae_mem_G : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G
  /-- On `G`: full support of the measure, and the metric is a length metric inducing the Euclidean topology. -/
  regular_G : ∀ L ∈ G, (K L).support = univ ∧ IsEuclideanLengthMetric (fun x y => d L (x, y))

/-- The frozen measurable existence gives the decoder data for every admissible `(γ, ξ, α₀)`. -/
theorem canonDecoderData_of_frozen (hEx : HarmonicBalls.LQGCanonicalDecodersMeasurableExistStmt.{0})
    {γ ξ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) : Nonempty (CanonDecoderData γ ξ α₀) := by
  obtain ⟨K, d, hK, hKf, hd, hid, G, hGm, hGa, hGs⟩ := hEx γ ξ α₀ hγ0 hγ2 hα
  exact ⟨⟨K, d, hK, hKf, hd, hid, G, hGm, hGa, hGs⟩⟩

namespace CanonDecoderData

variable {γ ξ α₀ : ℝ}

/-- `hDμ`: the measure decoder is measurable in the canonical field. -/
theorem measurable_K (D : CanonDecoderData γ ξ α₀) : Measurable D.K :=
  D.K.measurable

/-- `hDd`: each coordinate of the metric decoder is measurable in the canonical field. -/
theorem measurable_dd (D : CanonDecoderData γ ξ α₀) (x y : ℂ) :
    Measurable fun L : S11n.CanonSpace => D.d L (x, y) :=
  (ContinuousMap.measurable_eval (x, y)).comp D.measurable_d

/-- `hGreg`: on `G` the metric decoder is a Euclidean length metric. -/
theorem euclideanLength_on_G (D : CanonDecoderData γ ξ α₀) :
    ∀ L ∈ D.G, IsEuclideanLengthMetric (fun x y => D.d L (x, y)) :=
  fun L hL => (D.regular_G L hL).2

end CanonDecoderData

/-- `hG0`, `hG0a`, `hinv`, `hstep` for one whole-plane model: the dilation-covariant set `G0` of canonical fields,
from `B1_covariance`. The physical measure `μ` and metric `Dm` of this model are at the same insertion `α₀` as the
identification clause. -/
theorem canonG0_of_model {γ ξ α₀ : ℝ} (D : CanonDecoderData γ ξ α₀) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {Dm : Ω → ℂ → ℂ → ℝ} (hD : IsLQGMetricOfField P γ ξ α₀ hC Dm) :
    ∃ G0 : Set S11n.CanonSpace, MeasurableSet G0 ∧ (∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G0) ∧
      dilOp ⁻¹' G0 = G0 ∧
      ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        D.K (dilOp L) = ENNReal.ofReal a • (D.K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
        ∀ u v : ℂ, D.d (dilOp L) (u, v) = b * D.d L (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) :=
  HarmonicBalls.B1_covariance hγ0 hγ2 hα P hG hμ hD D.K D.d D.measurable_d D.finiteOnCompacts_K D.ident D.G
    D.measurableSet_G (D.ae_mem_G Ω P hC hcirc hG) D.regular_G

end HarmonicBalls.FirstPassS11rFrozenCanonDecoders

#print axioms HarmonicBalls.FirstPassS11rFrozenCanonDecoders.canonDecoderData_of_frozen
#print axioms HarmonicBalls.FirstPassS11rFrozenCanonDecoders.canonG0_of_model
