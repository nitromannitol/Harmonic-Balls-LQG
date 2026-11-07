import HarmonicBalls.Defs.LQG

/-!
# Liouville graph distance

The unrestricted Liouville graph distance of Ding--Gwynne,
arXiv:1807.01072v3, Definition 1.3, p. 6. Its point-to-point exponent
characterizes the LQG dimension in Theorem 1.4, p. 6, equation (1.8).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- A finite family of Euclidean balls of mass at most `ε` covers a path. -/
def IsLiouvilleGraphCover (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) (count : ℕ) : Prop :=
  ∃ balls : Fin count → ℂ × ℝ,
    (∀ index, 0 < (balls index).2 ∧
      μ (Metric.ball (balls index).1 (balls index).2) ≤ ENNReal.ofReal ε) ∧
    ∃ path : Path z w, ∀ time : unitInterval,
      ∃ index, path time ∈ Metric.ball (balls index).1 (balls index).2

/-- The minimum number of `μ`-mass-at-most-`ε` balls covering a path, or infinity if none exists. -/
noncomputable def liouvilleGraphDistance (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) : ℕ∞ :=
  sInf {number | ∃ count : ℕ, number = count ∧ IsLiouvilleGraphCover μ ε z w count}

/-- Any admissible cover bounds Liouville graph distance. -/
theorem liouvilleGraphDistance_le {μ : Measure ℂ} {ε : ℝ} {z w : ℂ} {count : ℕ}
    (cover : IsLiouvilleGraphCover μ ε z w count) :
    liouvilleGraphDistance μ ε z w ≤ count := by
  exact sInf_le ⟨count, rfl, cover⟩

/-- Increasing the allowed ball mass cannot increase Liouville graph distance. -/
theorem liouvilleGraphDistance_antitone (μ : Measure ℂ) (z w : ℂ) :
    Antitone fun ε => liouvilleGraphDistance μ ε z w := by
  intro ε₁ ε₂ hε
  apply sInf_le_sInf
  intro number hnumber
  obtain ⟨count, rfl, balls, hballs, path, hpath⟩ := hnumber
  refine ⟨count, rfl, balls, ?_, path, hpath⟩
  intro index
  exact ⟨(hballs index).1, (hballs index).2.trans (ENNReal.ofReal_le_ofReal hε)⟩

/-- The dyadic point-to-point Liouville graph-distance exponent. -/
noncomputable def liouvilleGraphExponent (μ : Measure ℂ) (z w : ℂ) (index : ℕ) : ℝ :=
  Real.log (liouvilleGraphDistance μ (dyadicScale index) z w).toNat /
    ((index : ℝ) * Real.log 2)

/-- A dimension characterized by the dyadic point-to-point graph-distance exponent. -/
def IsLiouvilleGraphDimension (μ : Measure ℂ) (z w : ℂ) (dimension : ℝ) : Prop :=
  0 < dimension ∧
    (∀ᶠ index : ℕ in atTop, liouvilleGraphDistance μ (dyadicScale index) z w ≠ ⊤) ∧
    Tendsto (liouvilleGraphExponent μ z w) atTop (𝓝 (1 / dimension))

/-- A given measure and pair of points determine at most one such dimension. -/
theorem IsLiouvilleGraphDimension.unique {μ : Measure ℂ} {z w : ℂ} {dimension dimension' : ℝ}
    (h : IsLiouvilleGraphDimension μ z w dimension)
    (h' : IsLiouvilleGraphDimension μ z w dimension') : dimension = dimension' := by
  apply inv_injective
  simpa only [one_div] using tendsto_nhds_unique h.2.2 h'.2.2

/-- Almost-sure graph-distance characterizations on the same probability space have the same dimension. -/
theorem IsLiouvilleGraphDimension.unique_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ) (z w : ℂ)
    {dimension dimension' : ℝ}
    (h : ∀ᵐ ω ∂P, IsLiouvilleGraphDimension (μ ω) z w dimension)
    (h' : ∀ᵐ ω ∂P, IsLiouvilleGraphDimension (μ ω) z w dimension') : dimension = dimension' := by
  obtain ⟨ω, hω, h'ω⟩ := (h.and h').exists
  exact hω.unique h'ω

end HarmonicBalls
