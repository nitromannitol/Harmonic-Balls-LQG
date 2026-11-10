import HarmonicBalls.Steps.Sec11.CountableClearanceChains

/-!
# Localized countable clearance chains (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 4.3 (internalization is a countable operation).

`denseClearanceChainCost` (`Steps/Sec11/CountableClearanceChains.lean`) tests clearance against all of `Uᶜ`, which is
uncountable, so it needs continuity of the metric in its second variable to be measurable. The decoded metric of
section 4 is only measurable coordinatewise and is not continuous for an arbitrary pairing. The localized cost below
tests clearance only against a countable set `Q` (inside the decoder's domain), and needs no continuity: each cost is
measurable in `ω` as soon as every value `D ω a b` is measurable, for `a, b` in a countable set.
-/

namespace HarmonicBalls.S11m

open Set MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped Classical in
/-- Cost of a dense chain `k` (vertices `x = v₀, v₁, …, v_{n+1} = y`, interior vertices in `S`) when clearance is
tested on `Q`: the sum of the edge lengths `D(v_i, v_{i+1})` if every edge has a rational `δ > 0` with
`D(v_i, v_{i+1}) < δ` and `δ ≤ D(v_i, q)` for all `q ∈ Q`; otherwise `∞`. -/
noncomputable def localClearanceCost {S : Set ℂ} (Q : Set ℂ) (D : ℂ → ℂ → ℝ) (x y : ℂ)
    (k : Σ n : ℕ, Fin n → S) : ℝ≥0∞ :=
  if ∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ q ∈ Q, (δ : ℝ) ≤ D (denseChainVertex x y k i) q
  then ∑ i ∈ Finset.range (k.1 + 1),
    ENNReal.ofReal (D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)))
  else ∞

/-- Infimum of the localized clearance-chain costs with interior vertices in `S`. -/
noncomputable def localClearanceInf (S : Set ℂ) (Q : Set ℂ) (D : ℂ → ℂ → ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ k : Σ n : ℕ, Fin n → S, localClearanceCost Q D x y k

/-- The clearance condition of a fixed chain is a measurable event in `ω`, when `Q` is countable. -/
theorem measurableSet_localClearance_condition {S : Set ℂ} {Q : Set ℂ} (hQ : Q.Countable)
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ a b, Measurable fun ω => D ω a b) (x y : ℂ)
    (k : Σ n : ℕ, Fin n → S) :
    MeasurableSet {ω | ∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D ω (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ q ∈ Q, (δ : ℝ) ≤ D ω (denseChainVertex x y k i) q} := by
  have : Countable Q := hQ.to_subtype
  have hset : {ω | ∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D ω (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ q ∈ Q, (δ : ℝ) ≤ D ω (denseChainVertex x y k i) q} =
      ⋂ i : ℕ, ⋂ (_ : i < k.1 + 1), ⋃ δ : ℚ,
        ({ω | 0 < δ} ∩ {ω | D ω (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ)} ∩
          ⋂ q : Q, {ω | (δ : ℝ) ≤ D ω (denseChainVertex x y k i) q}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff, Subtype.forall]
    constructor
    · intro h i hi
      obtain ⟨δ, hδ, h1, h2⟩ := h i hi
      exact ⟨δ, ⟨⟨hδ, h1⟩, h2⟩⟩
    · intro h i hi
      obtain ⟨δ, ⟨⟨hδ, h1⟩, h2⟩⟩ := h i hi
      exact ⟨δ, hδ, h1, h2⟩
  rw [hset]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun δ => ?_
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact MeasurableSet.const _
  · exact measurableSet_lt (hD _ _) measurable_const
  · exact MeasurableSet.iInter fun q => measurableSet_le measurable_const (hD _ _)

/-- The localized clearance cost of a fixed chain is measurable in `ω`, when `Q` is countable. -/
theorem measurable_localClearanceCost {S : Set ℂ} {Q : Set ℂ} (hQ : Q.Countable)
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ a b, Measurable fun ω => D ω a b) (x y : ℂ)
    (k : Σ n : ℕ, Fin n → S) :
    Measurable fun ω => localClearanceCost Q (D ω) x y k := by
  unfold localClearanceCost
  refine Measurable.ite (measurableSet_localClearance_condition hQ hD x y k) ?_ measurable_const
  exact Finset.measurable_sum _ fun i _ => (hD _ _).ennreal_ofReal

/-- The localized clearance-chain infimum is measurable in `ω`: a countable infimum of measurable costs. -/
theorem measurable_localClearanceInf {S : Set ℂ} [Countable S] {Q : Set ℂ} (hQ : Q.Countable)
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ a b, Measurable fun ω => D ω a b) (x y : ℂ) :
    Measurable fun ω => localClearanceInf S Q (D ω) x y := by
  unfold localClearanceInf
  exact Measurable.iInf fun k => measurable_localClearanceCost hQ hD x y k

end HarmonicBalls.S11m
