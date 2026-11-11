import HarmonicBalls.FirstPass.S11c.BadEventMeasurable11_7

/-!
# Lemma 11.7: measurability of the local bad set

For an s-finite kernel `K` from a measurable space `X` (the observations of `Σ_D`) to measures on `ℂ` (the decoded local
measures, `LocalLQGDecoderFrozen`), and a deterministic disk-index set `U`, the set of pairs `(z, x)` with `z ∈ U` such
that, for every `k`, some `N ≥ max(k, n_D)` has `∑_{n=N+1}^{2N} 1_{n ≥ n_D} 1_{C_{2M}(K x, 2^{-n}, z)} < aN`, is
measurable in `ℂ × X`. The window sums are finite sums of indicators of measurable sets, and the quantifiers over
`k` and `N` are countable.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

variable {X : Type*} [MeasurableSpace X]

/-- The local window set `T_n ⊆ ℂ × X`: scale index `n ≥ n_D` and the cone-mass event `C_M(K x, 2^{-n}, z)`. -/
def localConeSet (K : Kernel X ℂ) (Q : Set ℂ) (M : ℝ) (nD n : ℕ) : Set (ℂ × X) :=
  {p | nD ≤ n ∧ coneMassEvent (K p.2) Q M ((2 : ℝ)⁻¹ ^ n) p.1}

/-- The local window set is measurable (the cone-mass event is jointly measurable for an s-finite kernel). -/
theorem measurableSet_localConeSet (K : Kernel X ℂ) [IsSFiniteKernel K] {Q : Set ℂ} (hQ : MeasurableSet Q)
    (M : ℝ) (nD n : ℕ) : MeasurableSet (localConeSet K Q M nD n) := by
  have hS : MeasurableSet {q : X × ℂ | coneMassEvent (K q.1) Q M ((2 : ℝ)⁻¹ ^ n) q.2} :=
    measurableSet_coneMassEvent K hQ M ((2 : ℝ)⁻¹ ^ n)
  by_cases hn : nD ≤ n
  · have hEq : localConeSet K Q M nD n =
        (fun p : ℂ × X => (p.2, p.1)) ⁻¹' {q : X × ℂ | coneMassEvent (K q.1) Q M ((2 : ℝ)⁻¹ ^ n) q.2} :=
      Set.ext fun p => Iff.intro (fun h => h.2) (fun h => ⟨hn, h⟩)
    rw [hEq]
    exact hS.preimage (measurable_snd.prodMk measurable_fst)
  · have hEq : localConeSet K Q M nD n = ∅ :=
      Set.ext fun p => Iff.intro (fun h => absurd h.1 hn) (fun h => h.elim)
    rw [hEq]
    exact MeasurableSet.empty

/-- The local bad set: pairs `(z, x)` with `z ∈ U` such that for every `k` there is `N ≥ max(k, n_D)`
with window sum `∑_{n=N+1}^{2N} 1_{localConeSet} (z, x) < a N`. -/
def localBadSet (K : Kernel X ℂ) (Q : Set ℂ) (M a : ℝ) (U : Set ℂ) (nD : ℕ) : Set (ℂ × X) :=
  {p | p.1 ∈ U ∧ ∀ k : ℕ, ∃ N : ℕ, max k nD ≤ N ∧
    ∑ n ∈ Finset.Icc (N + 1) (2 * N), (localConeSet K Q M nD n).indicator (fun _ => (1 : ℝ)) p < a * N}

/-- The local bad set is measurable in `ℂ × X` (countably many quantifiers over measurable window sums). -/
theorem measurableSet_localBadSet (K : Kernel X ℂ) [IsSFiniteKernel K] {Q : Set ℂ} (hQ : MeasurableSet Q)
    (M a : ℝ) {U : Set ℂ} (hU : MeasurableSet U) (nD : ℕ) :
    MeasurableSet (localBadSet K Q M a U nD) := by
  have hsum : ∀ N : ℕ, Measurable (fun p : ℂ × X =>
      ∑ n ∈ Finset.Icc (N + 1) (2 * N), (localConeSet K Q M nD n).indicator (fun _ => (1 : ℝ)) p) :=
    fun N => Finset.measurable_sum _ fun n _ =>
      measurable_const.indicator (measurableSet_localConeSet K hQ M nD n)
  have hEq : localBadSet K Q M a U nD = {p : ℂ × X | p.1 ∈ U} ∩ ⋂ k : ℕ,
      ⋃ N : ℕ, {p : ℂ × X | max k nD ≤ N ∧
        ∑ n ∈ Finset.Icc (N + 1) (2 * N), (localConeSet K Q M nD n).indicator (fun _ => (1 : ℝ)) p < a * N} := by
    ext p
    simp [localBadSet]
  rw [hEq]
  refine (hU.preimage measurable_fst).inter (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N => ?_)
  exact (MeasurableSet.const _).inter (measurableSet_lt (hsum N) measurable_const)

end HarmonicBalls.S11c
