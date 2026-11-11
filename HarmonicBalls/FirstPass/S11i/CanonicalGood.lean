import HarmonicBalls.FirstPass.S11n

/-!
# Canonical good set by kernel integration (Lemma 11.13, sections 5-6, eqs. (33)-(35))

Let `κ` be the measure decoder of the canonical field space (a kernel `CanonSpace → Measure ℂ` with `IsSFiniteKernel`) and `d` the metric
decoder. Put `F = {(L, z) | the eventual frequency bound fails at the root z}` (eq. (33)).

* If every pinch event `{(L, z) | pinchPointEvent (κ L) (d L) ... 2^{-n} z}` is measurable (open item, sec. 5.1),
  then `F` is measurable: each count is a finite sum of indicators and the eventual quantifier is countable.
* `G = {L | κ L (F_L) = 0}` (`F_L` the section of `F` at `L`) is measurable by `measurable_kernel_prodMk_left`
  (kernel integration, eq. (34)); for `L ∈ G` the bound holds for `κ L`-almost every root.

Hence `CanonicalPinchConullStmt` holds once the probabilistic clause `P_{α₀}(G) = 1` is supplied (eq. (35); the
Campbell/Step 12 argument, a named hypothesis `hP` here). Nothing in this file proves `hP` or the measurability of the
pinch events.
-/

namespace HarmonicBalls.CanonicalGood

open MeasureTheory ProbabilityTheory Filter Set
open HarmonicBalls.S11n

universe u

/-- The pinch events at scale `2⁻ⁿ`, as a set of pairs (canonical decoded data, root) (eq. (27) without the cutoff). -/
def pinchSet (κ : Kernel CanonSpace ℂ) (d : CanonSpace → ℂ → ℂ → ℝ) (M : ℝ) (U T Q' Q : Set ℂ) (n : ℕ) :
    Set (CanonSpace × ℂ) :=
  {p | pinchPointEvent (κ p.1) (d p.1) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) p.2}

/-- The frequency bound of `CanonicalPinchConullStmt` at a pair `p = (L, z)`: eventually `δ N` of the scales
`n ∈ [N+1, 2N]` have a pinch event at `z`. -/
def FrequencyBound (κ : Kernel CanonSpace ℂ) (d : CanonSpace → ℂ → ℂ → ℝ) (M δ : ℝ) (U T Q' Q : Set ℂ)
    (p : CanonSpace × ℂ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (κ p.1) (d p.1) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) p.2}.ncard :
      ℝ)

/-- The bad set `F` of eq. (33): the pairs at which the frequency bound fails. -/
def badSet (κ : Kernel CanonSpace ℂ) (d : CanonSpace → ℂ → ℂ → ℝ) (M δ : ℝ) (U T Q' Q : Set ℂ) :
    Set (CanonSpace × ℂ) :=
  {p | ¬ FrequencyBound κ d M δ U T Q' Q p}

/-- The canonical good set of eq. (34): the decoded measures `κ L` give the frequency bound for `κ L`-a.e. root. -/
def goodSet (κ : Kernel CanonSpace ℂ) (d : CanonSpace → ℂ → ℂ → ℝ) (M δ : ℝ) (U T Q' Q : Set ℂ) :
    Set CanonSpace :=
  {L | κ L (Prod.mk L ⁻¹' badSet κ d M δ U T Q' Q) = 0}

lemma ncard_eq_sum_indicator {X : Type*} (P : ℕ → Set X) (N : ℕ) (x : X) :
    ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n}).ncard : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc (N + 1) (2 * N), (P n).indicator (fun _ => (1 : ℝ)) x := by
  classical
  have h : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n} =
      ↑((Finset.Icc (N + 1) (2 * N)).filter (fun n => x ∈ P n)) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  rw [h, Set.ncard_coe_finset]
  simp [Set.indicator_apply, Finset.sum_boole]

/-- Measurability of the eventual frequency bound: countable operations on finite sums of indicators. -/
lemma measurableSet_frequency {X : Type*} [MeasurableSpace X] (P : ℕ → Set X) (hP : ∀ n, MeasurableSet (P n))
    (δ : ℝ) :
    MeasurableSet {x : X | ∀ᶠ N : ℕ in atTop,
      δ * N ≤ ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n}).ncard : ℕ) : ℝ)} := by
  have hN : ∀ N : ℕ, MeasurableSet {x : X |
      δ * N ≤ ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n}).ncard : ℕ) : ℝ)} := by
    intro N
    have hm : Measurable fun x : X =>
        ∑ n ∈ Finset.Icc (N + 1) (2 * N), (P n).indicator (fun _ => (1 : ℝ)) x :=
      Finset.measurable_sum _ fun n _ => measurable_const.indicator (hP n)
    have hset : {x : X | δ * N ≤ ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n}).ncard : ℕ) : ℝ)} =
        (fun x : X => ∑ n ∈ Finset.Icc (N + 1) (2 * N), (P n).indicator (fun _ => (1 : ℝ)) x) ⁻¹'
          Set.Ici (δ * N) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_Ici, ncard_eq_sum_indicator]
    rw [hset]
    exact hm measurableSet_Ici
  have hset2 : {x : X | ∀ᶠ N : ℕ in atTop,
      δ * N ≤ ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n}).ncard : ℕ) : ℝ)} =
      ⋃ J : ℕ, ⋂ N : ℕ, ⋂ (_ : J ≤ N), {x : X |
        δ * N ≤ ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ x ∈ P n}).ncard : ℕ) : ℝ)} := by
    ext x
    simp only [Filter.eventually_atTop, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [hset2]
  exact MeasurableSet.iUnion fun J => MeasurableSet.iInter fun N =>
    MeasurableSet.iInter fun _ => hN N

lemma measurableSet_badSet (κ : Kernel CanonSpace ℂ) (d : CanonSpace → ℂ → ℂ → ℝ) (M δ : ℝ)
    (U T Q' Q : Set ℂ) (hpin : ∀ n : ℕ, MeasurableSet (pinchSet κ d M U T Q' Q n)) :
    MeasurableSet (badSet κ d M δ U T Q' Q) :=
  (measurableSet_frequency (pinchSet κ d M U T Q' Q) hpin δ).compl

lemma measurableSet_goodSet (κ : Kernel CanonSpace ℂ) [IsSFiniteKernel κ] (d : CanonSpace → ℂ → ℂ → ℝ)
    (M δ : ℝ) (U T Q' Q : Set ℂ) (hpin : ∀ n : ℕ, MeasurableSet (pinchSet κ d M U T Q' Q n)) :
    MeasurableSet (goodSet κ d M δ U T Q' Q) :=
  (Kernel.measurable_kernel_prodMk_left (κ := κ) (measurableSet_badSet κ d M δ U T Q' Q hpin))
    (measurableSet_singleton 0)

/-- Kernel integration (eq. (34)): for `L` in the good set, the frequency bound holds for `κ L`-almost every root. -/
lemma ae_frequencyBound_of_mem_goodSet (κ : Kernel CanonSpace ℂ) (d : CanonSpace → ℂ → ℂ → ℝ) (M δ : ℝ)
    (U T Q' Q : Set ℂ) {L : CanonSpace} (hL : L ∈ goodSet κ d M δ U T Q' Q) :
    ∀ᵐ z ∂(κ L), FrequencyBound κ d M δ U T Q' Q (L, z) := by
  rw [ae_iff]
  exact hL

/-- Assembly (eqs. (33)-(35)): if the pinch events are measurable in `(L, z)` and the decoded measure is a kernel,
and if the probabilistic clause `hP` (`P_{α₀}(G) = 1`, eq. (35)) holds for the good set, then the good set witnesses
`CanonicalPinchConullStmt` for the decoders `(κ, d)`. -/
theorem canonicalPinchConull_of_kernel {α₀ M δ : ℝ} {U T Q' Q : Set ℂ} (κ : Kernel CanonSpace ℂ)
    [IsSFiniteKernel κ] (d : CanonSpace → ℂ → ℂ → ℝ)
    (hpin : ∀ n : ℕ, MeasurableSet (pinchSet κ d M U T Q' Q n))
    (hP : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ goodSet κ d M δ U T Q' Q) :
    CanonicalPinchConullStmt.{u} α₀ M δ U T Q' Q (fun L => κ L) d :=
  ⟨goodSet κ d M δ U T Q' Q, measurableSet_goodSet κ d M δ U T Q' Q hpin, hP,
    fun _ hL => ae_frequencyBound_of_mem_goodSet κ d M δ U T Q' Q hL⟩

end HarmonicBalls.CanonicalGood
