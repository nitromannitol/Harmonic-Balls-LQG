import HarmonicBalls.FirstPass.S11i.CertCanonMeasurable
import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift
import HarmonicBalls.FirstPass.Frozen.S11n

/-!
# Canonical window failure set is measurable (Blocker 2 of Step 8)

The failure indicator of the Step 8 frequency statement is taken
from the measurable canonical decoders (frozen strengthening `LQGCanonicalDecodersExistStmt`, `FirstPass/Frozen/S11n.lean`:
kernel `K` measurable and s-finite, metric `d` Borel, conull set `G` on which `d` is a Euclidean length metric), not from the
arbitrary physical `μ(h)`, `D(h)`. This file proves only the measurability part: for a measurable map `f` from a measurable
space `Ω` to the canonical space, the canonical window events and the event that the canonical window frequency does not
converge to `q` are measurable subsets of `Ω × ℂ`. No new input.
-/

namespace HarmonicBalls.FirstPassS11iCanonFailure

open FirstPassS11i
open MeasureTheory Set Filter Topology Metric ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Canonical window event at level `n` (radius `2⁻ⁿ`): the certificate event of the canonical measure `K (f p.1)` and the
canonical metric `d (f p.1)`, restricted to the conull canonical set `G`. -/
def canonWindowSet (f : Ω → S11n.CanonSpace) (K : Kernel S11n.CanonSpace ℂ)
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (G : Set S11n.CanonSpace)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (n : ℕ) : Set (Ω × ℂ) :=
  {p | f p.1 ∈ G ∧ CertificateEvent (K (f p.1)) (fun x y => d (f p.1) (x, y)) Ostar U V W T Q' Q η M
    ((2 : ℝ)⁻¹ ^ n) p.2}

/-- Canonical window frequency: `N⁻¹` times the number of `n` in `[N+1, 2N]` whose canonical window event holds. -/
noncomputable def canonWindowFreq (f : Ω → S11n.CanonSpace) (K : Kernel S11n.CanonSpace ℂ)
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (G : Set S11n.CanonSpace)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (N : ℕ) (p : Ω × ℂ) : ℝ :=
  (∑ n ∈ Finset.Icc (N + 1) (2 * N),
    (canonWindowSet f K d G Ostar U V W T Q' Q η M n).indicator (fun _ => (1 : ℝ)) p) / (N : ℝ)

/-- Each canonical window event is measurable (from `measurableSet_certificateEvent_on`, with the kernel `K` pulled back
along `f`). -/
theorem measurableSet_canonWindowSet (f : Ω → S11n.CanonSpace) (hf : Measurable f)
    (K : Kernel S11n.CanonSpace ℂ) [IsSFiniteKernel K]
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d)
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G)
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (fun x y => d L (x, y)))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) (n : ℕ) :
    MeasurableSet (canonWindowSet f K d G Ostar U V W T Q' Q η M n) := by
  unfold canonWindowSet
  exact measurableSet_certificateEvent_on (K.comap f hf) (d := fun ω => d (f ω)) (hd.comp hf) (hf hG)
    (fun ω hω => hmet (f ω) hω) hOstar h0 hsph hU hη (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n)

/-- A sequence of real-valued measurable functions: the set where it does not converge to `q` is measurable. -/
theorem measurableSet_not_tendsto_real {α : Type*} [MeasurableSpace α] (g : ℕ → α → ℝ)
    (hg : ∀ N, Measurable (g N)) (q : ℝ) :
    MeasurableSet {x | ¬ Tendsto (fun N => g N x) atTop (𝓝 q)} := by
  have hset : {x | Tendsto (fun N => g N x) atTop (𝓝 q)} =
      ⋂ m : ℕ, ⋃ N₀ : ℕ, ⋂ N : ℕ, {x | N₀ ≤ N → |g N x - q| ≤ 1 / ((m : ℝ) + 1)} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro hx m
      obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hx (1 / ((m : ℝ) + 1)) (by positivity)
      refine ⟨N₀, fun N hN => ?_⟩
      have h := hN₀ N hN
      rw [Real.dist_eq] at h
      exact h.le
    · intro hx
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨N₀, hN₀⟩ := hx m
      refine ⟨N₀, fun N hN => ?_⟩
      show dist (g N x) q < ε
      rw [Real.dist_eq]
      have h := hN₀ N hN
      linarith
  have hmeas : ∀ (N₀ N : ℕ) (c : ℝ), MeasurableSet {x | N₀ ≤ N → |g N x - q| ≤ c} := by
    intro N₀ N c
    by_cases h : N₀ ≤ N
    · simp only [h, true_implies]
      exact measurableSet_le (continuous_abs.measurable.comp ((hg N).sub_const q)) measurable_const
    · simp [h]
  show MeasurableSet ({x | Tendsto (fun N => g N x) atTop (𝓝 q)})ᶜ
  rw [hset]
  exact (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun N₀ => MeasurableSet.iInter fun N =>
    hmeas N₀ N _).compl

/-- **Measurability of the canonical failure event (Blocker 2 of Step 8).** The set of `(ω, z)` at which the
canonical window frequency of certificate events does not converge to `q` is measurable in `Ω × ℂ` (product of the given
σ-algebra on `Ω` with the Borel σ-algebra on `ℂ`). -/
theorem measurableSet_canonFailure (f : Ω → S11n.CanonSpace) (hf : Measurable f)
    (K : Kernel S11n.CanonSpace ℂ) [IsSFiniteKernel K]
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d)
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G)
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (fun x y => d L (x, y)))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) (q : ℝ) :
    MeasurableSet {p : Ω × ℂ | ¬ Tendsto
      (fun N : ℕ => canonWindowFreq f K d G Ostar U V W T Q' Q η M N p) atTop (𝓝 q)} := by
  refine measurableSet_not_tendsto_real (fun N p => canonWindowFreq f K d G Ostar U V W T Q' Q η M N p)
    (fun N => ?_) q
  unfold canonWindowFreq
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ (fun n _ => ?_)
  exact measurable_const.indicator
    (measurableSet_canonWindowSet f hf K d hd hG hmet hOstar h0 hsph hU hη n)

end HarmonicBalls.FirstPassS11iCanonFailure

