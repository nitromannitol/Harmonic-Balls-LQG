import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementUnrootedDet
import HarmonicBalls.FirstPass.Phase2.InternalMetricFineChains
import LatticeProb.Topology.ChainsThroughDenseSet

/-!
# Deterministic membership of the unrooted distance function in the local-agreement event (step 5)

Let `F` be a Euclidean length metric, `D` an open path-connected set, `S ⊆ D` a dense subset, `K n` an exhaustion of
`D` by sets containing every compact subset of `D` from some index on, and `c ∈ [0, ∞)`. If the observation `o` is such
that `d o = c · internalMetric F D` on `S × S` and the local functions `Fam i o` are `c · internalMetric F (V i)` on the
points of `S` in the open sets `V i ⊆ D`, then `o` lies in the event `A = A1 ∩ A2 ∩ A3` of
`Phase2/RootedLocalAgreementEvent.lean`:

* `mem_eventMetricAxioms_of_internalMetric`: A1 from `internalMetric_axioms`;
* `mem_eventChains_of_internalMetric`: A2 from the fine chains of the internal metric
  (`internalMetric_fineChains`) moved into the dense set `S` (`exists_chain_through_dense`: the distance function
  `c · internalMetric F D` is continuous on `D × D`, `IsEuclideanLengthMetric.continuousOn_internalMetric_pair`);
* `mem_eventA_of_internalMetric`: A1, A2 and A3 (`mem_eventLocalAgreement_of_internalMetric`).

Terminology: internal metric `D(·,·;U)` (Armstrong-Kuusi-Mourrat); Euclidean length metric (Gwynne-Miller).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnrootedLocal

/-- **A1 for the unrooted distance function on `S`.** -/
theorem mem_eventMetricAxioms_of_internalMetric {Ω : Type*} {S D : Set ℂ} (hSD : S ⊆ D)
    {d : Ω → ℂ → ℂ → ℝ≥0∞} {o : Ω} {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) (hD : IsOpen D) {c : ℝ≥0∞}
    (hd : ∀ u ∈ S, ∀ v ∈ S, d o u v = c * internalMetric F D u v) : o ∈ eventMetricAxioms S d := by
  obtain ⟨h1, h2, h3⟩ := internalMetric_axioms hF hD c
  refine ⟨⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun x hx y hy w hw => ?_⟩
  · rw [hd x hx x hx, h1 x (hSD hx)]
  · rw [hd x hx y hy, hd y hy x hx, h2]
  · rw [hd x hx w hw, hd x hx y hy, hd y hy w hw]
    exact h3 x y w

/-- **A2 for the unrooted distance function on `S`.** -/
theorem mem_eventChains_of_internalMetric {Ω : Type*} {S D : Set ℂ} {K : ℕ → Set ℂ} {d : Ω → ℂ → ℂ → ℝ≥0∞}
    {o : Ω} {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) (hD : IsOpen D) (hDpc : IsPathConnected D)
    (hSD : S ⊆ D) (hdense : D ⊆ closure S) (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ D → ∃ n, C ⊆ K n)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hd : ∀ u ∈ S, ∀ v ∈ S, d o u v = c * internalMetric F D u v) :
    o ∈ eventChains S K d := by
  have hnn := nonneg_of_isEuclideanLengthMetric hF
  have hcont : ContinuousOn (fun q : ℂ × ℂ => c * internalMetric F D q.1 q.2) (D ×ˢ D) :=
    (ENNReal.continuous_const_mul hc).comp_continuousOn (hF.continuousOn_internalMetric_pair hnn hD)
  apply mem_eventChains_of_natChains
  intro x hx y hy ε hε
  have hch : LatticeProb.Topology.HasFineChainsAt D (fun u v => c * internalMetric F D u v) x y :=
    internalMetric_fineChains F hDpc hc x (hSD hx) y (hSD hy)
  obtain ⟨n, hn⟩ := LatticeProb.Topology.exists_chain_through_dense hD hSD hdense hcont hK hx hy hch hε
  refine ⟨n, fun δ hδ => ?_⟩
  obtain ⟨N, m, h0, hN, hm, hmδ, hsum⟩ := hn δ hδ
  refine ⟨N, m, h0, hN, hm, hmδ, ?_⟩
  rw [hd x hx y hy]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i hi => ?_) hsum
  have hi' := Finset.mem_range.1 hi
  exact hd _ (hm i hi'.le).1 _ (hm (i + 1) hi').1

/-- **Membership in the event `A = A1 ∩ A2 ∩ A3`.** -/
theorem mem_eventA_of_internalMetric {Ω : Type*} {ι κ : Type*} {S D : Set ℂ} {K : ℕ → Set ℂ}
    {adm : ι → κ → Prop} {T : ι → κ → Set ℂ} {d : Ω → ℂ → ℂ → ℝ≥0∞} {Fam : ι → Ω → ℂ → ℂ → ℝ≥0∞} {o : Ω}
    {F : ℂ → ℂ → ℝ} (hF : IsEuclideanLengthMetric F) (hD : IsOpen D) (hDpc : IsPathConnected D)
    (hSD : S ⊆ D) (hdense : D ⊆ closure S) (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ D → ∃ n, C ⊆ K n)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (hVD : ∀ i, V i ⊆ D)
    (hT : ∀ i k, adm i k → IsCompact (T i k) ∧ T i k ⊆ V i) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hd : ∀ u ∈ S, ∀ v ∈ S, d o u v = c * internalMetric F D u v)
    (hFam : ∀ i, ∀ u ∈ S, u ∈ V i → ∀ v ∈ S, v ∈ V i → Fam i o u v = c * internalMetric F (V i) u v) :
    o ∈ eventA S K adm T d Fam :=
  ⟨⟨mem_eventMetricAxioms_of_internalMetric hSD hF hD hd,
    mem_eventChains_of_internalMetric hF hD hDpc hSD hdense hK hc hd⟩,
    mem_eventLocalAgreement_of_internalMetric hF hD V hV hVD hT hd hFam⟩

end UnrootedLocal

end HarmonicBalls
