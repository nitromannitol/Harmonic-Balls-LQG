import HarmonicBalls.Proofs.Sec6.ScaledDenseCentreFullSupport
import HarmonicBalls.Proofs.Sec6.RootedMassTypicalEventTransfer
import HarmonicBalls.Proofs.Sec6.GoodAnnulusJointMeasurability

/-! # Rooted local good-annulus count tail

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A root sampled from the field's mass inside a smallest-scale ball obeys
 the count tail at relaxed good-annulus thresholds. -/
theorem exists_rooted_local_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ (x : ℂ) (s ε : ℝ), 0 < s → 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | p.2 ∈ ball x (s * ε / 100) ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  let := h.isProbabilityMeasure
  obtain ⟨a, ha, C, hCpos, htail⟩ :=
    exists_scaled_dense_goodAnnuli_count_tail hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a / 2, ⟨by linarith [ha.1], by linarith [ha.2]⟩, C, hCpos, ?_⟩
  intro κ _ hκ hac x s ε hs hε hlog
  obtain ⟨m, hm, hmfin, heq⟩ := exists_measurable_locallyFinite_rep
    (h.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ hω => hω.isLocallyFiniteMeasure)
  let q : ℕ → ℝ := fun n => (7 : ℝ)⁻¹ ^ n
  have hqi : Function.Injective q := by
    intro j k hjk
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1) hjk
  let T : Set ℝ := {r | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧ ∃ n : ℕ, r = q n}
  let S : Set ℕ := {n | q n ∈ Icc ε (ε ^ (3 / 4 : ℝ))}
  have hT : T.Finite := by
    apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε
    intro r hr
    obtain ⟨n, hn⟩ := hr.2
    exact ⟨hr.1.1, n, by simpa only [one_mul, q] using hn⟩
  let count : Ω × ℂ → ℝ := fun p =>
    ({n : ℕ | n ∈ S ∧ IsGoodAnnulus (m p.1) (s * q n) p.2 (a / 2) (b + 1)}.ncard : ℝ)
  have hcount : Measurable count := by
    apply measurable_goodAnnulus_count_joint (hm.comp measurable_fst) (fun p => hmfin p.1)
      (fun _ p => p.2) (fun n _ => s * q n)
      (fun _ => measurable_snd) (fun _ => measurable_const)
      (fun n _ => mul_pos hs (by dsimp [q]; positivity)) S (by linarith [ha.1]) (b + 1)
  have hcounteq (ω : Ω) (z : ℂ) : count (ω,z) =
      ({r ∈ T | IsGoodAnnulus (m ω) (s * r) z (a / 2) (b + 1)}.ncard : ℝ) := by
    have he : {r ∈ T | IsGoodAnnulus (m ω) (s * r) z (a / 2) (b + 1)} =
        q '' {n : ℕ | n ∈ S ∧ IsGoodAnnulus (m ω) (s * q n) z (a / 2) (b + 1)} := by
      ext r
      constructor
      · rintro ⟨⟨hr, ⟨n, rfl⟩⟩, hg⟩
        exact ⟨n, ⟨hr, hg⟩, rfl⟩
      · rintro ⟨n, ⟨hr, hg⟩, rfl⟩
        exact ⟨⟨hr, ⟨n, rfl⟩⟩, hg⟩
    dsimp only [count]
    rw [he, Set.ncard_image_of_injective _ hqi]
  let c : ℝ := (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))
  let E : Set (Ω × ℂ) := {p | p.2 ∈ ball x (s * ε / 100) ∧ count p < c}
  let F : Set Ω := {ω | ({r ∈ T | ∀ i, IsGoodAnnulus (m ω) (s * r)
      (x + (s * r) • nearbyDenseCentre i) a b}.ncard : ℝ) < c}
  have hE : MeasurableSet E := (measurableSet_ball.preimage measurable_snd).inter
    (measurableSet_lt hcount measurable_const)
  have hF : MeasurableSet F := by
    apply measurableSet_lt ?_ measurable_const
    simpa [T, q, and_assoc, Function.comp_def] using (measurable_nearby_goodAnnulus_count x
      (fun _ => nearbyDenseCentre) hs ε ha.1 b).comp hm
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have himp : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), (ω,z) ∈ E → ω ∈ F := by
    filter_upwards [heq, ae_lqg_ae_scaled_nearby_count_le_root_count_of_smallest_ball
      hgrowth hγ hγ2 hQ h hμ] with ω hω hcomp
    filter_upwards [hcomp] with z hz hEz
    have hle := hz T hT x s ε hs hε (fun r hr => hr.1.1) hEz.1
      (a := a) (a' := a / 2) (b := b) (b' := b + 1) (by linarith [ha.1]) (by linarith [ha.1]) hb.le (by linarith)
    rw [hω] at hle
    have hle' : (({r ∈ T | ∀ i, IsGoodAnnulus (m ω) (s * r)
        (x + (s * r) • nearbyDenseCentre i) a b}.ncard : ℕ) : ℝ) ≤
        ({r ∈ T | IsGoodAnnulus (m ω) (s * r) z (a / 2) (b + 1)}.ncard : ℝ) := by exact_mod_cast hle
    exact hle'.trans_lt (by simpa only [← hcounteq] using hEz.2)
  have hbound := compProd_measure_le_of_ae_mass_event_implication P μ κ hκ hac hE hF himp
  have hF_eq : F =ᵐ[P] {ω | ({r ∈ T | ∀ i, IsGoodAnnulus (μ ω) (s * r)
      (x + (s * r) • nearbyDenseCentre i) a b}.ncard : ℝ) < c} := by
    filter_upwards [heq] with ω hω
    simp only [F, mem_ofPred_eq, ← hω]
  have hFbound : P F ≤ ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
    rw [measure_congr hF_eq]
    simpa [T, q, c, and_assoc] using htail x s hs ε hε hlog
  have heqroot := (quasiMeasurePreserving_fst_compProd P κ).ae_eq_comp heq
  have hE_eq : E =ᵐ[P ⊗ₘ κ] {p | p.2 ∈ ball x (s * ε / 100) ∧
      ({r ∈ T | IsGoodAnnulus (μ p.1) (s * r) p.2 (a / 2) (b + 1)}.ncard : ℝ) < c} := by
    filter_upwards [heqroot] with p hp
    simp only [Function.comp_apply] at hp
    simp only [E, mem_ofPred_eq, hcounteq, ← hp]
  rw [measure_congr hE_eq] at hbound
  simpa [T, q, c, and_assoc] using hbound.trans hFbound

end HarmonicBalls.Section6
