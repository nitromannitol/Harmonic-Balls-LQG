import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Proposition 11.7, measurability of the scale events

* `measurable_lintegral_of_mass`: if `ω ↦ μ ω B` is measurable for every measurable `B`, then `ω ↦ ∫⁻ y, f y ∂(μ ω)` is
  measurable for every measurable `f`.
* `measurable_mass_borel_of_open`: if `ω ↦ μ ω U` is measurable for every open `U` and every `μ ω` is finite on balls,
  then `ω ↦ μ ω B` is measurable for every Borel `B` (Dynkin argument, sliced by balls).

Together with the locality of the LQG measure (paper Fact 2.1 II, line 407: `μ_h(U)` is a measurable function of `h|_U`
for open `U`), these reduce the measurability of the scale events `coneMassEvent` (`HarmonicBalls/Draft/Section11.lean:72`)
of Lemma 11.7 (paper `lemma:mu_h-bad-and-harnack`, corrected paper line 2896) to the open-set case. The annular
supremum `annulusGreenPotentialSup` (`HarmonicBalls/Defs/Annuli.lean:65`) is still open.
-/

open MeasureTheory Set Metric Function
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- If the masses `ω ↦ μ ω B` are measurable for all measurable `B`, the integrals `ω ↦ ∫⁻ f d(μ ω)` of a measurable
`f : α → ℝ≥0∞` are measurable in `ω`. -/
theorem measurable_lintegral_of_mass {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Ω → Measure α) (hμ : ∀ B : Set α, MeasurableSet B → Measurable fun ω => μ ω B)
    {f : α → ℝ≥0∞} (hf : Measurable f) : Measurable fun ω => ∫⁻ y, f y ∂(μ ω) :=
  (Measure.measurable_lintegral hf).comp (Measure.measurable_of_measurable_coe μ hμ)

/-- Open-set measurability and finiteness on balls give measurability of the masses of all Borel sets. -/
theorem measurable_mass_borel_of_open {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    (hfin : ∀ (ω : Ω) (n : ℕ), μ ω (ball (0 : ℂ) (n : ℝ)) ≠ ⊤)
    (hopen : ∀ U : Set ℂ, IsOpen U → Measurable fun ω => μ ω U) :
    ∀ B : Set ℂ, MeasurableSet B → Measurable fun ω => μ ω B := by
  have hborel : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom {t : Set ℂ | IsOpen t} :=
    BorelSpace.measurable_eq
  have slice : ∀ n : ℕ, ∀ B : Set ℂ, MeasurableSet B →
      Measurable fun ω => μ ω (B ∩ ball (0 : ℂ) (n : ℝ)) := by
    intro n B hB
    refine MeasurableSpace.induction_on_inter (s := {t : Set ℂ | IsOpen t}) hborel
      isPiSystem_isOpen ?_ ?_ ?_ ?_ B hB
    · simp only [Set.empty_inter, measure_empty]
      exact measurable_const
    · intro t ht
      exact hopen _ (IsOpen.inter ht isOpen_ball)
    · intro t htm IH
      show Measurable fun ω => μ ω (tᶜ ∩ ball (0 : ℂ) (n : ℝ))
      have key : (fun ω => μ ω (tᶜ ∩ ball (0 : ℂ) (n : ℝ))) =
          fun ω => μ ω (ball (0 : ℂ) (n : ℝ)) - μ ω (t ∩ ball (0 : ℂ) (n : ℝ)) := by
        funext ω
        have h1 := measure_inter_add_sdiff (μ := μ ω) (ball (0 : ℂ) (n : ℝ)) htm
        have e1 : tᶜ ∩ ball (0 : ℂ) (n : ℝ) = ball (0 : ℂ) (n : ℝ) \ t := by
          rw [Set.sdiff_eq, Set.inter_comm]
        have e2 : t ∩ ball (0 : ℂ) (n : ℝ) = ball (0 : ℂ) (n : ℝ) ∩ t := Set.inter_comm _ _
        have hle : μ ω (ball (0 : ℂ) (n : ℝ) ∩ t) ≠ ⊤ :=
          ne_top_of_le_ne_top (hfin ω n) (measure_mono Set.inter_subset_left)
        rw [e1, e2]
        exact ENNReal.eq_sub_of_add_eq hle (by rw [add_comm]; exact h1)
      rw [key]
      exact (hopen _ isOpen_ball).sub IH
    · intro f hd hfm IH
      show Measurable fun ω => μ ω ((⋃ i, f i) ∩ ball (0 : ℂ) (n : ℝ))
      rw [Set.iUnion_inter]
      have hd' : Pairwise (Disjoint on fun i => f i ∩ ball (0 : ℂ) (n : ℝ)) :=
        fun i j hij => (hd hij).mono Set.inter_subset_left Set.inter_subset_left
      have hsum : ∀ ω, μ ω (⋃ i, f i ∩ ball (0 : ℂ) (n : ℝ)) =
          ∑' i, μ ω (f i ∩ ball (0 : ℂ) (n : ℝ)) := fun ω =>
        measure_iUnion hd' (fun i => (hfm i).inter measurableSet_ball)
      simp_rw [hsum]
      exact Measurable.tsum IH
  intro B hB
  have hmono : Monotone fun n : ℕ => B ∩ ball (0 : ℂ) (n : ℝ) := fun a b hab =>
    Set.inter_subset_inter_right _ (ball_subset_ball (by exact_mod_cast hab))
  have hU : (⋃ n : ℕ, B ∩ ball (0 : ℂ) (n : ℝ)) = B := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨_, hz, _⟩
      exact hz
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact ⟨n, hz, mem_ball_zero_iff.mpr hn⟩
  have hsup : ∀ ω, μ ω B = ⨆ n : ℕ, μ ω (B ∩ ball (0 : ℂ) (n : ℝ)) := fun ω => by
    have h := hmono.measure_iUnion (μ := μ ω)
    rw [hU] at h
    exact h
  have hfun : (fun ω => μ ω B) = fun ω => ⨆ n : ℕ, μ ω (B ∩ ball (0 : ℂ) (n : ℝ)) := funext hsup
  rw [hfun]
  exact Measurable.iSup (fun n => slice n B hB)

end HarmonicBalls.S11c
