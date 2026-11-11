import Mathlib.Topology.TietzeExtension
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Steps.SecA.Basic

/-! # Closed-carrier representatives of general-domain competitors

The Laplacian locality lemma used here builds on the potential-theoretic
infrastructure of Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Set

/-- Competitor membership depends only on values on the closed carrier. -/
theorem mem_supersolutionsOn_of_eqOn {μ : Measure ℂ} {U : Set ℂ} {z : ℂ} {t : ℝ}
    (hU : MeasurableSet U) {w v : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t)
    (heq : EqOn w v (closure U)) : v ∈ supersolutionsOn μ U z t := by
  refine ⟨hw.1.congr heq.symm, hw.2.1.congr_eqOn hU (heq.mono subset_closure), ?_⟩
  intro x hx hxz
  rw [← heq hx]
  exact hw.2.2 x hx hxz

/-- Every competitor has a globally continuous competitor representative agreeing
on the closed carrier. -/
theorem exists_continuous_supersolutionOn_eqOn {μ : Measure ℂ} {U : Set ℂ}
    {z : ℂ} {t : ℝ} (hU : IsOpen U) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ U z t) :
    ∃ v : ℂ → ℝ, Continuous v ∧ v ∈ supersolutionsOn μ U z t ∧
      EqOn w v (closure U) := by
  let f : C(closure U, ℝ) := ⟨fun x => w x, hw.1.domRestrict⟩
  obtain ⟨g, hg⟩ := f.exists_restrict_eq isClosed_closure
  have heq : EqOn w g (closure U) := by
    intro x hx
    have h := congrArg (fun k : C(closure U, ℝ) => k ⟨x, hx⟩) hg
    exact h.symm
  exact ⟨g, g.continuous, mem_supersolutionsOn_of_eqOn hU.measurableSet hw heq, heq⟩

/-- Globally continuous competitors have exactly the same evaluation values on
the closed carrier as all competitors. -/
theorem supersolutionsOn_continuous_image_eq {μ : Measure ℂ} {U : Set ℂ}
    {z : ℂ} {t : ℝ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ closure U) :
    (fun w : ℂ → ℝ => w x) '' {w ∈ supersolutionsOn μ U z t | Continuous w} =
      (fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t := by
  apply Subset.antisymm
  · rintro y ⟨w, ⟨hw, _⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨v, hvc, hv, heq⟩ := exists_continuous_supersolutionOn_eqOn hU hw
    exact ⟨v, ⟨hv, hvc⟩, (heq hx).symm⟩

/-- Restriction to globally continuous competitors preserves the real infimum
at every point of the closed carrier, including the pole. -/
theorem leastSupersolutionOn_eq_sInf_continuous {μ : Measure ℂ} {U : Set ℂ}
    {z : ℂ} {t : ℝ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ closure U) :
    leastSupersolutionOn μ U z t x =
      sInf ((fun w : ℂ → ℝ => w x) '' {w ∈ supersolutionsOn μ U z t | Continuous w}) := by
  rw [supersolutionsOn_continuous_image_eq hU hx]
  rfl


end HarmonicBalls
