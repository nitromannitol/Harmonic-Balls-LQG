import HarmonicBalls.Draft.Section9
import HarmonicBalls.Draft.Section2

/-!
# Proposition 5.6: uniqueness from a no-entry step

The proof at lines 2415–2473 uses Lemma 9.3 to keep the boundary of `A_t`
inside the closure of `Λ̂_t`, then argues that a ball disjoint from that
closure cannot enter the increasing family `A`. The latter argument is
isolated below, including the small-time step noted as GRAPH G8. The
remaining reduction uses finite equal mass and Lemma 9.4.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- No-entry step in the proof of Proposition 5.6 (lines 2420–2471): a
ball outside `closure (Λ t)` cannot enter the increasing family `A` when the
boundary of each `A s` lies in `closure (Λ s)`. This includes the small-time
avoidance of the ball, which requires an argument beyond the printed text
(GRAPH G8). -/
def HarmonicBallNoEntryStep : Prop :=
  ∀ (μ : Measure ℂ), μ.IsOpenPosMeasure → ∀ (Λ A : ℝ → Set ℂ) (z : ℂ),
    IsRegularizedClusterFamily μ Λ z → IsHarmonicBallFamily μ A z →
    (∀ s : ℝ, 0 < s → frontier (A s) ⊆ closure (Λ s)) →
    ∀ t : ℝ, 0 < t → ∀ x : ℂ, ∀ r : ℝ, 0 < r →
      ball x r ⊆ (closure (Λ t))ᶜ → Disjoint (ball x r) (A t)

/-- Proposition 5.6 from the no-entry step, Lemmas 9.3–9.4 and full support
of the measure. The latter is a proved consequence of Section 2, not a new
literature input. -/
theorem uniquenessHarmonicBalls_of_steps (hentry : HarmonicBallNoEntryStep)
    (h93 : HarmonicBallBoundarySubsetStmt.{u}) (h94 : RegularOpenEqOfAEEqStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) : UniquenessHarmonicBallsStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λhat hΛhat
  filter_upwards [hΛhat, h93 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hΛhat,
    h94 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hΛ hboundary heq hsupport
  have hpos : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hsupport U hU hne).ne'⟩
  intro z A hA t ht
  have htpos : 0 < t := ht
  have hbound : ∀ s : ℝ, 0 < s → frontier (A s) ⊆ closure (Λhat ω z s) := by
    intro s hs
    obtain ⟨R, hR⟩ := ((hA.2.isBounded s hs).closure).subset_ball (0 : ℂ)
    have hzR : z ∈ ball (0 : ℂ) R := hR (subset_closure (hA.2.mem s hs))
    exact hboundary (A s) z R s hzR hR (hA.1 s hs) hs (hA.2.measure_eq s hs)
  have hsubset_closure : A t ⊆ closure (Λhat ω z t) := by
    intro x hx
    by_contra hxcl
    have hopen : IsOpen (A t \ closure (Λhat ω z t)) :=
      (hA.2.isRegularOpen t htpos).isOpen.sdiff isClosed_closure
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hopen x ⟨hx, hxcl⟩
    have haway : ball x r ⊆ (closure (Λhat ω z t))ᶜ := fun y hy => (hrsub hy).2
    have hdis := hentry (μ ω) hpos (Λhat ω z) A z (hΛ z) hA hbound t htpos x r hr haway
    exact Set.disjoint_left.1 hdis (mem_ball_self hr) hx
  have hsubset : A t ⊆ Λhat ω z t := by
    rw [← (hΛ z).1.isRegularOpen t htpos]
    exact (hA.2.isRegularOpen t htpos).isOpen.subset_interior_iff.2 hsubset_closure
  have hmassA := hA.2.measure_eq t htpos
  have hmassΛ := (hΛ z).1.measure_eq t htpos
  have hae : A t =ᵐ[μ ω] Λhat ω z t :=
    ae_eq_of_subset_of_measure_ge hsubset (by rw [hmassA, hmassΛ])
      (hA.2.isRegularOpen t htpos).isOpen.measurableSet.nullMeasurableSet
      (by rw [hmassΛ]; exact ENNReal.ofReal_ne_top)
  exact heq (A t) (Λhat ω z t) (hA.2.isRegularOpen t htpos).isOpen
    ((hΛ z).1.isRegularOpen t htpos).isOpen (hA.2.isRegularOpen t htpos)
    ((hΛ z).1.isRegularOpen t htpos) (ae_eq_set.1 hae).1 (ae_eq_set.1 hae).2

end HarmonicBalls
