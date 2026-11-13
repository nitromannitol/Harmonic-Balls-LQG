import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep2

/-!
# Restriction of mean-zero observations from a disk `D` to a subdomain `V ⊆ D` (step 3 of the local-agreement route for `hN2`)

The observations of the local-agreement argument live on a disk `D = ball c r` and are functions on the mean-zero test
functions supported in `D`. For a subdomain `V ⊆ D` every mean-zero test function supported in `V` is one supported in `D`,
so an observation on `D` restricts to one on `V` (precomposition with the inclusion of test functions).

* `obsRestrict h`: the restriction `Obs D → Obs V`, measurable for the product σ-algebras.
* `obsRestrict_localMeanZeroObs`, `obsRestrict_campbellReferenceObs`: restriction commutes (definitionally) with
  the observation of the field `h = h^ℂ - α log|·|`, and with the reference observation `g - γ log|· - z| + b`.
* `meanZeroTestOfSub`: for unit-mass bumps `ρ` on `D` and `ρ_V` on `V`, the difference `ρ - ρ_V` is a mean-zero test
  function on `D` (the test function whose pairing with the observation on `D` recovers the difference of the
  pairings `⟨h, ρ⟩ - ⟨h, ρ_V⟩`).
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ContDiff

/-- The mean-zero test functions supported in `U`: the index set of the local mean-zero observations on `U`. -/
abbrev MeanZeroTest (U : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0}

/-- A mean-zero test function supported in `V ⊆ D` is one supported in `D`. -/
def meanZeroTestIncl {V D : Set ℂ} (h : V ⊆ D) (φ : MeanZeroTest V) : MeanZeroTest D :=
  ⟨φ.1, ⟨φ.2.1.1, φ.2.1.2.1, subset_trans φ.2.1.2.2 h⟩, φ.2.2⟩

@[simp] theorem meanZeroTestIncl_val {V D : Set ℂ} (h : V ⊆ D) (φ : MeanZeroTest V) :
    (meanZeroTestIncl h φ).1 = φ.1 := rfl

/-- Restriction of a local mean-zero observation from `D` to `V ⊆ D`: precomposition with the inclusion of
mean-zero test functions. -/
def obsRestrict {V D : Set ℂ} (h : V ⊆ D) (o : MeanZeroTest D → ℝ) : MeanZeroTest V → ℝ :=
  fun φ => o (meanZeroTestIncl h φ)

theorem obsRestrict_apply {V D : Set ℂ} (h : V ⊆ D) (o : MeanZeroTest D → ℝ) (φ : MeanZeroTest V) :
    obsRestrict h o φ = o (meanZeroTestIncl h φ) := rfl

/-- The restriction of observations is measurable for the product σ-algebras. -/
theorem measurable_obsRestrict {V D : Set ℂ} (h : V ⊆ D) :
    Measurable (obsRestrict h) :=
  Measurable.of_eval fun φ => measurable_pi_apply (meanZeroTestIncl h φ)

/-- The restriction of the marked observation `(z, o)` to `(z, o|_V)`. -/
def markObsRestrict {V D : Set ℂ} (h : V ⊆ D) (p : ℂ × (MeanZeroTest D → ℝ)) :
    ℂ × (MeanZeroTest V → ℝ) :=
  (p.1, obsRestrict h p.2)

theorem measurable_markObsRestrict {V D : Set ℂ} (h : V ⊆ D) :
    Measurable (markObsRestrict h) :=
  measurable_fst.prodMk ((measurable_obsRestrict h).comp measurable_snd)

/-- Restriction of the local mean-zero observation of the field to `D` is its observation on `V`. -/
theorem obsRestrict_localMeanZeroObs {V D : Set ℂ} (h : V ⊆ D) (α : ℝ) (T : (ℂ → ℝ) → ℝ) :
    obsRestrict h (localMeanZeroObs α D T) = localMeanZeroObs α V T := rfl

/-- Restriction of the reference observation at the root `z` to `V`. -/
theorem obsRestrict_campbellReferenceObs {V D : Set ℂ} (h : V ⊆ D) (γ α : ℝ) (T : (ℂ → ℝ) → ℝ)
    (z : ℂ) :
    obsRestrict h (campbellReferenceObs γ α D T z).2 = (campbellReferenceObs γ α V T z).2 := rfl

theorem markObsRestrict_campbellReferenceObs {V D : Set ℂ} (h : V ⊆ D) (γ α : ℝ) (T : (ℂ → ℝ) → ℝ)
    (z : ℂ) :
    markObsRestrict h (campbellReferenceObs γ α D T z) = campbellReferenceObs γ α V T z := rfl

theorem markObsRestrict_campbellMarkedObs {V D : Set ℂ} (h : V ⊆ D) (α : ℝ) (T : (ℂ → ℝ) → ℝ)
    (z : ℂ) :
    markObsRestrict h (campbellMarkedObs α D T z) = campbellMarkedObs α V T z := rfl

/-- Restriction is compatible with composition of inclusions. -/
theorem obsRestrict_trans {W V D : Set ℂ} (h₁ : W ⊆ V) (h₂ : V ⊆ D) (o : MeanZeroTest D → ℝ) :
    obsRestrict h₁ (obsRestrict h₂ o) = obsRestrict (h₁.trans h₂) o := rfl

theorem obsRestrict_self {D : Set ℂ} (o : MeanZeroTest D → ℝ) : obsRestrict (subset_refl D) o = o := rfl

/-- Test functions are closed under differences. -/
theorem IsTestFunction.sub {U : Set ℂ} {f g : ℂ → ℝ} (hf : IsTestFunction U f) (hg : IsTestFunction U g) :
    IsTestFunction U (fun x => f x - g x) := by
  have hts : tsupport (fun x => f x - g x) ⊆ tsupport f ∪ tsupport g := by
    refine closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport g))
    intro x hx
    by_contra hxn
    simp only [mem_union, not_or] at hxn
    have hf0 : f x = 0 := by
      by_contra h
      exact hxn.1 (subset_closure h)
    have hg0 : g x = 0 := by
      by_contra h
      exact hxn.2 (subset_closure h)
    exact hx (by simp [hf0, hg0])
  exact ⟨hf.1.sub hg.1, IsCompact.of_isClosed_subset (hf.2.1.union hg.2.1) (isClosed_tsupport _) hts,
    hts.trans (union_subset hf.2.2 hg.2.2)⟩

/-- For unit-mass test functions `ρ` on `D` and `ρ_V` on `V ⊆ D`, the difference `ρ - ρ_V` is a mean-zero test
function on `D`. -/
def meanZeroTestOfSub {V D : Set ℂ} (hVD : V ⊆ D) {ρ ρV : ℂ → ℝ} (hρ : IsTestFunction D ρ)
    (hρV : IsTestFunction V ρV) (h1 : ∫ x, ρ x = 1) (h1V : ∫ x, ρV x = 1) : MeanZeroTest D :=
  ⟨fun x => ρ x - ρV x, hρ.sub (hρV.mono_set hVD), by
    rw [integral_sub (hρ.1.continuous.integrable_of_hasCompactSupport hρ.2.1)
      (hρV.1.continuous.integrable_of_hasCompactSupport hρV.2.1), h1, h1V, sub_self]⟩

@[simp] theorem meanZeroTestOfSub_val {V D : Set ℂ} (hVD : V ⊆ D) {ρ ρV : ℂ → ℝ} (hρ : IsTestFunction D ρ)
    (hρV : IsTestFunction V ρV) (h1 : ∫ x, ρ x = 1) (h1V : ∫ x, ρV x = 1) :
    (meanZeroTestOfSub hVD hρ hρV h1 h1V).1 = fun x => ρ x - ρV x := rfl

end HarmonicBalls
