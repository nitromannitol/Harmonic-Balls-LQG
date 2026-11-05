import HarmonicBalls.Proofs.Sec5.CompactGeneralDomainCompatibility
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift

/-! # An obstacle on a Green-regular domain

The enclosing-disc potential gives a continuous Laplacian shift on a bounded
open subdomain. The Green difference supplies continuity of the shifted
obstacle away from the pole. This uses the potential-theoretic infrastructure
of Leonardo Bonanno and the existing general-domain Green comparison.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- An enclosing-disc Green potential is a continuous distributional shift on
any open subdomain. It need not vanish on the subdomain boundary. -/
theorem enclosingDisc_potential_shift_on_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hsub : U ⊆ ball (0 : ℂ) R) :
    ContinuousOn (greenPotentialBall μ R) (closure U) ∧
      HasLaplacian (greenPotentialBall μ R) 0 μ U := by
  refine ⟨(greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ?_,
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV).mono_domain hsub⟩
  exact (closure_mono hsub).trans (closure_ball_subset_closedBall)

/-- The shifted obstacle is continuous up to a Green-regular boundary away
from the pole. The shift is the potential of an enclosing disc. -/
theorem continuousOn_greenRegular_shifted_obstacle
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) (t : ℝ)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    ContinuousOn (fun x => -t * greenFunction U z x + greenPotentialBall μ R x)
      (closure U \ {z}) := by
  obtain ⟨h, hc, _, heq⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hsub hz hboundary
  have hg : ContinuousOn (greenFunction U z) (closure U \ {z}) := by
    apply ContinuousOn.congr
      (((continuousOn_greenFunction_ball (hsub hz)).mono (by intro x hx; exact hx.2)).add
        (hc.mono sdiff_subset))
    intro x hx
    have hxz : x ≠ z := hx.2
    have h := heq x hx.1 hxz
    dsimp only [Pi.add_apply]
    linarith
  exact (continuousOn_const.mul hg).add
    ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono sdiff_subset)

/-- The shifted Green obstacle tends to minus infinity at the pole. -/
theorem tendsto_greenRegular_shifted_obstacle_atBot
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x => -t * greenFunction U z x + greenPotentialBall μ R x)
      (𝓝[≠] z) atBot := by
  obtain ⟨h, hh, heq⟩ :=
    exists_harmonicOnNhd_greenFunction_difference hU (isBounded_ball.subset hsub) hsub hz
  have hd : Tendsto (fun x => -t * h x) (𝓝[≠] z) (𝓝 (-t * h z)) :=
    (((hh z hz).1.continuousAt.tendsto).const_mul (-t)).mono_left nhdsWithin_le_nhds
  have hdisc := obstacleTendstoAtBotStep_holds μ R z t hR (hsub hz) ht
    (greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV)
  have hsum := hdisc.atBot_add hd
  apply hsum.congr'
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz), self_mem_nhdsWithin] with x hx hxz
  have hxz' : x ≠ z := hxz
  have h := heq x hx hxz'
  dsimp only [obstacle]
  nlinarith

#print axioms tendsto_greenRegular_shifted_obstacle_atBot

/-- Nonnegative superharmonic majorants of an obstacle with a distinguished
pole. No condition is imposed at the pole. -/
def nonnegativeSuperharmonicMajorants (U : Set ℂ) (z : ℂ) (β : ℂ → ℝ) : Set (ℂ → ℝ) :=
  {g | IsSuperharmonicOn U g ∧ (∀ x ∈ U, 0 ≤ g x) ∧
    ∀ x ∈ closure U, x ≠ z → β x ≤ g x}

/-- The pointwise infimum of the nonnegative majorants. -/
noncomputable def nonnegativeMajorantInf (U : Set ℂ) (z : ℂ) (β : ℂ → ℝ) (x : ℂ) : ℝ :=
  sInf ((fun g : ℂ → ℝ => g x) '' nonnegativeSuperharmonicMajorants U z β)

/-- On an open domain the infimum of nonnegative superharmonic majorants is
superharmonic, provided the obstacle is continuous away from the pole and
the class is nonempty. -/
theorem isSuperharmonicOn_nonnegativeMajorantInf
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} {β : ℂ → ℝ}
    (hβ : ContinuousOn β (U \ {z}))
    (hne : (nonnegativeSuperharmonicMajorants U z β).Nonempty) :
    IsSuperharmonicOn U (nonnegativeMajorantInf U z β) := by
  classical
  let F := nonnegativeSuperharmonicMajorants U z β
  let f := nonnegativeMajorantInf U z β
  obtain ⟨g₀, hg₀⟩ := hne
  have hval : ∀ x, ((fun g : ℂ → ℝ => g x) '' F).Nonempty :=
    fun x => ⟨g₀ x, g₀, hg₀, rfl⟩
  have hfge : ∀ x, ∀ a : ℝ, (∀ g ∈ F, a ≤ g x) → a ≤ f x := by
    intro x a ha
    exact le_csInf (hval x) (by rintro _ ⟨g, hg, rfl⟩; exact ha g hg)
  have hf0 : ∀ x ∈ U, 0 ≤ f x := by
    intro x hx
    exact hfge x 0 (fun g hg => hg.2.1 x hx)
  have hfle : ∀ g ∈ F, ∀ x ∈ U, f x ≤ g x := by
    intro g hg x hx
    exact csInf_le ⟨0, by rintro _ ⟨w, hw, rfl⟩; exact hw.2.1 x hx⟩ ⟨g, hg, rfl⟩
  have hfβ : ∀ x ∈ closure U, x ≠ z → β x ≤ f x := by
    intro x hx hxz
    exact hfge x (β x) (fun g hg => hg.2.2 x hx hxz)
  have hreg := isSuperharmonicOn_lscRegularization hU (fun g hg => hg.1) hg₀
    hfle (fun x _ a ha => hfge x a ha) hf0
  let ĝ : ℂ → ℝ := fun x => if x ∈ U then lscRegularization U f x else f x
  have heq : EqOn (lscRegularization U f) ĝ U := by
    intro x hx
    simp [ĝ, hx]
  have hĝ : ĝ ∈ F := by
    refine ⟨hreg.congr heq, ?_, ?_⟩
    · intro x hx
      rw [← heq hx]
      exact lscRegularization_nonneg hf0 hx
    · intro x hx hxz
      by_cases hxU : x ∈ U
      · rw [← heq hxU]
        apply le_lscRegularization hf0 hxU
        intro ε hε
        have hnhds : U \ {z} ∈ 𝓝 x := (hU.sdiff isClosed_singleton).mem_nhds ⟨hxU, hxz⟩
        have hc := hβ.continuousAt hnhds
        filter_upwards [hc.eventually (Ioi_mem_nhds (show β x - ε < β x by linarith)),
          hnhds] with y hy hyU _
        exact (le_of_lt hy).trans (hfβ y (subset_closure hyU.1) hyU.2)
      · simpa [ĝ, hxU] using hfβ x hx hxz
  have heqf : EqOn (lscRegularization U f) f U := by
    intro x hx
    exact le_antisymm (lscRegularization_le hf0 hx)
      ((hfle ĝ hĝ x hx).trans (heq hx).symm.le)
  exact hreg.congr heqf

/-- A Poisson modification gives upper semicontinuity of the infimum when
the obstacle admits a local constant barrier. -/
theorem upperSemicontinuousAt_nonnegativeMajorantInf_of_poisson
    {U : Set ℂ} (hU : IsOpen U) {z x₀ : ℂ} {β : ℂ → ℝ}
    (hβ : ContinuousOn β (U \ {z}))
    (hne : (nonnegativeSuperharmonicMajorants U z β).Nonempty)
    (h : ∀ ε > 0, ∃ δ > 0, closedBall x₀ δ ⊆ U ∧ ∃ L : ℝ,
      (∀ ζ ∈ sphere x₀ δ, L ≤ ε + nonnegativeMajorantInf U z β ζ) ∧
      ∀ y ∈ ball x₀ δ, y ≠ z → β y ≤ L) :
    UpperSemicontinuousAt (nonnegativeMajorantInf U z β) x₀ := by
  classical
  let F := nonnegativeSuperharmonicMajorants U z β
  let f := nonnegativeMajorantInf U z β
  obtain ⟨g₀, hg₀⟩ := hne
  have hval : ∀ x, ((fun g : ℂ → ℝ => g x) '' F).Nonempty :=
    fun x => ⟨g₀ x, g₀, hg₀, rfl⟩
  have hfobs : ∀ x ∈ closure U, x ≠ z → β x ≤ f x := by
    intro x hx hxz
    exact le_csInf (hval x) (by rintro _ ⟨g, hg, rfl⟩; exact hg.2.2 x hx hxz)
  have hf0 : ∀ x ∈ U, 0 ≤ f x := by
    intro x hx
    exact le_csInf (hval x) (by rintro _ ⟨g, hg, rfl⟩; exact hg.2.1 x hx)
  have hfle : ∀ g ∈ F, ∀ x ∈ U, f x ≤ g x := by
    intro g hg x hx
    exact csInf_le ⟨0, by rintro _ ⟨w, hw, rfl⟩; exact hw.2.1 x hx⟩ ⟨g, hg, rfl⟩
  have hfsh : IsSuperharmonicOn U f := isSuperharmonicOn_nonnegativeMajorantInf hU hβ ⟨g₀, hg₀⟩
  intro a ha
  have ha' : f x₀ < a := ha
  let ε := (a - f x₀) / 3
  have hε0 : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, hsub, L, hL, hβL⟩ := h ε hε0
  let u : ℂ → ℝ := fun y => ε + f y
  have hu : IsSuperharmonicOn U u := hfsh.const_add ε
  have hx₀U : x₀ ∈ U := hsub (mem_closedBall_self hδ.le)
  have hui : CircleIntegrable u x₀ δ := (hu.2 x₀ hx₀U δ hδ hsub).1
  obtain ⟨hgsh, _⟩ := isSuperharmonicOn_poissonModification hU hu hδ hsub
  have hgF : poissonModification u x₀ δ ∈ F := by
    refine ⟨hgsh, ?_, ?_⟩
    · intro y hy
      by_cases hyb : y ∈ ball x₀ δ
      · rw [poissonModification_of_mem hyb]
        apply le_discPoissonIntegral hui hyb
        intro ζ hζ
        have hζU := hsub (sphere_subset_closedBall hζ)
        have := hf0 ζ hζU
        dsimp [u]
        linarith
      · rw [poissonModification_of_notMem hyb]
        have := hf0 y hy
        dsimp [u]
        linarith
    · intro y hy hyz
      by_cases hyb : y ∈ ball x₀ δ
      · rw [poissonModification_of_mem hyb]
        exact (hβL y hyb hyz).trans (le_discPoissonIntegral hui hyb hL)
      · rw [poissonModification_of_notMem hyb]
        have := hfobs y hy hyz
        dsimp [u]
        linarith
  have hPc : ContinuousAt (discPoissonIntegral u x₀ δ) x₀ :=
    (continuousOn_discPoissonIntegral hui).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))
  have hPx₀ : discPoissonIntegral u x₀ δ x₀ ≤ ε + f x₀ :=
    discPoissonIntegral_le hu.1 (hu.localSuperMean hU) hδ hsub hui x₀ (mem_ball_self hδ)
  filter_upwards [hPc.eventually (gt_mem_nhds (show discPoissonIntegral u x₀ δ x₀ <
    discPoissonIntegral u x₀ δ x₀ + ε by linarith)), isOpen_ball.mem_nhds (mem_ball_self hδ)]
    with y hy hyb
  have h1 : f y ≤ poissonModification u x₀ δ y := hfle _ hgF y (hsub (ball_subset_closedBall hyb))
  rw [poissonModification_of_mem hyb] at h1
  show f y < a
  dsimp [ε] at *
  linarith

/-- A continuous obstacle yields a continuous least nonnegative majorant at
every interior point other than the pole. -/
theorem continuousAt_nonnegativeMajorantInf_of_ne_pole
    {U : Set ℂ} (hU : IsOpen U) {z x : ℂ} {β : ℂ → ℝ}
    (hβ : ContinuousOn β (U \ {z}))
    (hne : (nonnegativeSuperharmonicMajorants U z β).Nonempty)
    (hx : x ∈ U) (hxz : x ≠ z) :
    ContinuousAt (nonnegativeMajorantInf U z β) x := by
  have hfsh := isSuperharmonicOn_nonnegativeMajorantInf hU hβ hne
  have hlsc : LowerSemicontinuousAt (nonnegativeMajorantInf U z β) x := by
    intro a ha
    have h := hfsh.1 x hx a ha
    rwa [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx)] at h
  have hfobs : ∀ y ∈ closure U, y ≠ z → β y ≤ nonnegativeMajorantInf U z β y := by
    intro y hy hyz
    apply le_csInf (hne.image (fun g : ℂ → ℝ => g y))
    rintro _ ⟨g, hg, rfl⟩
    exact hg.2.2 y hy hyz
  have husc : UpperSemicontinuousAt (nonnegativeMajorantInf U z β) x := by
    apply upperSemicontinuousAt_nonnegativeMajorantInf_of_poisson hU hβ hne
    intro ε hε
    have hnhds : U \ {z} ∈ 𝓝 x := (hU.sdiff isClosed_singleton).mem_nhds ⟨hx, hxz⟩
    obtain ⟨δ₁, hδ₁, hδ₁β⟩ := Metric.continuousAt_iff.1 (hβ.continuousAt hnhds)
      (ε / 2) (by positivity)
    obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.1 (hU.sdiff isClosed_singleton) x ⟨hx, hxz⟩
    let δ := min (δ₁ / 2) (δ₂ / 2)
    have hδ0 : 0 < δ := by dsimp [δ]; positivity
    have hδ1 : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ2 : δ < δ₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hcb : closedBall x δ ⊆ U \ {z} := (closedBall_subset_ball hδ2).trans hδ₂sub
    refine ⟨δ, hδ0, hcb.trans sdiff_subset, β x + ε / 2, ?_, ?_⟩
    · intro ζ hζ
      have hζc := hcb (sphere_subset_closedBall hζ)
      have h1 := hδ₁β (show dist ζ x < δ₁ by rw [mem_sphere] at hζ; linarith)
      have h2 := hfobs ζ (subset_closure hζc.1) hζc.2
      rw [Real.dist_eq, abs_lt] at h1
      linarith
    · intro y hy hyz
      have h1 := hδ₁β (show dist y x < δ₁ by rw [mem_ball] at hy; linarith)
      rw [Real.dist_eq, abs_lt] at h1
      linarith
  exact continuousAt_iff_lower_upperSemicontinuousAt.2 ⟨hlsc, husc⟩

/-- The least nonnegative majorant is continuous at the pole if the obstacle
tends to minus infinity there. -/
theorem continuousAt_nonnegativeMajorantInf_pole
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) {β : ℂ → ℝ}
    (hβ : ContinuousOn β (U \ {z}))
    (hbot : Tendsto β (𝓝[≠] z) atBot)
    (hne : (nonnegativeSuperharmonicMajorants U z β).Nonempty) :
    ContinuousAt (nonnegativeMajorantInf U z β) z := by
  have hfsh := isSuperharmonicOn_nonnegativeMajorantInf hU hβ hne
  have hlsc : LowerSemicontinuousAt (nonnegativeMajorantInf U z β) z := by
    intro a ha
    have h := hfsh.1 z hz a ha
    rwa [nhdsWithin_eq_nhds.2 (hU.mem_nhds hz)] at h
  have hf0 : ∀ x ∈ U, 0 ≤ nonnegativeMajorantInf U z β x := by
    intro x hx
    apply le_csInf (hne.image (fun g : ℂ → ℝ => g x))
    rintro _ ⟨g, hg, rfl⟩
    exact hg.2.1 x hx
  have husc : UpperSemicontinuousAt (nonnegativeMajorantInf U z β) z := by
    apply upperSemicontinuousAt_nonnegativeMajorantInf_of_poisson hU hβ hne
    intro ε hε
    have hev : ∀ᶠ y in 𝓝[≠] z, β y < ε := hbot.eventually (eventually_lt_atBot ε)
    obtain ⟨δ₁, hδ₁, hδ₁β⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.1 hU z hz
    let δ := min (δ₁ / 2) (δ₂ / 2)
    have hδ0 : 0 < δ := by dsimp [δ]; positivity
    have hδ1 : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ2 : δ < δ₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hcb : closedBall z δ ⊆ U := (closedBall_subset_ball hδ2).trans hδ₂sub
    refine ⟨δ, hδ0, hcb, ε, ?_, ?_⟩
    · intro ζ hζ
      have := hf0 ζ (hcb (sphere_subset_closedBall hζ))
      linarith
    · intro y hy hyz
      exact (hδ₁β ⟨ball_subset_ball hδ1.le hy, hyz⟩).le
  exact continuousAt_iff_lower_upperSemicontinuousAt.2 ⟨hlsc, husc⟩

#print axioms continuousAt_nonnegativeMajorantInf_pole
#print axioms continuousAt_nonnegativeMajorantInf_of_ne_pole
#print axioms upperSemicontinuousAt_nonnegativeMajorantInf_of_poisson
#print axioms isSuperharmonicOn_nonnegativeMajorantInf

/-- At a Green-regular boundary point, the pointwise infimum attains its
zero boundary value continuously from the domain, without assuming it is
itself an admissible supersolution. -/
theorem continuousWithinAt_leastSupersolutionOn_of_green_boundary_limit
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    {t : ℝ} (ht : 0 ≤ t)
    (hboundary : Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    ContinuousWithinAt (leastSupersolutionOn μ U z t) U y := by
  have hyz : y ≠ z := fun h => hyU (h ▸ hz)
  have hvzero := leastSupersolutionOn_eq_zero_of_boundary (μ := μ) hUb ht hy hyU hyz
  have hnear : ∀ᶠ x in 𝓝[U] y, x ≠ z :=
    (show ∀ᶠ x in 𝓝 y, x ≠ z from isOpen_compl_singleton.mem_nhds hyz).filter_mono
      nhdsWithin_le_nhds
  have hlo : ∀ᶠ x in 𝓝[U] y,
      -t * greenFunction U z x ≤ leastSupersolutionOn μ U z t x := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx hxz
    apply le_csInf
    · exact ⟨0, 0, zero_mem_supersolutionsOn hUb ht, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2 x (subset_closure hx) hxz
  have hhi : ∀ᶠ x in 𝓝[U] y, leastSupersolutionOn μ U z t x ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx hxz
    exact leastSupersolutionOn_le_of_mem (zero_mem_supersolutionsOn hUb ht)
      (subset_closure hx) hxz
  change Tendsto (leastSupersolutionOn μ U z t) (𝓝[U] y)
    (𝓝 (leastSupersolutionOn μ U z t y))
  rw [hvzero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds hlo hhi
  simpa using (tendsto_const_nhds (x := -t)).mul hboundary

#print axioms continuousWithinAt_leastSupersolutionOn_of_green_boundary_limit

#print axioms enclosingDisc_potential_shift_on_domain
#print axioms continuousOn_greenRegular_shifted_obstacle

end HarmonicBalls
