import HarmonicBalls.Proofs.Sec5.LocalCountableDeletion
import HarmonicBalls.Defs.Geometry
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-! # Countable deletions and planar crossing components -/

namespace HarmonicBalls

open Set Metric MeasureTheory

/-- Removing a countable set from a planar disc leaves it path connected. -/
theorem isPathConnected_ball_sdiff_countable {c : ℂ} {r : ℝ} (hr : 0 < r)
    {K : Set ℂ} (hK : (K ∩ ball c r).Countable) :
    IsPathConnected (ball c r \ K) := by
  let e : ℂ ≃ₜ ball c r :=
    (Homeomorph.unitBall : ℂ ≃ₜ ball (0 : ℂ) 1).trans
      (OpenPartialHomeomorph.unitBallBall c r hr).toHomeomorphSourceTarget
  let f : ℂ → ℂ := fun x => e x
  have hf : Function.Injective f := fun x y h => e.injective (Subtype.ext h)
  have hk : (f ⁻¹' (K ∩ ball c r)).Countable := hK.preimage hf
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
    norm_num
  have hp := hk.isPathConnected_compl_of_one_lt_rank hrank
  have himage : f '' (f ⁻¹' (K ∩ ball c r))ᶜ = ball c r \ K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(e y).property, fun hx => hy ⟨hx, (e y).property⟩⟩
    · rintro ⟨hx, hxK⟩
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      refine ⟨y, ?_, congrArg Subtype.val hy⟩
      intro hm
      have heq : f y = x := congrArg Subtype.val hy
      exact hxK (heq ▸ hm.1)
  rw [← himage]
  exact hp.image (continuous_subtype_val.comp e.continuous)

/-- A countable deletion does not disconnect an open planar set. -/
theorem isPreconnected_sdiff_countable_of_isOpen {G K : Set ℂ}
    (hG : IsOpen G) (hGc : IsPreconnected G) (hK : (K ∩ G).Countable) :
    IsPreconnected (G \ K) := by
  by_cases hne : (G \ K).Nonempty
  · obtain ⟨a, ha⟩ := hne
    let C := connectedComponentIn (G \ K) a
    have haC : a ∈ C := mem_connectedComponentIn ha
    have hlocal : ∀ x ∈ G ∩ closure C, ∃ r : ℝ, 0 < r ∧
        ball x r ⊆ G ∧ ball x r \ K ⊆ C := by
      intro x hx
      obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.mp hG x hx.1
      obtain ⟨p, hpball, hpC⟩ := mem_closure_iff_nhds.mp hx.2 _
        (isOpen_ball.mem_nhds (mem_ball_self hr))
      have hpD : p ∈ G \ K := connectedComponentIn_subset _ _ hpC
      have hcount : (K ∩ ball x r).Countable := hK.mono (by
        intro y hy
        exact ⟨hy.1, hrG hy.2⟩)
      have hball : IsPreconnected (ball x r \ K) :=
        (isPathConnected_ball_sdiff_countable hr hcount).isConnected.isPreconnected
      have hp : p ∈ ball x r \ K := ⟨hpball, hpD.2⟩
      have hsub : ball x r \ K ⊆ connectedComponentIn (G \ K) p :=
        hball.subset_connectedComponentIn hp (by
          intro y hy
          exact ⟨hrG hy.1, hy.2⟩)
      refine ⟨r, hr, hrG, ?_⟩
      simpa only [C, connectedComponentIn_eq hpC] using hsub
    have hopen : IsOpen (G ∩ closure C) := by
      apply isOpen_iff_mem_nhds.mpr
      intro x hx
      obtain ⟨r, hr, hrG, hrC⟩ := hlocal x hx
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr))
      intro y hy
      refine ⟨hrG hy, ?_⟩
      have hcount : (K ∩ ball x r).Countable := hK.mono (by
        intro z hz
        exact ⟨hz.1, hrG hz.2⟩)
      have hcl := closure_sdiff_countable_inter (U := ball x r) (K := K)
        isOpen_ball hcount
      apply closure_mono hrC
      rw [hcl]
      exact subset_closure hy
    have hcover : G ⊆ (G ∩ closure C) ∪ (closure C)ᶜ := by
      intro x hx
      by_cases hxc : x ∈ closure C
      · exact Or.inl ⟨hx, hxc⟩
      · exact Or.inr hxc
    have hdisj : Disjoint (G ∩ closure C) (closure C)ᶜ := by
      apply disjoint_left.mpr
      intro x hx hy
      exact hy hx.2
    have hsubset : G ⊆ G ∩ closure C :=
      hGc.subset_left_of_subset_union hopen isClosed_closure.isOpen_compl hdisj hcover
        ⟨a, ha.1, ha.1, subset_closure haC⟩
    have hCD : G \ K ⊆ C := by
      intro x hx
      obtain ⟨r, hr, hrG, hrC⟩ := hlocal x (hsubset hx.1)
      exact hrC ⟨mem_ball_self hr, hx.2⟩
    exact (show IsPreconnected C from isPreconnected_connectedComponentIn).subset_closure
      (connectedComponentIn_subset _ _) (fun x hx => subset_closure (hCD hx))
  · simp only [not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact isPreconnected_empty

/-- The component after deletion is the original component with the deleted
points removed. -/
theorem connectedComponentIn_sdiff_countable {G K : Set ℂ}
    (hG : IsOpen G) (hK : (K ∩ G).Countable) {x : ℂ} (hx : x ∈ G \ K) :
    connectedComponentIn (G \ K) x = connectedComponentIn G x \ K := by
  let C := connectedComponentIn G x
  have hCo : IsOpen C := hG.connectedComponentIn
  have hCc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCK : (K ∩ C).Countable := hK.mono (by
    intro y hy
    exact ⟨hy.1, connectedComponentIn_subset G x hy.2⟩)
  have hpre := isPreconnected_sdiff_countable_of_isOpen hCo hCc hCK
  have hxC : x ∈ C \ K := ⟨mem_connectedComponentIn hx.1, hx.2⟩
  apply Subset.antisymm
  · intro y hy
    exact ⟨connectedComponentIn_mono x sdiff_subset hy,
      (connectedComponentIn_subset _ _ hy).2⟩
  · exact hpre.subset_connectedComponentIn hxC (by
      intro y hy
      exact ⟨connectedComponentIn_subset G x hy.1, hy.2⟩)

/-- The closure of a component is preserved by countable deletion. -/
theorem closure_connectedComponentIn_sdiff_countable {G K : Set ℂ}
    (hG : IsOpen G) (hK : (K ∩ G).Countable) {x : ℂ} (hx : x ∈ G \ K) :
    closure (connectedComponentIn (G \ K) x) = closure (connectedComponentIn G x) := by
  rw [connectedComponentIn_sdiff_countable hG hK hx]
  apply closure_sdiff_countable_inter hG.connectedComponentIn
  exact hK.mono (by
    intro y hy
    exact ⟨hy.1, connectedComponentIn_subset G x hy.2⟩)

/-- Crossing components after deletion are precisely the original crossing
components with the deleted points removed. -/
theorem crossingComponents_sdiff_countable {G K : Set ℂ}
    (hG : IsOpen G) (hK : (K ∩ G).Countable) (w : ℂ) (r R : ℝ) :
    crossingComponents (G \ K) w r R =
      (fun C : Set ℂ => C \ K) '' crossingComponents G w r R := by
  ext C
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hcross⟩
    refine ⟨connectedComponentIn G x, ⟨⟨x, hx.1, rfl⟩, ?_⟩, ?_⟩
    · simpa only [CrossesAnnulus,
        closure_connectedComponentIn_sdiff_countable hG hK hx] using hcross
    · exact (connectedComponentIn_sdiff_countable hG hK hx).symm
  · rintro ⟨D, ⟨⟨x, hx, rfl⟩, hcross⟩, rfl⟩
    have hCo : IsOpen (connectedComponentIn G x) := hG.connectedComponentIn
    obtain ⟨p, hpnot, hpC⟩ := (hK.dense_compl ℂ).exists_mem_open hCo
      ⟨x, mem_connectedComponentIn hx⟩
    have hpD : p ∈ G \ K := by
      refine ⟨connectedComponentIn_subset G x hpC, ?_⟩
      intro hpK
      exact hpnot ⟨hpK, connectedComponentIn_subset G x hpC⟩
    have heq : connectedComponentIn (G \ K) p = connectedComponentIn G x \ K := by
      rw [connectedComponentIn_sdiff_countable hG hK hpD, ← connectedComponentIn_eq hpC]
    refine ⟨⟨p, hpD, heq⟩, ?_⟩
    change CrossesAnnulus (connectedComponentIn G x \ K) w r R
    rw [← heq]
    simpa only [CrossesAnnulus,
      closure_connectedComponentIn_sdiff_countable hG hK hpD,
      ← connectedComponentIn_eq hpC] using hcross

/-- Countable deletion preserves the number of crossing components of an
open planar set, including crossings defined through component closures. -/
theorem encard_crossingComponents_sdiff_countable {G K : Set ℂ}
    (hG : IsOpen G) (hK : (K ∩ G).Countable) (w : ℂ) (r R : ℝ) :
    (crossingComponents (G \ K) w r R).encard =
      (crossingComponents G w r R).encard := by
  rw [crossingComponents_sdiff_countable hG hK]
  apply Set.InjOn.encard_image
  intro C hC D hD heq
  obtain ⟨x, hx, rfl⟩ := hC.1
  obtain ⟨y, hy, rfl⟩ := hD.1
  have hCo : IsOpen (connectedComponentIn G x) := hG.connectedComponentIn
  obtain ⟨p, hpnot, hpC⟩ := (hK.dense_compl ℂ).exists_mem_open hCo
    ⟨x, mem_connectedComponentIn hx⟩
  have hpK : p ∉ K := fun hp => hpnot ⟨hp, connectedComponentIn_subset G x hpC⟩
  change connectedComponentIn G x \ K = connectedComponentIn G y \ K at heq
  have hpD : p ∈ connectedComponentIn G y := (heq ▸ (show
    p ∈ connectedComponentIn G x \ K from ⟨hpC, hpK⟩)).1
  exact (connectedComponentIn_eq hpC).trans (connectedComponentIn_eq hpD).symm

/-- Under obstacle admissibility, relatively closed locally countable domain
deletions preserve every localized annular crossing count of the cluster. -/
theorem encard_clusterOn_crossings_sdiff_of_relative_countable
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t)) (w : ℂ) (r s ρ : ℝ) :
    (crossingComponents (clusterOn μ (U \ K) z t ∩ ball w ρ) w r s).encard =
      (crossingComponents (clusterOn μ U z t ∩ ball w ρ) w r s).encard := by
  rw [clusterOn_sdiff_of_relative_countable hμ hU hUb hUR hD hK hqc hq ht hz hw]
  have heq : (clusterOn μ U z t \ K) ∩ ball w ρ =
      (clusterOn μ U z t ∩ ball w ρ) \ K := by ext x; simp only [mem_inter_iff, mem_sdiff]; tauto
  rw [heq]
  apply encard_crossingComponents_sdiff_countable (hopen.inter isOpen_ball)
  exact hK.mono (by
    intro x hx
    exact ⟨hx.1, hx.2.1.1⟩)

end HarmonicBalls
