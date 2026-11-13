import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementEvent

/-!
# Local agreement near a point, from agreement on a dense set (step 7 of the route for `hN2`)

Deterministic part of the proof of the local identity near a point `q ≠ z` of the disk `D`. Suppose that

* on the pairs of points of a set `S` dense in an open set `V ⊆ D`, lying in a set `T ⊆ V` and at distance `< η`, the
  decoded function `d` equals `c₁ * g` (the local-agreement event at the index `V`);
* `g = c₂ * internalMetric e V` on `V × V` (the explicit rooted identity on `V`);
* near `q ∈ interior T`, the internal metrics of `e` on `D` and on `V` coincide (exit localization).

Then `d = c₁ * c₂ * internalMetric e D` on `ball q s × ball q s` for some `s > 0`, provided `d` and `g` are continuous
on `V × V` (`exists_ball_eq_mul_internalMetric_of_localAgreement`). The agreement passes from `S` to the ball by
density and continuity (`eqOn_prod_of_dense`). `exists_ball_eq_mul_internalMetric_of_decoders` is the same statement
for `d` and `g` decoded from continuous functions on `D × D` and `V × V` (`extendDist`).
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The extension `extendDist Z M` is `M` at the points of `Z`. -/
theorem extendDist_of_mem {Z : Set (ℂ × ℂ)} (M : C(Z, ℝ)) {u v : ℂ} (h : (u, v) ∈ Z) :
    extendDist Z M u v = M ⟨(u, v), h⟩ := by
  simp [extendDist, h]

/-- On `Z`, the extension `extendDist Z M` is continuous. -/
theorem continuousOn_extendDist (Z : Set (ℂ × ℂ)) (M : C(Z, ℝ)) :
    ContinuousOn (fun p : ℂ × ℂ => extendDist Z M p.1 p.2) Z := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine M.continuous.congr fun p => ?_
  exact (extendDist_of_mem M (u := p.1.1) (v := p.1.2) p.2).symm

/-- On every subset of `Z`, the function `ENNReal.ofReal ∘ extendDist Z M` is continuous. -/
theorem continuousOn_ofReal_extendDist {Z W : Set (ℂ × ℂ)} (M : C(Z, ℝ)) (hW : W ⊆ Z) :
    ContinuousOn (fun p : ℂ × ℂ => ENNReal.ofReal (extendDist Z M p.1 p.2)) W :=
  (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_extendDist Z M)).mono hW

/-- **Extension by density.** Two functions of a pair of points, continuous on `V ×ˢ V`, that agree at the pairs of
points of a set `S` dense in `V` lying in an open set `B ⊆ V`, agree at all pairs of points of `B`. -/
theorem eqOn_prod_of_dense {V S : Set ℂ} (hS : V ⊆ closure S) {f g : ℂ → ℂ → ℝ≥0∞}
    (hf : ContinuousOn (fun p : ℂ × ℂ => f p.1 p.2) (V ×ˢ V))
    (hg : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (V ×ˢ V))
    {B : Set ℂ} (hB : IsOpen B) (hBV : B ⊆ V)
    (h : ∀ u ∈ S, ∀ v ∈ S, u ∈ B → v ∈ B → f u v = g u v) :
    ∀ u ∈ B, ∀ v ∈ B, f u v = g u v := by
  have hW : IsOpen (B ×ˢ B) := hB.prod hB
  have hWV : B ×ˢ B ⊆ V ×ˢ V := prod_mono hBV hBV
  have hEq : EqOn (fun p : ℂ × ℂ => f p.1 p.2) (fun p => g p.1 p.2) (B ×ˢ B ∩ S ×ˢ S) := by
    rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, hu', hv'⟩
    exact h u hu' v hv' hu hv
  have hcl : B ×ˢ B ⊆ closure (B ×ˢ B ∩ S ×ˢ S) := by
    intro p hp
    apply hW.inter_closure
    refine ⟨hp, ?_⟩
    rw [closure_prod_eq]
    exact ⟨hS (hBV hp.1), hS (hBV hp.2)⟩
  intro u hu v hv
  exact hEq.of_subset_closure (hf.mono hWV) (hg.mono hWV) inter_subset_left hcl (mk_mem_prod hu hv)

/-- **Local identity near a point.** If `d = c₁ * g` at the pairs of points of a set `S` dense in the open set
`V ⊆ D` lying in `T ⊆ V` at distance `< η`, if `g = c₂ * internalMetric e V` on `V × V`, and if the internal metrics
of `e` on `D` and on `V` coincide near `q ∈ interior T`, then `d = c₁ * c₂ * internalMetric e D` on a ball around `q`
inside `D` (`d` and `g` continuous on `V × V`, `c₁ ≠ ⊤`). -/
theorem exists_ball_eq_mul_internalMetric_of_localAgreement
    {D V T S : Set ℂ} (hVD : V ⊆ D) (hTV : T ⊆ V) (hS : V ⊆ closure S)
    {d g : ℂ → ℂ → ℝ≥0∞}
    (hd : ContinuousOn (fun p : ℂ × ℂ => d p.1 p.2) (V ×ˢ V))
    (hg : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (V ×ˢ V))
    {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤) {η : ℝ} (hη : 0 < η)
    (hA3 : ∀ u ∈ S, ∀ v ∈ S, u ∈ T → v ∈ T → ‖u - v‖ < η → d u v = c₁ * g u v)
    {e : ℂ → ℂ → ℝ}
    (hroot : ∀ u ∈ V, ∀ v ∈ V, g u v = c₂ * internalMetric e V u v)
    {q : ℂ} (hq : q ∈ interior T)
    (hL3 : ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      internalMetric e D u v = internalMetric e V u v) :
    ∃ s > 0, ball q s ⊆ D ∧ ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      d u v = c₁ * c₂ * internalMetric e D u v := by
  obtain ⟨r₀, hr₀, hr₀T⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
  obtain ⟨s₁, hs₁, hL⟩ := hL3
  have hs : 0 < min (min r₀ s₁) (η / 2) := lt_min (lt_min hr₀ hs₁) (half_pos hη)
  set s := min (min r₀ s₁) (η / 2) with hs_def
  have hsr₀ : ball q s ⊆ ball q r₀ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hss₁ : ball q s ⊆ ball q s₁ := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hBT : ball q s ⊆ T := hsr₀.trans (hr₀T.trans interior_subset)
  have hBV : ball q s ⊆ V := hBT.trans hTV
  have hclose : ∀ u ∈ ball q s, ∀ v ∈ ball q s, ‖u - v‖ < η := by
    intro u hu v hv
    rw [← dist_eq_norm]
    calc dist u v ≤ dist u q + dist q v := dist_triangle u q v
      _ < s + s := add_lt_add (mem_ball.mp hu) (by rw [dist_comm]; exact mem_ball.mp hv)
      _ ≤ η / 2 + η / 2 := add_le_add (min_le_right _ _) (min_le_right _ _)
      _ = η := add_halves η
  have hcg : ContinuousOn (fun p : ℂ × ℂ => c₁ * g p.1 p.2) (V ×ˢ V) :=
    (ENNReal.continuous_const_mul hc₁).comp_continuousOn hg
  have hagree := eqOn_prod_of_dense (g := fun u v => c₁ * g u v) hS hd hcg isOpen_ball hBV
    (fun u hu v hv huB hvB => hA3 u hu v hv (hBT huB) (hBT hvB) (hclose u huB v hvB))
  refine ⟨s, hs, hBV.trans hVD, fun u hu v hv => ?_⟩
  rw [show d u v = c₁ * g u v from hagree u hu v hv, hroot u (hBV hu) v (hBV hv),
    hL u (hss₁ hu) v (hss₁ hv), mul_assoc]

/-- **Local identity near a point, decoded form.** The same as
`exists_ball_eq_mul_internalMetric_of_localAgreement`, for `d` and `g` decoded from continuous functions `M` on
`D × D` and `M_V` on `V × V` (`V` open), with the rooted identity `ofReal (M_V p) = c₂ * internalMetric e V p.1 p.2`
for every pair `p` of points of `V`. -/
theorem exists_ball_eq_mul_internalMetric_of_decoders
    {D V T S : Set ℂ} (hVD : V ⊆ D) (hTV : T ⊆ V) (hS : V ⊆ closure S)
    (M : C(↥(D ×ˢ D), ℝ)) (MV : C(↥(V ×ˢ V), ℝ)) {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤) {η : ℝ} (hη : 0 < η)
    (hA3 : ∀ u ∈ S, ∀ v ∈ S, u ∈ T → v ∈ T → ‖u - v‖ < η →
      ENNReal.ofReal (extendDist (D ×ˢ D) M u v) = c₁ * ENNReal.ofReal (extendDist (V ×ˢ V) MV u v))
    {e : ℂ → ℂ → ℝ}
    (hroot : ∀ p : ↥(V ×ˢ V), ENNReal.ofReal (MV p) = c₂ * internalMetric e V p.1.1 p.1.2)
    {q : ℂ} (hq : q ∈ interior T)
    (hL3 : ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      internalMetric e D u v = internalMetric e V u v) :
    ∃ s > 0, ball q s ⊆ D ∧ ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      ENNReal.ofReal (extendDist (D ×ˢ D) M u v) = c₁ * c₂ * internalMetric e D u v := by
  refine exists_ball_eq_mul_internalMetric_of_localAgreement
    (g := fun u v => ENNReal.ofReal (extendDist (V ×ˢ V) MV u v)) hVD hTV hS
    (continuousOn_ofReal_extendDist M (prod_mono hVD hVD)) (continuousOn_ofReal_extendDist MV subset_rfl)
    hc₁ hη hA3 (fun u hu v hv => ?_) hq hL3
  rw [extendDist_of_mem MV (mk_mem_prod hu hv)]
  exact hroot ⟨(u, v), mk_mem_prod hu hv⟩

end HarmonicBalls
