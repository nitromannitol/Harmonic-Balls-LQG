import HarmonicBalls.Steps.Sec11.InternalDiameterDecoder
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstLawTransfer

/-!
# First pass, Lemma 11.15: countable reduction of the open first certificate (fp-S11j, owner n4)

Route (notes/n4.md, round 11). The faithful event `pinchFirstEvent` contains the open-corridor certificate
`correctedOpenFirstCertificate` (`pinchFirstEvent_of_correctedOpenFirstCertificate`, FirstPass/S11e/FirstEvent.lean). For a
Euclidean length metric `D`, the open certificate is rewritten here as a countable formula: every supremum and infimum over an
uncountable set is replaced by one over a countable subset dense in that set. The only analytic inputs are the continuity of
the internal metric in its endpoints (`IsEuclideanLengthMetric.continuousOn_internalMetric`) and of `D` on `ℂ × ℂ`.
The whole-plane internal metric is used in place of `ENNReal.ofReal (D a b)` (`IsEuclideanLengthMetric.ofReal_eq_internalMetric`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- A supremum over `K ⊆ U` (`U` open) of a function continuous on `U` equals the supremum over a subset `S ⊆ K` dense in `K`. -/
theorem iSup_eq_iSup_of_dense_of_continuousOn {g : ℂ → ℝ≥0∞} {U K S : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) (hSK : S ⊆ K) (hKS : K ⊆ closure S) (hg : ContinuousOn g U) :
    (⨆ y ∈ K, g y) = ⨆ y ∈ S, g y := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp (hKS hy)
    have ht : Tendsto (fun n => g (s n)) atTop (𝓝 (g y)) :=
      ((hg.continuousAt (hU.mem_nhds (hKU hy))).tendsto).comp hst
    exact le_of_tendsto ht (Eventually.of_forall fun n => le_iSup₂_of_le (s n) (hs n) le_rfl)
  · exact iSup₂_le fun y hy => le_iSup₂_of_le y (hSK hy) le_rfl

/-- An infimum over a product `A × B` of a continuous function equals the infimum over subsets `A' ⊆ A`, `B' ⊆ B` dense in
`A`, `B` respectively. -/
theorem iInf_iInf_eq_iInf_iInf_of_dense {F : ℂ × ℂ → ℝ≥0∞} (hF : Continuous F) {A B A' B' : Set ℂ}
    (hAA : A' ⊆ A) (hBB : B' ⊆ B) (hAc : A ⊆ closure A') (hBc : B ⊆ closure B') :
    (⨅ a ∈ A, ⨅ b ∈ B, F (a, b)) = ⨅ a ∈ A', ⨅ b ∈ B', F (a, b) := by
  have h1 : ∀ a ∈ A, ∀ b ∈ B, (⨅ a ∈ A, ⨅ b ∈ B, F (a, b)) ≤ F (a, b) := fun a ha b hb =>
    (iInf₂_le a ha).trans (iInf₂_le b hb)
  have h2 : ∀ a ∈ A, ∀ b ∈ B, (⨅ a ∈ A', ⨅ b ∈ B', F (a, b)) ≤ F (a, b) := by
    intro a ha b hb
    obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp (hAc ha)
    obtain ⟨t, ht, htt⟩ := mem_closure_iff_seq_limit.mp (hBc hb)
    have hlim : Tendsto (fun n => F (s n, t n)) atTop (𝓝 (F (a, b))) :=
      (hF.tendsto (a, b)).comp (hst.prodMk_nhds htt)
    exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
      (iInf₂_le (s n) (hs n)).trans (iInf₂_le (t n) (ht n)))
  apply le_antisymm
  · exact le_iInf₂ fun a ha => le_iInf₂ fun b hb => h1 a (hAA ha) b (hBB hb)
  · exact le_iInf₂ fun a ha => le_iInf₂ fun b hb => h2 a ha b hb

/-- The set distance of a Euclidean length metric, as a countable infimum of whole-plane internal distances. -/
theorem ofReal_setDist_eq_countable {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A B A' B' : Set ℂ}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAA : A' ⊆ A) (hBB : B' ⊆ B) (hAc : A ⊆ closure A')
    (hBc : B ⊆ closure B') :
    ENNReal.ofReal (setDist D A B) = ⨅ a ∈ A', ⨅ b ∈ B', internalMetric D univ a b := by
  have hF : Continuous (fun p : ℂ × ℂ => ENNReal.ofReal (D p.1 p.2)) :=
    ENNReal.continuous_ofReal.comp hD.continuous_pair
  rw [ofReal_setDist_eq_iInf hA hB]
  refine (iInf_iInf_eq_iInf_iInf_of_dense hF hAA hBB hAc hBc).trans ?_
  simp only [hD.ofReal_eq_internalMetric]

/-- The internal diameter of a Euclidean length metric, as a countable supremum over a subset dense in the set. -/
theorem internalDiam_eq_countable {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {δ : ℝ} (hδ : 0 < δ) {A A' : Set ℂ} (hAA : A' ⊆ A) (hAc : A ⊆ closure A') :
    internalDiam D δ A = ⨆ x ∈ A', ⨆ y ∈ A', internalMetric D (thickening δ A) x y :=
  IsEuclideanLengthMetric.iSup_internalMetric_eq_of_dense_subset hD hnonneg isOpen_thickening
    (self_subset_thickening hδ A) hAA hAc

/-- The open-corridor first certificate `correctedOpenFirstCertificate` of a Euclidean length metric, as a countable formula:
the sup over the sphere `∂B₅` is taken over a dense subset `Sp`, the setDist over the dense subsets `Qp ⊆ Q'` and `Fp ⊆
∂Q`, the internal diameter over a dense subset `Cp` of `T \ B_{3δ}(W)`, and the setDist to `{0}` over a dense subset `Ep`
of `∂B_δ`. The open corridor `O = ball 0 6 \ (closure (B_{2δ}(Q)) ∪ closure (B_{2δ}(W)))` is open and contains `∂B₅`. -/
theorem correctedOpenFirstCertificate_iff_countable {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {W T Q' Q : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ' : Q'.Nonempty) (hFr : (frontier Q).Nonempty)
    (hS : sphere (0 : ℂ) 5 ⊆ ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
    {Sp Qp Fp Cp Ep : Set ℂ}
    (hSp : Sp ⊆ sphere (0 : ℂ) 5) (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp)
    (hQp : Qp ⊆ Q') (hQpc : Q' ⊆ closure Qp) (hFp : Fp ⊆ frontier Q) (hFpc : frontier Q ⊆ closure Fp)
    (hCp : Cp ⊆ T \ thickening (3 * δ) W) (hCpc : T \ thickening (3 * δ) W ⊆ closure Cp)
    (hEp : Ep ⊆ sphere (0 : ℂ) δ) (hEpc : sphere (0 : ℂ) δ ⊆ closure Ep) :
    correctedOpenFirstCertificate D W T Q' Q δ ↔
      ((⨆ y ∈ Sp, internalMetric D (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
          closure (thickening (2 * δ) W))) 0 y) < ⨅ a ∈ Qp, ⨅ b ∈ Fp, internalMetric D univ a b) ∧
        (⨆ x ∈ Cp, ⨆ y ∈ Cp, internalMetric D (thickening δ (T \ thickening (3 * δ) W)) x y) <
          ⨅ b ∈ Ep, internalMetric D univ 0 b := by
  have hO : IsOpen (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hsph : (sphere (0 : ℂ) δ).Nonempty := ⟨(δ : ℂ), by simp [abs_of_pos hδ]⟩
  have h1 := iSup_eq_iSup_of_dense_of_continuousOn hO hS hSp hSpc
    (hD.continuousOn_internalMetric hnonneg hO 0)
  have h2 := ofReal_setDist_eq_countable hD hQ' hFr hQp hFp hQpc hFpc
  have h3 := internalDiam_eq_countable hD hnonneg hδ hCp hCpc
  have h4 : ENNReal.ofReal (setDist D {0} (sphere 0 δ)) = ⨅ b ∈ Ep, internalMetric D univ 0 b := by
    have := ofReal_setDist_eq_countable hD (A := {0}) (A' := {0}) (B := sphere (0 : ℂ) δ) (B' := Ep)
      (Set.singleton_nonempty _) hsph (subset_refl _) hEp subset_closure hEpc
    simpa using this
  unfold correctedOpenFirstCertificate
  rw [h1, h2, h3, h4]

/-- Equal values on a set have equal suprema over that set. -/
theorem iSup_mem_congr {f g : ℂ → ℝ≥0∞} {S : Set ℂ} (h : ∀ y ∈ S, f y = g y) :
    (⨆ y ∈ S, f y) = ⨆ y ∈ S, g y :=
  le_antisymm (iSup₂_le fun y hy => le_iSup₂_of_le y hy (h y hy).le)
    (iSup₂_le fun y hy => le_iSup₂_of_le y hy (h y hy).ge)

/-- Equal values on a set have equal infima over that set. -/
theorem iInf_mem_congr {f g : ℂ → ℝ≥0∞} {S : Set ℂ} (h : ∀ y ∈ S, f y = g y) :
    (⨅ y ∈ S, f y) = ⨅ y ∈ S, g y :=
  le_antisymm (le_iInf₂ fun y hy => (iInf₂_le y hy).trans_eq (h y hy))
    (le_iInf₂ fun y hy => (iInf₂_le y hy).trans_eq (h y hy).symm)

/-- A supremum over a countable set of a measurable family is measurable. -/
theorem measurable_iSup_mem_of_countable {Ω : Type*} [MeasurableSpace Ω] {S : Set ℂ} (hS : S.Countable)
    {g : ℂ → Ω → ℝ≥0∞} (hg : ∀ y, Measurable (g y)) :
    Measurable fun ω => ⨆ y ∈ S, g y ω := by
  have := hS.to_subtype
  simp only [← iSup_subtype'']
  exact Measurable.iSup fun y : S => hg y.1

/-- An infimum over a countable set of a measurable family is measurable. -/
theorem measurable_iInf_mem_of_countable {Ω : Type*} [MeasurableSpace Ω] {S : Set ℂ} (hS : S.Countable)
    {g : ℂ → Ω → ℝ≥0∞} (hg : ∀ y, Measurable (g y)) :
    Measurable fun ω => ⨅ y ∈ S, g y ω := by
  have := hS.to_subtype
  simp only [← iInf_subtype'']
  exact Measurable.iInf fun y : S => hg y.1

/-- A property holding almost surely at each point of a countable set holds almost surely at all of them. -/
theorem ae_forall_mem_of_countable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Set ι}
    (hS : S.Countable) {p : ι → Ω → Prop} (h : ∀ i ∈ S, ∀ᵐ ω ∂P, p i ω) :
    ∀ᵐ ω ∂P, ∀ i ∈ S, p i ω := by
  have := hS.to_subtype
  filter_upwards [ae_all_iff.2 fun i : S => h i.1 i.2] with ω hω i hi using hω ⟨i, hi⟩

/-- The open first certificate written with value families: `vO y` (the internal distance on the open corridor from `0`
to `y`), `vU a b` (the whole-plane internal distance, i.e. the metric), `vT x y` (the internal distance on
`B_δ(T \ B_{3δ}(W))`). Its countable formula is the one of `correctedOpenFirstCertificate_iff_countable`. -/
def openFirstCountable (Sp Qp Fp Cp Ep : Set ℂ) (vO : ℂ → ℝ≥0∞) (vU vT : ℂ → ℂ → ℝ≥0∞) : Prop :=
  ((⨆ y ∈ Sp, vO y) < ⨅ a ∈ Qp, ⨅ b ∈ Fp, vU a b) ∧ ((⨆ x ∈ Cp, ⨆ y ∈ Cp, vT x y) < ⨅ b ∈ Ep, vU 0 b)

/-- The countable formula is measurable for measurable value families (any measurable space `Ω`). -/
theorem measurableSet_openFirstCountable {Ω : Type*} [MeasurableSpace Ω] {Sp Qp Fp Cp Ep : Set ℂ}
    (hSp : Sp.Countable) (hQp : Qp.Countable) (hFp : Fp.Countable) (hCp : Cp.Countable) (hEp : Ep.Countable)
    {vO : ℂ → Ω → ℝ≥0∞} {vU vT : ℂ → ℂ → Ω → ℝ≥0∞}
    (hvO : ∀ y, Measurable (vO y)) (hvU : ∀ a b, Measurable (vU a b)) (hvT : ∀ x y, Measurable (vT x y)) :
    MeasurableSet {ω | openFirstCountable Sp Qp Fp Cp Ep (fun y => vO y ω) (fun a b => vU a b ω)
      (fun x y => vT x y ω)} := by
  have h1 : Measurable fun ω => ⨆ y ∈ Sp, vO y ω := measurable_iSup_mem_of_countable hSp hvO
  have h2 : Measurable fun ω => ⨅ a ∈ Qp, ⨅ b ∈ Fp, vU a b ω :=
    measurable_iInf_mem_of_countable hQp fun a => measurable_iInf_mem_of_countable hFp fun b => hvU a b
  have h3 : Measurable fun ω => ⨆ x ∈ Cp, ⨆ y ∈ Cp, vT x y ω :=
    measurable_iSup_mem_of_countable hCp fun x => measurable_iSup_mem_of_countable hCp fun y => hvT x y
  have h4 : Measurable fun ω => ⨅ b ∈ Ep, vU 0 b ω := measurable_iInf_mem_of_countable hEp fun b => hvU 0 b
  exact (measurableSet_lt h1 h2).inter (measurableSet_lt h3 h4)

/-- Almost surely, the countable formula of the open first certificate of the family `M` agrees with the certificate of
`M ω`, once the value families agree a.s. with the internal distances of `M ω` at the countably many index pairs. -/
theorem ae_openFirstCountable_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → ℂ → ℂ → ℝ} {W T Q' Q : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ' : Q'.Nonempty) (hFr : (frontier Q).Nonempty)
    (hS : sphere (0 : ℂ) 5 ⊆ ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
    {Sp Qp Fp Cp Ep : Set ℂ}
    (hSp : Sp ⊆ sphere (0 : ℂ) 5) (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp)
    (hQp : Qp ⊆ Q') (hQpc : Q' ⊆ closure Qp) (hFp : Fp ⊆ frontier Q) (hFpc : frontier Q ⊆ closure Fp)
    (hCp : Cp ⊆ T \ thickening (3 * δ) W) (hCpc : T \ thickening (3 * δ) W ⊆ closure Cp)
    (hEp : Ep ⊆ sphere (0 : ℂ) δ) (hEpc : sphere (0 : ℂ) δ ⊆ closure Ep)
    (hCountS : Sp.Countable) (hCountQ : Qp.Countable) (hCountF : Fp.Countable) (hCountC : Cp.Countable)
    (hCountE : Ep.Countable)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (M ω) ∧ ∀ x y, 0 ≤ M ω x y)
    {vO : ℂ → Ω → ℝ≥0∞} {vU vT : ℂ → ℂ → Ω → ℝ≥0∞}
    (hvO : ∀ y ∈ Sp, ∀ᵐ ω ∂P, vO y ω = internalMetric (M ω)
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y)
    (hvU : ∀ a ∈ Qp, ∀ b ∈ Fp, ∀ᵐ ω ∂P, vU a b ω = internalMetric (M ω) univ a b)
    (hvE : ∀ b ∈ Ep, ∀ᵐ ω ∂P, vU 0 b ω = internalMetric (M ω) univ 0 b)
    (hvT : ∀ x ∈ Cp, ∀ y ∈ Cp, ∀ᵐ ω ∂P,
      vT x y ω = internalMetric (M ω) (thickening δ (T \ thickening (3 * δ) W)) x y) :
    ∀ᵐ ω ∂P, openFirstCountable Sp Qp Fp Cp Ep (fun y => vO y ω) (fun a b => vU a b ω)
      (fun x y => vT x y ω) ↔ correctedOpenFirstCertificate (M ω) W T Q' Q δ := by
  have hO' := ae_forall_mem_of_countable hCountS hvO
  have hU' := ae_forall_mem_of_countable (p := fun a ω => ∀ b ∈ Fp, vU a b ω = internalMetric (M ω) univ a b)
    hCountQ fun a ha => ae_forall_mem_of_countable hCountF fun b hb => hvU a ha b hb
  have hE' := ae_forall_mem_of_countable hCountE hvE
  have hT' := ae_forall_mem_of_countable (p := fun x ω => ∀ y ∈ Cp,
      vT x y ω = internalMetric (M ω) (thickening δ (T \ thickening (3 * δ) W)) x y)
    hCountC fun x hx => ae_forall_mem_of_countable hCountC fun y hy => hvT x hx y hy
  filter_upwards [hmetric, hO', hU', hE', hT'] with ω hω hO hU hE hT
  obtain ⟨hlen, hnn⟩ := hω
  have key := correctedOpenFirstCertificate_iff_countable hlen hnn hδ hQ' hFr hS hSp hSpc hQp hQpc hFp hFpc
    hCp hCpc hEp hEpc
  have e1 := iSup_mem_congr (S := Sp) hO
  have e2 : (⨅ a ∈ Qp, ⨅ b ∈ Fp, vU a b ω) = ⨅ a ∈ Qp, ⨅ b ∈ Fp, internalMetric (M ω) univ a b :=
    iInf_mem_congr fun a ha => iInf_mem_congr fun b hb => hU a ha b hb
  have e3 : (⨆ x ∈ Cp, ⨆ y ∈ Cp, vT x y ω) =
      ⨆ x ∈ Cp, ⨆ y ∈ Cp, internalMetric (M ω) (thickening δ (T \ thickening (3 * δ) W)) x y :=
    iSup_mem_congr fun x hx => iSup_mem_congr fun y hy => hT x hx y hy
  have e4 : (⨅ b ∈ Ep, vU 0 b ω) = ⨅ b ∈ Ep, internalMetric (M ω) univ 0 b := iInf_mem_congr hE
  simp only [openFirstCountable]
  rw [e1, e2, e3, e4]
  exact key.symm

end HarmonicBalls
