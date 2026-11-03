# α₀-uniformity of the constants printed as depending on γ (and b, p) only

One analysis for the whole family: [C8] (Lemma 4.2, E9), [C25] (Lemma 6.4, E28), [C26] (Lemma 6.7, E30), E22
(Lemma 10.1) and the constants of Props 6.1-6.2, Lemmas 6.3, 6.6, which `Draft/Section6.lean` now states in the
printed α₀-uniform order (E31, commit 1d4135b). Tasks `alpha-uniformity` and `alpha-uniformity-r2` (c2). Source:
`paper/lqg_harmonic_ball-corrected.tex` (tex line numbers below). Lean drafts: `HarmonicBalls/Draft/Section{4,6,10}.lean`.
Inputs used: Fact 2.1 (tex 402-414; `Proposed/LQG.lean`: Weyl scaling `LQGMeasureWeylScaling`, coordinate change
`LQGMeasureCoordChange`, locality), full support I1 (`LQGMeasureFullSupportStmt`), and the GFF facts of tex 355-389.
Two of these are now Lean theorems: the identity μ_h = |x|^{-α₀γ} μ_{h^ℂ} on ℂ \ {0}
(`singularWeightStep_of_weyl`, `Proofs/Sec2/SingularWeight.lean`) and I1 from the staged literature inputs
(`lqgMeasureFullSupportStmt_of_literature`, `Proofs/Sec2/Assembly.lean`).

Setting: γ ∈ (0,2) and α₀ ∈ (-∞, Q) are fixed once and for all (tex 373-377), h = h^ℂ - α₀ log|·| (tex 383).
"Uniform in α₀" means one constant for all α₀ < Q (quantifier order ∃ const ∀ α₀). In Section 6 the exponent β⁻ of
eq:alternate-size (tex 1128-1131) is a fixed number > (2+γ)²/2, quantified with γ in the drafts.

## Verdicts

| item | printed dependence | verdict | decisive step | tex lines |
|---|---|---|---|---|
| [C8], E9: Lemma 4.2 | α = α(γ) | **counterexample** as α₀ ↑ Q. Every admissible exponent satisfies α ≤ γ(Q-α₀) | §1, Steps 2-3: Poisson-Jensen at 0 and μ_h(B_s(0)) = s^{γ(Q-α₀)} e^{γ h^ℂ_s(0)} M_s | 717-727 |
| [C25], E28: Lemma 6.4 | a = a(b,p,γ) | **counterexample** as α₀ → -∞, at the admissible (r,z) = (1,0) for b < 0.41 and at (1,10) for every b | §2, Step 3: the weight \|x\|^{\|α₀\|γ} sends the mass fraction of a set with a fixed crossing probability to 0 | 1185-1220 |
| [C26], E30: Lemma 6.7, C₁⁻ | C₁^± = C₁^±(a,γ,p) | **counterexample for C₁⁻** as α₀ → -∞, at the admissible (ρ,x₀) = (1,0) and (1,10), whatever a, C₁⁺, C₂^±, N₁ are. C₁⁺, C₂^± not refuted | §5, Steps 2-3: M_1(0) is read on B_{1/8}(3/4), where the weight is ≤ (7/8)^{\|α₀\|γ}, while μ_h(𝔸_{1/4,2}(0)) ≥ 1.9^{\|α₀\|γ}(…) | 1307-1341, 1128-1131 |
| E31: Lemma 6.3 | a = a(b,γ), c universal | **true** (printed order); the paper's proof gives only a(b,γ,α₀) | §6.2: α₀ = 0 count on r ∈ [ε, ε^{3/4}] (S-SubRange) + flat weight (S-Flat) + transfer of E_r (S-Transfer) | 1169-1173, 1278-1291 |
| E31: Lemma 6.6 | a(b,γ); c, C₃ universal; C₁^±, C₂^± (a,γ); N₁(b,γ) | **true** (printed order); the paper's proof gives only α₀-dependent constants | §6.3: as §6.2 with (VG-i)-(VG-iii) | 1296-1299, 1145-1153 |
| E31: Prop 6.1 | α = α(γ), c universal | **true** (printed order) | §6.4: Lemma 6.6 uniform (§6.3) + Lemma 6.11 deterministic (S-Harnack), α = a 2^{-N₀β⁻}/(C₁⁻ ∨ 1) | 1065-1076, 1567, 1855, 1908, 1913 |
| E31: Prop 6.2 | α = α(γ) (setting of 6.1) | **true** (printed order) | §6.4: as Prop 6.1, component form of Lemma 6.11 | 1078-1083 |
| E22: Lemma 10.1 | K = ⌈1/α⌉, α = α(γ) | **true** (printed order); the paper's proof gives only K(γ,α₀): a gap, not a false statement | §3.3 (= §6.5): very good radii ρ ≤ ε^{3/4} ≪ \|x₀\|, where the weight is flat on B_{2ρ}(x₀) | 2496-2545 |
| downstream | — | **α₀ is fixed throughout; no proof needs uniformity in α₀.** [C8], [C25], [C26] lose nothing | §4 | 373-377 |

The pattern. A constant fails to be α₀-uniform exactly when the statement quantifies over all scales at a fixed
location relative to the singularity: the point 0 itself (Lemma 4.2) or annuli at distance ≍ their radius from 0
(Lemmas 6.4, 6.7, "for all r (ρ)"). There the weight |x|^{-α₀γ} has oscillation e^{Θ(|α₀|)} on the annulus. The
multi-scale prevalence statements (Lemmas 6.3, 6.6, Props 6.1-6.2, Lemma 10.1) only need many good scales around each
x₀ ∉ B_{10√ε}, and one may count only the scales ρ ≤ ε^{3/4} ≪ |x₀|, where the weight is flat (§6). Every
counterexample needs |α₀| → ∞ or α₀ ↑ Q: on α₀ ∈ [-A, Q) the constants of Lemmas 6.4 and 6.7 are uniform (§2, §5).

Lean status. `LeastSupersolutionHolderStmt` (Section4.lean:116, [C8]), `GoodAnnulusProbabilityStmt` (Section6.lean:270,
[C25]) and `VeryGoodAnnulusProbabilityStmt` (Section6.lean:331, [C26]) have the order ∀ α₀ ∃ constant, as the
counterexamples require. `HarnackTypeEstimateStmt` (Section6.lean:206), `HarnackTypeComponentStmt` (:230),
`ManyGoodAnnuliStmt` (:255), `ManyVeryGoodAnnuliStmt` (:311) and `ClusterBoundedCrossingsStmt` (Section10.lean:57) have
the printed order ∃ constant ∀ α₀; §6 shows that these are true and names the steps a proof needs beyond the paper's.

## 1. E9: Lemma 4.2 (odometer:cont, tex 721-727). Counterexample

**Claim.** Let γ ∈ (0,2), α > 0 and α₀ ∈ (Q - α/γ, Q), so that α > γ(Q-α₀). Fix t > 0. Almost surely there is no
C < ∞ with |w^0_t(x) - w^0_t(y)| ≤ C|x-y|^α for all x, y ∈ B_1. (Here w^0_t is the least supersolution
`leastSupersolution μ 1 0 t`, tex 588.) So no α = α(γ) > 0 serves all α₀ < Q, and [C8] needs α ≤ γ(Q-α₀).

*Step 1 (local equation; on the a.s. events of Lemmas 3.1, 3.2 and Prop 4.1).* w := w^0_t is continuous on the
closed unit disc (Lemma 3.1, tex 621-624). There is a random ε > 0 with B_ε(0) ⊂ Λ^0_t (Prop 4.1, tex 676-678,
with z = 0 ∈ B_1). On the open set B_ε(0) ⊂ Λ^0_t we have ∂Λ ∩ B_ε(0) = ∅, so Δw = μ_h there (Lemma 3.2,
tex 631). In particular w is subharmonic on B_ε(0).

*Step 2 (Poisson-Jensen formula at the centre).* For a continuous subharmonic u near the closed disc B̄_r(0) with
Riesz measure Δu (normalization Δ log|·| = 2π δ_0):
(1/2π)∫_0^{2π} u(re^{iθ}) dθ - u(0) = (1/2π) ∫_{B_r(0)} log(r/|y|) Δu(dy)
(Ransford, *Potential Theory in the Complex Plane*, §4.5; Armitage-Gardiner §4.5). The paper's Δ satisfies
ΔG_O(x,·) = -δ_x (tex 631, with G_O the Green function of BM, tex 469), so its Δ is a fixed positive multiple of
the standard one; write c_Δ > 0 for the resulting constant. For r < ε, with log(r/|y|) ≥ log 2 on B_{r/2}(0):
sup_{|x|=r} |w(x) - w(0)| ≥ avg_{∂B_r} w - w(0) ≥ c_Δ log 2 · μ_h(B_{r/2}(0)).
If the Hölder bound held with exponent α, then μ_h(B_{r/2}(0)) ≤ C r^α/(c_Δ log 2) for all r < ε. That is,
limsup_{s↓0} μ_h(B_s(0)) s^{-α} < ∞.

*Step 3 (law of the mass of small balls at the singularity).* Let s ∈ (0,1). The coordinate change for x ↦ sx
(Fact 2.1 IV, tex 412) and Weyl scaling by the constant Q log s + h_s(0) (Fact 2.1 III) give
μ_h(B_s(0)) = s^{γQ} e^{γ h_s(0)} M_s, where M_s := μ_{h(s·) - h_s(0)}(B_1(0)).
The circle average of -α₀ log|·| on ∂B_s(0) is -α₀ log s, so h_s(0) = h^ℂ_s(0) - α₀ log s. Hence
μ_h(B_s(0)) = s^{γ(Q-α₀)} e^{γ h^ℂ_s(0)} M_s.
By eq:h-coordinate-change (tex 386) and the measurability of the field-to-measure map (Fact 2.1 II),
M_s has the law of μ_h(B_1(0)). That law is supported in (0,∞): finiteness holds since μ_h is Radon, and
positivity by full support I1. Moreover h^ℂ_s(0) ~ N(0, log(1/s)) for the normalization h^ℂ_1(0) = 0 (tex 379).
Put δ := α - γ(Q-α₀) > 0 and fix K ≥ 1. A union bound gives
P[μ_h(B_s(0)) < K s^α] ≤ P[N(0,1) < -(δ/2γ) (log 1/s)^{1/2}] + P[μ_h(B_1(0)) < K s^{δ/2}],
and both terms tend to 0 as s ↓ 0. So F_K := {∃ s ∈ (0,1/K) : μ_h(B_s(0)) ≥ K s^α} has P(F_K) = 1, since it
contains each of these events. On ∩_K F_K we get limsup_{s↓0} μ_h(B_s(0)) s^{-α} = ∞, which contradicts Step 2.
This proves the claim, so the conclusion of Lemma 4.2 with exponent α has probability 0, not just less than 1. ∎

Remarks.
- The obstruction sits at the singularity and only as α₀ ↑ Q. It matches [C1]: the upper volume exponent at z = 0
  is γ(Q-α₀) (E1). The same argument bounds the random exponent of Prop 2.5 (`GreenPotentialLiouvilleHolderStmt`)
  for f = 1 and any O ∋ 0. That draft has a random exponent, so nothing there is false.
- For α₀ ≤ α₁ < Q one expects a uniform exponent below min{(2-γ)²/2, γ(Q-α₁)}, by the Campanato route of Prop 2.5.
  This is not needed (§4) and not proved here.

## 2. E28: Lemma 6.4 (lemma:annulus-hit, tex 1185-1189). Counterexample

Lemma 6.4: for b, p ∈ (0,1) there is a = a(b,p,γ) with P[E_r(z;a,b)] ≥ p for all r > 0 and all z with
dist(𝔸_{3r,5r}(z), 0) ≥ r/100. Here E_r(z;a,b) is eq:good-annulus-harmonic (tex 1117-1121).

*Step 1 (reading of the event).* Write A := 𝔸_{3r,5r}(z), τ_A and τ_Y for the exit times, and u ∈ ∂B_{4r}(z).
"B^u exits A before exiting Y" can only mean τ_A ≤ τ_Y, the reading recorded in `Defs/Annuli.lean` (slip at tex
1120). Indeed Y ⊂ A forces τ_Y ≤ τ_A, so the strict reading τ_A < τ_Y would make the probability 0 and E_r(z)
trivial.

*Step 2 (a set with a fixed crossing probability).* Take r = 1 and z = 0, which is admissible since
dist(𝔸_{3,5}(0), 0) = 3 ≥ 1/100. Let Y := 𝔸_{3,4.9}(0) and |u| = 4. If B^u hits ∂B_3 before ∂B_{4.9}, then
τ_A = τ_Y. Hence P[τ_A ≤ τ_Y] ≥ log(4.9/4)/log(4.9/3) = 0.4136… (the harmonic function log(4.9/|x|)/log(4.9/3)).
So for b < 0.4136 we have E_1(0;a,b) ⊂ {μ_h(Y) > a μ_h(A)}.

*Step 3 (Weyl scaling).* On the annulus 𝔸_{2,6}(0), h = h^ℂ + f with f := -α₀ log max{|·|, 1}. This f is continuous
on ℂ and equals -α₀ log|·| there. Locality and Weyl scaling (Fact 2.1 II, III; also tex 2211) give
μ_h = |x|^{-α₀γ} μ_{h^ℂ} on 𝔸_{2,6}(0). For α₀ < 0 the weight |x|^{|α₀|γ} is increasing in |x|, so
μ_h(Y)/μ_h(A) ≤ (4.9/4.95)^{|α₀|γ} R, with R := μ_{h^ℂ}(𝔸_{3,4.9}(0)) / μ_{h^ℂ}(𝔸_{4.95,5}(0)).
R is a.s. in (0,∞): the numerator is finite because μ is Radon, and the denominator is positive by full support I1.
The law of R does not depend on α₀.

*Step 4.* P[E_1(0;a,b)] ≤ P[R > a (4.95/4.9)^{|α₀|γ}] → 0 as α₀ → -∞. So for b ∈ (0, 0.41], p ∈ (0,1) and any
a ∈ (0,1), some α₀ < 0 gives P[E_1(0;a,b)] < p. Hence no a(b,p,γ) serves all α₀ < Q. ∎

*Strengthening: every b ∈ (0,1), with the configuration actually used.* The proof of Lemma 6.3 uses Lemma 6.4 for
z ∈ ℂ \ B_{10r} (tex 1289). Take r = 1 and z = 10, which is admissible (dist = 5). Let p₀ := 15 be the point of
∂B_5(z) farthest from 0. Put Cap_δ := A ∩ {|x| ≥ 15-δ} and Y := A \ Cap_δ. Cap_δ lies in B̄_{d}(p₀) with
d = d(δ) → 0 as δ → 0, because points y = x - z with |y| ≤ 5 and |x| ≥ 15-δ satisfy y·(z/|z|) ≥ 5 - 1.5δ.
BM from u ∈ ∂B_4(z) must hit B̄_d(p₀) before leaving B_{10}(p₀) ⊃ A, and |u - p₀| ≥ 1. So
P[τ_A ≤ τ_Y] ≥ 1 - log 10/log(10/d) → 1. Meanwhile
μ_h(Y)/μ_h(A) ≤ ((15-δ)/(15-δ/2))^{|α₀|γ} · μ_{h^ℂ}(A)/μ_{h^ℂ}(A ∩ {|x| > 15-δ/2}) → 0 as α₀ → -∞.
The denominator is a.s. positive by I1, since A ∩ {|x| > 15-δ/2} is a nonempty open set. So the obstruction is not
z = 0 itself: any annulus at distance ≍ r from the singularity fails as α₀ → -∞. This includes the uses at tex 1289
and in Lemma 6.7 Step 1 (tex 1321-1345, G19).

*What does hold.* For α₀ ∈ [-A, Q), a uniform a exists. If dist(𝔸_{3r,5r}(z), 0) ≥ r/100, then
sup/inf of |x|^{-α₀γ} on 𝔸_{3r,5r}(z) is ≤ 1001^{|α₀|γ}. (If |z| ≤ 2.99r then |x| ∈ [r/100, 7.99r]; if
|z| ≥ 5.01r then the ratio (|z|+5r)/(|z|-5r) is ≤ 1001.) So the corrected Step 1 (G19(i),(ii)) gives
a := a'·1001^{-max(A,Q)γ}, where a' is the α₀ = 0 constant. As α₀ ↑ Q there is no obstruction for 6.4: the
weight stays bounded on annuli away from 0. [C25] (a = a(b,p,γ,α₀)) is the natural correction.

## 3. E22: Lemma 10.1 (lemma:cannot-cross, tex 2496-2545)

Printed: K := ⌈1/α⌉ with α = α(γ) ∈ (0,1) "as in Prop 6.2" (tex 2499).

*3.1 What the paper's proof gives.* The proof (tex 2505-2545) takes a very good ρ ∈ [ε, ε^{1/2}] from Prop 6.1
plus Borel-Cantelli (tex 2505-2507). It then uses Prop 6.2 to give each crossing component mass
≥ α μ_h(𝔸_{ρ/2,ρ}(x₀)), and concludes there are ≤ 1/α of them. The α is that of eq:choice-of-alpha,
α = a 2^{-N₀β⁻}/(C₁⁻ ∨ 1) (tex 1855). Here a, C₁^±, C₂^±, N₀ come from Lemmas 6.6/6.7 (tex 1296-1316). Those get their
α₀-dependence from the Weyl reductions (tex 1198-1217, 1321-1341; G19(iii)), and §2 shows that dependence is
genuine for Lemmas 6.4/6.7 as stated "for all r (ρ)". The same computation as §2 refutes an α₀-uniform C₁⁻ in
Lemma 6.7 at the admissible x₀ = 0 (dist(𝔸_{ρ/4,2ρ}(0), 0) = ρ/4). As α₀ → -∞,
M^h_1(0)/μ_h(𝔸_{1/4,2}(0)) ≤ (5/(4·1.95))^{|α₀|γ} M^{h^ℂ}_1(0)/μ_{h^ℂ}(𝔸_{1.95,2}(0)) → 0 (details: §5).
So the paper's proof gives only **K = K(γ, α₀)**. This matches the Section 6 drafts (∀ α₀ ∃ α) but not
`ClusterBoundedCrossingsStmt`, which is drafted with α before α₀.

*3.2 No counterexample by the E9/E28 mechanism.* That mechanism needs either the singular point itself (E9) or an
annulus at distance ≍ its radius from 0 (E28). In Lemma 10.1 we have w ∉ B_{20√ε}. The radius ρ ∈ [ε, ε^{1/2}] is
ours to choose, and "each small enough ε" has a random threshold that may depend on α₀. By the definition at tex
338-339 (P ≥ 1 - O(r^p)), the same holds for every "polynomially high probability". Choosing ρ ≤ ε^{3/4} makes
ρ/|x₀| ≤ ε^{1/4}/10 → 0, so the weight is flat at the relevant scales.

*3.3 Localization proof that K can be chosen depending on γ only.* Fix α₀. Let P = (N₀, a, b, C₁^±, C₂^±, C₃) and
β⁻ = β⁻(γ) > (2+γ)²/2 be the parameters of the α₀ = 0 instance of the proof of Prop 6.1 (Lemma 6.6 at α₀ = 0;
b by eq:choice-of-b, tex 1908). Put P' := (N₀', a/2, b, C₁⁻/2, 2C₁⁺, C₂⁻/2, 2C₂⁺, C₃) with
N₀' := max{N₀, N₁(a/2, β⁻, C₁⁻/2, 2C₂⁺)} (eq:choice-of-N1, tex 1913). Raising N₀ only weakens (VG-iii). P' depends on γ
only.
- **(L1) Flatness.** Let |x₀| ≥ 10√ε, ρ ∈ [ε, ε^{3/4}] and u := 2ρ/|x₀| ≤ ε^{1/4}/5. For x ∈ B_{2ρ}(x₀) the weight
  g(x) := (|x|/|x₀|)^{-α₀γ} satisfies |log g| ≤ |α₀|γ·(-log(1-u)) ≤ 1.25 u|α₀|γ ≤ |α₀|γ ε^{1/4}/4. So
  g ∈ [2^{-1/2}, 2^{1/2}] once ε ≤ ε₀(α₀,γ) := (2 log 2/(|α₀|γ))^4.
- **(L2) Deterministic transfer.** On B_{2ρ}(x₀), μ_h = |x₀|^{-α₀γ} g μ_{h^ℂ}, by locality and Weyl scaling as in §2,
  Step 3. Each of (VG-i)-(VG-iii) involves μ only on B_{2ρ}(x₀): M_ρ uses balls in B_{5ρ/4}(x₀), SG uses
  𝔸_{ρ/4,2ρ}(x₀), and the annuli 𝔸_{3r,5r}(z) of (VG-iii) have z ∈ 𝔸_{ρ/2,ρ}(x₀) and r ≤ 2^{-N₀/2}ρ. Each condition is
  invariant under μ ↦ λμ (for E_r see tex 1290). Under μ ↦ gμ with sup g/inf g ≤ 2, each ratio moves by a factor
  ≤ 2, and BM probabilities do not involve μ. Hence E̅_ρ(x₀; P)[μ_{h^ℂ}] ⊂ E̅_ρ(x₀; P')[μ_h].
- **(L3) Counting at α₀ = 0 on the sub-range.** Run the proof of Lemma 6.6 (Lemma 6.5 iteration, tex 1262-1291,
  1371, with Lemma 6.7 at α₀ = 0) on the ≈ (1/4) log₈ ε^{-1} radii in [ε, ε^{3/4}] ∩ {8^{-n}} instead of
  [ε, ε^{1/2}]. With polynomially high probability, every grid x₀ ∈ B_{1+ε} \ B_{10√ε} then has ≥ c'' log ε^{-1}
  radii ρ ∈ [ε, ε^{3/4}] with E̅_ρ(x₀; P)[μ_{h^ℂ}], for a universal c'' > 0. The exponent of Lemma 6.5 is free, which
  beats the O(ε^{-2}) union bound exactly as at tex 1282-1291.
- **(L4) α₀-free Harnack constant.** The audit of tex 1386-1955 found that Lemma 6.11 is "purely deterministic"
  (tex 1600). It uses μ only on B_{2ρ}(x₀), and nothing in tex 1386-1955 mentions α₀, the origin or the weight. Its
  constants are explicit: α = a 2^{-N₀β⁻}/(C₁⁻ ∨ 1) (tex 1855), b = 2^{-2β⁻/((C'C₃)∨1)} (tex 1908), and
  N₁(a, β⁻, C₁⁻, C₂⁺, C₄, c) (tex 1913). The constants C', C₄, c come from Lemmas 6.13, 6.8, 6.10 and are geometric.
  β⁻ is only a chosen exponent there (eq:ball-volume is not used). Lines 1600, 1855, 1908 and 1913 were checked
  directly. Lemma 6.11 for μ_h at P' therefore gives α' := α(P', β⁻), which depends on γ only.

With (L1)-(L4), the proof of Lemma 10.1 at tex 2505-2545 runs verbatim with ρ ∈ [ε, ε^{3/4}] ⊂ [ε, ε^{1/2}] and
Borel-Cantelli over ε = 2^{-n}, n ≥ max{M₀, log₂ ε₀^{-1}}. It gives **K = ⌈1/α'⌉ = K(γ)**. The same argument shows
that the printed γ-only constants of Lemma 6.3 (a(b,γ)), Lemma 6.6 and Prop 6.1 (α(γ), universal c) are true: these
are multi-scale statements over x₀ ∉ B_{10√ε}. The α₀-independent gaps of the paper's own proofs (G18, G28, G32, the
constant slips at 1859, 1899, 1916) are unaffected. The ε^{3/4} cap is also compatible with the G32(d) fix
(ε' = 2^{-n} ≥ ε).

*Verdict E22.* The printed uniformity is **true** (proof §3.3). The paper's proof gives only K(γ,α₀): this is a gap,
not a false statement. Recommendation: keep `ClusterBoundedCrossingsStmt` uniform as printed, and register the gap
"10.1 needs (L1)-(L4)" in GRAPH. Alternatively, change the draft to ∀ α₀ ∃ α. That form follows from the drafted
Prop 6.1/6.2 by the printed proof, and nothing downstream needs more (§4). It would, however, be weaker than the
printed true statement.

## 4. Downstream: α₀ is fixed; nothing needs uniformity

- α₀ is fixed once (tex 373, 377) and every result is about that h. The paper never takes a limit, supremum or
  infimum over α₀. The only other values ever used are two fixed instances:
  - α₀ = 0: the reductions in Lemma 6.4 (tex 1195-1220), Lemma 6.7 (tex 1318-1349), Section 11 Step 1 (tex 2834)
    and Lemma 11.12 (tex 3136-3137);
  - α₀ = γ: Lemma 8.3 (lemma:doubling-alpha), applied inside the proof of Lemma 8.2 (tex 2220) at μ_h-typical
    points (DS14 Lemma A.10, tex 2213). Lemma 8.3 uses Lemma 6.7 at x₀ = 0 (tex 2175-2178), which is admissible.
    The constants are those at α₀ = γ, so they depend on γ.
  Statements quantified ∀ α₀ < Q ∃ constants (all Draft Stmts except 10.1) supply both instances.
- Consumers of the α of Prop 6.1, at the fixed α₀:
  - Prop 7.1 (tex 1969-1996), Prop 7.2 (tex 2031-2078) and Lemma 10.1 (tex 2505-2519);
  - Thm 5.5, through Props 5.1-5.4. Its scale invariance (Lemma 5.7, tex 885-899) rescales about 0 and keeps α₀.
  Each consumer needs α to be deterministic and positive, nothing more. Section 10 needs only K < ∞.
- Order of constants under [C25]. Only a, C₁^±, C₂^± (and N₁) gain α₀. C₃ and c stay universal: they come from
  Lemma 6.3's c and Lemma 6.5, and the Weyl steps change only a, C₁^±, C₂^±. So the order of G28,
  C₃ → b(γ, C₃, β⁻) (Lemma 6.11) → (a, C^±, N₀) (Lemma 8.3 at α₀ = γ, Lemma 6.6 at α₀), has no cycle.
- Same-type slip, harmless: Section 11 Step 2 (tex 2857-2866) calls the Weyl constant "universal" under only
  dist(𝔸_{r,6r}(z), 0) > r/100. It is universal (≤ 2, say) once n ≥ N(z, α₀), by (L1). The proof is free to take N(z)
  that large.
- **Conclusion.** [C8] (α = α(γ,α₀), with necessarily α ≤ γ(Q-α₀)) and [C25] (a = a(b,p,γ,α₀)) lose nothing
  downstream. Both are forced: §1 and §2 are counterexamples to the printed uniformity. For Lemma 10.1, Prop 6.1,
  Lemma 6.3 and Lemma 6.6 the printed uniformity is true (§3.3), but nothing downstream uses it.

## 5. C26 / E30: Lemma 6.7 (lemma:very-good-annuli-hit, tex 1307-1341). Counterexample for C₁⁻

Lemma 6.7: for b, p ∈ (0,1) there are a = a(b,p,γ), C₁^±, C₂^± depending on a, γ, p, a universal C₃ and
N₁(b,p,γ) with P[Ē_ρ(x₀)] ≥ p for all N₀ ≥ N₁, all ρ > 0 and all x₀ with dist(𝔸_{ρ/4,2ρ}(x₀), 0) ≥ ρ/100. Here
Ē_ρ(x₀) is (VG-i)-(VG-iii) (tex 1145-1153) and (VG-i) reads C₁⁻ ≤ M_ρ(x₀)/μ_h(𝔸_{ρ/4,2ρ}(x₀)) ≤ C₁⁺, with
M_ρ(x₀) = inf_{z ∈ 𝔸_{ρ/2,ρ}(x₀)} inf_{r ∈ (0,ρ/4)} μ_h(B_r(z)) (r/ρ)^{-β⁻} (eq:alternate-size, tex 1130).

**Claim.** Fix γ ∈ (0,2), β⁻ > (2+γ)²/2 and p ∈ (0,1). For every C > 0 there is α₀ < 0 with
P[M_1(0) ≥ C μ_h(𝔸_{1/4,2}(0))] < p. Hence no C₁⁻ chosen before α₀ works in Lemma 6.7, even if a, C₁⁺, C₂^±, N₁
may depend on α₀. In particular C₁⁻ = C₁⁻(a,γ,p) with a = a(b,p,γ), as printed, is false.

*Step 1 (admissible configuration).* Take ρ = 1 and x₀ = 0. Then dist(𝔸_{1/4,2}(0), 0) = 1/4 ≥ 1/100, so Lemma 6.7
applies. By (VG-i), Ē_1(0) ⊂ {M_1(0) ≥ C₁⁻ μ_h(𝔸_{1/4,2}(0))}.

*Step 2 (M is an infimum).* The point z₁ := 3/4 lies in 𝔸_{1/2,1}(0), and r₁ := 1/8 ∈ (0, 1/4). Hence
M_1(0) ≤ μ_h(B_{1/8}(3/4)) · 8^{β⁻}.

*Step 3 (Weyl scaling).* Almost surely μ_h = |x|^{-α₀γ} μ_{h^ℂ} on ℂ \ {0}. This follows from locality and Weyl scaling
(Fact 2.1 II-III) with the continuous functions -α₀ log max{|·|, η}, η ↓ 0; it is the Lean theorem
`singularWeightStep_of_weyl`. For α₀ < 0 the weight |x|^{|α₀|γ} is increasing in |x|. On B_{1/8}(3/4) we have
|x| ≤ 7/8, and on 𝔸_{1.9,2}(0) ⊂ 𝔸_{1/4,2}(0) we have |x| ≥ 1.9. Therefore
μ_h(B_{1/8}(3/4)) ≤ (7/8)^{|α₀|γ} μ_{h^ℂ}(B_{1/8}(3/4)) and μ_h(𝔸_{1/4,2}(0)) ≥ 1.9^{|α₀|γ} μ_{h^ℂ}(𝔸_{1.9,2}(0)),
and with Step 2,
M_1(0)/μ_h(𝔸_{1/4,2}(0)) ≤ 8^{β⁻} (7/15.2)^{|α₀|γ} R₁, where R₁ := μ_{h^ℂ}(B_{1/8}(3/4))/μ_{h^ℂ}(𝔸_{1.9,2}(0)).
R₁ is a.s. in (0, ∞): the numerator is finite because μ_{h^ℂ} is Radon, and the denominator is positive by full support
I1 at α₀ = 0, since 𝔸_{1.9,2}(0) is a nonempty open set. The law of R₁ does not depend on α₀: h^ℂ is the same field
for every α₀.

*Step 4.* Fix C > 0. By Steps 1-3,
P[M_1(0) ≥ C μ_h(𝔸_{1/4,2}(0))] ≤ P[R₁ ≥ C 8^{-β⁻} (15.2/7)^{|α₀|γ}] → 0 as α₀ → -∞,
because R₁ < ∞ a.s. and (15.2/7)^{|α₀|γ} → ∞. Choose α₀ < 0 with this probability < p. ∎

Remarks.
- *Generic location.* The obstruction is not the point 0. Take ρ = 1 and x₀ = 10, which is admissible:
  dist(𝔸_{1/4,2}(10), 0) = 8. The point z₁ = 9.25 lies in 𝔸_{1/2,1}(10), and B_{1/8}(9.25) ⊂ {|x| ≤ 9.375}. The set
  U := 𝔸_{1/4,2}(10) ∩ {|x| > 11.9} is nonempty and open. As in Step 3,
  M_1(10)/μ_h(𝔸_{1/4,2}(10)) ≤ 8^{β⁻} (9.375/11.9)^{|α₀|γ} μ_{h^ℂ}(B_{1/8}(9.25))/μ_{h^ℂ}(U) → 0.
  So every annulus at distance ≍ ρ from 0 fails as α₀ → -∞. Lemma 6.7 is used at such annuli: at x₀ = 0 in Lemma 8.3
  (tex 2175-2178, at α₀ = γ), and in the proof of Lemma 6.6 for x₀ with |x₀| ≍ 10√ε and ρ ≍ √ε.
- *What does hold.* If dist(𝔸_{ρ/4,2ρ}(x₀), 0) ≥ ρ/100, the sets used by (VG-i)-(VG-iii) lie in
  the closure of 𝔸_{ρ/4,2ρ}(x₀): M_ρ uses B_r(z) ⊂ 𝔸_{ρ/4,5ρ/4}(x₀), and for N₀ ≥ 10 the annuli 𝔸_{3r,5r}(z) of
  (VG-iii) lie in 𝔸_{ρ/4,2ρ}(x₀). Every point of that annulus has |x| ≥ ρ/100. Since 0 is not in its closure,
  either |x₀| < ρ/4, and then |x| ≤ 9ρ/4, or |x₀| ≥ 2ρ + ρ/100, and then |x| ∈ [|x₀| - 2ρ, |x₀| + 2ρ], a ratio
  ≤ 401. So the weight has sup/inf ≤ 401^{|α₀|γ} on these sets, and the Weyl reduction of tex 1321-1341 gives, for α₀ ∈ [-A, Q), the constants
  C₁⁻ := C₁⁻(0)·401^{-max(A,Q)γ}, C₁⁺ := C₁⁺(0)·401^{max(A,Q)γ} and the same for C₂^±; a as in §2 "What does hold".
  As α₀ ↑ Q there is no obstruction for Lemma 6.7.
- *The other constants.* As α₀ → -∞ the ratio in (VG-i) tends to 0 at these configurations, so C₁⁺ is not refuted by
  this mechanism. The mass of 𝔸_{1/4,2}(0) concentrates in a shell of width O(1/|α₀|) at ∂B_2, where
  G_{B_2(0)}(x, ·) vanishes. This suggests that C₂⁻ in (VG-ii) is not α₀-uniform either. That is not proved here,
  and C₁⁻ suffices for [C26].
- *Consequence for the proof of Lemma 6.6.* That proof combines Lemma 6.7 with Lemma 6.5 at every x₀ ∉ B_{10√ε}
  and every ρ ∈ [ε, ε^{1/2}], including the pairs with ρ ≍ |x₀|. At those pairs only α₀-dependent constants are
  available. So the printed proof of Lemma 6.6 gives only α₀-dependent constants. §6.3 repairs this.
- [C26] (C₁^±, C₂^± = C(a,γ,p,α₀)) is the minimal correction. Downstream α₀ is fixed (§4), and the constants of Lemma
  6.7 enter only Lemma 6.6 and Lemma 8.3 at fixed α₀, so the order of constants (§4, G28) has no cycle.

## 6. E31: the printed α₀-uniform constants of Lemmas 6.3, 6.6 and Props 6.1, 6.2 are true

The drafts state these results in the printed order (constants before α₀). The paper's proofs give only
α₀-dependent constants: each goes through Lemma 6.4 or Lemma 6.7 at all scales, and §2 and §5 show that those
constants genuinely depend on α₀. The printed statements are nevertheless true, by the localization argument of §3.3.
It is set out here as four named steps (candidate Lean step Props) and then applied to each item.

### 6.1 The four steps

Notation: P₀ := (N₀, a, b, C₁^±, C₂^±, C₃) are the parameters of the α₀ = 0 instance; β⁻ > (2+γ)²/2 is fixed;
μ₀ := μ_{h^ℂ} and μ := μ_h live on the same probability space (`LQGMeasureExistence` at α₀ = 0).

- **S-Flat (deterministic).** Let |x₀| ≥ 10√ε, ρ ≤ ε^{3/4} and u := 2ρ/|x₀| ≤ ε^{1/4}/5. For x ∈ B̄_{2ρ}(x₀) the
  weight g(x) := (|x|/|x₀|)^{-α₀γ} satisfies |log g(x)| ≤ |α₀|γ·(-log(1-u)) ≤ 1.25 u|α₀|γ. So
  sup g/inf g ≤ 2 on B̄_{2ρ}(x₀) once ε ≤ (2 log 2/(|α₀|γ))^4. For the annuli 𝔸_{3r,5r}(z) of Lemma 6.3 with
  |z| ≥ 10√ε and r ≤ ε^{3/4}, the same computation with u := 5r/|z| ≤ ε^{1/4}/2 gives sup/inf ≤ 2 once
  ε ≤ (log 2/(1.25|α₀|γ))^4. Both hold for ε ≤ ε₀(α₀,γ) := min{1/40, (log 2/(2|α₀|γ))^4} (the bound
  -log(1-u) ≤ 1.25u needs u ≤ 1/5).
- **S-Transfer (deterministic).** Let ν' = g·ν on B̄_{2ρ}(x₀) with sup g/inf g ≤ 2. Then
  E_r(z; a, b)[ν] ⊂ E_r(z; a/2, b)[ν'] for every annulus 𝔸_{3r,5r}(z) ⊂ B̄_{2ρ}(x₀), and
  Ē_ρ(x₀; P₀)[ν] ⊂ Ē_ρ(x₀; P₀')[ν'] with P₀' := (N₀, a/2, b, C₁⁻/2, 2C₁⁺, C₂⁻/2, 2C₂⁺, C₃). Reason: E_r and
  (VG-i)-(VG-iii) use the measure only on B̄_{2ρ}(x₀) (M_ρ on B_{5ρ/4}(x₀), SG_ρ on 𝔸_{ρ/4,2ρ}(x₀), and (VG-iii) on
  annuli 𝔸_{3r,5r}(z) with z ∈ 𝔸_{ρ/2,ρ}(x₀), r ≤ 2^{-N₀/2}ρ, inside B_{2ρ}(x₀) for N₀ ≥ 5). Each is invariant under
  ν ↦ λν (tex 1290). Under ν ↦ gν each mass ratio moves by a factor ≤ 2, and the Brownian probabilities do not
  involve the measure. With S-Flat and the Weyl identity (Lean `singularWeightStep_of_weyl`), this applies to
  ν = |x₀|^{-α₀γ} μ₀ and ν' = μ on B̄_{2ρ}(x₀) ⊂ ℂ \ {0}.
- **S-SubRange (α₀ = 0, probabilistic).** For the field h^ℂ: with polynomially high probability as ε → 0, every grid
  point (tex 1172, 1298) has at least c₀ log ε^{-1} radii in [ε, ε^{3/4}] ∩ {7^{-n}} (resp. {8^{-n}}) at which
  E_r(z; a, b)[μ₀] (resp. Ē_ρ(x₀; P₀)[μ₀]) occurs, where c₀ > 0 is universal. Proof: the paper's proofs of Lemmas
  6.3 and 6.6 at α₀ = 0, with K = ⌊(1/4) log₇ ε^{-1}⌋ (resp. log₈) radii instead of ⌊(1/2) log ε^{-1}⌋. At α₀ = 0,
  Lemmas 6.4 and 6.7 need no Weyl step, and their constants are those of Step 2 of their proofs. Lemma 6.5 (tex
  1262-1276) has a free exponent α. Choosing α universal and large beats the O(ε^{-2}) union bound, exactly as at tex
  1282-1291.
- **S-Harnack (deterministic, = (L4) of §3.3).** Lemma 6.11 (tex 1567) is purely deterministic (tex 1600), uses μ only
  on B_{2ρ}(x₀), and gives the Harnack-type implication of Props 6.1/6.2 for every very good annulus with parameters
  P, with α = a 2^{-N₀β⁻}/(C₁⁻ ∨ 1) (eq:choice-of-alpha, tex 1855), provided b = 2^{-2β⁻/((C'C₃)∨1)}
  (eq:choice-of-b, tex 1908) and N₀ ≥ N₁(a, β⁻, C₁⁻, C₂⁺, C₄, c) (eq:choice-of-N1, tex 1913). C', C₄, c are geometric
  (Lemmas 6.13, 6.8, 6.10). Nothing in tex 1386-1955 mentions α₀ or the origin.

### 6.2 Lemma 6.3 (a = a(b,γ), c universal)

Let a₀ = a₀(b,γ) and c₀ be the α₀ = 0 constants of S-SubRange. Put a := a₀/2 and c := c₀/2. Fix α₀. For
ε ≤ ε₀(α₀,γ), on the S-SubRange event, every grid z ∈ B_{1+ε} \ B_{10√ε} has ≥ c₀ log₇ ε^{-1} ≥ c log₇ ε^{-1/2}
radii r ∈ [ε, ε^{3/4}] ⊂ [ε, ε^{1/2}] with E_r(z; a₀, b)[μ₀]. By S-Flat and S-Transfer, E_r(z; a, b)[μ] occurs at
these radii. The failure probability is that of S-SubRange, polynomial in ε. The threshold ε₀(α₀,γ) is absorbed by
`PolyHighProb`, whose r₀ is chosen after α₀ in the draft. So `ManyGoodAnnuliStmt` holds in the printed order.

### 6.3 Lemma 6.6 (a(b,γ); c, C₃ universal; C₁^±, C₂^± depending on a, γ; N₁(b,γ))

The argument is the same with Ē_ρ(x₀) in place of E_r(z). Take a, C₁^±, C₂^±, C₃, N₁ from S-SubRange at α₀ = 0 and
output P₀' (S-Transfer); N₁ and C₃ are unchanged. For N₀ ≥ N₁ and ε ≤ ε₀(α₀,γ), every grid x₀ ∉ B_{10√ε} has
≥ c₀ log₈ ε^{-1} radii ρ ∈ [ε, ε^{3/4}] with Ē_ρ(x₀; P₀)[μ₀], hence with Ē_ρ(x₀; P₀')[μ]. So
`ManyVeryGoodAnnuliStmt` holds in the printed order. (By §5, the printed proof via Lemma 6.7 at all ρ ∈ [ε, ε^{1/2}]
does not give this.)

### 6.4 Props 6.1 and 6.2 (α = α(γ), c universal)

Fix β⁻ := (2+γ)²/2 + 1 and b from eq:choice-of-b (it depends on β⁻ and the universal C₃, C'). Take the uniform
constants of §6.3 for this b and set N₀ := max{N₁, N₁(a/2, β⁻, C₁⁻/2, 2C₂⁺, C₄, c)} (eq:choice-of-N1). Define the
events E_ρ(x₀) := Ē_ρ(x₀; P₀')[μ_h] for all ρ ∈ (0,1) and x₀ ∈ ℂ. S-Harnack gives the deterministic implication of
Prop 6.1 (resp. the component form of Prop 6.2, tex 1078-1083, from the same Lemma 6.11) with
α := (a/2) 2^{-N₀β⁻}/((C₁⁻/2) ∨ 1). This depends on γ only. The prevalence clause is §6.3, with c := c₀/2. So
`HarnackTypeEstimateStmt` and `HarnackTypeComponentStmt` hold in the printed order.

### 6.5 Lemma 10.1 (K = ⌈1/α⌉, α = α(γ))

This is §3.3. Use the very good radii ρ ∈ [ε, ε^{3/4}] from §6.3-6.4 at the point x₀ of tex 2505-2507. With α of §6.4,
the proof of tex 2505-2545 gives K = ⌈1/α⌉ = K(γ). So `ClusterBoundedCrossingsStmt` holds in the printed order.

### 6.6 What a Lean proof needs beyond the paper

S-Flat and S-Transfer are elementary and deterministic. The Weyl identity they use is proved
(`Proofs/Sec2/SingularWeight.lean`). S-SubRange is the paper's α₀ = 0 argument on a different range of K scales,
with no new input. S-Harnack is Lemma 6.11 as drafted (`VeryGoodAnnulusHarnackTypeStmt`, Section6.lean:415) at the
parameters P₀'. Recommendation: carve Props 6.1-6.2 and Lemmas 6.3, 6.6 as "α₀ = 0 instance on the sub-range" +
S-Flat + S-Transfer, and register in GRAPH the gap "the printed proofs of 6.3, 6.6, 6.1, 6.2, 10.1 give only
α₀-dependent constants; repaired by localization (AlphaUniformity.md §6)". The α₀-independent gaps G18, G28, G32
and the constant slips at tex 1859, 1899, 1916 are unaffected.
