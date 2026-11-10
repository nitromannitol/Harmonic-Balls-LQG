import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11ah.LocalCert
import HarmonicBalls.FirstPass.S11ah.FailureSet

/-!
# Steps 4 and 5 of the 11.13 local certificate sequence (fp-S11ah-11-13-steps-4-5, owner n4)

Step 4 (`notes/fp-gaps/CHATGPT-n3-Q1-eq34.md` section 5): `S11ah/Cutoff.lean` (cutoff `closedBall z (7·2^{-n}) ⊆ D_loc`,
uniform finite cutoff) and `S11ah/LocalCert.lean` (`FirstPassS11ah.localCert`, the indicator (J)).

Step 5: `S11ah/FailureSet.lean`: `failureSet A c q` (formula (K), in the window-average interface of
`ReferenceNullS11i.refWindowAverage`), its measurability `measurableSet_failureSet` (needs joint measurability `hc` of the
`c n`), and joint measurability of (J) for whole-plane decoders `measurable_localCert_of_decoder`.

OPEN: joint measurability of (J) for the LOCAL decoders `m_D : O → C(D_loc × D_loc, ℝ)` is not proved (see report).
-/
