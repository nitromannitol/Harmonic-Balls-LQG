import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11ah.LocalCert
import HarmonicBalls.FirstPass.S11ah.FailureSet
import HarmonicBalls.FirstPass.S11ah.Radial
import HarmonicBalls.FirstPass.S11ah.LengthTransport
import HarmonicBalls.FirstPass.S11ah.LocalMeasurable

/-!
# Steps 4 and 5 of the 11.13 local certificate sequence (fp-S11ah-11-13-steps-4-5, owner n4)

Step 4 (`notes/fp-gaps/CHATGPT-n3-Q1-eq34.md` section 5): `S11ah/Cutoff.lean` (cutoff `closedBall z (7·2^{-n}) ⊆ D_loc`,
uniform finite cutoff) and `S11ah/LocalCert.lean` (`FirstPassS11ah.localCert`, the indicator (J)).

Step 5: `S11ah/FailureSet.lean`: `failureSet A c q` (formula (K), in the window-average interface of
`ReferenceNullS11i.refWindowAverage`), its measurability `measurableSet_failureSet` (needs joint measurability `hc` of the
`c n`), and joint measurability of (J) for whole-plane decoders `measurable_localCert_of_decoder`.

Local domain (operator item (b)): `S11ah/Radial.lean` (radial homeomorphism `ℂ ≃ₜ ball c R`, identity on
`closedBall c ρ`), `S11ah/LengthTransport.lean` (`IsLengthMetricOn B D`; lift `liftMetric` to a whole-plane
`IsEuclideanLengthMetric`), `S11ah/LocalMeasurable.lean` (`localCertSet`, `measurableSet_localCertSet`,
`measurable_localCertLoc`: joint measurability of the local indicator (J) for a metric on a disc, no locality needed;
`localCertSet_iff_of_locality` uses the named hypothesis `CertificateEventLocality`, operator item (a), to be proved by q1).

OPEN (see reports/n4.md): hypothesis `∀ ω, IsLengthMetricOn (ball c R) (D ω)` for the decoders is not supplied by
`LocalMetricReplacementStmt` (metric identity only P-almost surely), and locality (a) is a named hypothesis.
-/
