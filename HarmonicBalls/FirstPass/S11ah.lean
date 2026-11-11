import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11ah.LocalCert
import HarmonicBalls.FirstPass.S11ah.FailureSet
import HarmonicBalls.FirstPass.S11ah.Radial
import HarmonicBalls.FirstPass.S11ah.LengthTransport
import HarmonicBalls.FirstPass.S11ah.LocalMeasurable
import HarmonicBalls.FirstPass.S11ah.Modified
import HarmonicBalls.FirstPass.S11ah.LengthScale
import HarmonicBalls.FirstPass.S11ah.LQGDecoder
import HarmonicBalls.FirstPass.S11ah.CutoffLength
import HarmonicBalls.FirstPass.S11ah.Step5Closed
import HarmonicBalls.FirstPass.S11ah.Step5Local
import HarmonicBalls.FirstPass.S11ah.Step5Rooted
import HarmonicBalls.FirstPass.S11ah.RootedLengthProperty

/-!
# The 11.13 local certificate: cutoff, failure set and decoders

Step 4: `S11ah/Cutoff.lean` (cutoff `closedBall z (7·2^{-n}) ⊆ D_loc`,
uniform finite cutoff) and `S11ah/LocalCert.lean` (`FirstPassS11ah.localCert`, the indicator (J)).

Step 5: `S11ah/FailureSet.lean`: `failureSet A c q` (formula (K), in the window-average interface of
`ReferenceNullS11i.refWindowAverage`), its measurability `measurableSet_failureSet` (needs joint measurability `hc` of the
`c n`), and joint measurability of (J) for whole-plane decoders `measurable_localCert_of_decoder`.

Local domain: `S11ah/Radial.lean` (radial homeomorphism `ℂ ≃ₜ ball c R`, identity on
`closedBall c ρ`), `S11ah/LengthTransport.lean` (`IsLengthMetricOn B D`; lift `liftMetric` to a whole-plane
`IsEuclideanLengthMetric`), `S11ah/LocalMeasurable.lean` (`localCertSet`, `measurableSet_localCertSet`,
`measurable_localCertLoc`: joint measurability of the local indicator (J) for a metric on a disc, no locality needed;
`localCertSet_iff_of_locality` uses the named hypothesis `CertificateEventLocality`, to be proved).

Failure sets, closed form: `exists_modified_failureSet_closed` has no named
input. The R1 cutoff transfer is proved (`S11ah/CutoffLength.lean`, `cutoffInternalLengthStmt`); the a.s. length property
of the decoders comes from identity (18) and the LQG axiom I (`S11ah/LQGDecoder.lean`); the P-a.s. modification is
`localLengthModification_of_ae`; measurability of the observables is derived from `IsWholePlaneGFF`; locality
is `certificateEventLocality_pinch` (containments of the pinch geometry).
-/
