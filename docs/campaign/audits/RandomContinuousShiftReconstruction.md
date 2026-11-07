# Random continuous shift and full-test reconstruction

Leonardo Bonanno's countable distribution reconstruction, `pairJInv_pairJ`,
and continuous-function distribution `ofCont` are used in this module. For
any measurable space, continuous sample paths and measurable point evaluations
produce a measurable `C(ℂ, ℝ)`-valued map for the compact-open Borel structure.
Bonanno's measurable test-pairing theorem then gives measurability of the
reconstruction of the shifted raw pairing process.

For `IsWholePlaneGFF P hC hcirc`, the distribution equality holds on one
full-measure event: the reconstruction of `addFunPairing (hC ω) (f ω)` is
the original full-test reconstruction plus `ofCont` of the sampled shift.
The event comes from the countable coordinate agreement for the unshifted
field; the equality is proved pointwise on that event. Consequently the shift
may depend on the field, and no simultaneous intersection over shifts is used.
At each fixed test the shifted reconstruction equals the shifted raw pairing
almost surely; that exceptional set may depend on the test. The integral
pairing is the Bochner integral appearing in `addFunPairing`, and its equality
with `ofCont` uses the existing continuous-function distribution theorem.
No new literature input or metric theorem is asserted.
