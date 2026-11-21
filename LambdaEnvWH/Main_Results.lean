import LambdaEnvWH.Readback
import LambdaEnvWH.Soundness

/-!
# Main results

Port of `Main_Results.thy`.

* `main_characterization`: `Typ M ↔ CFWHN M` for all raw λenv terms.
* `E1`: for pure λ-terms, λ-calculus weak-head normalizability of the readback coincides
  with `CFWHN` and with `CFWHSN`.
* `clash_not_Typ`: clashes are not typable.
-/

namespace LambdaEnvWH

open dB

theorem pure_characterization {M : Trm} (h : pure M) : Typ M ↔ lam_WHN (rb M DVar) :=
  main_characterization.trans (E1 h).1.symm

end LambdaEnvWH
