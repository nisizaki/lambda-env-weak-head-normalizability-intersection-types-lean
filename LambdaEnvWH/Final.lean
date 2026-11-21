import LambdaEnvWH.Uniform
import LambdaEnvWH.Classical
import LambdaEnvWH.Examples

/-!
# Summary of the main results

Port of `Final.thy`.

* `main_characterization_full`: `Typ M ↔ CFWHN M ∧ CFWHSN M` for all raw terms.
* `CFWHN_imp_CFWHSN_general`, `WHNF_unique`: weak and strong weak-head normalization
  coincide; the weak-head normal form is unique.
* `E1`, `pure_characterization`: conservativity over the λ-calculus.
* `classical_WHN`, `E2`: the classical CDV characterization and agreement of typability on
  pure terms.

Adaptation: the two conclusions of the Isabelle theorem are the conjunction
`Typ M ↔ CFWHN M` and `Typ M ↔ CFWHSN M`.
-/

namespace LambdaEnvWH

theorem lambda_env_WHN_characterization {M : Trm} :
    (Typ M ↔ CFWHN M) ∧ (Typ M ↔ CFWHSN M) :=
  ⟨main_characterization, ⟨fun h => (main_characterization_full.1 h).2,
    fun h => main_characterization.2 (CFWHSN_imp_CFWHN h)⟩⟩

end LambdaEnvWH
