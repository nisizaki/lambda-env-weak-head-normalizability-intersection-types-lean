import LambdaEnvWH.CDV
import LambdaEnvWH.Main_Results

/-!
# E2: agreement with the classical intersection-type system

Port of `Classical.thy`.

Remark.  Theorem `E2` is obtained through the classical theorem `classical_WHN` (in `CDV`):
both the λenv typability of a pure term and the CDV typability (with an essential type) of
its readback characterize weak-head normalizability of the readback.  It is not a syntactic
translation of derivations between the two systems.

Adaptation: `cess A` is a `Bool`, so the statement has `cess A = true`.
-/

namespace LambdaEnvWH

open dB

theorem E2 {M : Trm} (h : pure M) :
    Typ M ↔ ∃ (Γ : Nat → cty) (A : cty), cty_of Γ (rb M DVar) A ∧ cess A = true :=
  (pure_characterization h).trans classical_WHN

end LambdaEnvWH
