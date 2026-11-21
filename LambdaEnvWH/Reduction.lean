import LambdaEnvWH.Syntax
import LambdaEnvWH.ARS

/-!
# Weak-head reduction: full σ plus head β (with VarR)

Port of `Reduction.thy`.  Weak-head reduction is the union of full σ (all root rules
and all congruences) and head β (`Beta1`, `Beta2` with the congruences `AppL`, `CompL`
and `VarR`).  `VarR` evaluates the environment of a variable lookup.
-/

namespace LambdaEnvWH

open Trm

inductive Sig : Trm → Trm → Prop where
  | Ass (L M N : Trm) : Sig (comp (comp L M) N) (comp L (comp M N))
  | IdL (M : Trm) : Sig (comp iden M) M
  | IdR (M : Trm) : Sig (comp M iden) M
  | DExtn (L : Trm) (x : Var) (M N : Trm) : Sig (comp (extn L x M) N) (extn (comp L N) x (comp M N))
  | VarRef (x : Var) (M N : Trm) : Sig (comp (var x) (extn M x N)) M
  | VarSkip {x y : Var} (M N : Trm) : x ≠ y → Sig (comp (var y) (extn M x N)) (comp (var y) N)
  | DApp (M1 M2 N : Trm) : Sig (comp (app M1 M2) N) (app (comp M1 N) (comp M2 N))
  | AppL {M N : Trm} (L : Trm) : Sig M N → Sig (app M L) (app N L)
  | AppR {M N : Trm} (L : Trm) : Sig M N → Sig (app L M) (app L N)
  | Lam {M N : Trm} (x : Var) : Sig M N → Sig (lam x M) (lam x N)
  | CompL {M N : Trm} (L : Trm) : Sig M N → Sig (comp M L) (comp N L)
  | CompR {M N : Trm} (L : Trm) : Sig M N → Sig (comp L M) (comp L N)
  | ExtnL {M N : Trm} (x : Var) (L : Trm) : Sig M N → Sig (extn M x L) (extn N x L)
  | ExtnR {M N : Trm} (L : Trm) (x : Var) : Sig M N → Sig (extn L x M) (extn L x N)

inductive BetaH : Trm → Trm → Prop where
  | Beta1 (x : Var) (M L N : Trm) : BetaH (app (comp (lam x M) L) N) (comp M (extn N x L))
  | Beta2 (x : Var) (M N : Trm) : BetaH (app (lam x M) N) (comp M (extn N x iden))
  | AppL {M N : Trm} (L : Trm) : BetaH M N → BetaH (app M L) (app N L)
  | CompL {M N : Trm} (L : Trm) : BetaH M N → BetaH (comp M L) (comp N L)
  | VarR {M N : Trm} (x : Var) : BetaH M N → BetaH (comp (var x) M) (comp (var x) N)

def Wh (M N : Trm) : Prop := Sig M N ∨ BetaH M N

abbrev WhSteps : Trm → Trm → Prop := Star Wh

abbrev WHNF (M : Trm) : Prop := normal Wh M
abbrev WHSN (M : Trm) : Prop := SN_at Wh M
abbrev sig_normal (M : Trm) : Prop := normal Sig M

theorem sig_imp_wh {M N : Trm} (h : Sig M N) : Wh M N := Or.inl h
theorem beta_h_imp_wh {M N : Trm} (h : BetaH M N) : Wh M N := Or.inr h

theorem wh_AppL {M N : Trm} (L : Trm) (h : Wh M N) : Wh (app M L) (app N L) := by
  rcases h with h | h
  · exact Or.inl (.AppL L h)
  · exact Or.inr (.AppL L h)

theorem wh_CompL {M N : Trm} (L : Trm) (h : Wh M N) : Wh (comp M L) (comp N L) := by
  rcases h with h | h
  · exact Or.inl (.CompL L h)
  · exact Or.inr (.CompL L h)

theorem wh_VarR {M N : Trm} (x : Var) (h : Wh M N) : Wh (comp (var x) M) (comp (var x) N) := by
  rcases h with h | h
  · exact Or.inl (.CompR _ h)
  · exact Or.inr (.VarR x h)

theorem WHNF_imp_sig_normal {M : Trm} (h : WHNF M) : sig_normal M :=
  fun N hN => h N (Or.inl hN)

/-! ## σ terminates (measure `tlength`) -/

theorem sig_tlength_decrease {M N : Trm} (h : Sig M N) : tlength N < tlength M := by
  induction h with
  | Ass L M N =>
    simp only [tlength]
    have hL := tlength_pos L
    have hN := tlength_pos N
    have : tlength M * (tlength N + 1) + 1 < (tlength M + 1) * (tlength N + 1) := by
      rw [Nat.add_mul]; omega
    calc tlength L * (tlength M * (tlength N + 1) + 1)
        < tlength L * ((tlength M + 1) * (tlength N + 1)) := Nat.mul_lt_mul_of_pos_left this hL
      _ = tlength L * (tlength M + 1) * (tlength N + 1) := by rw [Nat.mul_assoc]
  | IdL M => simp only [tlength]; have := tlength_pos M; omega
  | IdR M => simp only [tlength]; have := tlength_pos M; omega
  | DExtn L x M N =>
    simp only [tlength]; have := tlength_pos N
    rw [Nat.add_mul, Nat.add_mul]; omega
  | VarRef x M N => simp only [tlength]; omega
  | VarSkip M N _ =>
    simp only [tlength]; omega
  | DApp M1 M2 N =>
    simp only [tlength]; have := tlength_pos N
    rw [Nat.add_mul, Nat.add_mul]; omega
  | AppL L _ ih => simp only [tlength]; omega
  | AppR L _ ih => simp only [tlength]; omega
  | Lam x _ ih => simp only [tlength]; omega
  | CompL L _ ih =>
    simp only [tlength]; exact Nat.mul_lt_mul_of_pos_right ih (Nat.succ_pos _)
  | CompR L _ ih =>
    simp only [tlength]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (tlength_pos L)
  | ExtnL x L _ ih => simp only [tlength]; omega
  | ExtnR L x _ ih => simp only [tlength]; omega

theorem sig_SN_aux : ∀ n (M : Trm), tlength M < n → SN_at Sig M := by
  intro n
  induction n with
  | zero => intro M h; omega
  | succ n ih =>
    intro M h
    exact SN_at.intro fun N hN => ih N (by have := sig_tlength_decrease hN; omega)

theorem sig_SN (M : Trm) : SN_at Sig M := sig_SN_aux _ M (Nat.lt_succ_self _)

/-! ## Finite branching -/

/-- All one-step weak-head successors, as a finite list. -/
def wh_succs : Trm → List Trm
  | var _ => []
  | iden => []
  | lam x M => (wh_succs M).map (fun M' => lam x M')
  | extn M x L => (wh_succs M).map (fun M' => extn M' x L) ++ (wh_succs L).map (fun L' => extn M x L')
  | app M N =>
      (wh_succs M).map (fun M' => app M' N) ++ (wh_succs N).map (fun N' => app M N') ++
      (match M with
       | lam x P => [comp P (extn N x iden)]
       | comp (lam x P) K => [comp P (extn N x K)]
       | _ => [])
  | comp M N =>
      (wh_succs M).map (fun M' => comp M' N) ++ (wh_succs N).map (fun N' => comp M N') ++
      (match M with | comp L K => [comp L (comp K N)] | _ => []) ++
      (if M = iden then [N] else []) ++ (if N = iden then [M] else []) ++
      (match M with | extn L x K => [extn (comp L N) x (comp K N)] | _ => []) ++
      (match M with | app M1 M2 => [app (comp M1 N) (comp M2 N)] | _ => []) ++
      (match M, N with
       | var x, extn L y K => if y = x then [L] else [comp (var x) K]
       | _, _ => [])

theorem sig_imp_wh_succs {M N : Trm} (h : Sig M N) : N ∈ wh_succs M := by
  induction h with
  | VarSkip M N hxy => simp [wh_succs, hxy]
  | _ => simp_all [wh_succs]

theorem beta_h_imp_wh_succs {M N : Trm} (h : BetaH M N) : N ∈ wh_succs M := by
  induction h <;> simp_all [wh_succs]

theorem wh_imp_wh_succs {M N : Trm} (h : Wh M N) : N ∈ wh_succs M := by
  rcases h with h | h
  · exact sig_imp_wh_succs h
  · exact beta_h_imp_wh_succs h

end LambdaEnvWH
