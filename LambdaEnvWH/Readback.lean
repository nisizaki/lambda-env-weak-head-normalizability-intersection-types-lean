import LambdaEnvWH.WHNF_Classes
import LambdaEnvWH.Lambda
import LambdaEnvWH.Soundness

/-!
# Readback into the λ-calculus and the extension theorem E1

Port of `Readback.thy`.

`tm`: term-sorted, `en`: environment-sorted.  Environments are built from `id`, extensions
and compositions; there are no environment variables.  Pure λ-terms are term-sorted, and
sortedness is preserved by `→wh`.

Adaptations: `f(x := v)` is `fupd f x v`; `tm`/`en` are `Prop`-valued; `t[s/k]` is `subst t s k`.
`CFWHSN_imp_CFWHN` (which lives in `Readback.thy`) is in this file as well.
-/

namespace LambdaEnvWH

open Trm dB

/-! ## Sorted (proper) terms -/

mutual
def tm : Trm → Prop
  | var _ => True
  | lam _ M => tm M
  | app M N => tm M ∧ tm N
  | comp M L => tm M ∧ en L
  | iden => False
  | extn _ _ _ => False
def en : Trm → Prop
  | var _ => False
  | lam _ _ => False
  | app _ _ => False
  | comp L1 L2 => en L1 ∧ en L2
  | iden => True
  | extn M _ L => tm M ∧ en L
end

def pure : Trm → Prop
  | var _ => True
  | lam _ M => pure M
  | app M N => pure M ∧ pure N
  | iden => False
  | extn _ _ _ => False
  | comp _ _ => False

theorem pure_tm {M : Trm} (h : pure M) : tm M := by
  induction M with
  | var => trivial
  | lam _ M ih => exact ih h
  | app M N ihM ihN => exact ⟨ihM h.1, ihN h.2⟩
  | iden => exact h
  | extn => exact h
  | comp => exact h.elim

/-! ## Readback -/

/-- Function update. -/
def fupd {α : Type} (f : Var → α) (x : Var) (v : α) : Var → α :=
  fun y => if y = x then v else f y

/-- `junk` is used for ill-sorted positions; it is closed, so substitution fixes it. -/
def junk : dB := DAbs (DVar 0)

@[simp] theorem subst_junk (s : dB) (k : Nat) : subst junk s k = junk := by
  simp [junk, subst_Abs]

mutual
def rb : Trm → (Var → dB) → dB
  | var x, ρ => ρ x
  | lam x M, ρ => DAbs (rb M (fupd (fun y => lift (ρ y) 0) x (DVar 0)))
  | app M N, ρ => DApp (rb M ρ) (rb N ρ)
  | comp M L, ρ => rb M (rbe L ρ)
  | iden, _ => junk
  | extn _ _ _, _ => junk
def rbe : Trm → (Var → dB) → (Var → dB)
  | var _, ρ => ρ
  | lam _ _, ρ => ρ
  | app _ _, ρ => ρ
  | comp L1 L2, ρ => rbe L1 (rbe L2 ρ)
  | iden, ρ => ρ
  | extn M x L, ρ => fupd (rbe L ρ) x (rb M ρ)
end

theorem rb_subst (M : Trm) :
    (∀ σ s k, subst (rb M σ) s k = rb M (fun y => subst (σ y) s k)) ∧
    (∀ σ s k, rbe M (fun y => subst (σ y) s k) = (fun y => subst (rbe M σ y) s k)) := by
  induction M with
  | var x => simp [rb, rbe]
  | lam x M ih =>
    refine ⟨fun σ s k => ?_, by simp [rbe]⟩
    have fe : (fun y => subst (fupd (fun y => lift (σ y) 0) x (DVar 0) y) (lift s 0) (k + 1))
        = fupd (fun y => lift (subst (σ y) s k) 0) x (DVar 0) := by
      funext y
      by_cases h : y = x
      · simp [fupd, h]
      · simp [fupd, h, lift_subst_lt]
    simp only [rb, subst_Abs]
    rw [ih.1, fe]
  | app M N ihM ihN =>
    exact ⟨fun σ s k => by simp [rb, ihM.1, ihN.1], by simp [rbe]⟩
  | iden => exact ⟨by simp [rb], by simp [rbe]⟩
  | extn M x L ihM ihL =>
    refine ⟨by simp [rb], fun σ s k => ?_⟩
    simp only [rbe]
    funext y
    rw [ihL.2, ← ihM.1 σ s k]
    by_cases h : y = x <;> simp [fupd, h]
  | comp M L ihM ihL =>
    refine ⟨fun σ s k => ?_, fun σ s k => ?_⟩
    · simp only [rb]; rw [ihM.1, ihL.2]
    · simp only [rbe]; rw [ihL.2, ihM.2]

theorem beta_rb (M : Trm) (σ : Var → dB) (x : Var) (t : dB) :
    subst (rb M (fupd (fun y => lift (σ y) 0) x (DVar 0))) t 0 = rb M (fupd σ x t) := by
  have : (fun y => subst (fupd (fun y => lift (σ y) 0) x (DVar 0) y) t 0) = fupd σ x t := by
    funext y
    by_cases h : y = x <;> simp [fupd, h]
  rw [(rb_subst M).1, this]

/-! ## Simulation -/

theorem sig_sorted {M N : Trm} (h : Sig M N) :
    (tm M → tm N ∧ ∀ ρ, rb N ρ = rb M ρ) ∧ (en M → en N ∧ ∀ ρ, rbe N ρ = rbe M ρ) := by
  induction h with
  | Ass L M N => simp [tm, en, rb, rbe, and_assoc]
  | IdL M => simp [tm, en, rb, rbe]
  | IdR M => simp [tm, en, rb, rbe]
  | DExtn L x M N => simp [tm, en, rb, rbe, and_assoc, and_comm, and_left_comm]
  | VarRef x M N => simp +contextual [tm, en, rb, rbe, fupd]
  | VarSkip M N hxy =>
    rename_i x y
    refine ⟨?_, ?_⟩ <;> simp [tm, en, rb, rbe, fupd, Ne.symm hxy]
  | DApp M1 M2 N => simp [tm, en, rb, rbe, and_assoc, and_comm, and_left_comm]
  | AppL L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨(ih.1 a).1, b⟩, fun ρ => ?_⟩, by simp [en]⟩
    simp [rb, (ih.1 a).2]
  | AppR L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨a, (ih.1 b).1⟩, fun ρ => ?_⟩, by simp [en]⟩
    simp [rb, (ih.1 b).2]
  | Lam x _ ih =>
    refine ⟨fun a => ⟨(ih.1 a).1, fun ρ => ?_⟩, by simp [en]⟩
    simp [rb, (ih.1 a).2]
  | CompL L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨(ih.1 a).1, b⟩, fun ρ => ?_⟩, fun ⟨a, b⟩ => ⟨⟨(ih.2 a).1, b⟩, fun ρ => ?_⟩⟩
    · simp [rb, (ih.1 a).2]
    · simp [rbe, (ih.2 a).2]
  | CompR L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨a, (ih.2 b).1⟩, fun ρ => ?_⟩, fun ⟨a, b⟩ => ⟨⟨a, (ih.2 b).1⟩, fun ρ => ?_⟩⟩
    · simp [rb, (ih.2 b).2]
    · simp [rbe, (ih.2 b).2]
  | ExtnL x L _ ih =>
    refine ⟨by simp [tm], fun ⟨a, b⟩ => ⟨⟨(ih.1 a).1, b⟩, fun ρ => ?_⟩⟩
    simp [rbe, (ih.1 a).2]
  | ExtnR L x _ ih =>
    refine ⟨by simp [tm], fun ⟨a, b⟩ => ⟨⟨a, (ih.2 b).1⟩, fun ρ => ?_⟩⟩
    simp [rbe, (ih.2 b).2]

theorem beta_not_en {M N : Trm} (h : BetaH M N) : ¬ en M := by
  induction h <;> simp_all [en]

theorem beta_sorted {M N : Trm} (h : BetaH M N) :
    tm M → tm N ∧ ∀ ρ, hred (rb M ρ) (rb N ρ) := by
  induction h with
  | Beta1 x M L N =>
    intro ⟨⟨a, b⟩, c⟩
    refine ⟨⟨a, c, b⟩, fun ρ => ?_⟩
    have := hred.hbeta (rb M (fupd (fun y => lift (rbe L ρ y) 0) x (DVar 0))) (rb N ρ)
    rw [beta_rb] at this
    simpa [rb, rbe] using this
  | Beta2 x M N =>
    intro ⟨a, b⟩
    refine ⟨⟨a, b, trivial⟩, fun ρ => ?_⟩
    have := hred.hbeta (rb M (fupd (fun y => lift (ρ y) 0) x (DVar 0))) (rb N ρ)
    rw [beta_rb] at this
    simpa [rb, rbe] using this
  | AppL L _ ih =>
    intro ⟨a, b⟩
    obtain ⟨c, d⟩ := ih a
    exact ⟨⟨c, b⟩, fun ρ => hred.happ _ (d ρ)⟩
  | CompL L _ ih =>
    intro ⟨a, b⟩
    obtain ⟨c, d⟩ := ih a
    exact ⟨⟨c, b⟩, fun ρ => d _⟩
  | VarR x h _ =>
    intro ⟨_, b⟩
    exact absurd b (beta_not_en h)

theorem wh_sorted {M N : Trm} (h : Wh M N) (t : tm M) :
    tm N ∧ (((∀ ρ, rb N ρ = rb M ρ) ∧ tlength N < tlength M) ∨ ∀ ρ, hred (rb M ρ) (rb N ρ)) := by
  rcases h with h | h
  · exact ⟨((sig_sorted h).1 t).1, Or.inl ⟨((sig_sorted h).1 t).2, sig_tlength_decrease h⟩⟩
  · exact ⟨(beta_sorted h t).1, Or.inr (beta_sorted h t).2⟩

theorem wh_steps_sorted {M N : Trm} (h : WhSteps M N) (t : tm M) {ρ : Var → dB} :
    tm N ∧ Star hred (rb M ρ) (rb N ρ) := by
  induction h with
  | refl => exact ⟨t, .refl _⟩
  | @step a b c hab _ ih =>
    obtain ⟨t1, h1⟩ := wh_sorted hab t
    obtain ⟨t2, h2⟩ := ih t1
    refine ⟨t2, ?_⟩
    rcases h1 with ⟨e, _⟩ | e
    · rw [e ρ] at h2; exact h2
    · exact .step (e ρ) h2

/-! ## Normal forms -/

theorem sorted_not_clash {M : Trm} (h : clash M) : ¬ tm M ∧ ¬ en M := by
  induction h with
  | CId => simp [tm, en]
  | CExtn => simp [tm, en]
  | CApp _ _ ih => simp [tm, en, ih.1]
  | CLam => simp [tm, en]
  | CClo => simp [tm, en]
  | CComp x _ ih => simp [tm, en, ih.2]

inductive hneu : dB → Prop where
  | hneu_var (i : Nat) : hneu (DVar i)
  | hneu_app {s : dB} (t : dB) : hneu s → hneu (DApp s t)

theorem hneu_normal {s : dB} (h : hneu s) : normal hred s := by
  induction h with
  | hneu_var i => intro b hb; cases hb
  | hneu_app t _ ih =>
    intro b hb
    cases hb with
    | hbeta => cases ‹hneu _›
    | happ _ h => exact ih _ h

theorem DAbs_normal (s : dB) : normal hred (DAbs s) := fun _ hb => DAbs_no_step hb

theorem neu_not_en {M : Trm} (h : neu M) : ¬ en M := by
  induction h <;> simp [en]

theorem neu_rb {M : Trm} (h : neu M) (t : tm M) : hneu (rb M DVar) := by
  induction h with
  | NVar x => exact .hneu_var x
  | NApp _ _ ih => exact .hneu_app _ (ih t.1)
  | NComp x h _ => exact absurd t.2 (neu_not_en h)

theorem rb_WHNF {M : Trm} (t : tm M) (n : WHNF M) : normal hred (rb M DVar) := by
  rcases WHNF_iff_classes.1 n with h | h | h
  · exact hneu_normal (neu_rb h t)
  · cases h with
    | VLam => exact DAbs_normal _
    | VClo => exact DAbs_normal _
    | VId => exact absurd t (by simp [tm])
    | VExtn => exact absurd t (by simp [tm])
  · exact absurd t (sorted_not_clash h).1

/-! ## E1 -/

theorem SN_at_normal_reachable {α : Type} {R : α → α → Prop} {a : α} (h : SN_at R a) :
    ∃ b, Star R a b ∧ normal R b := by
  refine h.induct (P := fun a => ∃ b, Star R a b ∧ normal R b) ?_
  intro a _ ih
  by_cases hn : ∃ b, R a b
  · obtain ⟨b, hb⟩ := hn
    obtain ⟨N, r, n⟩ := ih b hb
    exact ⟨N, .step hb r, n⟩
  · exact ⟨a, .refl _, fun b h => hn ⟨b, h⟩⟩

theorem CFWHSN_imp_CFWHN {M : Trm} (h : CFWHSN M) : CFWHN M := by
  obtain ⟨sn, cf⟩ := h
  obtain ⟨N, r, n⟩ := SN_at_normal_reachable sn
  exact ⟨N, r, n, cf N r n⟩

theorem CFWHN_imp_lam_WHN {M : Trm} (t : tm M) (c : CFWHN M) : lam_WHN (rb M DVar) := by
  obtain ⟨N, r, n, _⟩ := c
  obtain ⟨tN, h⟩ := wh_steps_sorted r t (ρ := DVar)
  exact ⟨_, h, rb_WHNF tN n⟩

theorem hdist_imp_WHSN {M : Trm} {n : Nat} (h : hdist (rb M DVar) n) (t : tm M) : WHSN M := by
  induction n using Nat.strongRecOn generalizing M with
  | _ n IHn =>
    have key : ∀ k (M : Trm), tlength M ≤ k → hdist (rb M DVar) n → tm M → WHSN M := by
      intro k
      induction k with
      | zero => intro M hk; have := tlength_pos M; omega
      | succ k ihk =>
        intro M hk hd tM
        refine SN_at.intro fun N s => ?_
        obtain ⟨tN, c⟩ := wh_sorted s tM
        rcases c with ⟨e, lt⟩ | e
        · exact ihk N (by omega) (by rw [e]; exact hd) tN
        · obtain ⟨m, hm, hd'⟩ := hdist_step hd (e DVar)
          exact IHn m (by omega) hd' tN
    exact key _ M (Nat.le_refl _) h t

theorem lam_WHN_imp_CFWHSN {M : Trm} (t : tm M) (w : lam_WHN (rb M DVar)) : CFWHSN M := by
  obtain ⟨n, hn⟩ := lam_WHN_hdist w
  refine ⟨hdist_imp_WHSN hn t, fun N r _ hc => ?_⟩
  exact (sorted_not_clash hc).1 (wh_steps_sorted r t (ρ := DVar)).1

theorem E1_sorted {M : Trm} (t : tm M) :
    (lam_WHN (rb M DVar) ↔ CFWHN M) ∧ (CFWHN M ↔ CFWHSN M) := by
  refine ⟨⟨fun w => CFWHSN_imp_CFWHN (lam_WHN_imp_CFWHSN t w), CFWHN_imp_lam_WHN t⟩,
    ⟨fun c => lam_WHN_imp_CFWHSN t (CFWHN_imp_lam_WHN t c), CFWHSN_imp_CFWHN⟩⟩

theorem E1 {M : Trm} (h : pure M) :
    (lam_WHN (rb M DVar) ↔ CFWHN M) ∧ (CFWHN M ↔ CFWHSN M) :=
  E1_sorted (pure_tm h)

end LambdaEnvWH
