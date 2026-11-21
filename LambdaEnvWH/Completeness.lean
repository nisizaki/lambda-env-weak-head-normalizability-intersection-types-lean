import LambdaEnvWH.Typing
import LambdaEnvWH.WHNF_Classes

/-!
# Completeness: `CFWHN M → Typ M`

Port of `Completeness.thy`.  Subject expansion for weak-head reduction and typability of
clash-free weak-head normal forms.
-/

namespace LambdaEnvWH

open Trm Ty

/-! ## Replacing a subterm by one with at least the same typings -/

def at_least (M N : Trm) : Prop := ∀ C A, Hasty C N A → Hasty C M A

theorem rep_AppL_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = app N L → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (app M L) A := by
  induction h with
  | TApp h1 h2 _ _ => intro e hy; cases e; exact .TApp (hy _ _ h1) h2
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_AppL {M N : Trm} (L : Trm) (h : at_least M N) : at_least (Trm.app M L) (Trm.app N L) :=
  fun _ _ ht => rep_AppL_aux ht rfl h

theorem rep_AppR_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = app L N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (app L M) A := by
  induction h with
  | TApp h1 h2 _ _ => intro e hy; cases e; exact .TApp h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_AppR {M N : Trm} (L : Trm) (h : at_least M N) : at_least (Trm.app L M) (Trm.app L N) :=
  fun _ _ ht => rep_AppR_aux ht rfl h

theorem rep_Lam_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N : Trm} {x : Var} :
    P = lam x N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (lam x M) A := by
  induction h with
  | TLam h1 h2 _ => intro e hy; cases e; exact .TLam h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_Lam {M N : Trm} (x : Var) (h : at_least M N) : at_least (Trm.lam x M) (Trm.lam x N) :=
  fun _ _ ht => rep_Lam_aux ht rfl h

theorem rep_CompL_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = comp N L → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (comp M L) A := by
  induction h with
  | TComp h1 h2 _ _ => intro e hy; cases e; exact .TComp h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_CompL {M N : Trm} (L : Trm) (h : at_least M N) : at_least (Trm.comp M L) (Trm.comp N L) :=
  fun _ _ ht => rep_CompL_aux ht rfl h

theorem rep_CompR_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = comp L N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (comp L M) A := by
  induction h with
  | TComp h1 h2 _ _ => intro e hy; cases e; exact .TComp (hy _ _ h1) h2
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_CompR {M N : Trm} (L : Trm) (h : at_least M N) : at_least (Trm.comp L M) (Trm.comp L N) :=
  fun _ _ ht => rep_CompR_aux ht rfl h

theorem rep_ExtnL_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} {x : Var} :
    P = extn N x L → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (extn M x L) A := by
  induction h with
  | TExtn h1 h2 _ _ => intro e hy; cases e; exact .TExtn (hy _ _ h1) h2
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_ExtnL {M N : Trm} (x : Var) (L : Trm) (h : at_least M N) : at_least (Trm.extn M x L) (Trm.extn N x L) :=
  fun _ _ ht => rep_ExtnL_aux ht rfl h

theorem rep_ExtnR_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} {x : Var} :
    P = extn L x N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (extn L x M) A := by
  induction h with
  | TExtn h1 h2 _ _ => intro e hy; cases e; exact .TExtn h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_ExtnR {M N : Trm} (L : Trm) (x : Var) (h : at_least M N) : at_least (Trm.extn L x M) (Trm.extn L x N) :=
  fun _ _ ht => rep_ExtnR_aux ht rfl h

/-! ## Root rules -/

theorem exp_Ass (L M N : Trm) : at_least (comp (comp L M) N) (comp L (comp M N)) := by
  intro C A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  obtain ⟨D', h3, h4⟩ := gen_Comp h1 rfl
  exact .TComp h3 (.TComp h4 h2)

theorem exp_IdL (M : Trm) : at_least (comp iden M) M :=
  fun _ _ h => .TComp h (.TId _)

theorem exp_IdR (M : Trm) : at_least (comp M iden) M :=
  fun _ _ h => .TComp (.TId _) h

theorem exp_VarRef (x : Var) (M N : Trm) : at_least (comp (var x) (extn M x N)) M := by
  intro C A h
  have h1 : Hasty C (extn M x N) (Env ((x, A) :: []) false) := .TExtn h (typ_env_om _ _)
  have h2 : Hasty (Env [(x, A)] false) (var x) A := .TVar (.s_refl _) (map_of_cons_self _ _ _)
  exact .TComp h1 h2

theorem exp_VarSkip {x y : Var} (M N : Trm) (xy : x ≠ y) :
    at_least (comp (var y) (extn M x N)) (comp (var y) N) := by
  intro C A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  rcases gen_Var h2 rfl with h3 | ⟨m, ob, B, d, l, b⟩
  · exact .TSub (.TOm _ _) h3
  · have h4 : Hasty C N (Env m ob) := .TSub h1 d
    have h5 : Hasty C (extn M x N) (Env ((x, Om) :: m) ob) := .TExtn (.TOm _ _) h4
    have h6 : Hasty (Env ((x, Om) :: m) ob) (var y) A :=
      .TSub (.TVar (.s_refl _) (by rw [map_of_cons_ne _ _ xy]; exact l)) b
    exact .TComp h5 h6

theorem exp_DExtn (L : Trm) (x : Var) (M N : Trm) :
    at_least (comp (extn L x M) N) (extn (comp L N) x (comp M N)) := by
  intro C A h
  obtain ⟨B, m, ob, h1, h2, s⟩ := gen_Extn h rfl
  obtain ⟨D1, a1, a2⟩ := gen_Comp h1 rfl
  obtain ⟨D2, b1, b2⟩ := gen_Comp h2 rfl
  have h3 : Hasty C N (Ty.Inter D1 D2) := .TInter a1 b1
  have h4 : Hasty (Ty.Inter D1 D2) (extn L x M) (Env ((x, B) :: m) ob) :=
    .TExtn (narrowing a2 (.s_il _ _)) (narrowing b2 (.s_ir _ _))
  exact .TSub (.TComp h3 h4) s

theorem exp_DApp_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M1 M2 N : Trm} :
    P = app (comp M1 N) (comp M2 N) → Hasty C (comp (app M1 M2) N) A := by
  induction h with
  | TApp p q _ _ =>
    intro e; cases e
    obtain ⟨D1, a1, a2⟩ := gen_Comp p rfl
    obtain ⟨D2, b1, b2⟩ := gen_Comp q rfl
    exact .TComp (.TInter a1 b1)
      (.TApp (narrowing a2 (.s_il _ _)) (narrowing b2 (.s_ir _ _)))
  | TOm => intro _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e; exact .TInter (ih1 e) (ih2 e)
  | TSub _ h2 ih => intro e; exact .TSub (ih e) h2
  | _ => intro e; cases e

theorem exp_DApp (M1 M2 N : Trm) :
    at_least (comp (app M1 M2) N) (app (comp M1 N) (comp M2 N)) :=
  fun _ _ h => exp_DApp_aux h rfl

theorem exp_Beta1 (x : Var) (M L N : Trm) :
    at_least (app (comp (lam x M) L) N) (comp M (extn N x L)) := by
  intro C A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  obtain ⟨B, m, ob, n, l, s⟩ := gen_Extn h1 rfl
  have h3 : Hasty (Env ((x, B) :: m) ob) M A := narrowing h2 s
  have h4 : Hasty (Env m ob) (lam x M) (Arr B A) := .TLam (.s_refl _) h3
  exact .TApp (.TComp l h4) n

theorem exp_Beta2 (x : Var) (M N : Trm) :
    at_least (app (lam x M) N) (comp M (extn N x iden)) := by
  intro C A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  obtain ⟨B, m, ob, n, l, s⟩ := gen_Extn h1 rfl
  have c : C ≼ Env m ob := gen_Id l rfl
  have h3 : Hasty (Env ((x, B) :: m) ob) M A := narrowing h2 s
  exact .TApp (.TLam c h3) n

/-! ## Subject expansion -/

theorem sig_expansion {M N : Trm} (h : Sig M N) : at_least M N := by
  induction h with
  | Ass L M N => exact exp_Ass L M N
  | IdL M => exact exp_IdL M
  | IdR M => exact exp_IdR M
  | DExtn L x M N => exact exp_DExtn L x M N
  | VarRef x M N => exact exp_VarRef x M N
  | VarSkip M N hxy => exact exp_VarSkip M N hxy
  | DApp M1 M2 N => exact exp_DApp M1 M2 N
  | AppL L _ ih => exact rep_AppL L ih
  | AppR L _ ih => exact rep_AppR L ih
  | Lam x _ ih => exact rep_Lam x ih
  | CompL L _ ih => exact rep_CompL L ih
  | CompR L _ ih => exact rep_CompR L ih
  | ExtnL x L _ ih => exact rep_ExtnL x L ih
  | ExtnR L x _ ih => exact rep_ExtnR L x ih

theorem beta_expansion {M N : Trm} (h : BetaH M N) : at_least M N := by
  induction h with
  | Beta1 x M L N => exact exp_Beta1 x M L N
  | Beta2 x M N => exact exp_Beta2 x M N
  | AppL L _ ih => exact rep_AppL L ih
  | CompL L _ ih => exact rep_CompL L ih
  | VarR x _ ih => exact rep_CompR _ ih

theorem subject_expansion {M N : Trm} {C A : Ty} (h : Wh M N) (t : Hasty C N A) :
    Hasty C M A := by
  rcases h with h | h
  · exact sig_expansion h C A t
  · exact beta_expansion h C A t

theorem subject_expansion_steps {M N : Trm} {C A : Ty} (h : WhSteps M N) (t : Hasty C N A) :
    Hasty C M A := by
  induction h with
  | refl => exact t
  | step h _ ih => exact subject_expansion h (ih t)

/-! ## Clash-free weak-head normal forms are typable -/

theorem neu_typable {M : Trm} (h : neu M) : ∀ {A : Ty}, ∃ m, Hasty (Env m true) M A := by
  induction h with
  | NVar x =>
    intro A
    exact ⟨[(x, A)], .TVar (.s_refl _) (map_of_cons_self _ _ _)⟩
  | NApp _ _ ih =>
    intro A
    obtain ⟨m, h⟩ := ih (A := Arr Om A)
    exact ⟨m, .TApp h (.TOm _ _)⟩
  | NComp x _ ih =>
    intro A
    obtain ⟨m, h⟩ := ih (A := Env [(x, A)] true)
    exact ⟨m, .TComp h (.TVar (.s_refl _) (map_of_cons_self _ _ _))⟩

theorem lam_typable {C : Ty} {m : List (Var × Ty)} {ob : Bool} (x : Var) (M : Trm)
    (h : C ≼ Env m ob) : Hasty C (lam x M) (Arr Om Om) :=
  .TLam h (.TOm _ _)

theorem val_Typ {M : Trm} (h : val M) : Typ M := by
  cases h with
  | VLam x _ => exact ⟨[], true, Arr Om Om, lam_typable x _ (.s_refl _), by simp [ess]⟩
  | VClo x _ _ _ =>
    exact ⟨[], true, Arr Om Om, .TComp (typ_env_om _ _) (lam_typable x _ (.s_refl _)), by simp [ess]⟩
  | VId => exact ⟨[], true, Env [] true, .TId _, by simp [ess]⟩
  | VExtn x _ _ =>
    exact ⟨[], true, Env ((x, Om) :: []) false, .TExtn (.TOm _ _) (typ_env_om _ _), by simp [ess]⟩

theorem neu_Typ {M : Trm} (h : neu M) : Typ M := by
  obtain ⟨m, h⟩ := neu_typable h (A := TV 0)
  exact ⟨m, true, TV 0, h, by simp [ess]⟩

theorem cf_WHNF_Typ {M : Trm} (h : WHNF M) (hc : ¬ clash M) : Typ M := by
  rcases WHNF_iff_classes.1 h with h | h | h
  · exact neu_Typ h
  · exact val_Typ h
  · exact absurd h hc

theorem completeness {M : Trm} (h : CFWHN M) : Typ M := by
  obtain ⟨N, r, n, c⟩ := h
  obtain ⟨m, ob, A, t, e⟩ := cf_WHNF_Typ n c
  exact ⟨m, ob, A, subject_expansion_steps r t, e⟩

end LambdaEnvWH
