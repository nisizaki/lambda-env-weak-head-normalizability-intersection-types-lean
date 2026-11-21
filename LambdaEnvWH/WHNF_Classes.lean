import LambdaEnvWH.Reduction

/-!
# Weak-head normal forms: neutral, value, clash

Port of `WHNF_Classes.thy`.
-/

namespace LambdaEnvWH

open Trm

inductive neu : Trm → Prop where
  | NVar (x : Var) : neu (var x)
  | NApp {M N : Trm} : neu M → sig_normal N → neu (app M N)
  | NComp {M : Trm} (x : Var) : neu M → neu (comp (var x) M)

inductive val : Trm → Prop where
  | VLam {M : Trm} (x : Var) : sig_normal M → val (lam x M)
  | VClo {M L : Trm} (x : Var) : sig_normal M → sig_normal L → L ≠ iden → val (comp (lam x M) L)
  | VId : val iden
  | VExtn {M L : Trm} (x : Var) : sig_normal M → sig_normal L → val (extn M x L)

inductive clash : Trm → Prop where
  | CId {N : Trm} : sig_normal N → clash (app iden N)
  | CExtn {M L N : Trm} (x : Var) : sig_normal M → sig_normal L → sig_normal N →
      clash (app (extn M x L) N)
  | CApp {M N : Trm} : clash M → sig_normal N → clash (app M N)
  | CLam {M : Trm} (x y : Var) : sig_normal M → clash (comp (var x) (lam y M))
  | CClo {M L : Trm} (x y : Var) : sig_normal M → sig_normal L → L ≠ iden →
      clash (comp (var x) (comp (lam y M) L))
  | CComp {M : Trm} (x : Var) : clash M → clash (comp (var x) M)

def cf_whnf (M : Trm) : Prop := neu M ∨ val M

/-! ## WHNF of each constructor -/

theorem WHNF_Var (x : Var) : WHNF (var x) := by
  intro N h; rcases h with h | h <;> cases h

theorem WHNF_Id : WHNF iden := by
  intro N h; rcases h with h | h <;> cases h

theorem WHNF_Lam_iff {x : Var} {M : Trm} : WHNF (lam x M) ↔ sig_normal M := by
  constructor
  · intro h N hN; exact h _ (Or.inl (.Lam x hN))
  · intro h N hN
    rcases hN with hN | hN
    · cases hN with
      | Lam _ hN => exact h _ hN
    · cases hN

theorem WHNF_Extn_iff {M L : Trm} {x : Var} :
    WHNF (extn M x L) ↔ sig_normal M ∧ sig_normal L := by
  constructor
  · intro h
    exact ⟨fun N hN => h _ (Or.inl (.ExtnL x L hN)), fun N hN => h _ (Or.inl (.ExtnR M x hN))⟩
  · intro ⟨h1, h2⟩ N hN
    rcases hN with hN | hN
    · cases hN with
      | ExtnL _ _ hN => exact h1 _ hN
      | ExtnR _ _ hN => exact h2 _ hN
    · cases hN

theorem WHNF_App_iff {M N : Trm} :
    WHNF (app M N) ↔
      WHNF M ∧ sig_normal N ∧ (∀ x P, M ≠ lam x P) ∧ (∀ x P L, M ≠ comp (lam x P) L) := by
  constructor
  · intro nf
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro Q hQ; exact nf _ (wh_AppL N hQ)
    · intro Q hQ; exact nf _ (Or.inl (.AppR M hQ))
    · intro x P h; subst h; exact nf _ (Or.inr (.Beta2 x P N))
    · intro x P L h; subst h; exact nf _ (Or.inr (.Beta1 x P L N))
  · intro ⟨hM, hN, h1, h2⟩ Q hQ
    rcases hQ with hQ | hQ
    · cases hQ with
      | AppL _ h => exact hM _ (Or.inl h)
      | AppR _ h => exact hN _ h
    · cases hQ with
      | Beta1 => exact h2 _ _ _ rfl
      | Beta2 => exact h1 _ _ rfl
      | AppL _ h => exact hM _ (Or.inr h)

/-- No root σ-redex at a composition. -/
def comp_root_ok (M N : Trm) : Prop :=
  (∀ L K, M ≠ comp L K) ∧ M ≠ iden ∧ N ≠ iden ∧ (∀ L x K, M ≠ extn L x K) ∧
  (∀ M1 M2, M ≠ app M1 M2) ∧ (∀ x L y K, ¬ (M = var x ∧ N = extn L y K))

theorem WHNF_Comp_iff {M N : Trm} :
    WHNF (comp M N) ↔
      WHNF M ∧ sig_normal N ∧ comp_root_ok M N ∧ (∀ x, M = var x → WHNF N) := by
  constructor
  · intro nf
    have r : ∀ Q, ¬ Sig (comp M N) Q := fun Q h => nf Q (Or.inl h)
    refine ⟨fun Q hQ => nf _ (wh_CompL N hQ), fun Q hQ => nf _ (Or.inl (.CompR M hQ)), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro L K h; subst h; exact r _ (.Ass L K N)
      · intro h; subst h; exact r _ (.IdL N)
      · intro h; subst h; exact r _ (.IdR M)
      · intro L x K h; subst h; exact r _ (.DExtn L x K N)
      · intro M1 M2 h; subst h; exact r _ (.DApp M1 M2 N)
      · intro x L y K ⟨h1, h2⟩; subst h1; subst h2
        by_cases hy : y = x
        · subst hy; exact r _ (.VarRef y L K)
        · exact r _ (.VarSkip (x := y) (y := x) L K hy)
    · intro x h Q hQ; subst h; exact nf _ (wh_VarR x hQ)
  · intro ⟨hM, hN, ⟨o1, o2, o3, o4, o5, o6⟩, hV⟩ Q hQ
    rcases hQ with hQ | hQ
    · cases hQ with
      | Ass => exact o1 _ _ rfl
      | IdL => exact o2 rfl
      | IdR => exact o3 rfl
      | DExtn => exact o4 _ _ _ rfl
      | VarRef => exact o6 _ _ _ _ ⟨rfl, rfl⟩
      | VarSkip _ _ _ => exact o6 _ _ _ _ ⟨rfl, rfl⟩
      | DApp => exact o5 _ _ rfl
      | CompL _ h => exact hM _ (Or.inl h)
      | CompR _ h => exact hN _ h
    · cases hQ with
      | CompL _ h => exact hM _ (Or.inr h)
      | VarR x h => exact hV x rfl _ (Or.inr h)

/-! ## Classification theorem -/

theorem neu_not_Id {M : Trm} (h : neu M) : M ≠ iden := by cases h <;> simp
theorem neu_not_Extn {M : Trm} {L : Trm} {x : Var} {K : Trm} (h : neu M) : M ≠ extn L x K := by
  cases h <;> simp
theorem neu_not_Lam {M : Trm} {x : Var} {P : Trm} (h : neu M) : M ≠ lam x P := by
  cases h <;> simp
theorem neu_not_Clo {M : Trm} {x : Var} {P L : Trm} (h : neu M) : M ≠ comp (lam x P) L := by
  cases h <;> simp
theorem clash_not_Id {M : Trm} (h : clash M) : M ≠ iden := by cases h <;> simp
theorem clash_not_Extn {M : Trm} {L : Trm} {x : Var} {K : Trm} (h : clash M) : M ≠ extn L x K := by
  cases h <;> simp
theorem clash_not_Lam {M : Trm} {x : Var} {P : Trm} (h : clash M) : M ≠ lam x P := by
  cases h <;> simp
theorem clash_not_Clo {M : Trm} {x : Var} {P L : Trm} (h : clash M) : M ≠ comp (lam x P) L := by
  cases h <;> simp

theorem val_Clo_WHNF {x : Var} {P L : Trm} (hP : sig_normal P) (hL : sig_normal L) (hI : L ≠ iden) :
    WHNF (comp (lam x P) L) := by
  rw [WHNF_Comp_iff]
  refine ⟨WHNF_Lam_iff.2 hP, hL, ⟨?_, ?_, hI, ?_, ?_, ?_⟩, ?_⟩ <;> simp

theorem WHNF_imp_sig_normal' {M : Trm} (h : WHNF M) : sig_normal M := WHNF_imp_sig_normal h

theorem neu_WHNF {M : Trm} (h : neu M) : WHNF M := by
  induction h with
  | NVar x => exact WHNF_Var x
  | NApp h hN ih =>
    rw [WHNF_App_iff]
    exact ⟨ih, hN, fun x P => neu_not_Lam h, fun x P L => neu_not_Clo h⟩
  | NComp x h ih =>
    rw [WHNF_Comp_iff]
    refine ⟨WHNF_Var x, WHNF_imp_sig_normal ih, ⟨?_, ?_, neu_not_Id h, ?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · intro x' L y K ⟨h1, h2⟩; exact neu_not_Extn h h2
    · intro x' h; cases h; exact ih

theorem val_WHNF {M : Trm} (h : val M) : WHNF M := by
  cases h with
  | VLam x h => exact WHNF_Lam_iff.2 h
  | VClo x h1 h2 h3 => exact val_Clo_WHNF h1 h2 h3
  | VId => exact WHNF_Id
  | VExtn x h1 h2 => exact WHNF_Extn_iff.2 ⟨h1, h2⟩

theorem clash_WHNF {M : Trm} (h : clash M) : WHNF M := by
  induction h with
  | CId hN => rw [WHNF_App_iff]; exact ⟨WHNF_Id, hN, by simp, by simp⟩
  | CExtn x h1 h2 h3 =>
    rw [WHNF_App_iff]; exact ⟨WHNF_Extn_iff.2 ⟨h1, h2⟩, h3, by simp, by simp⟩
  | CApp h hN ih =>
    rw [WHNF_App_iff]; exact ⟨ih, hN, fun x P => clash_not_Lam h, fun x P L => clash_not_Clo h⟩
  | CLam x y hM =>
    have : WHNF (lam y _) := WHNF_Lam_iff.2 hM
    rw [WHNF_Comp_iff]
    exact ⟨WHNF_Var x, WHNF_imp_sig_normal this,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩,
      fun x' h => by cases h; exact this⟩
  | CClo x y hM hL hI =>
    have := val_Clo_WHNF (x := y) hM hL hI
    rw [WHNF_Comp_iff]
    exact ⟨WHNF_Var x, WHNF_imp_sig_normal this,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩,
      fun x' h => by cases h; exact this⟩
  | CComp x h ih =>
    rw [WHNF_Comp_iff]
    exact ⟨WHNF_Var x, WHNF_imp_sig_normal ih,
      ⟨by simp, by simp, clash_not_Id h, by simp, by simp,
        fun x' L y K ⟨h1, h2⟩ => clash_not_Extn h h2⟩,
      fun x' h' => by cases h'; exact ih⟩

theorem WHNF_cases {M : Trm} (h : WHNF M) : neu M ∨ val M ∨ clash M := by
  induction M with
  | var x => exact Or.inl (.NVar x)
  | lam x M _ => exact Or.inr (Or.inl (.VLam x (WHNF_Lam_iff.1 h)))
  | app M N ihM _ =>
    obtain ⟨hM, hN, nL, nC⟩ := WHNF_App_iff.1 h
    rcases ihM hM with h1 | h1 | h1
    · exact Or.inl (.NApp h1 hN)
    · cases h1 with
      | VLam => exact absurd rfl (nL _ _)
      | VClo => exact absurd rfl (nC _ _ _)
      | VId => exact Or.inr (Or.inr (.CId hN))
      | VExtn x h1 h2 => exact Or.inr (Or.inr (.CExtn x h1 h2 hN))
    · exact Or.inr (Or.inr (.CApp h1 hN))
  | iden => exact Or.inr (Or.inl .VId)
  | extn M x L _ _ =>
    obtain ⟨h1, h2⟩ := WHNF_Extn_iff.1 h
    exact Or.inr (Or.inl (.VExtn x h1 h2))
  | comp M N ihM ihN =>
    obtain ⟨hM, hN, ok, hV⟩ := WHNF_Comp_iff.1 h
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ok
    cases M with
    | var x =>
      have nN := hV x rfl
      rcases ihN nN with h1 | h1 | h1
      · exact Or.inl (.NComp x h1)
      · cases h1 with
        | VLam y hP => exact Or.inr (Or.inr (.CLam x y hP))
        | VClo y hP hL hI => exact Or.inr (Or.inr (.CClo x y hP hL hI))
        | VId => exact absurd rfl o3
        | VExtn y h1 h2 => exact absurd ⟨rfl, rfl⟩ (o6 x _ y _)
      · exact Or.inr (Or.inr (.CComp x h1))
    | lam x P =>
      have hP := WHNF_Lam_iff.1 hM
      exact Or.inr (Or.inl (.VClo x hP hN o3))
    | app M1 M2 => exact absurd rfl (o5 _ _)
    | iden => exact absurd rfl o2
    | extn L x K => exact absurd rfl (o4 _ _ _)
    | comp L K => exact absurd rfl (o1 _ _)

theorem WHNF_iff_classes {M : Trm} : WHNF M ↔ neu M ∨ val M ∨ clash M := by
  constructor
  · exact WHNF_cases
  · rintro (h | h | h)
    · exact neu_WHNF h
    · exact val_WHNF h
    · exact clash_WHNF h

/-! ## Clash-free normalization predicates -/

def CFWHN (M : Trm) : Prop := ∃ N, WhSteps M N ∧ WHNF N ∧ ¬ clash N

def CFWHSN (M : Trm) : Prop := WHSN M ∧ ∀ N, WhSteps M N → WHNF N → ¬ clash N

end LambdaEnvWH
