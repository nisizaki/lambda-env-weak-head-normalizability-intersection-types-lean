import LambdaEnvWH.Main_Results

/-!
# Examples

Port of `Examples.thy`.  Variables are numbers: x = 0, y = 1, z = 1, w = 5 etc.
-/

namespace LambdaEnvWH

open Trm Ty dB

/-! ## Helper lemmas: σ-normality of concrete shapes -/

theorem sn_Var (x : Var) : sig_normal (var x) := fun _ h => by cases h
theorem sn_Id : sig_normal iden := fun _ h => by cases h

theorem sn_Lam {M : Trm} {x : Var} (h : sig_normal M) : sig_normal (lam x M) := by
  intro N hN; cases hN with
  | Lam _ h' => exact h _ h'

theorem sn_App {M N : Trm} (h1 : sig_normal M) (h2 : sig_normal N) : sig_normal (app M N) := by
  intro P hP; cases hP with
  | AppL _ h' => exact h1 _ h'
  | AppR _ h' => exact h2 _ h'

theorem sn_Comp_VarVar (x y : Var) : sig_normal (comp (var x) (var y)) := by
  intro P hP; cases hP with
  | CompL _ h' => cases h'
  | CompR _ h' => cases h'

theorem Typ_expand {M N : Trm} (h : Wh M N) (t : Typ N) : Typ M := by
  obtain ⟨m, ob, A, d, e⟩ := t
  exact ⟨m, ob, A, subject_expansion h d, e⟩

theorem Typ_expand_steps {M N : Trm} (h : WhSteps M N) (t : Typ N) : Typ M := by
  obtain ⟨m, ob, A, d, e⟩ := t
  exact ⟨m, ob, A, subject_expansion_steps h d, e⟩

/-! ## Row 1: `(id/x)·(λy.id)` -/

theorem ex1_val : val (extn iden 0 (lam 1 iden)) := .VExtn 0 sn_Id (sn_Lam sn_Id)

theorem ex1_WHNF : WHNF (extn iden 0 (lam 1 iden)) := val_WHNF ex1_val

theorem ex1_derivation :
    Hasty (Env [] true) (extn iden 0 (lam 1 iden)) (Env [(0, Om)] false) :=
  .TExtn (.TOm _ _) (typ_env_om _ _)

theorem ex1_Typ : Typ (extn iden 0 (lam 1 iden)) :=
  ⟨[], true, _, ex1_derivation, Or.inl (by simp)⟩

/-! ## Row 2: `(λy.id)∘(λy.id)` -/

theorem ex2_val : val (comp (lam 1 iden) (lam 1 iden)) :=
  .VClo 1 sn_Id (sn_Lam sn_Id) (by simp)

theorem ex2_derivation :
    Hasty (Env [] true) (comp (lam 1 iden) (lam 1 iden)) (Arr Om Om) :=
  .TComp (typ_env_om _ _) (lam_typable 1 _ (.s_refl _))

theorem ex2_Typ : Typ (comp (lam 1 iden) (lam 1 iden)) :=
  ⟨[], true, _, ex2_derivation, by simp [ess]⟩

/-! ## Row 3: `id∘(λx.id)` -/

theorem ex3_step : Wh (comp iden (lam 0 iden)) (lam 0 iden) := sig_imp_wh (.IdL _)

theorem ex3_not_WHNF : ¬ WHNF (comp iden (lam 0 iden)) := fun h => h _ ex3_step

theorem ex3_Typ : Typ (comp iden (lam 0 iden)) :=
  Typ_expand ex3_step (val_Typ (.VLam 0 sn_Id))

/-! ## Row 4: `id N` -/

theorem ex4_clash : clash (app iden (var 0)) := .CId (sn_Var 0)

theorem ex4_WHNF : WHNF (app iden (var 0)) := clash_WHNF ex4_clash

theorem ex4_not_Typ : ¬ Typ (app iden (var 0)) := clash_not_Typ ex4_WHNF ex4_clash

/-! ## Row 5: `(x y)∘w → (x∘w)(y∘w)` -/

theorem ex5_step :
    Wh (comp (app (var 0) (var 1)) (var 5)) (app (comp (var 0) (var 5)) (comp (var 1) (var 5))) :=
  sig_imp_wh (.DApp _ _ _)

theorem ex5_neu : neu (app (comp (var 0) (var 5)) (comp (var 1) (var 5))) :=
  .NApp (.NComp 0 (.NVar 5)) (sn_Comp_VarVar 1 5)

theorem ex5_Typ_reduct : Typ (app (comp (var 0) (var 5)) (comp (var 1) (var 5))) :=
  neu_Typ ex5_neu

theorem ex5_Typ : Typ (comp (app (var 0) (var 1)) (var 5)) :=
  Typ_expand ex5_step ex5_Typ_reduct

/-! ## Row 6: `x∘(λy.M)` -/

theorem ex6_clash : clash (comp (var 0) (lam 1 (var 1))) := .CLam 0 1 (sn_Var 1)

theorem ex6_not_Typ : ¬ Typ (comp (var 0) (lam 1 (var 1))) :=
  clash_not_Typ (clash_WHNF ex6_clash) ex6_clash

/-! ## Row 7: `x∘((λz.(z/x)·id) y)` with x = 0, z = 1, y = 2 -/

theorem ex7_reduction :
    WhSteps (comp (var 0) (app (lam 1 (extn (var 1) 0 iden)) (var 2))) (var 2) := by
  let E := extn (var 2) 1 iden
  have s1 : Wh (comp (var 0) (app (lam 1 (extn (var 1) 0 iden)) (var 2)))
      (comp (var 0) (comp (extn (var 1) 0 iden) E)) :=
    wh_VarR 0 (beta_h_imp_wh (.Beta2 _ _ _))
  have s2 : Wh (comp (var 0) (comp (extn (var 1) 0 iden) E))
      (comp (var 0) (extn (comp (var 1) E) 0 (comp iden E))) :=
    wh_VarR 0 (sig_imp_wh (.DExtn _ _ _ _))
  have s3 : Wh (comp (var 0) (extn (comp (var 1) E) 0 (comp iden E))) (comp (var 1) E) :=
    sig_imp_wh (.VarRef _ _ _)
  have s4 : Wh (comp (var 1) E) (var 2) := sig_imp_wh (.VarRef _ _ _)
  exact .step s1 (.step s2 (.step s3 (.single s4)))

theorem ex7_Typ : Typ (comp (var 0) (app (lam 1 (extn (var 1) 0 iden)) (var 2))) :=
  Typ_expand_steps ex7_reduction (neu_Typ (.NVar 2))

/-! ## Row 8: `x∘((id/x)·id) → id` -/

theorem ex8_step : Wh (comp (var 0) (extn iden 0 iden)) iden := sig_imp_wh (.VarRef _ _ _)

theorem ex8_Typ : Typ (comp (var 0) (extn iden 0 iden)) :=
  Typ_expand ex8_step (val_Typ .VId)

/-! ## Rows 9--11: `Ω`, `λx.Ω`, `x Ω` -/

def Omega : Trm := app (lam 0 (app (var 0) (var 0))) (lam 0 (app (var 0) (var 0)))

def dw : dB := DAbs (DApp (DVar 0) (DVar 0))

theorem pure_Omega : pure Omega := by simp [Omega, pure]

theorem rb_Omega : rb Omega DVar = DApp dw dw := by
  simp [Omega, dw, rb, fupd]

theorem dOmega_step : hred (DApp dw dw) (DApp dw dw) := by
  have := hred.hbeta (DApp (DVar 0) (DVar 0)) dw
  simpa [dw, subst_App] using this

theorem dOmega_reach {u : dB} (h : Star hred (DApp dw dw) u) : u = DApp dw dw := by
  have : ∀ s u, Star hred s u → s = DApp dw dw → u = DApp dw dw := by
    intro s u h
    induction h with
    | refl => exact id
    | step h _ ih =>
      intro e; subst e
      rw [hred_det h dOmega_step] at ih; exact ih rfl
  exact this _ _ h rfl

theorem not_lam_WHN_Omega : ¬ lam_WHN (rb Omega DVar) := by
  rintro ⟨u, r, n⟩
  rw [rb_Omega] at r
  have := dOmega_reach r
  subst this
  exact n _ dOmega_step

theorem ex9_not_CFWHN : ¬ CFWHN Omega := fun h =>
  not_lam_WHN_Omega ((E1 pure_Omega).1.2 h)

theorem ex9_not_Typ : ¬ Typ Omega := fun h => ex9_not_CFWHN (main_characterization.1 h)

theorem sn_Omega : sig_normal Omega :=
  sn_App (sn_Lam (sn_App (sn_Var 0) (sn_Var 0))) (sn_Lam (sn_App (sn_Var 0) (sn_Var 0)))

theorem ex10_val : val (lam 0 Omega) := .VLam 0 sn_Omega

theorem ex10_derivation : Hasty (Env [] true) (lam 0 Omega) (Arr Om Om) :=
  lam_typable 0 _ (.s_refl _)

theorem ex10_Typ : Typ (lam 0 Omega) :=
  ⟨[], true, _, ex10_derivation, by simp [ess]⟩

theorem ex11_neu : neu (app (var 0) Omega) := .NApp (.NVar 0) sn_Omega

theorem ex11_derivation :
    Hasty (Env [(0, Arr Om (TV 0))] true) (app (var 0) Omega) (TV 0) :=
  .TApp (.TVar (.s_refl _) (map_of_cons_self _ _ _)) (.TOm _ _)

theorem ex11_Typ : Typ (app (var 0) Omega) := neu_Typ ex11_neu

end LambdaEnvWH
