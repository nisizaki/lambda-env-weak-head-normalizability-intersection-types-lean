import LambdaEnvWH.Sig_Confluence
import LambdaEnvWH.Main_Results

/-!
# Uniform normalization: `CFWHN M → CFWHSN M`

Port of `Uniform.thy`.

`→β` (head β) is deterministic, σ is terminating and confluent, and a σ-step commutes with
the β-step (`beta_sig_commute`).  Hence every `→wh`-path follows one deterministic chain of
σ-normal forms, and the number of β-steps on any path is bounded by the length of that chain.

Adaptation: `snf` is defined with `Classical.choose` (Isabelle's `SOME`).
-/

namespace LambdaEnvWH

open Trm

/-! ## Head β is deterministic -/

theorem Var_no_beta {x : Var} {N : Trm} (h : BetaH (var x) N) : False := by cases h
theorem Id_no_beta {N : Trm} (h : BetaH iden N) : False := by cases h
theorem Lam_no_beta {x : Var} {M N : Trm} (h : BetaH (lam x M) N) : False := by cases h
theorem Extn_no_beta {M L N : Trm} {x : Var} (h : BetaH (extn M x L) N) : False := by cases h
theorem Clo_no_beta {x : Var} {M L N : Trm} (h : BetaH (comp (lam x M) L) N) : False := by
  cases h with
  | CompL _ h' => exact Lam_no_beta h'

theorem beta_det {M N1 : Trm} (h : BetaH M N1) : ∀ {N2 : Trm}, BetaH M N2 → N1 = N2 := by
  induction h with
  | Beta1 x M L N =>
    intro N2 h2
    cases h2 with
    | Beta1 => rfl
    | AppL _ h' => exact (Clo_no_beta h').elim
  | Beta2 x M N =>
    intro N2 h2
    cases h2 with
    | Beta2 => rfl
    | AppL _ h' => exact (Lam_no_beta h').elim
  | AppL L h ih =>
    intro N2 h2
    cases h2 with
    | Beta1 => exact (Clo_no_beta h).elim
    | Beta2 => exact (Lam_no_beta h).elim
    | AppL _ h' => rw [ih h']
  | CompL L h ih =>
    intro N2 h2
    cases h2 with
    | CompL _ h' => rw [ih h']
    | VarR _ h' => exact (Var_no_beta h).elim
  | VarR x h ih =>
    intro N2 h2
    cases h2 with
    | CompL _ h' => exact (Var_no_beta h').elim
    | VarR _ h' => rw [ih h']

/-! ## Congruences for σ* -/

theorem ss_lift {f : Trm → Trm} (hf : ∀ P Q, Sig P Q → Sig (f P) (f Q)) {M N : Trm}
    (h : Star Sig M N) : Star Sig (f M) (f N) :=
  Star.map f hf h

theorem ss_AppL {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (app M L) (app N L) :=
  ss_lift (f := fun P => app P L) (fun _ _ h => .AppL L h) h
theorem ss_CompR {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (comp L M) (comp L N) :=
  ss_lift (f := fun P => comp L P) (fun _ _ h => .CompR L h) h
theorem ss_CompL {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (comp M L) (comp N L) :=
  ss_lift (f := fun P => comp P L) (fun _ _ h => .CompL L h) h

theorem ss1 {M N : Trm} (h : Sig M N) : Star Sig M N := Star.single h

/-! ## Commutation of a σ-step with the β-step -/

theorem Lam_sig_inv {x : Var} {B P : Trm} (h : Sig (lam x B) P) :
    ∃ B', P = lam x B' ∧ Sig B B' := by
  obtain ⟨B', h1, h2⟩ := inv_Lam h
  exact ⟨B', h2, h1⟩

theorem Clo_sig_inv {x : Var} {B K P : Trm} (h : Sig (comp (lam x B) K) P) :
    (∃ B', P = comp (lam x B') K ∧ Sig B B') ∨ (∃ K', P = comp (lam x B) K' ∧ Sig K K') ∨
      (K = iden ∧ P = lam x B) := by
  cases h with
  | CompL _ h' =>
    obtain ⟨B', e, h2⟩ := Lam_sig_inv h'
    exact Or.inl ⟨B', by rw [e], h2⟩
  | CompR _ h' => exact Or.inr (Or.inl ⟨_, rfl, h'⟩)
  | IdR => exact Or.inr (Or.inr ⟨rfl, rfl⟩)

def comm (M1 M2 : Trm) : Prop := ∃ M1' M3, Star Sig M1 M1' ∧ BetaH M1' M3 ∧ Star Sig M2 M3

theorem commI {M1 M1' M3 M2 : Trm} (h1 : Star Sig M1 M1') (h2 : BetaH M1' M3)
    (h3 : Star Sig M2 M3) : comm M1 M2 := ⟨M1', M3, h1, h2, h3⟩

theorem comm_direct {M1 M3 M2 : Trm} (h1 : BetaH M1 M3) (h2 : Star Sig M2 M3) : comm M1 M2 :=
  ⟨M1, M3, .refl _, h1, h2⟩

theorem beta_sig_commute {M M2 : Trm} (hb : BetaH M M2) : ∀ {M1 : Trm}, Sig M M1 → comm M1 M2 := by
  induction hb with
  | Beta1 x B K N =>
    intro M1 hs
    cases hs with
    | AppL _ hP =>
      rcases Clo_sig_inv hP with ⟨B', rfl, h1⟩ | ⟨K', rfl, h1⟩ | ⟨rfl, rfl⟩
      · exact comm_direct (.Beta1 x B' K N) (ss1 (.CompL _ h1))
      · exact comm_direct (.Beta1 x B K' N) (ss1 (.CompR _ (.ExtnR _ _ h1)))
      · exact comm_direct (.Beta2 x B N) (.refl _)
    | AppR _ h1 =>
      exact comm_direct (.Beta1 x B K _) (ss1 (.CompR _ (.ExtnL _ _ h1)))
  | Beta2 x B N =>
    intro M1 hs
    cases hs with
    | AppL _ hP =>
      obtain ⟨B', rfl, h1⟩ := Lam_sig_inv hP
      exact comm_direct (.Beta2 x B' N) (ss1 (.CompL _ h1))
    | AppR _ h1 =>
      exact comm_direct (.Beta2 x B _) (ss1 (.CompR _ (.ExtnL _ _ h1)))
  | AppL L h ih =>
    intro M1 hs
    cases hs with
    | AppL _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact commI (ss_AppL L a1) (.AppL L a2) (ss_AppL L a3)
    | AppR _ h1 => exact comm_direct (.AppL _ h) (ss1 (.AppR _ h1))
  | CompL L h ih =>
    rename_i M M'
    intro M1 hs
    cases hs with
    | Ass Ma Mb =>
      cases h with
      | CompL _ h' => exact comm_direct (.CompL _ h') (ss1 (.Ass _ _ _))
      | VarR x h' => exact comm_direct (.VarR x (.CompL _ h')) (ss1 (.Ass _ _ _))
    | IdL => exact (Id_no_beta h).elim
    | IdR => exact comm_direct h (ss1 (.IdR _))
    | DExtn => exact (Extn_no_beta h).elim
    | VarRef => exact (Var_no_beta h).elim
    | VarSkip => exact (Var_no_beta h).elim
    | DApp P Q =>
      cases h with
      | Beta1 x B K =>
        have s1 : Star Sig (app (comp (comp (lam x B) K) L) (comp Q L))
            (app (comp (lam x B) (comp K L)) (comp Q L)) :=
          ss1 (.AppL _ (.Ass _ _ _))
        have b : BetaH (app (comp (lam x B) (comp K L)) (comp Q L))
            (comp B (extn (comp Q L) x (comp K L))) := .Beta1 _ _ _ _
        have s2 : Star Sig (comp (comp B (extn Q x K)) L)
            (comp B (extn (comp Q L) x (comp K L))) :=
          .step (.Ass _ _ _) (.single (.CompR _ (.DExtn _ _ _ _)))
        exact commI s1 b s2
      | Beta2 x B =>
        have b : BetaH (app (comp (comp (lam x B) L) (comp Q L)) (comp Q L) |> fun _ =>
            app (comp (lam x B) L) (comp Q L)) (comp B (extn (comp Q L) x L)) := .Beta1 _ _ _ _
        have s2 : Star Sig (comp (comp B (extn Q x iden)) L)
            (comp B (extn (comp Q L) x L)) :=
          .step (.Ass _ _ _) (.step (.CompR _ (.DExtn _ _ _ _))
            (.single (.CompR _ (.ExtnR _ _ (.IdL _)))))
        exact comm_direct b s2
      | AppL _ h' =>
        exact comm_direct (.AppL _ (.CompL _ h')) (ss1 (.DApp _ _ _))
    | CompL _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact commI (ss_CompL L a1) (.CompL L a2) (ss_CompL L a3)
    | CompR _ h1 => exact comm_direct (.CompL _ h) (ss1 (.CompR _ h1))
  | VarR x h ih =>
    intro M1 hs
    cases hs with
    | CompL _ h' => exact (sig_Var_no _ _ h').elim
    | CompR _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact commI (ss_CompR _ a1) (.VarR x a2) (ss_CompR _ a3)
    | IdR => exact (Id_no_beta h).elim
    | VarRef => exact (Extn_no_beta h).elim
    | VarSkip => exact (Extn_no_beta h).elim

/-! ## σ-normal forms -/

theorem sig_steps_tlength {M N : Trm} (h : Star Sig M N) : tlength N ≤ tlength M := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h _ ih => have := sig_tlength_decrease h; omega

noncomputable def snf (M : Trm) : Trm := Classical.choose (sig_nf M)

theorem snf_spec (M : Trm) : Star Sig M (snf M) ∧ sig_normal (snf M) :=
  Classical.choose_spec (sig_nf M)

theorem snf_unique {M N : Trm} (r : Star Sig M N) (n : sig_normal N) : snf M = N := by
  obtain ⟨P, p1, p2⟩ := sig_confluent (snf_spec M).1 r
  have e1 := normal_star (snf_spec M).2 p1
  have e2 := normal_star n p2
  rw [← e1, e2]

theorem snf_steps {M M' : Trm} (r : Star Sig M M') : snf M' = snf M := by
  have h : Star Sig M (snf M') := r.trans (snf_spec M').1
  exact (snf_unique h (snf_spec M').2).symm

theorem snf_beta {M M' : Trm} (hb : BetaH M M') : ∃ M3, BetaH (snf M) M3 ∧ Star Sig M' M3 := by
  have key : ∀ k (M M' : Trm), tlength M ≤ k → BetaH M M' →
      ∃ M3, BetaH (snf M) M3 ∧ Star Sig M' M3 := by
    intro k
    induction k with
    | zero => intro M _ hk; have := tlength_pos M; omega
    | succ k ih =>
      intro M M' hk hb
      by_cases hn : ∃ M1, Sig M M1
      · obtain ⟨M1, s⟩ := hn
        obtain ⟨M1', M3', a1, a2, a3⟩ := beta_sig_commute hb s
        have lt : tlength M1' < tlength M := by
          have := sig_tlength_decrease s
          have := sig_steps_tlength a1
          omega
        obtain ⟨M3, b1, b2⟩ := ih M1' M3' (by omega) a2
        have e : snf M1' = snf M := snf_steps (.step s a1)
        rw [e] at b1
        exact ⟨M3, b1, a3.trans b2⟩
      · have e : snf M = M := snf_unique (.refl _) (fun b h => hn ⟨b, h⟩)
        rw [e]
        exact ⟨M', hb, .refl _⟩
  exact key _ M M' (Nat.le_refl _) hb

/-! ## The deterministic chain -/

inductive cd : Trm → Nat → Trm → Prop where
  | cd0 {M : Trm} : normal BetaH (snf M) → cd M 0 (snf M)
  | cdS {M N : Trm} {n : Nat} {E : Trm} : BetaH (snf M) N → cd N n E → cd M (n + 1) E

theorem cd_snf {A B : Trm} {n : Nat} {E : Trm} (h : cd A n E) (e : snf A = snf B) : cd B n E := by
  cases h with
  | cd0 hn => rw [e] at hn ⊢; exact .cd0 hn
  | cdS h1 h2 => rw [e] at h1; exact .cdS h1 h2

theorem cd_det {M : Trm} {n : Nat} {E : Trm} (h : cd M n E) :
    ∀ {n' : Nat} {E' : Trm}, cd M n' E' → n = n' ∧ E = E' := by
  induction h with
  | cd0 hn =>
    intro n' E' h2
    cases h2 with
    | cd0 => exact ⟨rfl, rfl⟩
    | cdS h1 _ => exact (hn _ h1).elim
  | cdS h ih ih2 =>
    intro n' E' h2
    cases h2 with
    | cd0 hn => exact (hn _ h).elim
    | cdS h1 c' =>
      have := beta_det h h1
      subst this
      obtain ⟨a, b⟩ := ih2 c'
      exact ⟨by rw [a], b⟩

theorem cd_back_sig {M M' : Trm} {n : Nat} {E : Trm} (h : Sig M M') (c : cd M' n E) : cd M n E :=
  cd_snf c (snf_steps (ss1 h))

theorem cd_fwd_sig {M M' : Trm} {n : Nat} {E : Trm} (h : Sig M M') (c : cd M n E) : cd M' n E :=
  cd_snf c (snf_steps (ss1 h)).symm

theorem cd_back_beta {M M' : Trm} {n : Nat} {E : Trm} (b : BetaH M M') (c : cd M' n E) :
    cd M (n + 1) E := by
  obtain ⟨M3, m1, m2⟩ := snf_beta b
  have : cd M3 n E := cd_snf c (snf_steps m2).symm
  exact .cdS m1 this

theorem cd_fwd_beta {M M' : Trm} {n : Nat} {E : Trm} (b : BetaH M M') (c : cd M n E) :
    ∃ m, n = m + 1 ∧ cd M' m E := by
  obtain ⟨M3, m1, m2⟩ := snf_beta b
  cases c with
  | cd0 hn => exact (hn _ m1).elim
  | cdS h1 h2 =>
    have e := beta_det h1 m1
    subst e
    exact ⟨_, rfl, cd_snf h2 (snf_steps m2)⟩

theorem WHNF_cd {N : Trm} (n : WHNF N) : cd N 0 N := by
  have sn : snf N = N := snf_unique (.refl _) (WHNF_imp_sig_normal n)
  have hn : normal BetaH N := fun b h => n b (Or.inr h)
  have := cd.cd0 (M := N) (by rw [sn]; exact hn)
  rwa [sn] at this

theorem steps_cd {M N : Trm} (r : WhSteps M N) (n : WHNF N) : ∃ k, cd M k N := by
  induction r with
  | refl => exact ⟨0, WHNF_cd n⟩
  | step h _ ih =>
    obtain ⟨k, c⟩ := ih n
    rcases h with h | h
    · exact ⟨k, cd_back_sig h c⟩
    · exact ⟨k + 1, cd_back_beta h c⟩

theorem cd_WHSN {M : Trm} {n : Nat} {E : Trm} (h : cd M n E) : WHSN M := by
  induction n using Nat.strongRecOn generalizing M with
  | _ n IHn =>
    have key : ∀ k (M : Trm), tlength M ≤ k → cd M n E → WHSN M := by
      intro k
      induction k with
      | zero => intro M hk; have := tlength_pos M; omega
      | succ k ihk =>
        intro M hk c
        refine SN_at.intro fun N s => ?_
        rcases s with s | s
        · exact ihk N (by have := sig_tlength_decrease s; omega) (cd_fwd_sig s c)
        · obtain ⟨m, hm, c'⟩ := cd_fwd_beta s c
          exact IHn m (by omega) c'
    exact key _ M (Nat.le_refl _) h

theorem cd_reach_end {M N' : Trm} (r : WhSteps M N') {n : Nat} {E : Trm} (c : cd M n E)
    (w : WHNF N') : N' = E := by
  induction r generalizing n with
  | refl => exact (cd_det (WHNF_cd w) c).2
  | step h _ ih =>
    rcases h with h | h
    · exact ih (cd_fwd_sig h c) w
    · obtain ⟨m, _, c'⟩ := cd_fwd_beta h c
      exact ih c' w

theorem CFWHN_imp_CFWHSN_general {M : Trm} (h : CFWHN M) : CFWHSN M := by
  obtain ⟨N, r, n, c⟩ := h
  obtain ⟨k, cdM⟩ := steps_cd r n
  refine ⟨cd_WHSN cdM, fun N' r' n' hc => ?_⟩
  have := cd_reach_end r' cdM n'
  subst this
  exact c hc

theorem WHNF_unique {M N1 N2 : Trm} (r1 : WhSteps M N1) (n1 : WHNF N1) (r2 : WhSteps M N2)
    (n2 : WHNF N2) : N1 = N2 := by
  obtain ⟨k, c⟩ := steps_cd r1 n1
  exact (cd_reach_end r2 c n2).symm

theorem main_characterization_full {M : Trm} : Typ M ↔ CFWHN M ∧ CFWHSN M :=
  ⟨fun h => ⟨main_characterization.1 h, CFWHN_imp_CFWHSN_general (main_characterization.1 h)⟩,
   fun h => main_characterization.2 h.1⟩

end LambdaEnvWH
