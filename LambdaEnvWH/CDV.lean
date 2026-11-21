import LambdaEnvWH.Lambda

/-!
# Classical intersection types (CDV style, with `ω` and `≤₀`) on de Bruijn terms

Port of `CDV.thy`.

Types, the subtyping relation `≤₀` (without `ω ≤ ω → ω` and without arrow
distributivity), essential types, and the typing relation.  Main result
`classical_WHN`: a term is weak-head normalizable iff it has an essential type.

Adaptations: Isabelle sets of terms (`dB set`) are predicates `dB → Prop`
(`t ∈ csem A` is `csem A t`); `A ≤₀ B` is `csub A B`; `Γ ⊢c t : A` is
`cty_of Γ t A`; `rtranclp` is `Star`.
-/

namespace LambdaEnvWH

open dB

inductive cty where
  | CTV : Nat → cty
  | COm : cty
  | CArr : cty → cty → cty
  | CInter : cty → cty → cty

open cty

inductive csub : cty → cty → Prop where
  | cs_refl (A : cty) : csub A A
  | cs_trans {A B C : cty} : csub A B → csub B C → csub A C
  | cs_om (A : cty) : csub A COm
  | cs_inter1 (A B : cty) : csub (CInter A B) A
  | cs_inter2 (A B : cty) : csub (CInter A B) B
  | cs_glb {A B C : cty} : csub A B → csub A C → csub A (CInter B C)
  | cs_arr {A' A B B' : cty} : csub A' A → csub B B' → csub (CArr A B) (CArr A' B')

def cess : cty → Bool
  | CTV _ => true
  | COm => false
  | CArr _ _ => true
  | CInter A B => cess A || cess B

/-- Stream cons (`a ## f` in Isabelle). -/
def scons {α : Type} (a : α) (f : Nat → α) : Nat → α
  | 0 => a
  | j + 1 => f j

infixr:65 " ## " => scons

@[simp] theorem scons_0 {α : Type} (a : α) (f : Nat → α) : (a ## f) 0 = a := rfl

@[simp] theorem scons_Suc {α : Type} (a : α) (f : Nat → α) (j : Nat) : (a ## f) (j + 1) = f j := rfl

@[simp] theorem scons_comp_Suc {α : Type} (a : α) (f : Nat → α) : (a ## f) ∘ Nat.succ = f := rfl

theorem scons_eta {α : Type} (f : Nat → α) : (f 0 ## (fun i => f (i + 1))) = f := by
  funext i; cases i <;> rfl

inductive cty_of : (Nat → cty) → dB → cty → Prop where
  | cVar {Γ : Nat → cty} {i : Nat} {A : cty} : Γ i = A → cty_of Γ (DVar i) A
  | cAbs {A : cty} {Γ : Nat → cty} {t : dB} {B : cty} :
      cty_of (A ## Γ) t B → cty_of Γ (DAbs t) (CArr A B)
  | cApp {Γ : Nat → cty} {s : dB} {A B : cty} {u : dB} :
      cty_of Γ s (CArr A B) → cty_of Γ u A → cty_of Γ (DApp s u) B
  | cOm {Γ : Nat → cty} {t : dB} : cty_of Γ t COm
  | cInter {Γ : Nat → cty} {t : dB} {A B : cty} :
      cty_of Γ t A → cty_of Γ t B → cty_of Γ t (CInter A B)
  | cSub {Γ : Nat → cty} {t : dB} {A B : cty} :
      cty_of Γ t A → csub A B → cty_of Γ t B

/-! ### Renamings and simultaneous substitution -/

def rup (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => r j + 1

@[simp] theorem rup_0 (r : Nat → Nat) : rup r 0 = 0 := rfl
@[simp] theorem rup_Suc (r : Nat → Nat) (j : Nat) : rup r (j + 1) = r j + 1 := rfl

def dbren : dB → (Nat → Nat) → dB
  | DVar i, r => DVar (r i)
  | DApp s t, r => DApp (dbren s r) (dbren t r)
  | DAbs s, r => DAbs (dbren s (rup r))

def dbup (s : Nat → dB) : Nat → dB
  | 0 => DVar 0
  | j + 1 => dbren (s j) Nat.succ

@[simp] theorem dbup_0 (s : Nat → dB) : dbup s 0 = DVar 0 := rfl
@[simp] theorem dbup_Suc (s : Nat → dB) (j : Nat) : dbup s (j + 1) = dbren (s j) Nat.succ := rfl

def dbsub : dB → (Nat → dB) → dB
  | DVar i, s => s i
  | DApp t u, s => DApp (dbsub t s) (dbsub u s)
  | DAbs t, s => DAbs (dbsub t (dbup s))

@[simp] theorem dbren_Var (i : Nat) (r : Nat → Nat) : dbren (DVar i) r = DVar (r i) := rfl
@[simp] theorem dbren_App (s t : dB) (r : Nat → Nat) :
    dbren (DApp s t) r = DApp (dbren s r) (dbren t r) := rfl
@[simp] theorem dbren_Abs (s : dB) (r : Nat → Nat) : dbren (DAbs s) r = DAbs (dbren s (rup r)) := rfl
@[simp] theorem dbsub_Var (i : Nat) (s : Nat → dB) : dbsub (DVar i) s = s i := rfl
@[simp] theorem dbsub_App (t u : dB) (s : Nat → dB) :
    dbsub (DApp t u) s = DApp (dbsub t s) (dbsub u s) := rfl
@[simp] theorem dbsub_Abs (t : dB) (s : Nat → dB) : dbsub (DAbs t) s = DAbs (dbsub t (dbup s)) := rfl

theorem rup_comp (r' r : Nat → Nat) : rup r' ∘ rup r = rup (r' ∘ r) := by
  funext i; cases i <;> rfl

theorem ren_ren (t : dB) : ∀ (r r' : Nat → Nat), dbren (dbren t r) r' = dbren t (r' ∘ r) := by
  induction t with
  | DVar i => intro r r'; rfl
  | DApp a b iha ihb => intro r r'; simp [iha, ihb]
  | DAbs a ih => intro r r'; simp [ih, rup_comp]

theorem dbup_rup (s : Nat → dB) (r : Nat → Nat) : dbup s ∘ rup r = dbup (s ∘ r) := by
  funext i; cases i <;> rfl

theorem sub_ren (t : dB) : ∀ (r : Nat → Nat) (s : Nat → dB), dbsub (dbren t r) s = dbsub t (s ∘ r) := by
  induction t with
  | DVar i => intro r s; rfl
  | DApp a b iha ihb => intro r s; simp [iha, ihb]
  | DAbs a ih => intro r s; simp [ih, dbup_rup]

theorem ren_dbup (s : Nat → dB) (r : Nat → Nat) :
    (fun i => dbren (dbup s i) (rup r)) = dbup (fun i => dbren (s i) r) := by
  funext i
  cases i with
  | zero => rfl
  | succ j => simp only [dbup_Suc]; rw [ren_ren, ren_ren]; rfl

theorem ren_sub (t : dB) : ∀ (r : Nat → Nat) (s : Nat → dB),
    dbren (dbsub t s) r = dbsub t (fun i => dbren (s i) r) := by
  induction t with
  | DVar i => intro r s; rfl
  | DApp a b iha ihb => intro r s; simp [iha, ihb]
  | DAbs a ih => intro r s; simp [ih, ren_dbup]

theorem sub_dbup (s τ : Nat → dB) :
    (fun i => dbsub (dbup s i) (dbup τ)) = dbup (fun i => dbsub (s i) τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    simp only [dbup_Suc]
    rw [sub_ren, ren_sub]
    rfl

theorem sub_sub (t : dB) : ∀ (s τ : Nat → dB),
    dbsub (dbsub t s) τ = dbsub t (fun i => dbsub (s i) τ) := by
  induction t with
  | DVar i => intro s τ; rfl
  | DApp a b iha ihb => intro s τ; simp [iha, ihb]
  | DAbs a ih => intro s τ; simp [ih, sub_dbup]

theorem dbup_var : dbup DVar = DVar := by
  funext i; cases i <;> rfl

@[simp] theorem sub_var (t : dB) : dbsub t DVar = t := by
  induction t with
  | DVar i => rfl
  | DApp a b iha ihb => simp [iha, ihb]
  | DAbs a ih => simp [dbup_var, ih]

def dl (k : Nat) : Nat → Nat := fun i => if i < k then i else i + 1

@[simp] theorem dl_simp (k i : Nat) : dl k i = (if i < k then i else i + 1) := rfl

theorem rup_dl (k : Nat) : rup (dl k) = dl (k + 1) := by
  funext i
  cases i with
  | zero => simp [dl]
  | succ j => by_cases h : j < k <;> simp [h]

theorem lift_ren (t : dB) : ∀ k, lift t k = dbren t (dl k) := by
  induction t with
  | DVar i => intro k; by_cases h : i < k <;> simp [h]
  | DApp a b iha ihb => intro k; simp [iha, ihb]
  | DAbs a ih => intro k; simp [ih, rup_dl]

theorem dl_0 : dl 0 = Nat.succ := by
  funext i; simp

def ins (k : Nat) (u : dB) (i : Nat) : dB :=
  if i < k then DVar i else if i = k then u else DVar (i - 1)

theorem dbup_ins (k : Nat) (u : dB) : dbup (ins k u) = ins (k + 1) (lift u 0) := by
  funext i
  cases i with
  | zero => simp [ins]
  | succ j =>
    simp only [dbup_Suc]
    by_cases h1 : j < k
    · simp [ins, h1]
    · by_cases h2 : j = k
      · subst h2; simp [ins, lift_ren, dl_0]
      · have h3 : ¬ j + 1 < k + 1 := by omega
        have h4 : j + 1 ≠ k + 1 := by omega
        simp [ins, h1, h2, h3, h4]
        cases j with
        | zero => omega
        | succ j' => rfl

theorem subst_sub (t : dB) : ∀ (k : Nat) (u : dB), subst t u k = dbsub t (ins k u) := by
  induction t with
  | DVar i =>
    intro k u
    simp only [subst_Var, ins, dbsub_Var]
    by_cases h1 : k < i
    · have : ¬ i < k := by omega
      have : i ≠ k := by omega
      simp [h1, *]
    · by_cases h2 : i = k <;> simp [h1, h2] <;> omega
  | DApp a b iha ihb => intro k u; simp [iha, ihb]
  | DAbs a ih => intro k u; simp [ih, dbup_ins]

theorem lift_subst0 (s t : dB) (k : Nat) :
    lift (subst s t 0) k = subst (lift s (k + 1)) (lift t k) 0 := by
  have e : (fun i => dbren (ins 0 t i) (dl k)) = ins 0 (lift t k) ∘ dl (k + 1) := by
    funext i
    cases i with
    | zero => simp [ins, lift_ren]
    | succ j =>
      by_cases h : j < k
      · simp [ins, h]
      · simp [ins, h]
  rw [subst_sub, lift_ren, ren_sub, e, subst_sub, ← sub_ren]
  simp only [lift_ren]

theorem sub_up (t : dB) (σ : Nat → dB) (u : dB) :
    subst (dbsub t (dbup σ)) u 0 = dbsub t (u ## σ) := by
  have e : (fun i => dbsub (dbup σ i) (ins 0 u)) = (u ## σ) := by
    funext i
    cases i with
    | zero => simp [ins]
    | succ j =>
      have : ins 0 u ∘ Nat.succ = DVar := by funext i; simp [ins]
      simp only [dbup_Suc]
      rw [sub_ren, this, sub_var]; rfl
  rw [subst_sub, sub_sub, e]

/-! ### Reduction, lifting, neutral terms -/

theorem hred_lift {s t : dB} (h : hred s t) : ∀ k, hred (lift s k) (lift t k) := by
  induction h with
  | hbeta s t =>
    intro k
    have := hred.hbeta (lift s (k + 1)) (lift t k)
    simpa [lift_subst0] using this
  | happ t _ ih => intro k; exact hred.happ _ (ih k)

theorem hred_lift_star {s t : dB} (h : Star hred s t) (k : Nat) :
    Star hred (lift s k) (lift t k) :=
  Star.map (fun s => lift s k) (fun _ _ h => hred_lift h k) h

inductive neutral : dB → Prop where
  | nvar (i : Nat) : neutral (DVar i)
  | napp {s : dB} (u : dB) : neutral s → neutral (DApp s u)

theorem neutral_lift {n : dB} (h : neutral n) (k : Nat) : neutral (lift n k) := by
  induction h with
  | nvar i => simp only [lift_Var]; split <;> exact neutral.nvar _
  | napp u _ ih => exact neutral.napp _ ih

theorem hred_app_inv {s u b : dB} (h : hred (DApp s u) b) :
    (∃ s0, s = DAbs s0) ∨ (∃ s', hred s s') := by
  cases h with
  | hbeta => exact Or.inl ⟨_, rfl⟩
  | happ _ h => exact Or.inr ⟨_, h⟩

theorem neutral_normal {n : dB} (h : neutral n) : normal hred n := by
  induction h with
  | nvar i => intro b hb; cases hb
  | napp u hs ih =>
    intro b hb
    rcases hred_app_inv hb with ⟨s0, e⟩ | ⟨s', h'⟩
    · subst e; cases hs
    · exact ih s' h'

theorem normal_shape {u : dB} : normal hred u → (∃ s, u = DAbs s) ∨ neutral u := by
  induction u with
  | DVar i => intro _; exact Or.inr (neutral.nvar i)
  | DApp s t ihs iht =>
    intro hn
    have ns : normal hred s := fun b h => hn _ (hred.happ t h)
    rcases ihs ns with ⟨x, e⟩ | h
    · subst e; exact absurd (hred.hbeta x t) (hn _)
    · exact Or.inr (neutral.napp t h)
  | DAbs s _ => intro _; exact Or.inl ⟨s, rfl⟩

theorem whn_abs (s : dB) : lam_WHN (DAbs s) :=
  ⟨DAbs s, Star.refl _, fun _ h => DAbs_no_step h⟩

theorem whn_neutral {n : dB} (h : neutral n) : lam_WHN n :=
  ⟨n, Star.refl _, neutral_normal h⟩

theorem whn_lift {t : dB} (h : lam_WHN t) (k : Nat) : lam_WHN (lift t k) := by
  obtain ⟨u, r, nf⟩ := h
  refine ⟨lift u k, hred_lift_star r k, ?_⟩
  rcases normal_shape nf with ⟨s, e⟩ | h
  · subst e; intro b hb; exact DAbs_no_step hb
  · exact neutral_normal (neutral_lift h k)

theorem whn_exp {t t' : dB} (h : hred t t') (w : lam_WHN t') : lam_WHN t := by
  obtain ⟨u, r, nf⟩ := w
  exact ⟨u, Star.step h r, nf⟩

def liftl : List Nat → dB → dB
  | [], t => t
  | k :: ks, t => liftl ks (lift t k)

@[simp] theorem liftl_nil (t : dB) : liftl [] t = t := rfl
@[simp] theorem liftl_cons (k : Nat) (ks : List Nat) (t : dB) :
    liftl (k :: ks) t = liftl ks (lift t k) := rfl

theorem liftl_hred {s t : dB} (h : hred s t) (ks : List Nat) : hred (liftl ks s) (liftl ks t) := by
  induction ks generalizing s t with
  | nil => exact h
  | cons k ks ih => exact ih (hred_lift h k)

theorem liftl_neutral {n : dB} (h : neutral n) (ks : List Nat) : neutral (liftl ks n) := by
  induction ks generalizing n with
  | nil => exact h
  | cons k ks ih => exact ih (neutral_lift h k)

theorem liftl_sub (t : dB) (ks : List Nat) :
    ∀ (s : Nat → dB), liftl ks (dbsub t s) = dbsub t (fun i => liftl ks (s i)) := by
  induction ks with
  | nil => intro s; rfl
  | cons k ks ih =>
    intro s
    rw [liftl_cons, lift_ren, ren_sub, ih]
    simp [lift_ren]

/-! ### Realizability semantics -/

/-- `csem A t` is Isabelle's `t ∈ csem A`. -/
def csem : cty → dB → Prop
  | CTV _, t => lam_WHN t
  | COm, _ => True
  | CArr A B, t => lam_WHN t ∧ ∀ ks u, csem A u → csem B (DApp (liftl ks t) u)
  | CInter A B, t => csem A t ∧ csem B t

theorem csem_lift (A : cty) : ∀ {t : dB}, csem A t → ∀ k, csem A (lift t k) := by
  induction A with
  | CTV a => intro t h k; exact whn_lift h k
  | COm => intro t h k; trivial
  | CArr A B _ _ =>
    intro t h k
    exact ⟨whn_lift h.1 k, fun ks u hu => h.2 (k :: ks) u hu⟩
  | CInter A B iha ihb => intro t h k; exact ⟨iha h.1 k, ihb h.2 k⟩

theorem csem_liftl {A : cty} {t : dB} (h : csem A t) (ks : List Nat) : csem A (liftl ks t) := by
  induction ks generalizing t with
  | nil => exact h
  | cons k ks ih => exact ih (csem_lift A h k)

theorem csem_neutral (A : cty) : ∀ {n : dB}, neutral n → csem A n := by
  induction A with
  | CTV a => intro n h; exact whn_neutral h
  | COm => intro n h; trivial
  | CArr A B _ ihb =>
    intro n h
    exact ⟨whn_neutral h, fun ks u _ => ihb (neutral.napp u (liftl_neutral h ks))⟩
  | CInter A B iha ihb => intro n h; exact ⟨iha h, ihb h⟩

theorem csem_exp (A : cty) : ∀ {t t' : dB}, hred t t' → csem A t' → csem A t := by
  induction A with
  | CTV a => intro t t' h m; exact whn_exp h m
  | COm => intro t t' h m; trivial
  | CArr A B _ ihb =>
    intro t t' h m
    refine ⟨whn_exp h m.1, fun ks u hu => ?_⟩
    exact ihb (hred.happ u (liftl_hred h ks)) (m.2 ks u hu)
  | CInter A B iha ihb => intro t t' h m; exact ⟨iha h m.1, ihb h m.2⟩

theorem csem_sub {A B : cty} (h : csub A B) : ∀ t, csem A t → csem B t := by
  induction h with
  | cs_refl => intro t m; exact m
  | cs_trans _ _ ih1 ih2 => intro t m; exact ih2 t (ih1 t m)
  | cs_om => intro t m; trivial
  | cs_inter1 => intro t m; exact m.1
  | cs_inter2 => intro t m; exact m.2
  | cs_glb _ _ ih1 ih2 => intro t m; exact ⟨ih1 t m, ih2 t m⟩
  | cs_arr _ _ ih1 ih2 =>
    intro t m
    exact ⟨m.1, fun ks u hu => ih2 _ (m.2 ks u (ih1 u hu))⟩

theorem csem_ess (A : cty) : cess A = true → ∀ t, csem A t → lam_WHN t := by
  induction A with
  | CTV a => intro _ t m; exact m
  | COm => intro h; cases h
  | CArr A B _ _ => intro _ t m; exact m.1
  | CInter A B iha ihb =>
    intro h t m
    simp only [cess, Bool.or_eq_true] at h
    rcases h with h | h
    · exact iha h t m.1
    · exact ihb h t m.2

theorem fund {Γ : Nat → cty} {t : dB} {A : cty} (h : cty_of Γ t A) :
    ∀ σ : Nat → dB, (∀ i, csem (Γ i) (σ i)) → csem A (dbsub t σ) := by
  induction h with
  | cVar e => intro σ hσ; subst e; exact hσ _
  | @cAbs A Γ t B _ ih =>
    intro σ h
    refine ⟨whn_abs _, fun ks u hu => ?_⟩
    have e : liftl ks (dbsub (DAbs t) σ) = DAbs (dbsub t (dbup (fun i => liftl ks (σ i)))) :=
      liftl_sub (DAbs t) ks σ
    have hs : ∀ i, csem ((A ## Γ) i) ((u ## (fun i => liftl ks (σ i))) i) := by
      intro i
      cases i with
      | zero => exact hu
      | succ j => exact csem_liftl (h j) ks
    have m := ih _ hs
    rw [← sub_up] at m
    rw [e]
    exact csem_exp B (hred.hbeta _ _) m
  | cApp _ _ ih1 ih2 =>
    intro σ h
    exact (ih1 σ h).2 [] _ (ih2 σ h)
  | cOm => intro σ _; trivial
  | cInter _ _ ih1 ih2 => intro σ h; exact ⟨ih1 σ h, ih2 σ h⟩
  | cSub _ hs ih => intro σ h; exact csem_sub hs _ (ih σ h)

theorem classical_sound {Γ : Nat → cty} {t : dB} {A : cty} (h : cty_of Γ t A)
    (e : cess A = true) : lam_WHN t := by
  have := fund h DVar (fun i => csem_neutral _ (neutral.nvar i))
  rw [sub_var] at this
  exact csem_ess A e t this

/-! ### Completeness: typing lemmas and subject expansion -/

theorem gen_var_aux {Γ : Nat → cty} {r : dB} {C : cty} (h : cty_of Γ r C) :
    ∀ i, r = DVar i → csub (Γ i) C := by
  induction h with
  | cVar e => intro i hi; cases hi; subst e; exact csub.cs_refl _
  | cAbs _ _ => intro i hi; cases hi
  | cApp _ _ _ _ => intro i hi; cases hi
  | cOm => intro i _; exact csub.cs_om _
  | cInter _ _ ih1 ih2 => intro i hi; exact csub.cs_glb (ih1 i hi) (ih2 i hi)
  | cSub _ hs ih => intro i hi; exact csub.cs_trans (ih i hi) hs

theorem gen_var {Γ : Nat → cty} {i : Nat} {C : cty} (h : cty_of Γ (DVar i) C) :
    csub (Γ i) C := gen_var_aux h i rfl

theorem ctx_mono_aux {Γ : Nat → cty} {t : dB} {A : cty} (h : cty_of Γ t A) :
    ∀ Γ' : Nat → cty, (∀ i, csub (Γ' i) (Γ i)) → cty_of Γ' t A := by
  induction h with
  | @cVar Γ i A e =>
    intro Γ' h
    subst e
    exact cty_of.cSub (cty_of.cVar rfl) (h i)
  | @cAbs A Γ t B _ ih =>
    intro Γ' h
    apply cty_of.cAbs
    apply ih
    intro i
    cases i with
    | zero => exact csub.cs_refl _
    | succ j => exact h j
  | cApp _ _ ih1 ih2 => intro Γ' h; exact cty_of.cApp (ih1 Γ' h) (ih2 Γ' h)
  | cOm => intro Γ' _; exact cty_of.cOm
  | cInter _ _ ih1 ih2 => intro Γ' h; exact cty_of.cInter (ih1 Γ' h) (ih2 Γ' h)
  | cSub _ hs ih => intro Γ' h; exact cty_of.cSub (ih Γ' h) hs

theorem ctx_mono {Γ Γ' : Nat → cty} {t : dB} {A : cty} (h : cty_of Γ t A)
    (hs : ∀ i, csub (Γ' i) (Γ i)) : cty_of Γ' t A :=
  ctx_mono_aux h Γ' hs

theorem strengthen_aux {Γ : Nat → cty} {r : dB} {A : cty} (h : cty_of Γ r A) :
    ∀ (ρ : Nat → Nat) (t : dB), r = dbren t ρ → cty_of (Γ ∘ ρ) t A := by
  induction h with
  | @cVar Γ i A e =>
    intro ρ t hr
    cases t with
    | DVar j =>
      simp only [dbren_Var, dB.DVar.injEq] at hr
      subst hr; exact cty_of.cVar e
    | DApp _ _ => simp at hr
    | DAbs _ => simp at hr
  | @cAbs A Γ t B _ ih =>
    intro ρ s hr
    cases s with
    | DVar _ => simp at hr
    | DApp _ _ => simp at hr
    | DAbs s1 =>
      simp only [dbren_Abs, dB.DAbs.injEq] at hr
      have := ih (rup ρ) s1 hr
      have e : (A ## Γ) ∘ rup ρ = A ## (Γ ∘ ρ) := by funext i; cases i <;> rfl
      rw [e] at this
      exact cty_of.cAbs this
  | cApp _ _ ih1 ih2 =>
    intro ρ s hr
    cases s with
    | DVar _ => simp at hr
    | DAbs _ => simp at hr
    | DApp s1 s2 =>
      simp only [dbren_App, dB.DApp.injEq] at hr
      exact cty_of.cApp (ih1 ρ s1 hr.1) (ih2 ρ s2 hr.2)
  | cOm => intro ρ t _; exact cty_of.cOm
  | cInter _ _ ih1 ih2 => intro ρ t hr; exact cty_of.cInter (ih1 ρ t hr) (ih2 ρ t hr)
  | cSub _ hs ih => intro ρ t hr; exact cty_of.cSub (ih ρ t hr) hs

theorem strengthen {Γ : Nat → cty} {t : dB} {ρ : Nat → Nat} {A : cty}
    (h : cty_of Γ (dbren t ρ) A) : cty_of (Γ ∘ ρ) t A :=
  strengthen_aux h ρ t rfl

theorem expand_var {Γ : Nat → cty} {σ : Nat → dB} {j : Nat} {A : cty}
    (h : cty_of Γ (σ j) A) :
    ∃ Δ : Nat → cty, (∀ i, cty_of Γ (σ i) (Δ i)) ∧ cty_of Δ (DVar j) A := by
  refine ⟨fun k => if k = j then A else COm, fun i => ?_, cty_of.cVar (by simp)⟩
  by_cases e : i = j
  · subst e; simpa using h
  · simpa [e] using cty_of.cOm

theorem expand_aux {Γ : Nat → cty} {r : dB} {A : cty} (h : cty_of Γ r A) :
    ∀ (s : dB) (σ : Nat → dB), r = dbsub s σ →
      ∃ Δ : Nat → cty, (∀ i, cty_of Γ (σ i) (Δ i)) ∧ cty_of Δ s A := by
  induction h with
  | @cVar Γ i A e =>
    intro s σ hr
    cases s with
    | DVar j =>
      have : σ j = DVar i := hr.symm
      exact expand_var (this ▸ cty_of.cVar e)
    | DApp _ _ => simp at hr
    | DAbs _ => simp at hr
  | @cAbs A Γ t B _ ih =>
    intro s σ hr
    cases s with
    | DVar j =>
      have : σ j = DAbs t := hr.symm
      exact expand_var (this ▸ cty_of.cAbs ‹_›)
    | DApp _ _ => simp at hr
    | DAbs s1 =>
      simp only [dbsub_Abs, dB.DAbs.injEq] at hr
      obtain ⟨Δ', h1, h2⟩ := ih s1 (dbup σ) hr
      have h0 : cty_of (A ## Γ) (DVar 0) (Δ' 0) := by simpa using h1 0
      have AC : csub A (Δ' 0) := gen_var h0
      have h2' : cty_of (Δ' 0 ## (fun i => Δ' (i + 1))) s1 B := by
        rw [scons_eta]; exact h2
      have d : cty_of (fun i => Δ' (i + 1)) (DAbs s1) (CArr A B) :=
        cty_of.cSub (cty_of.cAbs h2') (csub.cs_arr AC (csub.cs_refl _))
      refine ⟨fun i => Δ' (i + 1), fun i => ?_, d⟩
      have : cty_of (A ## Γ) (dbren (σ i) Nat.succ) (Δ' (i + 1)) := by simpa using h1 (i + 1)
      exact strengthen (ρ := Nat.succ) this
  | cApp _ _ ih1 ih2 =>
    rename_i Γ p A B q _ _
    intro s σ hr
    cases s with
    | DVar j =>
      have : σ j = DApp p q := hr.symm
      exact expand_var (this ▸ cty_of.cApp ‹_› ‹_›)
    | DAbs _ => simp at hr
    | DApp s1 s2 =>
      simp only [dbsub_App, dB.DApp.injEq] at hr
      obtain ⟨Δ1, a1, a2⟩ := ih1 s1 σ hr.1
      obtain ⟨Δ2, b1, b2⟩ := ih2 s2 σ hr.2
      refine ⟨fun i => CInter (Δ1 i) (Δ2 i), fun i => cty_of.cInter (a1 i) (b1 i), ?_⟩
      exact cty_of.cApp (ctx_mono a2 fun i => csub.cs_inter1 _ _)
        (ctx_mono b2 fun i => csub.cs_inter2 _ _)
  | cOm => intro s σ _; exact ⟨fun _ => COm, fun i => cty_of.cOm, cty_of.cOm⟩
  | cInter _ _ ih1 ih2 =>
    intro s σ hr
    obtain ⟨Δ1, a1, a2⟩ := ih1 s σ hr
    obtain ⟨Δ2, b1, b2⟩ := ih2 s σ hr
    refine ⟨fun i => CInter (Δ1 i) (Δ2 i), fun i => cty_of.cInter (a1 i) (b1 i), ?_⟩
    exact cty_of.cInter (ctx_mono a2 fun i => csub.cs_inter1 _ _)
      (ctx_mono b2 fun i => csub.cs_inter2 _ _)
  | cSub _ hs ih =>
    intro s σ hr
    obtain ⟨Δ, a1, a2⟩ := ih s σ hr
    exact ⟨Δ, a1, cty_of.cSub a2 hs⟩

theorem expand_beta {Γ : Nat → cty} {s u : dB} {A : cty} (h : cty_of Γ (subst s u 0) A) :
    cty_of Γ (DApp (DAbs s) u) A := by
  rw [subst_sub] at h
  obtain ⟨Δ, h1, h2⟩ := expand_aux h s (ins 0 u) rfl
  have h3 : ∀ i, csub (Γ i) (Δ (i + 1)) := by
    intro i
    have : cty_of Γ (ins 0 u (i + 1)) (Δ (i + 1)) := h1 (i + 1)
    have : cty_of Γ (DVar i) (Δ (i + 1)) := by simpa [ins] using this
    exact gen_var this
  have h4 : cty_of (Δ 0 ## Γ) s A := by
    apply ctx_mono h2
    intro i
    cases i with
    | zero => exact csub.cs_refl _
    | succ j => exact h3 j
  have h5 : cty_of Γ u (Δ 0) := by simpa [ins] using h1 0
  exact cty_of.cApp (cty_of.cAbs h4) h5

theorem expand_appL {Γ : Nat → cty} {r s s' u : dB} {A : cty} (h : cty_of Γ r A)
    (IH : ∀ (Γ : Nat → cty) (A : cty), cty_of Γ s' A → cty_of Γ s A) :
    r = DApp s' u → cty_of Γ (DApp s u) A := by
  induction h with
  | cVar _ => intro e; cases e
  | cAbs _ => intro e; cases e
  | cApp h1 h2 _ _ =>
    intro e
    cases e
    exact cty_of.cApp (IH _ _ h1) h2
  | cOm => intro _; exact cty_of.cOm
  | cInter _ _ ih1 ih2 => intro e; exact cty_of.cInter (ih1 e) (ih2 e)
  | cSub _ hs ih => intro e; exact cty_of.cSub (ih e) hs

theorem subject_expansion_hred {t t' : dB} (h : hred t t') :
    ∀ {Γ : Nat → cty} {A : cty}, cty_of Γ t' A → cty_of Γ t A := by
  induction h with
  | hbeta s t => intro Γ A h; exact expand_beta h
  | happ t _ ih => intro Γ A h; exact expand_appL h (fun Γ A h => ih h) rfl

/-! ### Completeness and the classical theorem -/

theorem neutral_typable {n : dB} (h : neutral n) : ∀ A, ∃ Γ : Nat → cty, cty_of Γ n A := by
  induction h with
  | nvar i => intro A; exact ⟨fun _ => A, cty_of.cVar rfl⟩
  | napp u _ ih =>
    intro A
    obtain ⟨Γ, h⟩ := ih (CArr COm A)
    exact ⟨Γ, cty_of.cApp h cty_of.cOm⟩

theorem normal_typable {u : dB} (nf : normal hred u) :
    ∃ (Γ : Nat → cty) (A : cty), cty_of Γ u A ∧ cess A = true := by
  rcases normal_shape nf with ⟨s, e⟩ | h
  · subst e
    exact ⟨fun _ => COm, CArr COm COm, cty_of.cAbs cty_of.cOm, rfl⟩
  · obtain ⟨Γ, h⟩ := neutral_typable h (CTV 0)
    exact ⟨Γ, CTV 0, h, rfl⟩

theorem classical_complete {t : dB} (h : lam_WHN t) :
    ∃ (Γ : Nat → cty) (A : cty), cty_of Γ t A ∧ cess A = true := by
  obtain ⟨u, r, nf⟩ := h
  have := normal_typable nf
  induction r with
  | refl => exact this
  | step h _ ih =>
    obtain ⟨Γ, A, h1, h2⟩ := ih nf this
    exact ⟨Γ, A, subject_expansion_hred h h1, h2⟩

theorem classical_WHN {t : dB} :
    lam_WHN t ↔ ∃ (Γ : Nat → cty) (A : cty), cty_of Γ t A ∧ cess A = true :=
  ⟨classical_complete, fun ⟨_, _, h, e⟩ => classical_sound h e⟩

end LambdaEnvWH
