/-
The correctness of `strongconnect` (exec.go, Tarjan's algorithm with an executed-on-pop component),
as pure lemmas over an abstract graph: the invariant `TInv` of the search state (the stack, the
active calls, `Index`/`Lowlink` of the visited nodes, the parent of each finished node) and one
lemma per transition of the code (`push`, the lowlink updates `lowStack`/`merge`, `pop`), with
`pop_ready`: a popped component is closed and strongly connected inside itself (the model's
`sccReady`).

The graph: edges `E` (the `deps` edges, fixed during a pass), the executed set `ex` (grows by the
popped components), `rd` (committed with commands). Reachability `Reach` follows edges into
non-executed nodes only, so that executing a closed component keeps the reachability between the
others (`reach_pop`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.State

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.tarjan

variable {α : Type} [DecidableEq α]

/-- Reflexive-transitive closure (built at the end). -/
inductive Reach (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Reach R a a
  | tail {a b c : α} : Reach R a b → R b c → Reach R a c

theorem Reach.single {R : α → α → Prop} {a b : α} (h : R a b) : Reach R a b :=
  .tail (.refl a) h

theorem Reach.trans {R : α → α → Prop} {a b c : α} (h1 : Reach R a b) (h2 : Reach R b c) :
    Reach R a c := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact .tail ih h

/-- The graph during a pass. -/
structure Gr (α : Type) where
  E : α → α → Prop
  ex : α → Prop
  rd : α → Prop

/-- An edge into a non-executed node. -/
def Gr.step (g : Gr α) (a b : α) : Prop := g.E a b ∧ ¬ g.ex b

/-- The search state: the stack `S` (bottom first), the active calls `A` (outermost first),
`Index`/`Lowlink` of the visited nodes, parents, the counter `*index`. -/
structure St (α : Type) where
  S : List α
  A : List α
  ix : α → Option (Nat × Nat)
  par : α → α
  n : Nat

def St.num (t : St α) (x : α) : Nat := ((t.ix x).map Prod.fst).getD 0
def St.low (t : St α) (x : α) : Nat := ((t.ix x).map Prod.snd).getD 0
def St.vis (t : St α) (x : α) : Prop := (t.ix x).isSome

/-- Edge `a → y` handled: `y` executed, or on the stack with `low a ≤ num y`. -/
def Done (g : Gr α) (t : St α) (a y : α) : Prop := g.ex y ∨ (y ∈ t.S ∧ t.low a ≤ t.num y)

def DoneAll (g : Gr α) (t : St α) (a : α) : Prop := ∀ y, g.E a y → Done g t a y

/-- A finished node (on the stack, its call returned without popping). -/
def Fin (g : Gr α) (t : St α) (x : α) : Prop :=
  t.low x < t.num x ∧ t.par x ∈ t.S ∧ t.num (t.par x) < t.num x ∧ g.E (t.par x) x ∧
    t.low (t.par x) ≤ t.low x ∧ (∀ a ∈ t.A, t.num a < t.num x → t.num a ≤ t.num (t.par x)) ∧
    DoneAll g t x

structure TInv (g : Gr α) (t : St α) : Prop where
  nodup : t.S.Nodup
  sorted : t.S.Pairwise (fun a b => t.num a < t.num b)
  onS : ∀ x ∈ t.S, t.vis x ∧ 0 < t.num x ∧ t.num x < t.n ∧ ¬ g.ex x ∧ g.rd x
  actS : ∀ a ∈ t.A, a ∈ t.S
  actSorted : t.A.Pairwise (fun a b => t.num a < t.num b)
  visS : ∀ x, t.vis x → ¬ g.ex x → x ∈ t.S
  reachUp : ∀ x ∈ t.S, ∀ y ∈ t.S, t.num x ≤ t.num y → Reach g.step x y
  lowW : ∀ x ∈ t.S, t.low x ≤ t.num x ∧ ∃ u ∈ t.S, t.num u = t.low x ∧ Reach g.step x u
  fin : ∀ x ∈ t.S, x ∉ t.A → Fin g t x

/-- What a failed search keeps: every visited non-executed node is on the stack (their `Index`
is reset by `findSCC`). -/
def WInv (g : Gr α) (t : St α) : Prop := ∀ x, t.vis x → ¬ g.ex x → x ∈ t.S

theorem TInv.winv {g : Gr α} {t : St α} (h : TInv g t) : WInv g t := h.visS

/-! ## List helpers -/

theorem pw_inj {f : α → Nat} : ∀ {l : List α}, l.Pairwise (fun a b => f a < f b) →
    ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · have := h.1 _ hy'; omega
    · have := h.1 _ hx'; omega
    · exact pw_inj h.2 hx' hy' he

theorem pw_last {f : α → Nat} {l : List α} {v : α}
    (h : (l ++ [v]).Pairwise (fun a b => f a < f b)) : ∀ a ∈ l ++ [v], f a ≤ f v := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rw [List.pairwise_append] at h
    have := h.2.2 a ha v (by simp); omega
  · simp at ha; subst ha; omega

/-- In `S0 ++ v :: T` sorted: `S0` below `v`, `T` above. -/
theorem pw_split {f : α → Nat} {S0 T : List α} {v : α}
    (h : (S0 ++ v :: T).Pairwise (fun a b => f a < f b)) :
    (∀ x ∈ S0, f x < f v) ∧ (∀ x ∈ T, f v < f x) := by
  rw [List.pairwise_append] at h
  refine ⟨fun x hx => h.2.2 x hx v (by simp), fun x hx => ?_⟩
  have := h.2.1; rw [List.pairwise_cons] at this; exact this.1 x hx

/-! ## Reachability -/

/-- Every stack node reaches the innermost active call. -/
theorem reach_top {g : Gr α} {t : St α} (h : TInv g t) {A0 : List α} {a : α}
    (hA : t.A = A0 ++ [a]) : ∀ x ∈ t.S, Reach g.step x a := by
  have haS : a ∈ t.S := h.actS a (by simp [hA])
  have hmax : ∀ b ∈ t.A, t.num b ≤ t.num a := by
    have := h.actSorted; rw [hA] at this ⊢; exact pw_last this
  intro x hx
  induction hn : t.num x using Nat.strongRecOn generalizing x with
  | _ k ih =>
    by_cases hle : t.num x ≤ t.num a
    · exact h.reachUp x hx a haS hle
    · have hxA : x ∉ t.A := fun hxa => hle (hmax x hxa)
      obtain ⟨hlt, -⟩ := h.fin x hx hxA
      obtain ⟨-, u, hu, hnu, hr⟩ := h.lowW x hx
      exact hr.trans (ih _ (by omega) u hu rfl)

/-- A path from inside a closed set stays inside it. -/
theorem reach_closed {g : Gr α} {C : List α}
    (hcl : ∀ a ∈ C, ∀ b, g.E a b → g.ex b ∨ b ∈ C) {x y : α} (hr : Reach g.step x y)
    (hx : x ∈ C) : y ∈ C ∧ (x = y ∨ Relation.TransGen (fun a b => g.E a b ∧ a ∈ C ∧ b ∈ C) x y) := by
  induction hr with
  | refl => exact ⟨hx, Or.inl rfl⟩
  | @tail b c _ hs ih =>
    obtain ⟨hb, hxb⟩ := ih
    have hc : c ∈ C := (hcl b hb c hs.1).resolve_left hs.2
    refine ⟨hc, Or.inr ?_⟩
    rcases hxb with rfl | hxb
    · exact .single ⟨hs.1, hb, hc⟩
    · exact .tail hxb ⟨hs.1, hb, hc⟩

/-- Executing (part of) a closed set keeps the paths that end outside it. -/
theorem reach_pop {g g' : Gr α} {C : List α}
    (hcl : ∀ a ∈ C, ∀ b, g.E a b → g.ex b ∨ b ∈ C)
    (hE : g'.E = g.E) (hex : ∀ z, g'.ex z → g.ex z ∨ z ∈ C) {x y : α}
    (hr : Reach g.step x y) (hy : y ∉ C) : Reach g'.step x y := by
  induction hr with
  | refl => exact .refl _
  | @tail b c _ hs ih =>
    have hb : b ∉ C := fun hb => hy ((hcl b hb c hs.1).resolve_left hs.2)
    refine .tail (ih hb) ⟨hE ▸ hs.1, fun he => ?_⟩
    rcases hex c he with h | h
    · exact hs.2 h
    · exact hy h

/-! ## Lowlinks along the parents -/

/-- Below the innermost active call `v`, every node above it has a lowlink `≥ low v`. -/
theorem low_chain {g : Gr α} {t : St α} (h : TInv g t) {A0 : List α} {v : α}
    (hA : t.A = A0 ++ [v]) : ∀ x ∈ t.S, t.num v < t.num x → t.low v ≤ t.low x := by
  have hvS : v ∈ t.S := h.actS v (by simp [hA])
  have hmax : ∀ b ∈ t.A, t.num b ≤ t.num v := by
    have := h.actSorted; rw [hA] at this ⊢; exact pw_last this
  intro x hx hlt
  induction hn : t.num x using Nat.strongRecOn generalizing x with
  | _ k ih =>
    have hxA : x ∉ t.A := fun hxa => by have := hmax x hxa; omega
    obtain ⟨-, hpS, hpn, -, hpl, hpa, -⟩ := h.fin x hx hxA
    have hvp := hpa v (by simp [hA]) hlt
    by_cases hpv : t.par x = v
    · rw [hpv] at hpl; exact hpl
    · have : t.num v < t.num (t.par x) := by
        rcases Nat.lt_or_eq_of_le hvp with h' | h'
        · exact h'
        · exact absurd (pw_inj h.sorted hpS hvS h'.symm) hpv
      exact Nat.le_trans (ih _ (by omega) _ hpS this rfl) hpl

/-! ## Pop: the component is ready -/

section pop
variable {g : Gr α} {t : St α} {A0 S0 T : List α} {v : α}

theorem pop_closed (h : TInv g t) (hA : t.A = A0 ++ [v]) (hS : t.S = S0 ++ v :: T)
    (hlv : t.low v = t.num v) (hdv : DoneAll g t v) :
    ∀ x ∈ v :: T, ∀ y, g.E x y → g.ex y ∨ y ∈ v :: T := by
  have hsort := h.sorted; rw [hS] at hsort
  obtain ⟨hlo, hhi⟩ := pw_split hsort
  have hvS : v ∈ t.S := by simp [hS]
  have hmax : ∀ b ∈ t.A, t.num b ≤ t.num v := by
    have := h.actSorted; rw [hA] at this ⊢; exact pw_last this
  -- a stack node at or above `num v` is in `v :: T`
  have hup : ∀ y ∈ t.S, t.num v ≤ t.num y → y ∈ v :: T := by
    intro y hy hle
    rw [hS] at hy
    rcases List.mem_append.mp hy with hy | hy
    · have := hlo y hy; omega
    · exact hy
  intro x hx y he
  rcases List.mem_cons.mp hx with rfl | hxT
  · rcases hdv y he with hy | ⟨hy, hl⟩
    · exact Or.inl hy
    · exact Or.inr (hup y hy (by omega))
  · have hxS : x ∈ t.S := by simp [hS, hxT]
    have hgt := hhi x hxT
    have hxA : x ∉ t.A := fun hxa => by have := hmax x hxa; omega
    obtain ⟨-, -, -, -, -, -, hd⟩ := h.fin x hxS hxA
    have hch := low_chain h hA x hxS hgt
    rcases hd y he with hy | ⟨hy, hl⟩
    · exact Or.inl hy
    · exact Or.inr (hup y hy (by omega))

theorem pop_reach_root (h : TInv g t) (hA : t.A = A0 ++ [v]) (hS : t.S = S0 ++ v :: T)
    (hlv : t.low v = t.num v) : ∀ x ∈ v :: T, Reach g.step x v := by
  have hsort := h.sorted; rw [hS] at hsort
  obtain ⟨hlo, hhi⟩ := pw_split hsort
  have hmax : ∀ b ∈ t.A, t.num b ≤ t.num v := by
    have := h.actSorted; rw [hA] at this ⊢; exact pw_last this
  intro x hx
  induction hn : t.num x using Nat.strongRecOn generalizing x with
  | _ k ih =>
    rcases List.mem_cons.mp hx with rfl | hxT
    · exact .refl _
    · have hxS : x ∈ t.S := by simp [hS, hxT]
      have hgt := hhi x hxT
      have hxA : x ∉ t.A := fun hxa => by have := hmax x hxa; omega
      obtain ⟨hlt, -⟩ := h.fin x hxS hxA
      obtain ⟨-, u, hu, hnu, hr⟩ := h.lowW x hxS
      have hch := low_chain h hA x hxS hgt
      have huC : u ∈ v :: T := by
        rw [hS] at hu
        rcases List.mem_append.mp hu with hu | hu
        · have := hlo u hu; omega
        · exact hu
      exact hr.trans (ih _ (by omega) u huC rfl)

/-- **The popped component is the model's `sccReady` (abstractly).** -/
theorem pop_ready (h : TInv g t) (hA : t.A = A0 ++ [v]) (hS : t.S = S0 ++ v :: T)
    (hlv : t.low v = t.num v) (hdv : DoneAll g t v) :
    (v :: T).Nodup ∧ (∀ x ∈ v :: T, g.rd x ∧ ¬ g.ex x) ∧
    (∀ x ∈ v :: T, ∀ y, g.E x y → g.ex y ∨ y ∈ v :: T) ∧
    (∀ x ∈ v :: T, ∀ y ∈ v :: T, x = y ∨
      Relation.TransGen (fun a b => g.E a b ∧ a ∈ v :: T ∧ b ∈ v :: T) x y) := by
  have hcl := pop_closed h hA hS hlv hdv
  refine ⟨?_, ?_, hcl, ?_⟩
  · have := h.nodup; rw [hS] at this; exact (List.nodup_append.mp this).2.1
  · intro x hx
    have hxS : x ∈ t.S := by rw [hS]; exact List.mem_append_right _ hx
    obtain ⟨-, -, -, h1, h2⟩ := h.onS x hxS
    exact ⟨h2, h1⟩
  · intro x hx y hy
    have hvS : v ∈ t.S := by simp [hS]
    have hyS : y ∈ t.S := by rw [hS]; exact List.mem_append_right _ hy
    have hsort := h.sorted; rw [hS] at hsort
    obtain ⟨-, hhi⟩ := pw_split hsort
    have hvy : t.num v ≤ t.num y := by
      rcases List.mem_cons.mp hy with rfl | hyT
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (hhi y hyT)
    have hr := (pop_reach_root h hA hS hlv x hx).trans (h.reachUp v hvS y hyS hvy)
    exact (reach_closed hcl hr hx).2

/-- After the component is executed, the search state without it is a search state. -/
theorem pop_inv (h : TInv g t) (hA : t.A = A0 ++ [v]) (hS : t.S = S0 ++ v :: T)
    (hlv : t.low v = t.num v) (hdv : DoneAll g t v) (g' : Gr α)
    (hE : g'.E = g.E) (hex : ∀ z, g'.ex z ↔ g.ex z ∨ z ∈ v :: T)
    (hrd : ∀ z, z ∉ v :: T → g.rd z → g'.rd z) :
    TInv g' { t with S := S0, A := A0 } := by
  have hcl := pop_closed h hA hS hlv hdv
  have hsort := h.sorted; rw [hS] at hsort
  obtain ⟨hlo, hhi⟩ := pw_split hsort
  have hnd := h.nodup; rw [hS] at hnd
  have hdisj : ∀ x ∈ S0, x ∉ v :: T := fun x hx hx' =>
    (List.nodup_append.mp hnd).2.2 x hx x hx' rfl
  have hS0 : ∀ x ∈ S0, x ∈ t.S := fun x hx => by rw [hS]; exact List.mem_append_left _ hx
  have hmax : ∀ b ∈ t.A, t.num b ≤ t.num v := by
    have := h.actSorted; rw [hA] at this ⊢; exact pw_last this
  -- a stack node below `num v` is in `S0`
  have hdown : ∀ y ∈ t.S, t.num y < t.num v → y ∈ S0 := by
    intro y hy hlt
    rw [hS] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hy
    · rcases List.mem_cons.mp hy with rfl | hyT
      · omega
      · have := hhi y hyT; omega
  have hrp : ∀ x y, Reach g.step x y → y ∉ v :: T → Reach g'.step x y := fun x y hr hy =>
    reach_pop hcl hE (fun z hz => (hex z).mp hz) hr hy
  constructor
  · exact (List.nodup_append.mp hnd).1
  · exact (List.pairwise_append.mp hsort).1
  · intro x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.onS x (hS0 x hx)
    refine ⟨h1, h2, h3, fun he => ?_, hrd x (hdisj x hx) h5⟩
    rcases (hex x).mp he with he | he
    · exact h4 he
    · exact hdisj x hx he
  · intro a ha
    have haA : a ∈ t.A := by rw [hA]; exact List.mem_append_left _ ha
    have hlt : t.num a < t.num v := by
      have := h.actSorted; rw [hA, List.pairwise_append] at this
      exact this.2.2 a ha v (by simp)
    exact hdown a (h.actS a haA) hlt
  · have := h.actSorted; rw [hA] at this; exact (List.pairwise_append.mp this).1
  · intro x hv hne
    have hne' : ¬ g.ex x := fun he => hne ((hex x).mpr (Or.inl he))
    have hxS := h.visS x hv hne'
    have hxC : x ∉ v :: T := fun hc => hne ((hex x).mpr (Or.inr hc))
    rw [hS] at hxS
    rcases List.mem_append.mp hxS with hx | hx
    · exact hx
    · exact absurd hx hxC
  · intro x hx y hy hle
    exact hrp x y (h.reachUp x (hS0 x hx) y (hS0 y hy) hle) (hdisj y hy)
  · intro x hx
    obtain ⟨hl, u, hu, hnu, hr⟩ := h.lowW x (hS0 x hx)
    have hux : t.num u < t.num v := by have := hlo x hx; omega
    have hu0 := hdown u hu hux
    exact ⟨hl, u, hu0, hnu, hrp x u hr (hdisj u hu0)⟩
  · intro x hx hxA0
    have hxv : x ≠ v := fun he => hdisj x hx (by simp [he])
    have hxA : x ∉ t.A := by
      rw [hA]; intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hxA0 hm
      · simp at hm; exact hxv hm
    obtain ⟨h1, hpS, hpn, hpe, hpl, hpa, hd⟩ := h.fin x (hS0 x hx) hxA
    have hxv' := hlo x hx
    refine ⟨h1, hdown (t.par x) hpS (by omega), hpn, hE ▸ hpe, hpl, ?_, ?_⟩
    · intro a ha; exact hpa a (by rw [hA]; exact List.mem_append_left _ ha)
    · intro y he
      rcases hd y (hE ▸ he) with hy | ⟨hy, hl⟩
      · exact Or.inl ((hex y).mpr (Or.inl hy))
      · by_cases hyC : y ∈ v :: T
        · exact Or.inl ((hex y).mpr (Or.inr hyC))
        · right; refine ⟨?_, hl⟩
          rw [hS] at hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hy
          · exact absurd hy hyC

end pop

/-! ## Push -/

/-- `strongconnect(v)`'s start: `Index = Lowlink = *index`, `*index++`, `v` pushed and active (its
caller `a`, the innermost active call, has an edge to it). -/
def St.push (t : St α) (v : α) : St α :=
  { t with S := t.S ++ [v], A := t.A ++ [v],
           ix := fun x => if x = v then some (t.n, t.n) else t.ix x,
           par := fun x => if x = v then (t.A.getLast?.getD v) else t.par x,
           n := t.n + 1 }

theorem push_num (t : St α) (v x : α) :
    (t.push v).num x = if x = v then t.n else t.num x := by
  unfold St.num St.push; split <;> simp_all

theorem push_low (t : St α) (v x : α) :
    (t.push v).low x = if x = v then t.n else t.low x := by
  unfold St.low St.push; split <;> simp_all

theorem push_inv {g : Gr α} {t : St α} (h : TInv g t) {v : α} (hv : ¬ t.vis v)
    (hex : ¬ g.ex v) (hrd : g.rd v) (hroot : t.A = [] → t.S = [])
    (hedge : ∀ a, t.A.getLast? = some a → g.E a v) (hn0 : 0 < t.n) :
    TInv g (t.push v) := by
  have hvS : v ∉ t.S := fun hm => hv (h.onS v hm).1
  have hnum : ∀ x, x ≠ v → (t.push v).num x = t.num x := fun x hx => by
    rw [push_num]; simp [hx]
  have hlow : ∀ x, x ≠ v → (t.push v).low x = t.low x := fun x hx => by
    rw [push_low]; simp [hx]
  have hnv : (t.push v).num v = t.n := by rw [push_num]; simp
  have hlv : (t.push v).low v = t.n := by rw [push_low]; simp
  have hne : ∀ x ∈ t.S, x ≠ v := fun x hx he => hvS (he ▸ hx)
  have hnA : ∀ x ∈ t.A, x ≠ v := fun x hx => hne x (h.actS x hx)
  -- every old stack node reaches `v`
  have hreachv : ∀ x ∈ t.S, Reach g.step x v := by
    intro x hx
    rcases hA : t.A.getLast? with _ | a
    · rw [List.getLast?_eq_none_iff] at hA; rw [hroot hA] at hx; cases hx
    · obtain ⟨A0, hA0⟩ : ∃ A0, t.A = A0 ++ [a] := by
        rw [List.getLast?_eq_some_iff] at hA; exact hA
      exact (reach_top h hA0 x hx).tail ⟨hedge a (by rw [hA]), hex⟩
  constructor
  · show (t.S ++ [v]).Nodup
    rw [List.nodup_append]; exact ⟨h.nodup, by simp, fun x hx y hy he => hvS (by simp at hy; subst hy; subst he; exact hx)⟩
  · show (t.S ++ [v]).Pairwise _
    rw [List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · exact List.Pairwise.imp_of_mem (fun {a b} ha hb hlt => by
        rw [hnum a (hne a ha), hnum b (hne b hb)]; exact hlt) h.sorted
    · intro a ha b hb; simp at hb; subst hb
      rw [hnum a (hne a ha), hnv]; exact (h.onS a ha).2.2.1
  · intro x hx
    show (t.push v).vis x ∧ _
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h1, h2, h3, h4, h5⟩ := h.onS x hx
      refine ⟨?_, by rw [hnum x (hne x hx)]; exact h2, by rw [hnum x (hne x hx)]; simp only [St.push]; omega, h4, h5⟩
      unfold St.vis St.push; simp [hne x hx]; exact h1
    · simp at hx; subst hx
      refine ⟨by unfold St.vis St.push; simp, by rw [hnv]; exact hn0, by rw [hnv]; show t.n < t.n + 1; omega, hex, hrd⟩
  · intro a ha
    show a ∈ t.S ++ [v]
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (h.actS a ha)
    · exact List.mem_append_right _ ha
  · show (t.A ++ [v]).Pairwise _
    rw [List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · exact List.Pairwise.imp_of_mem (fun {a b} ha hb hlt => by
        rw [hnum a (hnA a ha), hnum b (hnA b hb)]; exact hlt) h.actSorted
    · intro a ha b hb; simp at hb; subst hb
      rw [hnum a (hnA a ha), hnv]; exact (h.onS a (h.actS a ha)).2.2.1
  · intro x hvx hexx
    show x ∈ t.S ++ [v]
    by_cases hxv : x = v
    · subst hxv; simp
    · have : t.vis x := by unfold St.vis St.push at hvx; simp [hxv] at hvx; exact hvx
      exact List.mem_append_left _ (h.visS x this hexx)
  · intro x hx y hy hle
    rcases List.mem_append.mp hy with hy1 | hy1
    · rcases List.mem_append.mp hx with hx1 | hx1
      · rw [hnum x (hne x hx1), hnum y (hne y hy1)] at hle
        exact h.reachUp x hx1 y hy1 hle
      · have hxv : x = v := by simpa using hx1
        rw [hxv, hnv, hnum y (hne y hy1)] at hle
        have := (h.onS y hy1).2.2.1; omega
    · have hyv : y = v := by simpa using hy1
      rw [hyv]
      rcases List.mem_append.mp hx with hx1 | hx1
      · exact hreachv x hx1
      · have hxv : x = v := by simpa using hx1
        rw [hxv]; exact .refl _
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨hl, u, hu, hnu, hr⟩ := h.lowW x hx
      refine ⟨by rw [hlow x (hne x hx), hnum x (hne x hx)]; exact hl, u, List.mem_append_left _ hu, ?_, hr⟩
      rw [hnum u (hne u hu), hlow x (hne x hx)]; exact hnu
    · simp at hx; subst hx
      exact ⟨by rw [hlv, hnv]; exact Nat.le_refl _, x, by simp [St.push], by rw [hlv, hnv], .refl _⟩
  · intro x hx hxA
    have hxv : x ≠ v := fun he => hxA (by simp [St.push, he])
    have hxS : x ∈ t.S := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · simp at hx; exact absurd hx hxv
    have hxA' : x ∉ t.A := fun hm => hxA (List.mem_append_left _ hm)
    obtain ⟨h1, hpS, hpn, hpe, hpl, hpa, hd⟩ := h.fin x hxS hxA'
    have hpv := hne _ hpS
    have hpar : (t.push v).par x = t.par x := by simp [St.push, hxv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlow x hxv, hnum x hxv]; exact h1
    · rw [hpar]; exact List.mem_append_left _ hpS
    · rw [hpar, hnum _ hpv, hnum x hxv]; exact hpn
    · rw [hpar]; exact hpe
    · rw [hpar, hlow _ hpv, hlow x hxv]; exact hpl
    · intro a ha hlt
      rw [hpar]
      rcases List.mem_append.mp ha with ha | ha
      · rw [hnum a (hnA a ha), hnum x hxv] at hlt
        rw [hnum a (hnA a ha), hnum _ hpv]; exact hpa a ha hlt
      · simp at ha; subst ha
        rw [hnv, hnum x hxv] at hlt
        have := (h.onS x hxS).2.2.1; omega
    · intro y hy
      rcases hd y hy with hy' | ⟨hy', hl⟩
      · exact Or.inl hy'
      · right; refine ⟨List.mem_append_left _ hy', ?_⟩
        rw [hlow x hxv, hnum y (hne y hy')]; exact hl

/-! ## Lowlink updates of the innermost active call -/

/-- `v.Lowlink = l` in the state. -/
def St.setLow (t : St α) (v : α) (l : Nat) : St α :=
  { t with ix := fun x => if x = v then some (t.num v, l) else t.ix x }

theorem setLow_num (t : St α) (v x : α) (hv : t.vis v) : (t.setLow v l).num x = t.num x := by
  by_cases hx : x = v
  · subst hx; simp [St.num, St.setLow]
  · simp [St.num, St.setLow, hx]

theorem setLow_low (t : St α) (v x : α) : (t.setLow v l).low x = if x = v then l else t.low x := by
  by_cases hx : x = v
  · subst hx; simp [St.low, St.setLow]
  · simp [St.low, St.setLow, hx]

theorem setLow_vis (t : St α) (v x : α) (hv : t.vis v) : (t.setLow v l).vis x ↔ t.vis x := by
  by_cases hx : x = v
  · subst hx; simp [St.vis, St.setLow]; exact hv
  · simp [St.vis, St.setLow, hx]

/-- Lowering the innermost active call's lowlink to `l`, with a witness `u` on the stack reached
from it, `num u = l`. -/
theorem setLow_inv {g : Gr α} {t : St α} (h : TInv g t) {A0 : List α} {v : α}
    (hA : t.A = A0 ++ [v]) (l : Nat) (hl : l ≤ t.low v) (u : α) (hu : u ∈ t.S)
    (hnu : t.num u = l) (hr : Reach g.step v u) : TInv g (t.setLow v l) := by
  have hvS : v ∈ t.S := h.actS v (by simp [hA])
  have hvv : t.vis v := (h.onS v hvS).1
  have hnum := fun x => setLow_num (l := l) t v x hvv
  have hvis := fun x => setLow_vis (l := l) t v x hvv
  have hlow := fun x => setLow_low (l := l) t v x
  constructor
  · exact h.nodup
  · show t.S.Pairwise _
    simp only [hnum]; exact h.sorted
  · intro x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.onS x hx
    exact ⟨(hvis x).mpr h1, by rw [hnum]; exact h2, by rw [hnum]; exact h3, h4, h5⟩
  · exact h.actS
  · show t.A.Pairwise _
    simp only [hnum]; exact h.actSorted
  · intro x hx hne; exact h.visS x ((hvis x).mp hx) hne
  · intro x hx y hy hle; rw [hnum, hnum] at hle; exact h.reachUp x hx y hy hle
  · intro x hx
    rw [hlow, hnum]
    by_cases hxv : x = v
    · subst hxv; simp only [↓reduceIte]
      exact ⟨Nat.le_trans hl (h.lowW x hx).1, u, hu, by rw [hnum]; exact hnu, hr⟩
    · simp only [hxv, ↓reduceIte]
      obtain ⟨h1, u', hu', hnu', hr'⟩ := h.lowW x hx
      exact ⟨h1, u', hu', by rw [hnum]; exact hnu', hr'⟩
  · intro x hx hxA
    have hxA' : x ∉ t.A := hxA
    have hxv : x ≠ v := fun he => hxA' (by rw [hA, he]; simp)
    obtain ⟨h1, hpS, hpn, hpe, hpl, hpa, hd⟩ := h.fin x hx hxA'
    unfold Fin
    rw [show (t.setLow v l).par = t.par from rfl, show (t.setLow v l).S = t.S from rfl,
      show (t.setLow v l).A = t.A from rfl]
    simp only [hnum, hlow, hxv, ↓reduceIte]
    refine ⟨h1, hpS, hpn, hpe, ?_, hpa, ?_⟩
    · split
      · rename_i hp; rw [hp] at hpl; exact Nat.le_trans hl hpl
      · exact hpl
    · intro y hy
      rcases hd y hy with hy' | ⟨hy', hl'⟩
      · exact Or.inl hy'
      · right; refine ⟨hy', ?_⟩; simp only [hlow, hnum, hxv, ↓reduceIte]; exact hl'

theorem setLow_done {g : Gr α} {t : St α} {v a y : α} (hv : t.vis v) {l : Nat}
    (hd : Done g t a y) (hl : a = v → l ≤ t.low v) : Done g (t.setLow v l) a y := by
  rcases hd with hy | ⟨hy, hle⟩
  · exact Or.inl hy
  · right; refine ⟨hy, ?_⟩
    rw [setLow_low, setLow_num _ _ _ hv]
    split
    · rename_i he; subst he; exact Nat.le_trans (hl rfl) hle
    · exact hle

/-- The edge `v → w` to a node on the stack: `if w.Index < v.Lowlink { v.Lowlink = w.Index }`. -/
theorem lowStack_inv {g : Gr α} {t : St α} (h : TInv g t) {A0 : List α} {v w : α}
    (hA : t.A = A0 ++ [v]) (hw : w ∈ t.S) (he : g.E v w) (hlt : t.num w < t.low v) :
    TInv g (t.setLow v (t.num w)) :=
  setLow_inv h hA _ (Nat.le_of_lt hlt) w hw rfl (.single ⟨he, (h.onS w hw).2.2.2.1⟩)

/-- The child `w` returned finished: it leaves the active calls and `v.Lowlink` takes the
minimum (`if w.Lowlink < v.Lowlink { v.Lowlink = w.Lowlink }`). -/
def St.merge (t : St α) (A0 : List α) (v w : α) : St α :=
  ({ t with A := A0 ++ [v] } : St α).setLow v (min (t.low v) (t.low w))

theorem merge_inv {g : Gr α} {t : St α} {A0 : List α} {v w : α}
    (h : TInv g t) (hA : t.A = A0 ++ [v, w]) (hlw : t.low w < t.num w) (hdw : DoneAll g t w)
    (hpar : t.par w = v) (he : g.E v w) :
    TInv g (t.merge A0 v w) := by
  have hwS : w ∈ t.S := h.actS w (by simp [hA])
  have hvS : v ∈ t.S := h.actS v (by simp [hA])
  have hvv : t.vis v := (h.onS v hvS).1
  have hA' : t.A = (A0 ++ [v]) ++ [w] := by simp [hA]
  have hpw := h.actSorted; rw [hA', List.pairwise_append] at hpw
  have hvw : t.num v < t.num w := hpw.2.2 v (by simp) w (by simp)
  have hwv : w ≠ v := fun e => by rw [e] at hvw; omega
  have hmax : ∀ a ∈ A0 ++ [v], t.num a ≤ t.num v := pw_last hpw.1
  have hsub : ∀ a ∈ A0 ++ [v], a ∈ t.A := fun a ha => by rw [hA']; exact List.mem_append_left _ ha
  have hnum : ∀ x, (t.merge A0 v w).num x = t.num x := fun x => by
    exact setLow_num ({ t with A := A0 ++ [v] } : St α) v x hvv
  have hvis : ∀ x, (t.merge A0 v w).vis x ↔ t.vis x := fun x => by
    exact setLow_vis ({ t with A := A0 ++ [v] } : St α) v x hvv
  have hlow : ∀ x, (t.merge A0 v w).low x = if x = v then min (t.low v) (t.low w) else t.low x :=
    fun x => setLow_low ({ t with A := A0 ++ [v] } : St α) v x
  have hS : (t.merge A0 v w).S = t.S := rfl
  have hAm : (t.merge A0 v w).A = A0 ++ [v] := rfl
  have hparm : (t.merge A0 v w).par = t.par := rfl
  constructor
  · exact h.nodup
  · rw [hS]; simp only [hnum]; exact h.sorted
  · intro x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.onS x hx
    exact ⟨(hvis x).mpr h1, by rw [hnum]; exact h2, by rw [hnum]; exact h3, h4, h5⟩
  · intro a ha; exact h.actS a (hsub a ha)
  · rw [hAm]; simp only [hnum]; exact hpw.1
  · intro x hx hne; exact h.visS x ((hvis x).mp hx) hne
  · intro x hx y hy hle; rw [hnum, hnum] at hle; exact h.reachUp x hx y hy hle
  · intro x hx
    rw [hlow, hnum]
    by_cases hxv : x = v
    · subst hxv; simp only [↓reduceIte]
      obtain ⟨hl, u, hu, hnu, hr⟩ := h.lowW x hx
      refine ⟨Nat.le_trans (Nat.min_le_left _ _) hl, ?_⟩
      by_cases hm : t.low x ≤ t.low w
      · exact ⟨u, hu, by rw [hnum, hnu]; omega, hr⟩
      · obtain ⟨-, u', hu', hnu', hr'⟩ := h.lowW w hwS
        exact ⟨u', hu', by rw [hnum, hnu']; omega,
          (Reach.single ⟨he, (h.onS w hwS).2.2.2.1⟩).trans hr'⟩
    · simp only [hxv, ↓reduceIte]
      obtain ⟨h1, u', hu', hnu', hr'⟩ := h.lowW x hx
      exact ⟨h1, u', hu', by rw [hnum]; exact hnu', hr'⟩
  · intro x hx hxA
    rw [hAm] at hxA
    show Fin g (t.merge A0 v w) x
    have hxv : x ≠ v := fun e => hxA (by simp [e])
    unfold Fin
    rw [hparm, hS, hAm]
    simp only [hnum, hlow, hxv, ↓reduceIte]
    have hdone : ∀ y, Done g t x y → Done g (t.merge A0 v w) x y := by
      intro y hd
      rcases hd with hy | ⟨hy, hl⟩
      · exact Or.inl hy
      · right; refine ⟨hy, ?_⟩; rw [hlow, hnum]; simp only [hxv, ↓reduceIte]; exact hl
    by_cases hxw : x = w
    · subst hxw
      refine ⟨hlw, ?_, ?_, ?_, ?_, ?_, fun y hy => hdone y (hdw y hy)⟩
      · rw [hpar]; exact hvS
      · rw [hpar]; exact hvw
      · rw [hpar]; exact he
      · rw [hpar]; simp only [↓reduceIte]; exact Nat.min_le_right _ _
      · intro a ha _; rw [hpar]; exact hmax a ha
    · have hxA' : x ∉ t.A := by
        rw [hA']; intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hxA hm
        · simp at hm; exact hxw hm
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h.fin x hx hxA'
      refine ⟨f1, f2, f3, f4, ?_, fun a ha => f6 a (hsub a ha), fun y hy => hdone y (f7 y hy)⟩
      split
      · rename_i hp; rw [hp] at f5; exact Nat.le_trans (Nat.min_le_left _ _) f5
      · exact f5

/-! ## The root -/

/-- A search from an empty stack whose root returned with `v` still on the stack is impossible:
the root's lowlink witness would lie below it. -/
theorem root_pops {g : Gr α} {t : St α} (h : TInv g t) {v : α} {T : List α}
    (hS : t.S = v :: T) (hlt : t.low v < t.num v) : False := by
  have hvS : v ∈ t.S := by simp [hS]
  obtain ⟨-, u, hu, hnu, -⟩ := h.lowW v hvS
  have hs := h.sorted; rw [hS, List.pairwise_cons] at hs
  rw [hS] at hu
  rcases List.mem_cons.mp hu with rfl | hu
  · omega
  · have := hs.1 u hu; omega

/-! ## Stability of handled edges -/

/-- What a call (`strongconnect` of a child) does to its caller's state: the stack extended, the
visited nodes kept with their `Index`/`Lowlink`, the executed set grown, the edges kept. -/
structure Ext (g : Gr α) (t : St α) (g' : Gr α) (t' : St α) : Prop where
  stk : ∃ T, t'.S = t.S ++ T
  ix : ∀ x, t.vis x → t'.ix x = t.ix x
  ex : ∀ x, g.ex x → g'.ex x
  E : g'.E = g.E
  par : ∀ x, t.vis x → t'.par x = t.par x

theorem Ext.done {g g' : Gr α} {t t' : St α} (he : Ext g t g' t') {a y : α} (ha : t.vis a)
    (hS : ∀ z ∈ t.S, t.vis z) (hd : Done g t a y) : Done g' t' a y := by
  rcases hd with hy | ⟨hy, hl⟩
  · exact Or.inl (he.ex y hy)
  · right
    obtain ⟨T, hT⟩ := he.stk
    refine ⟨by rw [hT]; exact List.mem_append_left _ hy, ?_⟩
    unfold St.low St.num
    rw [he.ix a ha, he.ix y (hS y hy)]; exact hl

theorem Ext.refl (g : Gr α) (t : St α) : Ext g t g t :=
  ⟨⟨[], by simp⟩, fun _ _ => rfl, fun _ h => h, rfl, fun _ _ => rfl⟩

theorem Ext.vis {g g' : Gr α} {t t' : St α} (he : Ext g t g' t') {x : α} (h : t.vis x) :
    t'.vis x := by
  unfold St.vis at *; rw [he.ix x h]; exact h

theorem Ext.trans {g1 g2 g3 : Gr α} {t1 t2 t3 : St α} (h1 : Ext g1 t1 g2 t2)
    (h2 : Ext g2 t2 g3 t3) : Ext g1 t1 g3 t3 := by
  obtain ⟨T1, e1⟩ := h1.stk; obtain ⟨T2, e2⟩ := h2.stk
  refine ⟨⟨T1 ++ T2, by rw [e2, e1, List.append_assoc]⟩, fun x hx => ?_, fun x hx => h2.ex x (h1.ex x hx),
    by rw [h2.E, h1.E], fun x hx => ?_⟩
  · rw [h2.ix x (h1.vis hx), h1.ix x hx]
  · rw [h2.par x (h1.vis hx), h1.par x hx]

/-- Changing the search state of a node the base state had not visited keeps `Ext`. -/
theorem Ext.setIx {g g' : Gr α} {t t' : St α} (he : Ext g t g' t') {v : α} (hv : ¬ t.vis v)
    (t'' : St α) (hS : t''.S = t'.S) (hix : ∀ x, x ≠ v → t''.ix x = t'.ix x)
    (hpar : t''.par = t'.par) : Ext g t g' t'' := by
  refine ⟨by rw [hS]; exact he.stk, fun x hx => ?_, he.ex, he.E, fun x hx => by rw [hpar]; exact he.par x hx⟩
  have : x ≠ v := fun e => hv (e ▸ hx)
  rw [hix x this, he.ix x hx]

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.tarjan
