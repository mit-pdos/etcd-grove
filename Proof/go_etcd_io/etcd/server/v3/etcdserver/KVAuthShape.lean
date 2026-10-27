/-
**The model's auth states keep their users' roles sorted, so its admin entries are determinate**
(the auth plan's E3m, 2026-10-27; `notes/decisions.md`, "E3m of the auth plan"). Lean-first (no
Rocq counterpart).

The mode-`on` model (`kvRaftOfOn`, E2q) needs every committed admin entry determinate at the state
it meets (`authDet`): a function of the committed log. `UserAddF`, `roleAddF`, `authEnableF` are
functions; `userGrantRoleR` is a relation (the user's roles after the append and `sort.Strings`,
any strictly sorted permutation) whose successor is unique, and exists, exactly when the user's
roles are without duplicates: here, an invariant of every state the model reaches, its users'
roles strictly ascending (`rolesSorted`: what `UserGrantRole` writes, and `UserAdd`'s empty list),
kept by every admin step (`rolesSorted_adminStateR`) and so along the whole model
(`rolesSorted_kvRaftOfOn`), whether or not its entries were determinate.

`roleGrantPermissionR` is looser: the role's permissions after the append and `sort.Sort` are any
permutation of the old ones with the new one (Go's `permSlice` compares keys only and `sort.Sort`
is not stable, so the model does not pin the order; S4, "the grants"). Its successor is unique
only when that list has one element: the role has no permission yet (`grantPermFresh`). No
invariant of the states gives that; the proposer of a `RoleGrantPermission` must know it of the
state its entry meets (`examples/authkv`'s `SetUp`: one grant to a fresh role).

`authDet_of_sorted`: an admin entry is determinate at a sorted state when it is `UserAdd` with a
password choice that cannot fail (`pwSure`, E2t/E2x), `RoleAdd`, `UserGrantRole`, `AuthEnable`, or
any other kind (which keeps the state), or a `RoleGrantPermission` to a fresh role.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [ext : FfiSyntax]

/-! ## Strictly sorted role lists -/

/-- Insert into a strictly ascending list. -/
def insLt (x : GoString) : List GoString → List GoString
  | [] => [x]
  | y :: ys => if go.GoStringLt x y then x :: y :: ys else y :: insLt x ys

theorem insLt_perm (x : GoString) : ∀ l : List GoString, (insLt x l).Perm (l ++ [x])
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insLt
    split
    · exact (List.perm_append_singleton x (y :: ys)).symm
    · exact List.Perm.cons y (insLt_perm x ys)

theorem insLt_mem (x z : GoString) (l : List GoString) (h : z ∈ insLt x l) : z = x ∨ z ∈ l := by
  have := (insLt_perm x l).mem_iff.1 h
  rcases List.mem_append.1 this with h | h
  · exact Or.inr h
  · simp only [List.mem_singleton] at h; exact Or.inl h

theorem insLt_sorted (x : GoString) :
    ∀ l : List GoString, l.Pairwise go.GoStringLt → x ∉ l → (insLt x l).Pairwise go.GoStringLt
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, h, hx => by
    unfold insLt
    rw [List.pairwise_cons] at h
    split
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact go.goStringLt_trans hxy (h.1 z hz)
    · rename_i hxy
      have hne : x ≠ y := fun e => hx (e ▸ List.mem_cons_self ..)
      have hyx : go.GoStringLt y x := by
        apply Classical.byContradiction
        intro hn
        exact hne (go.goStringLt_eq_of_not_lt hxy hn)
      refine List.pairwise_cons.2 ⟨?_, insLt_sorted x ys h.2 (fun hm => hx (List.mem_cons_of_mem _ hm))⟩
      intro z hz
      rcases insLt_mem x z ys hz with rfl | hz
      · exact hyx
      · exact h.1 z hz

/-- Two strictly ascending permutations of one list are equal. -/
theorem eq_of_perm_sorted :
    ∀ (l1 l2 : List GoString), l1.Perm l2 → l1.Pairwise go.GoStringLt →
      l2.Pairwise go.GoStringLt → l1 = l2
  | [], l2, hp, _, _ => List.Perm.nil_eq hp
  | a :: l1, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: l1, b :: l2, hp, h1, h2 => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha : a ∈ b :: l2 := hp.mem_iff.1 (List.mem_cons_self ..)
      have hb : b ∈ a :: l1 := hp.mem_iff.2 (List.mem_cons_self ..)
      rcases List.mem_cons.1 ha with ha | ha
      · exact ha
      rcases List.mem_cons.1 hb with hb | hb
      · exact hb.symm
      exact absurd (h1.1 b hb) (go.goStringLt_asymm (h2.1 a ha))
    subst hab
    rw [eq_of_perm_sorted l1 l2 (List.Perm.cons_inv hp) h1.2 h2.2]

/-! ## The invariant -/

/-- **Every user's roles strictly ascending** (see the header). -/
def rolesSorted (st : auth.AuthState) : Prop :=
  ∀ u us, st.users !! u = some us → us.Pairwise go.GoStringLt

theorem rolesSorted_bump (st : auth.AuthState) (h : rolesSorted st) : rolesSorted (auth.bump st) :=
  h

theorem rolesSorted_enabled (st : auth.AuthState) (b : Bool) (h : rolesSorted st) :
    rolesSorted { st with enabled := b } := h

theorem rolesSorted_putRole (st : auth.AuthState) (r : GoString) (ps : auth.Role)
    (h : rolesSorted st) : rolesSorted (auth.putRole st r ps) := h

theorem rolesSorted_putUser (st : auth.AuthState) (name : GoString) (us : auth.User)
    (hus : us.Pairwise go.GoStringLt) (h : rolesSorted st) :
    rolesSorted (auth.putUser st name us) := by
  intro u us' hu
  by_cases e : name = u
  · subst e; simp only [auth.putUser, GMap.lookup_insert] at hu; cases hu; exact hus
  · simp only [auth.putUser, GMap.lookup_insert_ne _ _ e] at hu; exact h u us' hu

theorem rolesSorted_bootState : rolesSorted auth.bootState := by
  intro u us h
  simp [auth.bootState] at h

theorem rolesSorted_outState (st : auth.AuthState) (o : auth.Outcome) (h : rolesSorted st)
    (ho : ∀ st', o = .next st' → rolesSorted st') : rolesSorted (outState st o) := by
  cases o with
  | err e => exact h
  | same => exact h
  | next st' => exact ho st' rfl

/-- **Every admin step keeps the users' roles sorted.** -/
theorem rolesSorted_adminStateR (rq : apply.IRRModel) (st st' : auth.AuthState)
    (h : rolesSorted st) (hR : adminStateR rq st st') : rolesSorted st' := by
  unfold adminStateR at hR
  split at hR
  · split at hR
    · split at hR
      · rename_i m _
        rcases hR with ⟨-, rfl⟩ | ⟨o, ho, rfl⟩
        · exact h
        · apply rolesSorted_outState st o h
          intro s hs
          simp only [auth.stepOf, auth.userAddF] at ho
          subst ho
          split at hs
          · cases hs
          · split at hs
            · cases hs
            · cases hs
              exact rolesSorted_bump _ (rolesSorted_putUser st _ [] List.Pairwise.nil h)
      · subst hR; exact h
    · split at hR
      · obtain ⟨o, ho, rfl⟩ := hR
        apply rolesSorted_outState st o h
        intro s hs
        simp only [auth.stepOf, auth.roleAddF] at ho
        subst ho
        split at hs
        · cases hs
        · split at hs
          · cases hs
          · cases hs; exact rolesSorted_bump _ (rolesSorted_putRole st _ [] h)
      · subst hR; exact h
    · split at hR
      · obtain ⟨o, ho, rfl⟩ := hR
        apply rolesSorted_outState st o h
        intro s hs
        subst hs
        simp only [auth.userGrantRoleR] at ho
        split at ho
        · cases ho
        · split at ho
          · cases ho
          · split at ho
            · cases ho
            · obtain ⟨u', -, hsorted, ho⟩ := ho
              cases ho
              exact rolesSorted_bump _ (rolesSorted_putUser st _ u' hsorted h)
      · subst hR; exact h
    · split at hR
      · obtain ⟨o, ho, rfl⟩ := hR
        apply rolesSorted_outState st o h
        intro s hs
        subst hs
        simp only [auth.roleGrantPermissionR] at ho
        split at ho
        · cases ho
        · split at ho
          · cases ho
          · split at ho
            · cases ho
            · split at ho
              · obtain ⟨ps', -, ho⟩ := ho
                cases ho; exact rolesSorted_bump _ (rolesSorted_putRole st _ _ h)
              · obtain ⟨ps', -, -, -, ho⟩ := ho
                cases ho; exact rolesSorted_bump _ (rolesSorted_putRole st _ _ h)
      · subst hR; exact h
    · obtain ⟨o, ho, rfl⟩ := hR
      apply rolesSorted_outState st o h
      intro s hs
      simp only [auth.stepOf, auth.authEnableF] at ho
      subst ho
      split at hs
      · cases hs
      · split at hs
        · cases hs
        · split at hs
          · cases hs; exact rolesSorted_enabled st true h
          · cases hs
    · subst hR; exact h
  · subst hR; exact h

/-- The model's admin step keeps the users' roles sorted (a successor, or the state kept). -/
theorem rolesSorted_adminNext (rq : apply.IRRModel) (st : auth.AuthState) (h : rolesSorted st) :
    rolesSorted (adminNext rq st) := by
  unfold adminNext
  split
  · rename_i hd
    exact rolesSorted_adminStateR rq st _ h (Classical.choose_spec hd).1
  · exact h

theorem rolesSorted_kvEntryOn (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (h : rolesSorted s.1) : rolesSorted (kvEntryOn c₀ ch s m).1 := by
  unfold kvEntryOn
  split
  · split
    · split
      · exact rolesSorted_adminNext _ _ h
      · split
        · exact h
        · exact h
    · exact h
  · exact h

/-- **The users' roles stay sorted along the whole model** (of any log). -/
theorem rolesSorted_kvRaftOfOn (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A : List EntryModel) (h : rolesSorted s₀.1) : rolesSorted (kvRaftOfOn c₀ ch s₀ A).1 := by
  induction A generalizing s₀ with
  | nil => exact h
  | cons m A ih =>
    show rolesSorted (List.foldl (kvEntryOn c₀ ch) (kvEntryOn c₀ ch s₀ m) A).1
    exact ih _ (rolesSorted_kvEntryOn c₀ ch s₀ m h)

/-! ## Determinacy -/

/-- A relation with exactly one successor `s`. -/
theorem authDet_of_iff (rq : apply.IRRModel) (st s : auth.AuthState)
    (h : ∀ st', adminStateR rq st st' ↔ st' = s) : authDet rq st :=
  ⟨s, (h s).2 rfl, fun st'' h'' => (h st'').1 h''⟩

theorem relState_stepOf_iff (f : auth.AuthState → auth.Outcome) (st st' : auth.AuthState) :
    authRelState (auth.stepOf f) st st' ↔ st' = outState st (f st) := by
  unfold authRelState auth.stepOf
  constructor
  · rintro ⟨o, rfl, h⟩; exact h
  · intro h; exact ⟨f st, rfl, h⟩

/-- `UserGrantRole` at a sorted state has exactly one successor. -/
theorem relState_userGrantRole_unique (u r : GoString) (st : auth.AuthState) (h : rolesSorted st) :
    ∃ s, ∀ st', authRelState (auth.userGrantRoleR u r) st st' ↔ st' = s := by
  unfold authRelState auth.userGrantRoleR
  cases hu : st.users !! u with
  | none =>
    exact ⟨outState st (.err .userNotFound), fun st' =>
      ⟨fun ⟨o, ho, he⟩ => by subst ho; exact he, fun he => ⟨_, rfl, he⟩⟩⟩
  | some us =>
    simp only
    by_cases hc : r ≠ auth.rootRole ∧ (st.roles !! r).isNone
    · simp only [if_pos hc]
      exact ⟨outState st (.err .roleNotFound), fun st' =>
        ⟨fun ⟨o, ho, he⟩ => by subst ho; exact he, fun he => ⟨_, rfl, he⟩⟩⟩
    · simp only [if_neg hc]
      by_cases hm : r ∈ us
      · simp only [if_pos hm]
        exact ⟨outState st .same, fun st' =>
          ⟨fun ⟨o, ho, he⟩ => by subst ho; exact he, fun he => ⟨_, rfl, he⟩⟩⟩
      · simp only [if_neg hm]
        have hs := h u us hu
        refine ⟨auth.bump (auth.putUser st u (insLt r us)), fun st' => ⟨?_, ?_⟩⟩
        · rintro ⟨o, ⟨u', hp, hsorted, rfl⟩, rfl⟩
          have := eq_of_perm_sorted u' (insLt r us) (hp.trans (insLt_perm r us).symm) hsorted
            (insLt_sorted r us hs hm)
          subst this
          rfl
        · intro he
          exact ⟨_, ⟨insLt r us, insLt_perm r us, insLt_sorted r us hs hm, rfl⟩, he⟩

/-- **A grant to a fresh role**: the role `RoleGrantPermission` names has no permission at `st`. -/
def grantPermFresh (rq : apply.IRRModel) (st : auth.AuthState) : Prop :=
  ∀ r w ps, rq.authRoleGrantPermission = some (r, w) → st.roles !! r = some ps → ps = []

/-- `RoleGrantPermission` to a role with no permission has exactly one successor. -/
theorem relState_roleGrantPermission_unique (r : GoString) (w : Option auth.PermW)
    (st : auth.AuthState) (h : ∀ ps, st.roles !! r = some ps → ps = []) :
    ∃ s, ∀ st', authRelState (auth.roleGrantPermissionR r w) st st' ↔ st' = s := by
  unfold authRelState auth.roleGrantPermissionR
  cases w with
  | none =>
    exact ⟨outState st (.err .permissionNotGiven), fun st' =>
      ⟨fun ⟨o, ho, he⟩ => by subst ho; exact he, fun he => ⟨_, rfl, he⟩⟩⟩
  | some w =>
    simp only
    by_cases hv : auth.rangeValid w.key w.rangeEnd
    · simp only [if_neg (not_not_intro hv)]
      cases hr : st.roles !! r with
      | none =>
        exact ⟨outState st (.err .roleNotFound), fun st' =>
          ⟨fun ⟨o, ho, he⟩ => by subst ho; exact he, fun he => ⟨_, rfl, he⟩⟩⟩
      | some ps =>
        have hps : ps = [] := h ps hr
        subst hps
        simp only
        cases hp : auth.permOfWire w with
        | some perm =>
          refine ⟨auth.bump (auth.putRole st r [perm]), fun st' => ⟨?_, ?_⟩⟩
          · rintro ⟨o, ⟨ps', hps', rfl⟩, rfl⟩
            rcases hps' with hps' | ⟨i, p, hi, -, -⟩
            · simp only [List.nil_append] at hps'
              rw [List.perm_singleton.1 hps']
              rfl
            · simp at hi
          · intro he
            exact ⟨_, ⟨[perm], Or.inl (List.Perm.refl _), rfl⟩, he⟩
        | none =>
          refine ⟨auth.bump (auth.putRole st r []), fun st' => ⟨?_, ?_⟩⟩
          · rintro ⟨o, ⟨ps', ps'', hsub, hp', rfl⟩, rfl⟩
            rw [List.sublist_nil.1 hsub] at hp'
            rw [List.Perm.nil_eq hp'.symm]
            rfl
          · intro he
            exact ⟨_, ⟨[], [], List.Sublist.slnil, List.Perm.refl _, rfl⟩, he⟩
    · simp only [if_pos hv]
      exact ⟨outState st (.err .invalidAuthMgmt), fun st' =>
        ⟨fun ⟨o, ho, he⟩ => by subst ho; exact he, fun he => ⟨_, rfl, he⟩⟩⟩

/-- **The proposer's side of an admin entry's determinacy** (see the header): a `UserAdd` whose
password choice cannot fail; a `RoleGrantPermission` only to a fresh role (`grantPermFresh`, of the
state the entry meets); every other kind as it is. -/
def adminDetReq (rq : apply.IRRModel) (st : auth.AuthState) : Prop :=
  (∀ m, rq.authUserAdd = some m → m.pwSure) ∧ grantPermFresh rq st

/-- **An admin entry is determinate at a sorted state** meeting `adminDetReq`. -/
theorem authDet_of_sorted (rq : apply.IRRModel) (st : auth.AuthState) (h : rolesSorted st)
    (hr : adminDetReq rq st) : authDet rq st := by
  obtain ⟨hpw, hgp⟩ := hr
  unfold authDet adminStateR
  split
  · split
    · split
      · rename_i m hm
        have hsure := hpw m hm
        obtain ⟨s, hs⟩ := (⟨_, relState_stepOf_iff (auth.userAddF m.name) st⟩ :
          ∃ s, ∀ st', authRelState (auth.stepOf (auth.userAddF m.name)) st st' ↔ st' = s)
        refine ⟨s, Or.inr ((hs s).2 rfl), fun st'' h'' => ?_⟩
        rcases h'' with ⟨hn, -⟩ | h''
        · exact absurd hsure hn
        · exact (hs st'').1 h''
      · exact ⟨st, rfl, fun _ h => h⟩
    · split
      · obtain ⟨s, hs⟩ := (⟨_, relState_stepOf_iff (auth.roleAddF _) st⟩ :
          ∃ s, ∀ st', authRelState (auth.stepOf (auth.roleAddF _)) st st' ↔ st' = s)
        exact ⟨s, (hs s).2 rfl, fun st'' h'' => (hs st'').1 h''⟩
      · exact ⟨st, rfl, fun _ h => h⟩
    · split
      · obtain ⟨s, hs⟩ := relState_userGrantRole_unique _ _ st h
        exact ⟨s, (hs s).2 rfl, fun st'' h'' => (hs st'').1 h''⟩
      · exact ⟨st, rfl, fun _ h => h⟩
    · split
      · rename_i r w hrw
        obtain ⟨s, hs⟩ := relState_roleGrantPermission_unique r w st
          (fun ps hps => hgp r w ps hrw hps)
        exact ⟨s, (hs s).2 rfl, fun st'' h'' => (hs st'').1 h''⟩
      · exact ⟨st, rfl, fun _ h => h⟩
    · obtain ⟨s, hs⟩ := (⟨_, relState_stepOf_iff (auth.authEnableF st.enabled) st⟩ :
        ∃ s, ∀ st', authRelState (auth.stepOf (auth.authEnableF st.enabled)) st st' ↔ st' = s)
      exact ⟨s, (hs s).2 rfl, fun st'' h'' => (hs st'').1 h''⟩
    · exact ⟨st, rfl, fun _ h => h⟩
  · exact ⟨st, rfl, fun _ h => h⟩

/-- **The model's state after any log is sorted**, from a sorted start (the server's,
`bump bootState`). -/
theorem rolesSorted_model_boot (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log)
    (A : List EntryModel) : rolesSorted (kvRaftOfOn c₀ ch (auth.bump auth.bootState, log₀) A).1 :=
  rolesSorted_kvRaftOfOn c₀ ch _ A (rolesSorted_bump _ rolesSorted_bootState)

end pure

end EtcdGrove
end Perennial
