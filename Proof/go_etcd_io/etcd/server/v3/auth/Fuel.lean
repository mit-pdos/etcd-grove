/-
**The admin steps' budget from time receipts** (the auth plan's E2l, 2026-10-26;
`notes/decisions.md`, "E2l of the auth plan"). Lean-first (no Rocq counterpart).

S4's step specs take `stepOk` (`Steps.lean`): at the state the batch transaction finds, the
revision fits a `uint64` after the bump, and a next state's permissions fit the cache's trees
(`permsFit`). Neither follows from a single state: both bound how much the admin side has written.
As the server's other lifetime bounds (D19b, `notes/decisions.md`: ids, applied entries, the
store's changes), the bound is a count backed by time receipts: the admin side holds, with its
authority, `⧗ k` with the latest state's revision at most `k + 1` (`authFuel`); each admin request
takes one more receipt at a Go step of its own (`wp_go_step_receipt'`), so `k + 1 < receiptBound
GF ≤ 2 ^ 48`, which gives the revision's bound (`stepOk_of_fuel`). The permissions are bounded by
the revision through the state's size (`authSmall`): every user's roles without duplicates (so a
user's permissions are at most all the roles' permissions, `userPerms_le`) and all the roles'
permissions together at most the revision; every step keeps it and raises the revision by at most
one (`StepSmall`, proved of the eleven steps). No ticket from the request's sender: the receipt is
the apply thread's, so a request delivered several times (E2h's persistent `□ ▷ Spec m Q`) costs one
receipt per application.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Steps
public import Proof.go_etcd_io.etcd.server.v3.auth.GrantLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI

/-! ## The size of a state -/

/-- The number of permissions of the roles `L` in `st` (a missing role has none). -/
def permsOn (st : AuthState) (L : List GoString) : Nat :=
  (L.map fun r => ((st.roles !! r).getD []).length).sum

/-- **The state is small** (see the file header): every user's roles without duplicates and at
most the revision in number, every user's name a bbolt key, and some list of the roles (each once)
whose permissions are together at most the revision. -/
structure authSmall (st : AuthState) : Prop where
  nodup : ∀ u us, st.users !! u = some us → us.Nodup
  roles : ∀ u us, st.users !! u = some us → us.length ≤ st.revision
  names : ∀ n, (st.users !! n).isSome → n.length ≤ backend.maxKeySize
  perms : ∃ L : List GoString, L.Nodup ∧ (∀ r, (st.roles !! r).isSome → r ∈ L) ∧
    permsOn st L ≤ st.revision

theorem sum_map_le_of_nodup (f : GoString → Nat) :
    ∀ (us L : List GoString), us.Nodup → L.Nodup → (∀ x ∈ us, f x ≠ 0 → x ∈ L) →
      (us.map f).sum ≤ (L.map f).sum
  | [], _, _, _, _ => by simp
  | r :: us, L, hnd, hL, h => by
    rw [List.nodup_cons] at hnd
    by_cases hr : r ∈ L
    · have hp := (List.perm_cons_erase hr).map f
      rw [hp.sum_nat]
      simp only [List.map_cons, List.sum_cons]
      have := sum_map_le_of_nodup f us (L.erase r) hnd.2 (hL.erase r) (fun x hx hfx =>
        (List.mem_erase_of_ne (fun e : x = r => hnd.1 (e ▸ hx))).2 (h x (List.mem_cons_of_mem _ hx) hfx))
      omega
    · have hf : f r = 0 := by
        apply Classical.byContradiction; intro hne; exact hr (h r (List.mem_cons_self ..) hne)
      simp only [List.map_cons, List.sum_cons, hf, Nat.zero_add]
      exact sum_map_le_of_nodup f us L hnd.2 hL (fun x hx hfx => h x (List.mem_cons_of_mem _ hx) hfx)

theorem sum_map_le_pointwise (f g : GoString → Nat) :
    ∀ L : List GoString, (∀ x ∈ L, g x ≤ f x) → (L.map g).sum ≤ (L.map f).sum
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_map_le_pointwise f g L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x (List.mem_cons_self ..)
    omega

/-- Updating a map at one key `n` of a list without duplicates that has it. -/
theorem sum_map_update (f g : GoString → Nat) (n : GoString) (hfg : ∀ x, x ≠ n → g x = f x) :
    ∀ L : List GoString, L.Nodup → n ∈ L → (L.map g).sum + f n = (L.map f).sum + g n
  | [], _, h => by simp at h
  | x :: L, hnd, h => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : x = n
    · subst hx
      have : L.map g = L.map f := List.map_congr_left (fun y hy => hfg y (fun e => hnd.1 (e ▸ hy)))
      rw [this]; omega
    · have hn : n ∈ L := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm hx
        · exact e
      have := sum_map_update f g n hfg L hnd.2 hn
      rw [hfg x hx]; omega

/-- A user's permissions are at most all the roles' (its roles without duplicates). -/
theorem userPerms_le (st : AuthState) (us L : List GoString) (hus : us.Nodup) (hL : L.Nodup)
    (hdom : ∀ r, (st.roles !! r).isSome → r ∈ L) : (userPerms st us).length ≤ permsOn st L := by
  unfold userPerms permsOn
  rw [List.length_flatMap]
  apply sum_map_le_of_nodup _ us L hus hL
  intro x _ hx
  apply hdom
  cases h : st.roles !! x with
  | none => rw [h] at hx; simp at hx
  | some _ => rfl

/-- A small state whose revision is below `2 ^ 63` has its permissions fit the cache's trees. -/
theorem permsFit_of_small (st : AuthState) (h : authSmall st) (hr : st.revision < 2 ^ 63) :
    permsFit st := by
  intro u us hu
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  have := userPerms_le st us L (h.nodup u us hu) hL hdom
  omega

/-! ## The steps keep a state small -/

theorem authSmall_bump (st : AuthState) (h : authSmall st) : authSmall (bump st) := by
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  exact ⟨h.nodup, fun u us hu => Nat.le_succ_of_le (h.roles u us hu), h.names, L, hL, hdom,
    by simp only [bump, permsOn] at hle ⊢; omega⟩

theorem authSmall_enabled (st : AuthState) (b : Bool) (h : authSmall st) :
    authSmall { st with enabled := b } := by
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  exact ⟨h.nodup, h.roles, h.names, L, hL, hdom, by simp only [permsOn] at hle ⊢; omega⟩

/-- A user's record written (its roles without duplicates, at most the bumped revision in number,
its name a bbolt key), with the revision bumped. -/
theorem authSmall_bump_putUser (st : AuthState) (name : GoString) (us : User) (hus : us.Nodup)
    (hlen : us.length ≤ st.revision + 1) (hn : name.length ≤ backend.maxKeySize)
    (h : authSmall st) : authSmall (bump (putUser st name us)) := by
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  refine ⟨?_, ?_, ?_, L, hL, hdom, by simp only [bump, putUser, permsOn] at hle ⊢; omega⟩
  · intro u us' hu
    by_cases e : name = u
    · subst e; simp only [bump, putUser, GMap.lookup_insert] at hu; cases hu; exact hus
    · simp only [bump, putUser, GMap.lookup_insert_ne _ _ e] at hu; exact h.nodup u us' hu
  · intro u us' hu
    show us'.length ≤ st.revision + 1
    by_cases e : name = u
    · subst e; simp only [bump, putUser, GMap.lookup_insert] at hu; cases hu; exact hlen
    · simp only [bump, putUser, GMap.lookup_insert_ne _ _ e] at hu
      have := h.roles u us' hu; omega
  · intro n hn'
    by_cases e : name = n
    · subst e; exact hn
    · simp only [bump, putUser, GMap.lookup_insert_ne _ _ e] at hn'; exact h.names n hn'

theorem authSmall_bump_delUser (st : AuthState) (name : GoString) (h : authSmall st) :
    authSmall (bump (delUser st name)) := by
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  refine ⟨?_, ?_, ?_, L, hL, hdom, by simp only [bump, delUser, permsOn] at hle ⊢; omega⟩
  · intro u us' hu
    by_cases e : name = u
    · subst e; simp [bump, delUser] at hu
    · simp only [bump, delUser, GMap.lookup_delete_ne _ e] at hu; exact h.nodup u us' hu
  · intro u us' hu
    show us'.length ≤ st.revision + 1
    by_cases e : name = u
    · subst e; simp [bump, delUser] at hu
    · simp only [bump, delUser, GMap.lookup_delete_ne _ e] at hu
      have := h.roles u us' hu; omega
  · intro n hn'
    by_cases e : name = n
    · subst e; simp [bump, delUser] at hn'
    · simp only [bump, delUser, GMap.lookup_delete_ne _ e] at hn'; exact h.names n hn'

/-- A role's permissions replaced by at most one more, with the revision bumped. -/
theorem authSmall_bump_putRole (st : AuthState) (name : GoString) (ps : Role)
    (hps : ps.length ≤ ((st.roles !! name).getD []).length + 1) (h : authSmall st) :
    authSmall (bump (putRole st name ps)) := by
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  have hg : ∀ x, x ≠ name → (((putRole st name ps).roles !! x).getD []).length =
      ((st.roles !! x).getD []).length := by
    intro x hx
    simp only [putRole, GMap.lookup_insert_ne _ _ (Ne.symm hx)]
  have hgn : (((putRole st name ps).roles !! name).getD []).length = ps.length := by
    simp only [putRole, GMap.lookup_insert, Option.getD_some]
  refine ⟨h.nodup, fun u us hu => Nat.le_succ_of_le (h.roles u us hu), h.names, ?_⟩
  by_cases hn : name ∈ L
  · refine ⟨L, hL, ?_, ?_⟩
    · intro r hr
      by_cases e : name = r
      · exact e ▸ hn
      · apply hdom; simpa only [bump, putRole, GMap.lookup_insert_ne _ _ e] using hr
    · have := sum_map_update (fun r => ((st.roles !! r).getD []).length)
        (fun r => (((putRole st name ps).roles !! r).getD []).length) name hg L hL hn
      simp only [bump, permsOn] at hle ⊢
      simp only [hgn] at this
      change (L.map fun r => (((putRole st name ps).roles !! r).getD []).length).sum ≤
        st.revision + 1
      omega
  · have hnone : st.roles !! name = none := by
      cases e : st.roles !! name with
      | none => rfl
      | some _ => exact absurd (hdom name (by rw [e]; rfl)) hn
    rw [hnone] at hps
    simp only [Option.getD_none, List.length_nil] at hps
    refine ⟨name :: L, List.nodup_cons.2 ⟨hn, hL⟩, ?_, ?_⟩
    · intro r hr
      by_cases e : name = r
      · exact e ▸ List.mem_cons_self ..
      · apply List.mem_cons_of_mem
        apply hdom; simpa only [bump, putRole, GMap.lookup_insert_ne _ _ e] using hr
    · have hm : (L.map fun r => (((putRole st name ps).roles !! r).getD []).length) =
          L.map fun r => ((st.roles !! r).getD []).length :=
        List.map_congr_left (fun y hy => hg y (fun e => hn (e ▸ hy)))
      simp only [bump, permsOn] at hle ⊢
      change (((putRole st name ps).roles !! name).getD []).length +
        (L.map fun r => (((putRole st name ps).roles !! r).getD []).length).sum ≤ st.revision + 1
      rw [hm, hgn]; omega

theorem authSmall_bump_delRole (st : AuthState) (name : GoString) (h : authSmall st) :
    authSmall (bump (delRole st name)) := by
  obtain ⟨L, hL, hdom, hle⟩ := h.perms
  refine ⟨?_, ?_, ?_, L, hL, ?_, ?_⟩
  · intro u us hu
    simp only [bump, delRole, GMap.lookup_fmap] at hu
    cases e : st.users !! u with
    | none => rw [e] at hu; cases hu
    | some us0 =>
      rw [e] at hu; simp only [Option.map_some, Option.some.injEq] at hu
      subst hu; exact (h.nodup u us0 e).filter _
  · intro u us hu
    show us.length ≤ st.revision + 1
    simp only [bump, delRole, GMap.lookup_fmap] at hu
    cases e : st.users !! u with
    | none => rw [e] at hu; cases hu
    | some us0 =>
      rw [e] at hu; simp only [Option.map_some, Option.some.injEq] at hu
      subst hu
      have := h.roles u us0 e
      have := List.length_filter_le (fun r => decide (r ≠ name)) us0
      omega
  · intro n hn
    simp only [bump, delRole, GMap.lookup_fmap] at hn
    apply h.names n
    cases e : st.users !! n with
    | none => rw [e] at hn; simp at hn
    | some _ => rfl
  · intro r hr
    by_cases e : name = r
    · subst e; simp [bump, delRole] at hr
    · apply hdom; simpa only [bump, delRole, GMap.lookup_delete_ne _ e] using hr
  · have : permsOn (delRole st name) L ≤ permsOn st L := by
      unfold permsOn
      apply sum_map_le_pointwise
      intro x _
      by_cases e : name = x
      · subst e; simp only [delRole, GMap.lookup_delete, Option.getD_none, List.length_nil]
        exact Nat.zero_le _
      · simp only [delRole, GMap.lookup_delete_ne _ e]; exact Nat.le_refl _
    simp only [bump, delRole, permsOn] at this hle ⊢
    omega

/-- **A step keeps a state small, raising the revision by at most one.** -/
def StepSmall (R : StepRel) : Prop :=
  ∀ st st', authSmall st → R st (.next st') → st'.revision ≤ st.revision + 1 ∧ authSmall st'

theorem stepSmall_authEnable (en : Bool) : StepSmall (stepOf (authEnableF en)) := by
  intro st st' h hR
  simp only [stepOf, authEnableF] at hR
  split at hR
  · cases hR
  · split at hR
    · cases hR
    · split at hR
      · cases hR; exact ⟨by simp, authSmall_enabled st true h⟩
      · cases hR

theorem stepSmall_authDisable (en : Bool) : StepSmall (stepOf (authDisableF en)) := by
  intro st st' h hR
  simp only [stepOf, authDisableF] at hR
  split at hR
  · cases hR; exact ⟨by simp [bump], authSmall_bump _ (authSmall_enabled st false h)⟩
  · cases hR

/-- `UserAdd` of a name within bbolt's key bound (the request's premise). -/
theorem stepSmall_userAdd (name : GoString) (hn : name.length ≤ backend.maxKeySize) :
    StepSmall (stepOf (userAddF name)) := by
  intro st st' h hR
  simp only [stepOf, userAddF] at hR
  split at hR
  · cases hR
  · split at hR
    · cases hR
    · cases hR
      exact ⟨by simp [bump, putUser],
        authSmall_bump_putUser st name [] List.nodup_nil (by simp) hn h⟩

theorem stepSmall_userDelete (en : Bool) (name : GoString) :
    StepSmall (stepOf (userDeleteF en name)) := by
  intro st st' h hR
  simp only [stepOf, userDeleteF] at hR
  split at hR
  · cases hR
  · split at hR
    · cases hR
    · cases hR; exact ⟨by simp [bump, delUser], authSmall_bump_delUser st name h⟩

theorem stepSmall_userChangePassword (name : GoString) :
    StepSmall (stepOf (userChangePasswordF name)) := by
  intro st st' h hR
  simp only [stepOf, userChangePasswordF] at hR
  split at hR
  · cases hR
  · cases hR; exact ⟨by simp [bump], authSmall_bump _ h⟩

theorem stepSmall_userGrantRole (user role : GoString) : StepSmall (userGrantRoleR user role) := by
  intro st st' h hR
  simp only [userGrantRoleR] at hR
  split at hR
  · cases hR
  · rename_i u hu
    split at hR
    · cases hR
    · split at hR
      · cases hR
      · obtain ⟨u', hperm, hsorted, hR⟩ := hR
        cases hR
        have hlen : u'.length ≤ st.revision + 1 := by
          rw [hperm.length_eq]; simp only [List.length_append, List.length_cons, List.length_nil]
          have := h.roles user u hu; omega
        exact ⟨by simp [bump, putUser],
          authSmall_bump_putUser st user u' (nodup_of_pairwise_lt u' hsorted) hlen
            (h.names user (by rw [hu]; rfl)) h⟩

theorem stepSmall_userRevokeRole (en : Bool) (name role : GoString) :
    StepSmall (stepOf (userRevokeRoleF en name role)) := by
  intro st st' h hR
  simp only [stepOf, userRevokeRoleF] at hR
  split at hR
  · cases hR
  · split at hR
    · cases hR
    · rename_i u hu
      split at hR
      · cases hR
        have hlen : (u.filter fun r => r ≠ role).length ≤ st.revision + 1 := by
          have := List.length_filter_le (fun r => decide (r ≠ role)) u
          have := h.roles name u hu; omega
        exact ⟨by simp [bump, putUser],
          authSmall_bump_putUser st name _ ((h.nodup name u hu).filter _) hlen
            (h.names name (by rw [hu]; rfl)) h⟩
      · cases hR

theorem stepSmall_roleAdd (name : GoString) : StepSmall (stepOf (roleAddF name)) := by
  intro st st' h hR
  simp only [stepOf, roleAddF] at hR
  split at hR
  · cases hR
  · split at hR
    · cases hR
    · cases hR
      exact ⟨by simp [bump, putRole], authSmall_bump_putRole st name [] (by simp) h⟩

theorem stepSmall_roleDelete (en : Bool) (role : GoString) :
    StepSmall (stepOf (roleDeleteF en role)) := by
  intro st st' h hR
  simp only [stepOf, roleDeleteF] at hR
  split at hR
  · cases hR
  · split at hR
    · cases hR
    · cases hR; exact ⟨by simp [bump, delRole], authSmall_bump_delRole st role h⟩

theorem stepSmall_roleRevokePermission (role key rangeEnd : GoString) :
    StepSmall (roleRevokePermissionR role key rangeEnd) := by
  intro st st' h hR
  simp only [roleRevokePermissionR] at hR
  split at hR
  · cases hR
  · rename_i ps hps
    rcases hR with ⟨hR, -⟩ | hR
    · cases hR
    · cases hR
      refine ⟨by simp [bump, putRole], authSmall_bump_putRole st role _ ?_ h⟩
      rw [hps]; simp only [Option.getD_some]
      have := List.length_filter_le (fun p => decide ¬ permAt key rangeEnd p) ps
      omega

theorem stepSmall_roleGrantPermission (role : GoString) (w : Option PermW) :
    StepSmall (roleGrantPermissionR role w) := by
  intro st st' h hR
  simp only [roleGrantPermissionR] at hR
  split at hR
  · cases hR
  · rename_i w
    split at hR
    · cases hR
    · split at hR
      · cases hR
      · rename_i ps hps
        cases hR
        refine ⟨by simp [bump, putRole], authSmall_bump_putRole st role _ ?_ h⟩
        rw [hps]; simp only [Option.getD_some, grantPerms, List.length_append]
        have := List.length_filter_le (fun p => decide ¬ permAt w.key w.rangeEnd p) ps
        cases permOfWire w <;> simp only [Option.toList_none, Option.toList_some, List.length_nil,
          List.length_singleton] <;> omega

/-! ## The fuel -/

/-- **The fuel's pure part**: the latest state small, its revision at most `k + 1` for `k`
receipts held. -/
def fuelOk (hs : List AuthState) (k : Nat) : Prop :=
  ∀ st, hs.getLast? = some st → st.revision ≤ k + 1 ∧ authSmall st

theorem fuelOk_mono (hs : List AuthState) (k : Nat) (h : fuelOk hs k) : fuelOk hs (k + 1) := by
  intro st hst
  obtain ⟨h1, h2⟩ := h st hst
  exact ⟨by omega, h2⟩

theorem fuelOk_next (hs : List AuthState) (k : Nat) (R : StepRel) (st st' : AuthState)
    (hf : fuelOk hs k) (hR : StepSmall R) (hl : hs.getLast? = some st) (hst : R st (.next st')) :
    fuelOk (hs ++ [st']) (k + 1) := by
  intro x hx
  rw [List.getLast?_concat] at hx
  cases hx
  obtain ⟨h1, h2⟩ := hf st hl
  obtain ⟨h3, h4⟩ := hR st st' h2 hst
  exact ⟨by omega, h4⟩

/-- The latest state of a fueled history: small, its revision at most `k + 1`. -/
theorem fuelOk_last (γa : AuthNames) (hs : List AuthState) (k : Nat) (st : AuthState)
    (hf : fuelOk hs k) (hl : histLast (.on γa) hs st) : st.revision ≤ k + 1 ∧ authSmall st :=
  hf st hl

/-- **The step's premises from the fuel** (see the file header): with `k + 1` receipts' bound. -/
theorem stepOk_of_fuel (γa : AuthNames) (hs : List AuthState) (R : StepRel) (k : Nat)
    (hR : StepSmall R) (hf : fuelOk hs k) (hk : k + 1 < 2 ^ 48) : stepOk (.on γa) hs R := by
  intro st hst
  simp only [histLast] at hst
  obtain ⟨h1, h2⟩ := hf st hst
  refine ⟨by omega, ?_⟩
  intro o st' hro ho
  subst ho
  obtain ⟨h3, h4⟩ := hR st st' h2 hro
  exact permsFit_of_small st' h4 (by omega)

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Iris.ProofMode

/-- **The admin side's fuel** for the history `hs` (see the file header): `k` receipts, the latest
state small with its revision at most `k + 1`. -/
def authFuel (hs : List AuthState) : IProp GF :=
  iprop(∃ k : Nat, ⧗ k ∗ ⌜fuelOk hs k⌝)

/-- The fuel charged with a request's receipt, before its step. -/
def authFuelT (hs : List AuthState) : IProp GF :=
  iprop(∃ k : Nat, ⧗ (k + 1) ∗ ⌜fuelOk hs k⌝ ∗ ⌜k + 1 < receiptBound GF⌝)

/-- **The authority with its fuel** (the mode `on γa`). -/
def authOwnFu (γa : AuthNames) (hs : List AuthState) : IProp GF :=
  iprop(authOwn (.on γa) hs ∗ authFuel hs)

/-- The fuel at a history whose latest state is small with revision at most one (the store's
start: `NewAuthStore`'s `[bootState, bump bootState]`). -/
theorem authFuel_init (hs : List AuthState) (st : AuthState) (hl : hs.getLast? = some st)
    (hst : authSmall st) (hr : st.revision ≤ 1) : ⊢ |==> authFuel (GF := GF) hs := by
  imod (receipt_zero (GF := GF)) with H
  imodintro
  iunfold authFuel
  iexists 0
  iframe H
  ipureintro
  intro x hx
  rw [hl] at hx; cases hx
  exact ⟨by omega, hst⟩

/-- A request's receipt charges the fuel. -/
theorem authFuel_charge (hs : List AuthState) :
    authFuel (GF := GF) hs ∗ ⧗ 1 ⊢ authFuelT hs := by
  iintro ⟨H, Hr⟩
  iunfold authFuel at H
  icases H with ⟨%k, Hk, %Hf⟩
  icases receipt_add_one_lt k $$ [Hr Hk] with ⟨%Hlt, Hk⟩
  · iframe
  iunfold authFuelT
  iexists k
  iframe Hk
  ipureintro; exact ⟨Hf, Hlt⟩

/-- **The step's premises from the charged fuel**, under the receipts' bound `2 ^ 48`. -/
theorem authFuelT_stepOk (γa : AuthNames) (hs : List AuthState) (R : StepRel) (hR : StepSmall R)
    (hb : receiptBound GF ≤ 2 ^ 48) :
    authFuelT (GF := GF) hs ⊢ ⌜stepOk (.on γa) hs R⌝ := by
  iintro H
  iunfold authFuelT at H
  icases H with ⟨%k, -, %Hf, %Hlt⟩
  ipureintro
  exact stepOk_of_fuel γa hs R k hR Hf (by omega)

/-- The charged fuel's pure part, kept: the fuel's count below the receipts' bound `2 ^ 48`. -/
theorem authFuelT_fuel (hs : List AuthState) (hb : receiptBound GF ≤ 2 ^ 48) :
    authFuelT (GF := GF) hs ⊢ authFuelT hs ∗ ⌜∃ k, fuelOk hs k ∧ k + 1 < 2 ^ 48⌝ := by
  iintro H
  iunfold authFuelT at H
  icases H with ⟨%k, Hk, %Hf, %Hlt⟩
  isplitl [Hk]
  · iunfold authFuelT; iexists k; iframe Hk; ipureintro; exact ⟨Hf, Hlt⟩
  · ipureintro; exact ⟨k, Hf, by omega⟩

/-- The fuel after a refusal or no change (the history kept). -/
theorem authFuelT_keep (hs : List AuthState) : authFuelT (GF := GF) hs ⊢ authFuel hs := by
  iintro H
  iunfold authFuelT at H
  icases H with ⟨%k, Hk, %Hf, -⟩
  iunfold authFuel
  iexists k + 1
  iframe Hk
  ipureintro; exact fuelOk_mono hs k Hf

/-- The fuel after a step to `st'` from the latest state `st`. -/
theorem authFuelT_next (hs : List AuthState) (R : StepRel) (st st' : AuthState)
    (hR : StepSmall R) (hl : hs.getLast? = some st) (hst : R st (.next st')) :
    authFuelT (GF := GF) hs ⊢ authFuel (hs ++ [st']) := by
  iintro H
  iunfold authFuelT at H
  icases H with ⟨%k, Hk, %Hf, -⟩
  iunfold authFuel
  iexists k + 1
  iframe Hk
  ipureintro; exact fuelOk_next hs k R st st' Hf hR hl hst

/-- The authority with its fuel after the outcome `o` (as `outRes`). -/
def outResFu (γa : AuthNames) (hs : List AuthState) (o : Outcome) (err : GoInterface) : IProp GF :=
  match o with
  | .err e => iprop(authOwnFu γa hs ∗ authErrOf e err)
  | .same => iprop(authOwnFu γa hs ∗ ⌜err = GoInterface.nil⌝)
  | .next st' => iprop(authOwnFu γa (hs ++ [st']) ∗ ⌜err = GoInterface.nil⌝)

/-- **An admin operation's result with the fuel** (as `adminOut` in the mode `on γa`, with
`authOwnFu` for `authOwn`). -/
def adminOutFu (γa : AuthNames) (hs : List AuthState) (R : StepRel) (extra : AuthErr → Prop)
    (err : GoInterface) : IProp GF :=
  iprop((∃ e : AuthErr, ⌜extra e⌝ ∗ authOwnFu γa hs ∗ authErrOf e err) ∨
    (∃ (st : AuthState) (o : Outcome), ⌜histLast (.on γa) hs st ∧ R st o⌝ ∗
      outResFu γa hs o err))

/-- **The step's result with the fuel back**: the charged fuel follows the authority. -/
theorem adminOut_fu (γa : AuthNames) (hs : List AuthState) (R : StepRel) (extra : AuthErr → Prop)
    (err : GoInterface) (hR : StepSmall R) :
    authFuelT (GF := GF) hs ∗ adminOut (.on γa) hs R extra err ⊢ adminOutFu γa hs R extra err := by
  iintro ⟨Hf, Ho⟩
  iunfold adminOut at Ho
  iunfold adminOutFu
  icases Ho with (⟨%e, %He, Hown, Herr⟩ | ⟨%st, %o, %Hst, Hres⟩)
  · ileft
    iexists e
    ihave Hf := authFuelT_keep hs $$ Hf
    isplitr
    · ipureintro; exact He
    isplitl [Hown Hf]
    · iunfold authOwnFu; iframe Hown Hf
    · iexact Herr
  · iright
    iexists st, o
    isplitr
    · ipureintro; exact Hst
    cases o with
    | err e =>
      simp only [outRes, outResFu, authOwnFu]
      icases Hres with ⟨Hown, Herr⟩
      ihave Hf := authFuelT_keep hs $$ Hf
      iframe Hown Hf Herr
    | same =>
      simp only [outRes, outResFu, authOwnFu]
      icases Hres with ⟨Hown, Herr⟩
      ihave Hf := authFuelT_keep hs $$ Hf
      iframe Hown Hf Herr
    | next st' =>
      simp only [outRes, outResFu, authOwnFu]
      icases Hres with ⟨Hown, Herr⟩
      ihave Hf := authFuelT_next hs R st st' hR Hst.1 Hst.2 $$ Hf
      iframe Hown Hf Herr

end ghost

end auth
end EtcdGrove
end Perennial
