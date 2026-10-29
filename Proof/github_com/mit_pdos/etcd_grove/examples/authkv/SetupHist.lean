/-
**The auth history `SetUp` writes** (the auth-mode merge's 5b, 2026-10-29). Lean-first (no Rocq
counterpart).

`SetUp`'s client holds the only view of the auth history (`authHistView`), so the history's states
are the boot state followed by the states its own admin requests (`setupRq`) record. Each request
may be delivered several times (the client retries an attempt), and an attempt may commit after
the client has moved on, so the history is not the eight calls in order. What holds of it:
- while auth is disabled, every state has the set-up's shape (`setupLike`: the users `root`, `u`,
  `v` and the role `r`, each absent or at a stage of its set-up), and a request's step keeps it
  (`setup_step`);
- the set-up's effects (`setupEff`: a user added, a role granted, ...) are never undone
  (`setup_step`'s monotonicity);
- a recorded step of a request has its effect (`setup_step_eff`), and so does a successful reply
  that recorded nothing (`setup_notRec_eff`, the one case a `UserGrantRole` already applied);
- `AuthEnable` at a state with every effect enables exactly `setupSt` (`setup_enable`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthEntry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open auth go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The permission `SetUp` grants role `r` on the wire: `READWRITE` (`2`) on `[a, b)`. -/
def permRW : PermW := ⟨W32 2, lo, hi⟩

theorem permOfWire_permRW : permOfWire permRW = some permR := by
  simp [permOfWire, permRW, permR]

/-- **A state of the set-up's shape**: disabled, the users `root`, `u`, `v` and the role `r`
each absent or at a stage of its set-up, no other user or role. -/
def setupLike (st : AuthState) : Prop :=
  st.enabled = false ∧
  (st.users !! go!"root" = none ∨ st.users !! go!"root" = some [] ∨
    st.users !! go!"root" = some [rootRole]) ∧
  (st.users !! go!"u" = none ∨ st.users !! go!"u" = some [] ∨
    st.users !! go!"u" = some [go!"r"]) ∧
  (st.users !! go!"v" = none ∨ st.users !! go!"v" = some []) ∧
  (∀ k, k ≠ go!"root" → k ≠ go!"u" → k ≠ go!"v" → st.users !! k = none) ∧
  (st.roles !! go!"r" = none ∨ st.roles !! go!"r" = some [] ∨ st.roles !! go!"r" = some [permR]) ∧
  (∀ k, k ≠ go!"r" → st.roles !! k = none)

/-- **The set-up's effects**, one per request but `AuthEnable` (`0` to `6`, in `SetUp`'s order). -/
def setupEff (j : Nat) (st : AuthState) : Prop :=
  match j with
  | 0 => (st.users !! go!"root").isSome
  | 1 => ∃ x, st.users !! go!"root" = some x ∧ rootRole ∈ x
  | 2 => (st.roles !! go!"r").isSome
  | 3 => ∃ ps, st.roles !! go!"r" = some ps ∧ permR ∈ ps
  | 4 => (st.users !! go!"u").isSome
  | 5 => ∃ x, st.users !! go!"u" = some x ∧ go!"r" ∈ x
  | 6 => (st.users !! go!"v").isSome
  | _ => True

/-- **`SetUp`'s `j`-th admin request** (`0` to `7`, in `SetUp`'s order; see `setupRq`). -/
def setupReqAt (j : Nat) (rq : apply.IRRModel) : Prop :=
  match j with
  | 0 => ∃ um : apply.UserAddModel, rq = irrUserAdd um ∧ um.pwSure ∧ um.name = go!"root"
  | 1 => rq = irrUserGrantRole go!"root" go!"root"
  | 2 => rq = irrRoleAdd go!"r"
  | 3 => rq = irrRoleGrantPermission go!"r" (some permRW)
  | 4 => ∃ um : apply.UserAddModel, rq = irrUserAdd um ∧ um.pwSure ∧ um.name = go!"u"
  | 5 => rq = irrUserGrantRole go!"u" go!"r"
  | 6 => ∃ um : apply.UserAddModel, rq = irrUserAdd um ∧ um.pwSure ∧ um.name = go!"v"
  | 7 => rq = irrAuthEnable
  | _ => False

/-- **`SetUp`'s admin requests** (before the server stamps a header). -/
def setupRq (rq : apply.IRRModel) : Prop := ∃ j, setupReqAt j rq

theorem srvAuthSt0_setupLike : setupLike srvAuthSt0 := by
  simp [setupLike, srvAuthSt0, auth.bump, auth.bootState]

/-- The model's step is one the relation allows (at a determinate entry). -/
theorem adminStateR_adminNext (rq : apply.IRRModel) (st : AuthState) (hd : authDet rq st) :
    adminStateR rq st (adminNext rq st) := by
  unfold adminNext
  rw [dif_pos hd]
  exact (Classical.choose_spec hd).1

/-- At a disabled state, every principal is admin-permitted. -/
theorem adminOk_disabled (st : AuthState) (ai : Option AuthInfoM) (h : st.enabled = false) :
    adminOk st ai := Or.inl h

theorem bump_ne (st : AuthState) : bump st ≠ st := by
  intro h
  have := congrArg AuthState.revision h
  simp [bump] at this

theorem setup_step_userAdd (um : apply.UserAddModel) (hm : apply.HeaderModel) (st st' : AuthState)
    (hpw : um.pwSure) (hl : setupLike st)
    (hn : um.name = go!"root" ∨ um.name = go!"u" ∨ um.name = go!"v")
    (hR : adminStateR (apply.withHeader (irrUserAdd um) hm) st st') :
    st' = st ∨ ((st.users !! um.name) = none ∧ st' = bump (putUser st um.name [])) := by
  unfold adminStateR at hR
  rw [if_pos (adminOk_disabled _ _ hl.1)] at hR
  simp only [dispatchKind_withHeader] at hR
  have hk : apply.dispatchKind (irrUserAdd um) = .authUserAdd := by
    simp [apply.dispatchKind, irrUserAdd, apply.irrEmpty]
  rw [hk] at hR
  have hR' : (¬ um.pwSure ∧ st' = st) ∨ authRelState (stepOf (userAddF um.name)) st st' := hR
  rcases hR' with ⟨h, -⟩ | ⟨o, ho, rfl⟩
  · exact absurd hpw h
  · unfold stepOf at ho
    subst ho
    unfold userAddF
    have hne : um.name ≠ [] := by rcases hn with h | h | h <;> rw [h] <;> decide
    rw [if_neg hne]
    by_cases hs : (st.users !! um.name).isSome
    · rw [if_pos hs]; left; rfl
    · rw [if_neg hs]; right
      exact ⟨Option.not_isSome_iff_eq_none.1 hs, rfl⟩

theorem setup_step_ugr (user role : GoString) (hm : apply.HeaderModel) (st st' : AuthState)
    (hl : setupLike st)
    (hR : adminStateR (apply.withHeader (irrUserGrantRole user role) hm) st st') :
    st' = st ∨ ∃ u u' : User, st.users !! user = some u ∧ role ∉ u ∧ u'.Perm (u ++ [role]) ∧
      st' = bump (putUser st user u') := by
  unfold adminStateR at hR
  rw [if_pos (adminOk_disabled _ _ hl.1)] at hR
  simp only [dispatchKind_withHeader] at hR
  have hk : apply.dispatchKind (irrUserGrantRole user role) = .authUserGrantRole := by
    simp [apply.dispatchKind, irrUserGrantRole, apply.irrEmpty]
  rw [hk] at hR
  have hR' : authRelState (userGrantRoleR user role) st st' := hR
  obtain ⟨o, ho, rfl⟩ := hR'
  unfold userGrantRoleR at ho
  split at ho
  · subst ho; left; rfl
  · rename_i u hu
    split at ho
    · subst ho; left; rfl
    · split at ho
      · subst ho; left; rfl
      · rename_i hnin
        obtain ⟨u', hp, -, rfl⟩ := ho
        right
        exact ⟨u, u', hu, hnin, hp, rfl⟩

theorem setup_step_roleAdd (n : GoString) (hm : apply.HeaderModel) (st st' : AuthState)
    (hl : setupLike st) (hR : adminStateR (apply.withHeader (irrRoleAdd n) hm) st st') :
    st' = st ∨ (st.roles !! n = none ∧ st' = bump (putRole st n [])) := by
  unfold adminStateR at hR
  rw [if_pos (adminOk_disabled _ _ hl.1)] at hR
  simp only [dispatchKind_withHeader] at hR
  have hk : apply.dispatchKind (irrRoleAdd n) = .authRoleAdd := by
    simp [apply.dispatchKind, irrRoleAdd, apply.irrEmpty]
  rw [hk] at hR
  have hR' : authRelState (stepOf (roleAddF n)) st st' := hR
  obtain ⟨o, ho, rfl⟩ := hR'
  unfold stepOf at ho
  subst ho
  unfold roleAddF
  by_cases hne : n = []
  · rw [if_pos hne]; left; rfl
  rw [if_neg hne]
  by_cases hs : (st.roles !! n).isSome
  · rw [if_pos hs]; left; rfl
  · rw [if_neg hs]; right
    exact ⟨Option.not_isSome_iff_eq_none.1 hs, rfl⟩

theorem setup_step_rgp (n : GoString) (w : PermW) (hm : apply.HeaderModel) (st st' : AuthState)
    (hl : setupLike st)
    (hR : adminStateR (apply.withHeader (irrRoleGrantPermission n (some w)) hm) st st') :
    st' = st ∨ ∃ ps, st.roles !! n = some ps ∧ st' = bump (putRole st n (grantPerms ps w)) := by
  unfold adminStateR at hR
  rw [if_pos (adminOk_disabled _ _ hl.1)] at hR
  simp only [dispatchKind_withHeader] at hR
  have hk : apply.dispatchKind (irrRoleGrantPermission n (some w)) = .authRoleGrantPermission := by
    simp [apply.dispatchKind, irrRoleGrantPermission, apply.irrEmpty]
  rw [hk] at hR
  have hR' : authRelState (roleGrantPermissionR n (some w)) st st' := hR
  obtain ⟨o, ho, rfl⟩ := hR'
  unfold roleGrantPermissionR at ho
  simp only at ho
  split at ho
  · subst ho; left; rfl
  · split at ho
    · subst ho; left; rfl
    · rename_i ps hps
      subst ho
      right
      exact ⟨ps, hps, rfl⟩

theorem setup_step_enable (hm : apply.HeaderModel) (st st' : AuthState) (hl : setupLike st)
    (hR : adminStateR (apply.withHeader irrAuthEnable hm) st st') :
    st' = st ∨ ∃ u, st.users !! rootRole = some u ∧ isRoot u ∧ st' = { st with enabled := true } := by
  unfold adminStateR at hR
  rw [if_pos (adminOk_disabled _ _ hl.1)] at hR
  simp only [dispatchKind_withHeader] at hR
  have hk : apply.dispatchKind irrAuthEnable = .authEnable := by
    simp [apply.dispatchKind, irrAuthEnable, apply.irrEmpty]
  rw [hk] at hR
  have hR' : authRelState (stepOf (authEnableF st.enabled)) st st' := hR
  obtain ⟨o, ho, rfl⟩ := hR'
  unfold stepOf at ho
  subst ho
  unfold authEnableF
  rw [hl.1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · left; rfl
  · rename_i u hu
    split
    · right; exact ⟨u, hu, by assumption, rfl⟩
    · left; rfl

/-! ### The shape and the effects under a step -/

theorem setupLike_putUser (st : AuthState) (n : GoString) (x : User) (hl : setupLike st)
    (hx : (n = go!"root" ∧ (x = [] ∨ x = [rootRole])) ∨ (n = go!"u" ∧ (x = [] ∨ x = [go!"r"])) ∨
      (n = go!"v" ∧ x = [])) :
    setupLike (bump (putUser st n x)) := by
  obtain ⟨he, hr, hu, hv, ho, hrr, hro⟩ := hl
  simp only [setupLike, bump, putUser]
  rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, rfl⟩
  · refine ⟨he, ?_, ?_, ?_, ?_, hrr, hro⟩
    · rw [GMap.lookup_insert]; rcases hx with rfl | rfl <;> simp
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hu
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hv
    · intro k h1 h2 h3; rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)]; exact ho k h1 h2 h3
  · refine ⟨he, ?_, ?_, ?_, ?_, hrr, hro⟩
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hr
    · rw [GMap.lookup_insert]; rcases hx with rfl | rfl <;> simp
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hv
    · intro k h1 h2 h3; rw [GMap.lookup_insert_ne _ _ (Ne.symm h2)]; exact ho k h1 h2 h3
  · refine ⟨he, ?_, ?_, ?_, ?_, hrr, hro⟩
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hr
    · rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hu
    · rw [GMap.lookup_insert]; simp
    · intro k h1 h2 h3; rw [GMap.lookup_insert_ne _ _ (Ne.symm h3)]; exact ho k h1 h2 h3

theorem setupLike_putRole (st : AuthState) (x : auth.Role) (hl : setupLike st)
    (hx : x = [] ∨ x = [permR]) :
    setupLike (bump (putRole st go!"r" x)) := by
  obtain ⟨he, hr, hu, hv, ho, hrr, hro⟩ := hl
  simp only [setupLike, bump, putRole]
  refine ⟨he, hr, hu, hv, ho, ?_, ?_⟩
  · rw [GMap.lookup_insert]; rcases hx with rfl | rfl <;> simp
  · intro k h1; rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)]; exact hro k h1

theorem setupEff_putUser (st : AuthState) (n : GoString) (x : User) (i : Nat)
    (hsub : ∀ u0, st.users !! n = some u0 → ∀ r ∈ u0, r ∈ x) (h : setupEff i st) :
    setupEff i (bump (putUser st n x)) := by
  have key : ∀ k, (st.users !! k).isSome → ((bump (putUser st n x)).users !! k).isSome := by
    intro k hk
    simp only [bump, putUser]
    by_cases hkn : n = k
    · subst hkn; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ hkn]; exact hk
  have key2 : ∀ k r, (∃ y, st.users !! k = some y ∧ r ∈ y) →
      ∃ y, (bump (putUser st n x)).users !! k = some y ∧ r ∈ y := by
    rintro k r ⟨y, hy, hr⟩
    simp only [bump, putUser]
    by_cases hkn : n = k
    · subst hkn; rw [GMap.lookup_insert]; exact ⟨x, rfl, hsub y hy r hr⟩
    · rw [GMap.lookup_insert_ne _ _ hkn]; exact ⟨y, hy, hr⟩
  match i, h with
  | 0, h => exact key _ h
  | 1, h => exact key2 _ _ h
  | 2, h => exact h
  | 3, h => exact h
  | 4, h => exact key _ h
  | 5, h => exact key2 _ _ h
  | 6, h => exact key _ h
  | _ + 7, h => trivial

theorem setupEff_putRole (st : AuthState) (x : auth.Role) (i : Nat)
    (hsub : ∀ ps, st.roles !! go!"r" = some ps → permR ∈ ps → permR ∈ x) (h : setupEff i st) :
    setupEff i (bump (putRole st go!"r" x)) := by
  match i, h with
  | 0, h => exact h
  | 1, h => exact h
  | 2, h => show ((GMap.insert go!"r" x st.roles) !! go!"r").isSome; rw [GMap.lookup_insert]; rfl
  | 3, h =>
    obtain ⟨ps, hps, hp⟩ := h
    exact ⟨x, GMap.lookup_insert _ _ _, hsub ps hps hp⟩
  | 4, h => exact h
  | 5, h => exact h
  | 6, h => exact h
  | _ + 7, h => trivial

theorem grantPerms_permRW (ps : auth.Role) (h : ps = [] ∨ ps = [permR]) :
    grantPerms ps permRW = [permR] := by
  rcases h with rfl | rfl <;> simp only [grantPerms, permOfWire_permRW] <;> simp [permAt, permR, permRW]

/-- A user's roles granted one more, at the set-up's stage before it. -/
theorem setup_ugr_roles (u u' : User) (role : GoString) (h : u = [] ∨ u = [role])
    (hnin : role ∉ u) (hp : u'.Perm (u ++ [role])) : u = [] ∧ u' = [role] := by
  rcases h with rfl | rfl
  · exact ⟨rfl, List.perm_singleton.1 hp⟩
  · simp at hnin

/-- **A step of a set-up request but `AuthEnable`** at a state of the set-up's shape: the shape
kept, every effect kept, and the request's own effect if the state changed. -/
theorem setup_step (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀) (hj7 : j < 7)
    (hm : apply.HeaderModel) (st st' : AuthState) (hl : setupLike st)
    (hR : adminStateR (apply.withHeader rq₀ hm) st st') :
    setupLike st' ∧ (∀ i, setupEff i st → setupEff i st') ∧ (st' ≠ st → setupEff j st') := by
  have same : st' = st → setupLike st' ∧ (∀ i, setupEff i st → setupEff i st') ∧
      (st' ≠ st → setupEff j st') := by
    rintro rfl; exact ⟨hl, fun _ h => h, fun h => absurd rfl h⟩
  have hadd : ∀ (n : GoString), st.users !! n = none →
      ((n = go!"root" ∧ ([] : User) = []) ∨ (n = go!"u" ∧ ([] : User) = []) ∨
        (n = go!"v" ∧ ([] : User) = [])) →
      setupLike (bump (putUser st n [])) ∧
        (∀ i, setupEff i st → setupEff i (bump (putUser st n []))) := by
    intro n hnone hn
    refine ⟨setupLike_putUser st n [] hl ?_, fun i h => setupEff_putUser st n [] i ?_ h⟩
    · rcases hn with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl ⟨h, Or.inl rfl⟩
      · exact Or.inr (Or.inl ⟨h, Or.inl rfl⟩)
      · exact Or.inr (Or.inr ⟨h, rfl⟩)
    · intro u0 hu0; rw [hnone] at hu0; cases hu0
  have hlook : ∀ n x, (bump (putUser st n x)).users !! n = some x := by
    intro n x; simp only [bump, putUser]; exact GMap.lookup_insert _ _ _
  match j, hj with
  | 0, ⟨um, hrq, hpw, hn⟩ =>
    subst hrq
    rcases setup_step_userAdd um hm st st' hpw hl (Or.inl hn) hR with h | ⟨hnone, rfl⟩
    · exact same h
    · obtain ⟨h1, h2⟩ := hadd um.name hnone (Or.inl ⟨hn, rfl⟩)
      refine ⟨h1, h2, fun _ => ?_⟩
      show ((bump (putUser st um.name [])).users !! go!"root").isSome
      rw [← hn, hlook]; rfl
  | 4, ⟨um, hrq, hpw, hn⟩ =>
    subst hrq
    rcases setup_step_userAdd um hm st st' hpw hl (Or.inr (Or.inl hn)) hR with h | ⟨hnone, rfl⟩
    · exact same h
    · obtain ⟨h1, h2⟩ := hadd um.name hnone (Or.inr (Or.inl ⟨hn, rfl⟩))
      refine ⟨h1, h2, fun _ => ?_⟩
      show ((bump (putUser st um.name [])).users !! go!"u").isSome
      rw [← hn, hlook]; rfl
  | 6, ⟨um, hrq, hpw, hn⟩ =>
    subst hrq
    rcases setup_step_userAdd um hm st st' hpw hl (Or.inr (Or.inr hn)) hR with h | ⟨hnone, rfl⟩
    · exact same h
    · obtain ⟨h1, h2⟩ := hadd um.name hnone (Or.inr (Or.inr ⟨hn, rfl⟩))
      refine ⟨h1, h2, fun _ => ?_⟩
      show ((bump (putUser st um.name [])).users !! go!"v").isSome
      rw [← hn, hlook]; rfl
  | 1, hrq =>
    subst hrq
    rcases setup_step_ugr _ _ hm st st' hl hR with h | ⟨u, u', hu, hnin, hp, rfl⟩
    · exact same h
    · have hu2 : u = [] ∨ u = [rootRole] := by
        rcases hl.2.1 with h | h | h <;> rw [hu] at h <;> cases h
        · exact Or.inl rfl
        · exact Or.inr rfl
      obtain ⟨-, rfl⟩ := setup_ugr_roles u u' rootRole hu2 hnin hp
      refine ⟨setupLike_putUser st _ _ hl (Or.inl ⟨rfl, Or.inr rfl⟩),
        fun i h => setupEff_putUser st _ _ i ?_ h, fun _ => ⟨_, hlook _ _, by simp⟩⟩
      intro u0 hu0 r hr
      rw [hu] at hu0; cases hu0; exact hp.mem_iff.2 (List.mem_append_left _ hr)
  | 5, hrq =>
    subst hrq
    rcases setup_step_ugr _ _ hm st st' hl hR with h | ⟨u, u', hu, hnin, hp, rfl⟩
    · exact same h
    · have hu2 : u = [] ∨ u = [go!"r"] := by
        rcases hl.2.2.1 with h | h | h <;> rw [hu] at h <;> cases h
        · exact Or.inl rfl
        · exact Or.inr rfl
      obtain ⟨-, rfl⟩ := setup_ugr_roles u u' _ hu2 hnin hp
      refine ⟨setupLike_putUser st _ _ hl (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)),
        fun i h => setupEff_putUser st _ _ i ?_ h, fun _ => ⟨_, hlook _ _, by simp⟩⟩
      intro u0 hu0 r hr
      rw [hu] at hu0; cases hu0; exact hp.mem_iff.2 (List.mem_append_left _ hr)
  | 2, hrq =>
    subst hrq
    rcases setup_step_roleAdd _ hm st st' hl hR with h | ⟨hnone, rfl⟩
    · exact same h
    · refine ⟨setupLike_putRole st [] hl (Or.inl rfl),
        fun i h => setupEff_putRole st [] i ?_ h, fun _ => ?_⟩
      · intro ps hps; rw [hnone] at hps; cases hps
      · show ((GMap.insert go!"r" [] st.roles) !! go!"r").isSome
        rw [GMap.lookup_insert]; rfl
  | 3, hrq =>
    subst hrq
    rcases setup_step_rgp _ _ hm st st' hl hR with h | ⟨ps, hps, rfl⟩
    · exact same h
    · have hps2 : ps = [] ∨ ps = [permR] := by
        rcases hl.2.2.2.2.2.1 with h | h | h <;> rw [hps] at h <;> cases h
        · exact Or.inl rfl
        · exact Or.inr rfl
      rw [grantPerms_permRW ps hps2]
      refine ⟨setupLike_putRole st _ hl (Or.inr rfl),
        fun i h => setupEff_putRole st _ i (fun _ _ _ => by simp) h,
        fun _ => ⟨[permR], GMap.lookup_insert _ _ _, by simp⟩⟩

/-- **`AuthEnable` after every set-up effect** enables exactly `setupSt` at the state's
revision. -/
theorem setup_enable (st : AuthState) (hl : setupLike st) (he : ∀ i, i < 7 → setupEff i st) :
    { st with enabled := true } = setupSt st.revision := by
  obtain ⟨-, hr, hu, hv, ho, hrr, hro⟩ := hl
  have hr' : st.users !! go!"root" = some [rootRole] := by
    obtain ⟨x, hx, hm⟩ := (he 1 (by omega) : setupEff 1 st)
    rcases hr with h | h | h <;> rw [hx] at h <;> cases h
    · simp at hm
    · exact hx
  have hu' : st.users !! go!"u" = some [go!"r"] := by
    obtain ⟨x, hx, hm⟩ := (he 5 (by omega) : setupEff 5 st)
    rcases hu with h | h | h <;> rw [hx] at h <;> cases h
    · simp at hm
    · exact hx
  have hv' : st.users !! go!"v" = some [] := by
    have h6 : (st.users !! go!"v").isSome := he 6 (by omega)
    rcases hv with h | h
    · rw [h] at h6; cases h6
    · exact h
  have hrr' : st.roles !! go!"r" = some [permR] := by
    obtain ⟨x, hx, hm⟩ := (he 3 (by omega) : setupEff 3 st)
    rcases hrr with h | h | h <;> rw [hx] at h <;> cases h
    · simp at hm
    · exact hx
  obtain ⟨en, rev, us, rs⟩ := st
  simp only [setupSt, AuthState.mk.injEq, true_and]
  simp only at hr' hu' hv' hrr' ho hro
  constructor
  · apply GMap.ext
    intro k
    show us !! k = _
    by_cases h1 : k = go!"root"
    · subst h1; rw [hr', GMap.lookup_insert]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)]
    by_cases h2 : k = go!"u"
    · subst h2; rw [hu', GMap.lookup_insert]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h2)]
    by_cases h3 : k = go!"v"
    · subst h3; rw [hv', GMap.lookup_insert]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h3), ho k h1 h2 h3]
    rfl
  · apply GMap.ext
    intro k
    show rs !! k = _
    by_cases h1 : k = go!"r"
    · subst h1; rw [hrr', GMap.lookup_insert]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h1), hro k h1]
    rfl

/-- **A successful set-up request that recorded nothing** (its step left the state, at a state of
the set-up's shape): not `AuthEnable`, and its effect was already there (a `UserGrantRole` of a
role the user has; every other request changes the state when it succeeds). -/
theorem setup_notRec_eff (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀)
    (hm : apply.HeaderModel) (st : AuthState) (hl : setupLike st)
    (hok : adminStepOk (apply.withHeader rq₀ hm) st (adminNext (apply.withHeader rq₀ hm) st))
    (hsame : adminNext (apply.withHeader rq₀ hm) st = st) :
    j < 7 ∧ setupEff j st := by
  obtain ⟨-, o, hO, hne, hst⟩ := hok
  rw [hsame] at hst
  unfold adminStepO at hO
  simp only [dispatchKind_withHeader] at hO
  have hbump : ∀ x : AuthState, x.revision = st.revision → outState st (.next (bump x)) ≠ st := by
    intro x hx h
    have := congrArg AuthState.revision h
    simp [outState, bump, hx] at this
  match j, hj with
  | 0, ⟨um, hrq, _, _⟩ | 4, ⟨um, hrq, _, _⟩ | 6, ⟨um, hrq, _, _⟩ =>
    subst hrq
    have hk : apply.dispatchKind (irrUserAdd um) = .authUserAdd := by
      simp [apply.dispatchKind, irrUserAdd, apply.irrEmpty]
    rw [hk] at hO
    obtain ⟨m, hm', ho⟩ := hO
    cases hm'
    unfold stepOf at ho
    subst ho
    unfold userAddF at hne hst
    by_cases h1 : um.name = []
    · simp [h1] at hne
    by_cases h2 : (st.users !! um.name).isSome = true
    · simp [h1, h2] at hne
    simp only [h1, h2, if_false] at hst
    exact absurd hst.symm (hbump _ rfl)
  | 2, hrq =>
    subst hrq
    have hk : apply.dispatchKind (irrRoleAdd go!"r") = .authRoleAdd := by
      simp [apply.dispatchKind, irrRoleAdd, apply.irrEmpty]
    rw [hk] at hO
    obtain ⟨n, hn', ho⟩ := hO
    cases hn'
    unfold stepOf at ho
    subst ho
    unfold roleAddF at hne hst
    by_cases h2 : (st.roles !! go!"r").isSome = true
    · simp [h2] at hne
    simp only [h2, if_false, show go!"r" ≠ [] by decide] at hst
    exact absurd hst.symm (hbump _ rfl)
  | 3, hrq =>
    subst hrq
    have hk : apply.dispatchKind (irrRoleGrantPermission go!"r" (some permRW)) =
        .authRoleGrantPermission := by
      simp [apply.dispatchKind, irrRoleGrantPermission, apply.irrEmpty]
    rw [hk] at hO
    obtain ⟨n, w, hn', ho⟩ := hO
    cases hn'
    unfold roleGrantPermissionR at ho
    simp only at ho
    split at ho
    · exact absurd ho (hne _)
    · split at ho
      · exact absurd ho (hne _)
      · subst ho; exact absurd hst.symm (hbump _ rfl)
  | 1, hrq | 5, hrq =>
    subst hrq
    have hk : ∀ u r : GoString, apply.dispatchKind (irrUserGrantRole u r) = .authUserGrantRole := by
      intro u r; simp [apply.dispatchKind, irrUserGrantRole, apply.irrEmpty]
    rw [hk] at hO
    obtain ⟨u, r, hu', ho⟩ := hO
    cases hu'
    unfold userGrantRoleR at ho
    split at ho
    · exact absurd ho (hne _)
    · rename_i x hx
      split at ho
      · exact absurd ho (hne _)
      · split at ho
        · exact ⟨by omega, x, hx, by assumption⟩
        · obtain ⟨u', -, -, rfl⟩ := ho
          exact absurd hst.symm (hbump _ rfl)
  | 7, hrq =>
    subst hrq
    have hk : apply.dispatchKind irrAuthEnable = .authEnable := by
      simp [apply.dispatchKind, irrAuthEnable, apply.irrEmpty]
    rw [hk] at hO
    unfold stepOf at hO
    subst hO
    unfold authEnableF at hne hst
    rw [hl.1] at hne hst
    simp only [Bool.false_eq_true, ↓reduceIte] at hne hst
    cases hu : st.users !! rootRole with
    | none => simp [hu] at hne
    | some u =>
      by_cases hr : isRoot u
      · simp only [hu, hr, if_true] at hst
        have := congrArg AuthState.enabled hst
        simp [outState, hl.1] at this
      · simp [hu, hr] at hne

end pure

end authkv
end EtcdGrove
end Perennial
