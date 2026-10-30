/-
**The tie of the auth store's history to the log** (H5, 2026-10-29; `notes/decisions.md`, "H5: the
auth history's cap"): the pure facts the server's tie (`authHistTie`, `KVApplyOn.lean`) rests on.

- `authOrd`: a state's order, twice its revision plus its flag. Every admin step the model
  records raises it (`adminNext_ord`): the steps bump the revision, but for `AuthEnable`, which
  sets the flag from `false`.
- `srvHist_pairwise`: so the history the log records, the boot state then `admStates`
  (`srvHist`), is strictly ordered, with no state twice (`srvHist_nodup`).
- `prefix_eq_of_last`: a prefix of a history of the log that ends where another history of the
  log does is that history (what pins the store's history, below the cap, to the applied log's).
- `authHistTie_raise`: at an admin entry `m` after the applied log `A`, the apply thread raises
  the cap to the history of `A ++ [m]` and gives the admin step's cap permission
  (`apply.adminExtraG`): the store's history is the applied log's (`srvHist A`), and a step the
  check admits appends the model's next state, which is the history of `A ++ [m]`'s last.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyAdminL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A state's order** (H5): twice its revision, plus one if enabled. -/
def authOrd (st : auth.AuthState) : Nat := 2 * st.revision + (if st.enabled then 1 else 0)

/-- A step whose next state is a bump of `s` raises the order. -/
theorem authOrd_bump (st s : auth.AuthState) (h : st.revision ≤ s.revision) :
    authOrd st < authOrd (auth.bump s) := by
  unfold authOrd auth.bump
  simp only
  split <;> split <;> omega

/-- **An admitted admin step that changes the state raises its order.** -/
theorem adminStateR_ord (rq : apply.IRRModel) (st st' : auth.AuthState)
    (h : adminStateR rq st st') (hne : st' ≠ st) : authOrd st < authOrd st' := by
  unfold adminStateR at h
  split at h
  · split at h
    all_goals first
      | exact absurd h hne
      | skip
    · split at h
      · rcases h with ⟨-, h⟩ | ⟨o, ho, rfl⟩
        · exact absurd h hne
        · simp only [auth.stepOf, auth.userAddF] at ho
          subst ho
          split
          · simp_all [outState]
          split
          · simp_all [outState]
          · exact authOrd_bump st _ (by simp [auth.putUser])
      · exact absurd h hne
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.stepOf, auth.roleAddF] at ho
        subst ho
        split
        · simp_all [outState]
        split
        · simp_all [outState]
        · exact authOrd_bump st _ (by simp [auth.putRole])
      · exact absurd h hne
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.userGrantRoleR] at ho
        split at ho
        · subst ho; simp_all [outState]
        · split at ho
          · subst ho; simp_all [outState]
          · split at ho
            · subst ho; simp_all [outState]
            · obtain ⟨u', -, -, rfl⟩ := ho
              exact authOrd_bump st _ (by simp [auth.putUser])
      · exact absurd h hne
    · split at h
      · obtain ⟨o, ho, rfl⟩ := h
        simp only [auth.roleGrantPermissionR] at ho
        split at ho
        · subst ho; simp_all [outState]
        · split at ho
          · subst ho; simp_all [outState]
          · split at ho
            · subst ho; simp_all [outState]
            · subst ho
              exact authOrd_bump st _ (by simp [auth.putRole])
      · exact absurd h hne
    · obtain ⟨o, ho, rfl⟩ := h
      simp only [auth.stepOf, auth.authEnableF] at ho
      subst ho
      split
      · simp_all [outState]
      · rename_i hen
        split
        · simp_all [outState]
        · split
          · unfold authOrd outState
            simp only [Bool.not_eq_true] at hen
            simp [hen]
          · simp_all [outState]
  · exact absurd h hne

/-- **The model's admin step, where it changes the state, raises its order.** -/
theorem adminNext_ord (rq : apply.IRRModel) (st : auth.AuthState) (hne : adminNext rq st ≠ st) :
    authOrd st < authOrd (adminNext rq st) := by
  unfold adminNext at hne ⊢
  split
  · rename_i hd
    rw [dif_pos hd] at hne
    exact adminStateR_ord rq st _ (Classical.choose_spec hd).1 hne
  · rename_i hd
    rw [dif_neg hd] at hne
    simp_all [outState]

/-- **The history the log `L` records** (H5): the store's boot state, then `admStates` from the
start's state `bump bootState` (the store's history at the start is `[bootState, bump bootState]`). -/
def srvHist (γk : KVNames) (L : List EntryModel) : List auth.AuthState :=
  auth.bootState :: admStates γk (auth.bump auth.bootState) L

theorem srvHist_nil (γk : KVNames) :
    srvHist γk [] = [auth.bootState, auth.bump auth.bootState] := rfl

theorem srvHist_last (γk : KVNames) (L : List EntryModel) :
    (srvHist γk L).getLast? = some (srvAuthAtLog γk (auth.bump auth.bootState) L) := by
  unfold srvHist
  rw [List.getLast?_cons, admStates_last]
  rfl

/-- Appending `x` above the last element keeps a list strictly ordered. -/
theorem pairwise_ord_snoc (l : List auth.AuthState) (z x : auth.AuthState)
    (hl : l.Pairwise (fun a b => authOrd a < authOrd b)) (hz : l.getLast? = some z)
    (hx : authOrd z < authOrd x) :
    (l ++ [x]).Pairwise (fun a b => authOrd a < authOrd b) := by
  rw [List.pairwise_append]
  refine ⟨hl, List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  obtain ⟨ys, hl'⟩ := List.getLast?_eq_some_iff.mp hz
  rw [hl'] at ha hl
  rw [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rw [List.pairwise_append] at hl
    exact Nat.lt_trans (hl.2.2 a ha z (List.mem_singleton_self _)) hx
  · exact hx

/-- **The history the log records is strictly ordered.** -/
theorem srvHist_pairwise (γk : KVNames) (L : List EntryModel) :
    (srvHist γk L).Pairwise (fun a b => authOrd a < authOrd b) := by
  suffices h : ∀ R : List EntryModel,
      (srvHist γk R.reverse).Pairwise (fun a b => authOrd a < authOrd b) by
    simpa using h L.reverse
  intro R
  induction R with
  | nil =>
    simp only [List.reverse_nil]
    rw [srvHist_nil]
    simp [authOrd, auth.bump, auth.bootState]
  | cons m R ih =>
    rw [List.reverse_cons]
    by_cases ha : admEntry γk.c0 (srvAuthAtLog γk (auth.bump auth.bootState) R.reverse) m
    · unfold srvHist at ih ⊢
      rw [admStates_snoc_adm _ _ _ _ ha, ← List.cons_append]
      apply pairwise_ord_snoc _ _ _ ih
      · rw [List.getLast?_cons, admStates_last]
      · obtain ⟨ht, hd, rq, hdec, hv, hna, -, hne⟩ := ha
        rw [srvAuthAtLog_snoc_adm _ _ _ _ rq ht hd hdec hv hna]
        exact adminNext_ord rq _ hne
    · unfold srvHist at ih ⊢
      rw [admStates_snoc_other _ _ _ _ ha]
      exact ih

theorem srvHist_nodup (γk : KVNames) (L : List EntryModel) : (srvHist γk L).Nodup :=
  (srvHist_pairwise γk L).imp (fun h => Nat.ne_of_lt h ∘ congrArg authOrd)

/-- **Two prefixes of a list with no element twice that end at the same element are equal.** -/
theorem prefix_eq_of_last {α : Type} (l h1 h2 : List α) (hn : l.Nodup) (p1 : h1 <+: l)
    (p2 : h2 <+: l) (hl : h1.getLast? = h2.getLast?) (h1n : h1 ≠ []) : h1 = h2 := by
  -- the two prefixes are comparable; the shorter one is a prefix of the longer
  have hc : h1 <+: h2 ∨ h2 <+: h1 := by
    rcases Nat.le_total h1.length h2.length with h | h
    · exact Or.inl (List.prefix_of_prefix_length_le p1 p2 h)
    · exact Or.inr (List.prefix_of_prefix_length_le p2 p1 h)
  have key : ∀ a b : List α, a <+: b → b <+: l → a ≠ [] → a.getLast? = b.getLast? → a = b := by
    intro a b hab hbl ha hlast
    obtain ⟨t, rfl⟩ := hab
    cases t with
    | nil => simp
    | cons y t =>
      exfalso
      obtain ⟨z, hz⟩ : ∃ z, a.getLast? = some z := by
        cases h : a.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h) ha
        | some z => exact ⟨z, rfl⟩
      have hb : (a ++ y :: t).getLast? = some z := by rw [← hlast, hz]
      have hnb : (a ++ y :: t).Nodup := hbl.sublist.nodup hn
      have hza : z ∈ a := List.mem_of_getLast? hz
      have hzt : z ∈ y :: t := by
        rw [List.getLast?_append, List.getLast?_cons] at hb
        simp at hb
        exact List.mem_of_getLast? (by rw [List.getLast?_cons, hb])
      rw [List.nodup_append] at hnb
      exact hnb.2.2 z hza z hzt rfl
  rcases hc with h | h
  · exact key h1 h2 h p2 h1n hl
  · have h2n : h2 ≠ [] := by
      intro he; rw [he] at hl; simp at hl; exact h1n hl
    exact (key h2 h1 h p1 h2n hl.symm).symm

theorem srvHist_prefix (γk : KVNames) (A B : List EntryModel) (h : A <+: B) :
    srvHist γk A <+: srvHist γk B := by
  obtain ⟨t, ht⟩ := admStates_prefix γk (auth.bump auth.bootState) A B h
  exact ⟨t, by simp [srvHist, ← ht]⟩

/-- **The step an appending admin request's cap permission is for** (H5): its step relation
(`AuthEnable`'s at the state's own flag, `auth.authEnableOwnR`); an `Authenticate` appends nothing. -/
def apply.AdminReq.capRel : apply.AdminReq → auth.StepRel
  | .userAdd n => auth.stepOf (auth.userAddF n)
  | .roleAdd n => auth.stepOf (auth.roleAddF n)
  | .userGrantRole u ro => auth.userGrantRoleR u ro
  | .roleGrantPermission n w => auth.roleGrantPermissionR n w
  | .authEnable => auth.authEnableOwnR
  | .authenticate _ _ => fun _ _ => False

/-- **A next state of a request's step is above it in order.** -/
theorem capRel_ord (ad : apply.AdminReq) (sa st' : auth.AuthState)
    (hR : ad.capRel sa (.next st')) : authOrd sa < authOrd st' := by
  cases ad with
  | userAdd n =>
    simp only [apply.AdminReq.capRel, auth.stepOf, auth.userAddF] at hR
    split at hR
    · cases hR
    · split at hR
      · cases hR
      · injection hR with hR; subst hR; exact authOrd_bump _ _ (by simp [auth.putUser])
  | roleAdd n =>
    simp only [apply.AdminReq.capRel, auth.stepOf, auth.roleAddF] at hR
    split at hR
    · cases hR
    · split at hR
      · cases hR
      · injection hR with hR; subst hR; exact authOrd_bump _ _ (by simp [auth.putRole])
  | userGrantRole u ro =>
    simp only [apply.AdminReq.capRel, auth.userGrantRoleR] at hR
    split at hR
    · cases hR
    · split at hR
      · cases hR
      · split at hR
        · cases hR
        · obtain ⟨u', -, -, hR⟩ := hR
          injection hR with hR; subst hR; exact authOrd_bump _ _ (by simp [auth.putUser])
  | roleGrantPermission n w =>
    simp only [apply.AdminReq.capRel, auth.roleGrantPermissionR] at hR
    split at hR
    · cases hR
    · split at hR
      · cases hR
      · split at hR
        · cases hR
        · injection hR with hR; subst hR; exact authOrd_bump _ _ (by simp [auth.putRole])
  | authEnable =>
    simp only [apply.AdminReq.capRel, auth.authEnableOwnR, auth.authEnableF] at hR
    split at hR
    · cases hR
    · rename_i hen
      split at hR
      · cases hR
      · split at hR
        · injection hR with hR; subst hR
          unfold authOrd
          simp only [Bool.not_eq_true] at hen
          simp [hen]
        · cases hR
  | authenticate n p => exact hR.elim

/-- **An admitted step of the request is the model's** (`adminStateR`). -/
theorem capRel_adminStateR (rq : apply.IRRModel) (ad : apply.AdminReq) (sa st' : auth.AuthState)
    (had : apply.adminReqOf rq = some ad)
    (hok : auth.adminOk sa (some (auth.authInfoM (apply.principalOf rq))))
    (hR : ad.capRel sa (.next st')) : adminStateR rq sa st' := by
  unfold adminStateR
  rw [if_pos hok]
  unfold apply.adminReqOf at had
  split at had
  all_goals rename_i hk
  all_goals simp only [hk]
  · cases hm : rq.authUserAdd with
    | none => simp [hm] at had
    | some mm =>
      simp only [hm, Option.map_some, Option.some.injEq] at had
      subst had
      exact Or.inr ⟨.next st', hR, rfl⟩
  · cases hm : rq.authRoleAdd with
    | none => simp [hm] at had
    | some n =>
      simp only [hm, Option.map_some, Option.some.injEq] at had
      subst had
      exact ⟨.next st', hR, rfl⟩
  · cases hm : rq.authUserGrantRole with
    | none => simp [hm] at had
    | some ur =>
      simp only [hm, Option.map_some, Option.some.injEq] at had
      subst had
      exact ⟨.next st', hR, rfl⟩
  · cases hm : rq.authRoleGrantPermission with
    | none => simp [hm] at had
    | some nw =>
      simp only [hm, Option.map_some, Option.some.injEq] at had
      subst had
      exact ⟨.next st', hR, rfl⟩
  · simp only [Option.some.injEq] at had
    subst had
    exact ⟨.next st', hR, rfl⟩
  · cases hm : rq.authenticate with
    | none => simp [hm] at had
    | some am =>
      simp only [hm, Option.map_some, Option.some.injEq] at had
      subst had
      exact hR.elim
  · cases had

/-- An `Authenticate` request model's admin request is of its kind. -/
theorem adminReqOf_authn (rq : apply.IRRModel) (n p : GoString)
    (h : apply.adminReqOf rq = some (.authenticate n p)) : apply.dispatchKind rq = .authenticate := by
  unfold apply.adminReqOf at h
  split at h <;> first | assumption | (simp at h) | (cases h) |
    (rename_i hk; revert h; cases rq.authUserAdd <;> cases rq.authRoleAdd <;>
      cases rq.authUserGrantRole <;> cases rq.authRoleGrantPermission <;> simp)

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `extraPre` of an appending request is its cap permission. -/
theorem extraPre_cap (E : apply.AEnv GF) (γa : auth.AuthNames) (hs : List auth.AuthState)
    (Pre : IProp GF) (ad : apply.AdminReq) (h : ∀ n p, ad ≠ .authenticate n p) :
    ad.extraPre E γa hs Pre = auth.capNextM (.on γa) hs ad.capRel := by
  cases ad with
  | authenticate n p => exact absurd rfl (h n p)
  | _ => rfl

theorem capAuth_lb_prefixW (γa : auth.AuthNames) (C C' : List auth.AuthState) :
    ⊢ auth.capAuth (GF := GF) γa C -∗ auth.capLb γa C' -∗ ⌜C' <+: C⌝ := by
  iintro H Hl
  iapply auth.capAuth_lb_prefix γa C C'
  isplitl [H]
  · iexact H
  · iexact Hl

/-- The admin step's cap permission, from the cap's lower bound at the history of `A ++ [m]` when
the store's history is `A`'s (`authHistTie_raise`'s last step). -/
theorem adminExtraG_of_capLb (E : apply.AEnv GF) (γr : ReadNames) (γa : auth.AuthNames)
    (A : List EntryModel) (m : EntryModel) (rq : apply.IRRModel) (hs : List auth.AuthState)
    (sa : auth.AuthState) (Pre : IProp GF) (hM : E.authMode = .on γa)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z γr.kv.c0 < uint.Z m.index) (hna : apply.needAdminPermission rq = true)
    (hk : apply.dispatchKind rq ≠ .authenticate)
    (hsa : srvAuthAtLog γr.kv (auth.bump auth.bootState) A = sa) (hdet : authDet rq sa)
    (hl : hs.getLast? = some sa) (hseq : hs = srvHist γr.kv A) :
    auth.capLb γa (srvHist γr.kv (A ++ [m])) ⊢ apply.adminExtraG E γa rq hs Pre := by
  unfold apply.adminExtraG
  iintro #Hcl %Hpass
  iunfold apply.adminExtra
  cases had : apply.adminReqOf rq with
  | none => itrivial
  | some ad =>
    have hna' : ∀ n p, ad ≠ .authenticate n p := by
      intro n p he; subst he; exact hk (adminReqOf_authn rq n p had)
    simp only []
    rw [extraPre_cap E γa hs Pre ad hna']
    unfold auth.capNextM
    iintro !> %st %st' %hh
    obtain ⟨hlast, hR⟩ := hh
    have hst : st = sa := by
      have : hs.getLast? = some st := hlast
      rw [hl] at this; exact (Option.some.inj this).symm
    subst hst
    have hok : auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) := by
      rw [hM] at Hpass; exact Hpass hna st hl
    have hR' := capRel_adminStateR rq ad st st' had hok hR
    have hord := capRel_ord ad st st' hR
    have hnext : adminNext rq st = st' := adminNext_of_det rq st st' hdet hR'
    have hne : adminNext rq st ≠ st := by
      rw [hnext]; intro h; rw [h] at hord; exact Nat.lt_irrefl _ hord
    have hadm : admEntry γr.kv.c0 (srvAuthAtLog γr.kv (auth.bump auth.bootState) A) m := by
      rw [hsa]; exact ⟨ht, hd, rq, hdec, hv, hna, hok, hne⟩
    have hH : srvHist γr.kv (A ++ [m]) = hs ++ [st'] := by
      unfold srvHist
      rw [admStates_snoc_adm _ _ _ _ hadm, srvAuthAtLog_snoc_adm _ _ _ _ rq ht hd hdec hv hna, hsa,
        hnext, hseq]
      rfl
    unfold auth.capNext
    rw [← hH]
    iexact Hcl

/-- **The apply thread raises the cap at an admin entry** (H5; see the file header): at the entry
`m` after the applied log `A`, whose auth state is `sa`, the latest of the store's history `hs`,
the cap's permission for the request's step (guarded by its check, `apply.adminExtraG`), the cap
raised to the history of `A ++ [m]` (the log `m` is committed in). -/
theorem authHistTie_raise (E : apply.AEnv GF) (γr : ReadNames) (γa : auth.AuthNames)
    (A : List EntryModel) (m : EntryModel) (rq : apply.IRRModel) (hs : List auth.AuthState)
    (sa : auth.AuthState) (Pre : IProp GF) (E' : CoPset) (hM : E.authMode = .on γa)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z γr.kv.c0 < uint.Z m.index) (hna : apply.needAdminPermission rq = true)
    (hk : apply.dispatchKind rq ≠ .authenticate)
    (hsa : srvAuthAtLog γr.kv (auth.bump auth.bootState) A = sa) (hdet : authDet rq sa)
    (hl : hs.getLast? = some sa) (hE1 : ↑authTieN ⊆ E') (hE2 : ↑(nroot.@"authRev") ⊆ E') :
    authHistTie E γr (auth.bump auth.bootState) ∗ srvRLogLb γr.raft (A ++ [m]) ∗
        auth.authOwn (.on γa) hs ={E'}=∗
      auth.authOwn (.on γa) hs ∗ apply.adminExtraG E γa rq hs Pre := by
  have hfin := adminExtraG_of_capLb (Pre := Pre) E γr γa A m rq hs sa hM ht hd hdec hv hna hk hsa
    hdet hl
  have hHA : srvHist γr.kv A <+: srvHist γr.kv (A ++ [m]) :=
    srvHist_prefix γr.kv A (A ++ [m]) (List.prefix_append A [m])
  have hne : hs ≠ [] := by intro he; rw [he] at hl; cases hl
  have hlast : hs.getLast? = (srvHist γr.kv A).getLast? := by rw [hl, srvHist_last, hsa]
  unfold authHistTie
  rw [hM]
  iintro ⟨⟨⟨%stl, %R, #Hinv⟩, #Htinv⟩, #Hlb, Ho⟩
  imod auth.authOwn_capped stl R γa hs E' hE2 $$ [Hinv Ho] with ⟨Ho, #Hhc⟩
  · iframe Hinv Ho
  iinv Htinv with Hi Hclose
  icases Hi with ⟨%A₀, >#HA₀, >Hcap⟩
  ihave Hcap : auth.capAuth γa (srvHist γr.kv A₀) $$ [Hcap]
  · simp only [srvHist]; iexact Hcap
  ihave %Hcmp := srvRLogLb_prefix γr.raft A₀ (A ++ [m]) $$ [HA₀ Hlb]
  · iframe HA₀ Hlb
  ihave %Hhs0 := capAuth_lb_prefixW γa _ hs $$ Hcap Hhc
  rcases Hcmp with h0 | h0
  · imod auth.capAuth_update γa (srvHist γr.kv (A ++ [m])) (srvHist_prefix γr.kv A₀ _ h0) $$ Hcap
      with Hcap
    ihave ⟨Hcap, #Hcl⟩ := auth.capAuth_lb γa _ $$ Hcap
    imod Hclose $$ [Hcap] with -
    · inext; iexists (A ++ [m]); iframe Hlb; unfold srvHist; iexact Hcap
    imodintro
    iframe Ho
    have hseq : hs = srvHist γr.kv A :=
      prefix_eq_of_last _ hs _ (srvHist_nodup γr.kv (A ++ [m]))
        ((by exact Hhs0 : hs <+: srvHist γr.kv A₀).trans (srvHist_prefix γr.kv A₀ _ h0)) hHA
        hlast hne
    iapply (hfin hseq) $$ Hcl
  · ihave ⟨Hcap, #Hcl0⟩ := auth.capAuth_lb γa _ $$ Hcap
    imod Hclose $$ [Hcap] with -
    · inext; iexists A₀; iframe HA₀; simp only [srvHist]; iexact Hcap
    imodintro
    iframe Ho
    have hseq : hs = srvHist γr.kv A :=
      prefix_eq_of_last _ hs _ (srvHist_nodup γr.kv A₀) Hhs0
        (hHA.trans (srvHist_prefix γr.kv _ A₀ h0)) hlast hne
    iapply (hfin hseq)
    iapply (auth.capLb_le γa (srvHist γr.kv (A ++ [m])) (srvHist_prefix γr.kv _ A₀ h0)) $$ Hcl0

end ghost

end EtcdGrove
end Perennial
