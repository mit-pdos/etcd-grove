/-
**The checks' reads become the mode's verdicts** (the auth plan's S3, 2026-10-23): what
`isOpPermitted` and `IsAdminPermitted` read -- the enabled flag (`enabledVerdict`), the revision
(`revisionVerdict`), the user of the backend's read transaction (`authSnap`, `userOut`) and the
permission cache's answer (`cacheVerdict`) -- gives `permVerdict`, resp. `adminVerdict`, in every
mode, one lemma per branch of the Go function (`store.go`). In `off` the flag is false, so the
checks pass at their first step (a flag `true` is absurd); in `any` the verdicts are trivial; in
`on γa` the recorded states of the reads are the verdict's states (`Model.lean`: `permitted` of
one state, the revision of another, `refusedV` of the view).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The user read -/

/-- `UnsafeGetUser(name)` returned `nil`: the state has no such user. -/
theorem userOut_null (st : AuthState) (name : GoString) :
    userOut (GF := GF) null st name ⊢ ⌜st.users !! name = none⌝ := by
  unfold userOut
  cases h : st.users !! name with
  | none => iintro -; ipureintro; rfl
  | some roles =>
    iintro ⟨%ur, -, Hu⟩
    iunfold ownUser at Hu
    icases Hu with ⟨%s1, %n, %pw, %rl, %o, %uf, %sc, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hp
    exact absurd rfl Hnn

/-- `UnsafeGetUser(name)` returned a message: the state's user, as a record of sorted roles. -/
theorem userOut_some (u : Loc) (st : AuthState) (name : GoString) (hnn : u ≠ null) :
    userOut (GF := GF) u st name ⊢ ∃ (roles : User) (ur : UserRec),
      ⌜st.users !! name = some roles ∧ ur.roles = roles ∧ roles.Pairwise go.GoStringLt⌝ ∗
      ownUser u ur := by
  unfold userOut
  cases h : st.users !! name with
  | none => iintro %Hn; exact absurd Hn hnn
  | some roles =>
    iintro ⟨%ur, %Hur, Hu⟩
    iexists roles, ur
    iframe Hu
    ipureintro; exact ⟨rfl, Hur.2.1, Hur.2.2⟩

/-! ## The permission types the callers pass -/

theorem permVerdict_permOp_read (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (err : GoInterface) :
    permVerdict (GF := GF) M info key rangeEnd (permOp (W32 0)) err ⊢
      permVerdict M info key rangeEnd .read err := by
  have h : permOp (W32 0) = .read := by simp [permOp]
  rw [h]

theorem permVerdict_permOp_write (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (err : GoInterface) :
    permVerdict (GF := GF) M info key rangeEnd (permOp (W32 1)) err ⊢
      permVerdict M info key rangeEnd .write err := by
  have h : permOp (W32 1) = .write := by simp [permOp]
  rw [h]

/-! ## `isOpPermitted` -/

/-- `!as.IsAuthEnabled()`: the check passes. -/
theorem permVerdict_of_disabled (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) :
    enabledVerdict (GF := GF) M false ⊢ permVerdict M info key rangeEnd op GoInterface.nil := by
  cases M with
  | off => unfold permVerdict; iintro -; ipureintro; rfl
  | any => unfold permVerdict; iintro -; itrivial
  | on γa =>
    unfold enabledVerdict permVerdict
    iintro ⟨%i, %st, #Hst, %Hb⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; intro _; unfold permitted; left; exact Hb.symm
    isplitr
    · iexists i, st; iframe #; ipureintro; intro _; left; exact Hb.symm
    · iexists ⟨st, st, st, st⟩
      isplitr
      · iapply recordedV_diag γa i st $$ Hst
      · ipureintro; intro h; exact absurd rfl h

/-- `revision == 0`: `ErrUserEmpty`. -/
theorem permVerdict_rev0 (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) (herr : err ≠ GoInterface.nil)
    (h0 : uint.nat info.Revision' = 0) :
    enabledVerdict (GF := GF) M true ⊢ permVerdict M info key rangeEnd op err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H; cases H
  | any => unfold permVerdict; iintro -; itrivial
  | on γa =>
    unfold enabledVerdict permVerdict
    iintro ⟨%i, %st, #Hst, %Hb⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; intro h; exact absurd h herr
    isplitr
    · iexists i, st; iframe #; ipureintro; intro h; exact absurd h herr
    · iexists ⟨st, st, st, st⟩
      isplitr
      · iapply recordedV_diag γa i st $$ Hst
      · ipureintro; intro _; unfold refusedV; exact ⟨Hb.symm, Or.inl h0⟩

/-- `revision < rev`: `ErrAuthOldRevision`. -/
theorem permVerdict_oldRev (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) (cur : w64) (herr : err ≠ GoInterface.nil)
    (hlt : uint.nat info.Revision' < uint.nat cur) :
    enabledVerdict (GF := GF) M true ⊢ revisionVerdict M cur -∗
      permVerdict M info key rangeEnd op err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H -; cases H
  | any => unfold permVerdict; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdict revisionVerdict permVerdict
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, %sr, #Hsr, %Hr⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h; exact absurd h herr
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h; exact absurd h herr
    · iexists ⟨sf, sr, sf, sf⟩
      isplitr
      · iapply (recordedV_intro γa i j i i sf sr sf sf) $$ Hsf Hsr Hsf Hsf
      · ipureintro; intro _; unfold refusedV
        exact ⟨Hb.symm, Or.inr (Or.inl (Nat.lt_of_lt_of_eq hlt Hr))⟩

/-- `tx.UnsafeGetUser(userName) == nil`: `ErrPermissionDenied`. -/
theorem permVerdict_noUser (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (err : GoInterface) (sta : AuthState) (herr : err ≠ GoInterface.nil)
    (hu : sta.users !! info.Username' = none) :
    enabledVerdict (GF := GF) M true ⊢ authSnap M sta -∗
      permVerdict M info key rangeEnd op err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H -; cases H
  | any => unfold permVerdict; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdict authSnap permVerdict
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h; exact absurd h herr
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h; exact absurd h herr
    · iexists ⟨sf, sf, sta, sf⟩
      isplitr
      · iapply (recordedV_intro γa i i j i sf sf sta sf) $$ Hsf Hsf Hsu Hsf
      · ipureintro; intro _; unfold refusedV
        refine ⟨Hb.symm, Or.inr (Or.inr fun u hu' => ?_)⟩
        have hu'' : sta.users !! info.Username' = some u := hu'
        rw [hu] at hu''; cases hu''

/-- `hasRootRole(user)`: the check passes. -/
theorem permVerdict_root (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (op : PermType) (cur : w64) (sta : AuthState) (roles : User)
    (h0 : uint.nat info.Revision' ≠ 0) (hcur : uint.nat cur ≤ uint.nat info.Revision')
    (hu : sta.users !! info.Username' = some roles) (hroot : isRoot roles) :
    revisionVerdict (GF := GF) M cur ⊢ authSnap M sta -∗
      permVerdict M info key rangeEnd op GoInterface.nil := by
  cases M with
  | off => unfold permVerdict; iintro - -; ipureintro; rfl
  | any => unfold permVerdict; iintro - -; itrivial
  | on γa =>
    unfold revisionVerdict authSnap permVerdict
    iintro ⟨%j, %sr, #Hsr, %Hr⟩ ⟨%i, #Hsu⟩
    isplitr
    · iexists i, sta; iframe #; ipureintro; intro _; unfold permitted granted
      exact Or.inr ⟨h0, roles, hu, Or.inl hroot⟩
    isplitr
    · iexists j, sr; iframe #; ipureintro; intro _; right; rw [← Hr]; exact hcur
    · iexists ⟨sta, sta, sta, sta⟩
      isplitr
      · iapply recordedV_diag γa i sta $$ Hsu
      · ipureintro; intro h; exact absurd rfl h

/-- `as.isRangeOpPermitted(...)` true: the check passes. -/
theorem permVerdict_cache_pass (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (cur : w64) (sta : AuthState)
    (roles : User) (h0 : uint.nat info.Revision' ≠ 0) (hcur : uint.nat cur ≤ uint.nat info.Revision')
    (hu : sta.users !! info.Username' = some roles) :
    revisionVerdict (GF := GF) M cur ⊢ authSnap M sta -∗
      cacheVerdict M info.Username' key rangeEnd pt true -∗
      permVerdict M info key rangeEnd (permOp pt) GoInterface.nil := by
  cases M with
  | off => unfold permVerdict; iintro - - -; ipureintro; rfl
  | any => unfold permVerdict; iintro - - -; itrivial
  | on γa =>
    unfold revisionVerdict authSnap cacheVerdict permVerdict
    iintro ⟨%j, %sr, #Hsr, %Hr⟩ ⟨%i, #Hsu⟩ ⟨%k, %sc, #Hsc, %Hc⟩
    ihave %Hk := authStateAt_permKeysOk γa k sc $$ Hsc
    isplitr
    · by_cases hs : reqShape key rangeEnd
      · iexists k, sc; iframe #; ipureintro; intro _
        obtain ⟨roles', hu', hcov⟩ := (Hc hs.1 hs.2 Hk).1 rfl
        unfold permitted granted
        exact Or.inr ⟨h0, roles', hu', Or.inr fun _ => hcov⟩
      · iexists i, sta; iframe #; ipureintro; intro _
        unfold permitted granted
        exact Or.inr ⟨h0, roles, hu, Or.inr fun h => absurd h hs⟩
    isplitr
    · iexists j, sr; iframe #; ipureintro; intro _; right; rw [← Hr]; exact hcur
    · iexists ⟨sta, sta, sta, sta⟩
      isplitr
      · iapply recordedV_diag γa i sta $$ Hsu
      · ipureintro; intro h; exact absurd rfl h

/-- Not root, and `as.isRangeOpPermitted(...)` false: `ErrPermissionDenied`. -/
theorem permVerdict_cache_refused (M : AuthMode) (info : AuthInfo) (key rangeEnd : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (err : GoInterface) (sta : AuthState)
    (roles : User) (herr : err ≠ GoInterface.nil)
    (hu : sta.users !! info.Username' = some roles) (hnroot : ¬ isRoot roles) :
    enabledVerdict (GF := GF) M true ⊢ authSnap M sta -∗
      cacheVerdict M info.Username' key rangeEnd pt false -∗
      permVerdict M info key rangeEnd (permOp pt) err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H - -; cases H
  | any => unfold permVerdict; iintro - - -; itrivial
  | on γa =>
    unfold enabledVerdict authSnap cacheVerdict permVerdict
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu⟩ ⟨%k, %sc, #Hsc, %Hc⟩
    ihave %Hk := authStateAt_permKeysOk γa k sc $$ Hsc
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h; exact absurd h herr
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h; exact absurd h herr
    · iexists ⟨sf, sf, sta, sc⟩
      isplitr
      · iapply (recordedV_intro γa i i j k sf sf sta sc) $$ Hsf Hsf Hsu Hsc
      · ipureintro; intro _; unfold refusedV
        refine ⟨Hb.symm, Or.inr (Or.inr fun u hu' => ?_)⟩
        have hu'' : sta.users !! info.Username' = some u := hu'
        rw [hu] at hu''; cases hu''
        refine ⟨hnroot, fun hs u' hu2 hcov => ?_⟩
        have hu2' : sc.users !! info.Username' = some u' := hu2
        have hf := (Hc hs.1 hs.2 Hk).2 ⟨u', hu2', hcov⟩
        cases hf

/-! ## `IsAdminPermitted` -/

/-- `!as.IsAuthEnabled()`: the check passes. -/
theorem adminVerdict_of_disabled (M : AuthMode) (ai : Option AuthInfo) :
    enabledVerdict (GF := GF) M false ⊢ adminVerdict M ai GoInterface.nil := by
  cases M with
  | off => unfold adminVerdict; iintro -; ipureintro; rfl
  | any => unfold adminVerdict; iintro -; itrivial
  | on γa =>
    unfold enabledVerdict adminVerdict
    iintro ⟨%i, %st, #Hst, %Hb⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; intro _; unfold adminOk; left; exact Hb.symm
    · iexists i, i, st, st; iframe #; ipureintro; intro h; exact absurd rfl h

/-- `authInfo == nil || authInfo.Username == ""`: `ErrUserEmpty`. -/
theorem adminVerdict_noPrincipal (M : AuthMode) (ai : Option AuthInfo) (err : GoInterface)
    (herr : err ≠ GoInterface.nil) (h : ∀ info, ai = some info → info.Username' = []) :
    enabledVerdict (GF := GF) M true ⊢ adminVerdict M ai err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H; cases H
  | any => unfold adminVerdict; iintro -; itrivial
  | on γa =>
    unfold enabledVerdict adminVerdict
    iintro ⟨%i, %st, #Hst, %Hb⟩
    isplitr
    · iexists i, st; iframe #; ipureintro; intro h'; exact absurd h' herr
    · iexists i, i, st, st; iframe #; ipureintro; intro _; unfold adminRefused
      refine ⟨Hb.symm, fun a u ha hname _ => ?_⟩
      cases ai with
      | none => cases ha
      | some info =>
        simp only [Option.map_some] at ha
        cases ha
        exact absurd (h info rfl) hname

/-- `tx.UnsafeGetUser(authInfo.Username) == nil`: `ErrUserNotFound`. -/
theorem adminVerdict_noUser (M : AuthMode) (info : AuthInfo) (err : GoInterface)
    (sta : AuthState) (herr : err ≠ GoInterface.nil)
    (hu : sta.users !! info.Username' = none) :
    enabledVerdict (GF := GF) M true ⊢ authSnap M sta -∗ adminVerdict M (some info) err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H -; cases H
  | any => unfold adminVerdict; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdict authSnap adminVerdict
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h'; exact absurd h' herr
    · iexists i, j, sf, sta; iframe #; ipureintro; intro _; unfold adminRefused
      refine ⟨Hb.symm, fun a u ha _ hu' => ?_⟩
      simp only [Option.map_some] at ha
      cases ha
      have hu'' : sta.users !! info.Username' = some u := hu'
      rw [hu] at hu''; cases hu''

/-- `!hasRootRole(u)`: `ErrPermissionDenied`. -/
theorem adminVerdict_notRoot (M : AuthMode) (info : AuthInfo) (err : GoInterface)
    (sta : AuthState) (roles : User) (herr : err ≠ GoInterface.nil)
    (hu : sta.users !! info.Username' = some roles) (hn : ¬ isRoot roles) :
    enabledVerdict (GF := GF) M true ⊢ authSnap M sta -∗ adminVerdict M (some info) err := by
  cases M with
  | off => unfold enabledVerdict; iintro %H -; cases H
  | any => unfold adminVerdict; iintro - -; itrivial
  | on γa =>
    unfold enabledVerdict authSnap adminVerdict
    iintro ⟨%i, %sf, #Hsf, %Hb⟩ ⟨%j, #Hsu⟩
    isplitr
    · iexists i, sf; iframe #; ipureintro; intro h'; exact absurd h' herr
    · iexists i, j, sf, sta; iframe #; ipureintro; intro _; unfold adminRefused
      refine ⟨Hb.symm, fun a u ha _ hu' => ?_⟩
      simp only [Option.map_some] at ha
      cases ha
      have hu'' : sta.users !! info.Username' = some u := hu'
      rw [hu] at hu''; cases hu''
      exact hn

/-- A named user with the root role: the check passes. -/
theorem adminVerdict_root (M : AuthMode) (info : AuthInfo) (sta : AuthState) (roles : User)
    (hname : info.Username' ≠ []) (hu : sta.users !! info.Username' = some roles)
    (hroot : isRoot roles) :
    authSnap (GF := GF) M sta ⊢ adminVerdict M (some info) GoInterface.nil := by
  cases M with
  | off => unfold adminVerdict; iintro -; ipureintro; rfl
  | any => unfold adminVerdict; iintro -; itrivial
  | on γa =>
    unfold authSnap adminVerdict
    iintro ⟨%i, #Hsu⟩
    isplitr
    · iexists i, sta; iframe #; ipureintro; intro _; unfold adminOk
      exact Or.inr ⟨authInfoM info, roles, rfl, hname, hu, hroot⟩
    · iexists i, i, sta, sta; iframe #; ipureintro; intro h; exact absurd rfl h

end lemmas

end auth
end EtcdGrove
end Perennial
