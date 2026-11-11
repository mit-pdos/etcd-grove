/-
**The lease API's key checks: what their proofs share** (the lease-keys plan, Part B, 2026-10-31;
`notes/lease-keys-plan.md`). Lean-first (no Rocq counterpart).

- `leaseCheckSetup`: the server's auth store with the checks' methods at the caller's lower bound
  `n` (`srvAuthAt`, `srvAuthLeaseLb` and `authPubLbM` together).
- `leaseCheckErrs`: the two errors the checks return of their own, `auth.ErrUserEmpty` and
  `auth.ErrAuthOldRevision`, with their `applyErrIs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server's auth store, for the lease checks**: its field, the request path's auth
(`AuthInfoFromCtx`'s premises) and the checks' methods no older than `n`. -/
theorem leaseCheckSetup (s : Loc) (E : apply.AEnv GF) (n : Nat) :
    srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ auth.authPubLbM E.authMode n ⊢
      ∃ (st : GoInterface) (cca : Bool), srvAuthStoreAddr s ↦□ st ∗ isReqAuth st E.RD ∗
        □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound st E.RD E.authMode) ∗
        srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗
        isAuthStoreLeaseLb st E.RD E.authMode n := by
  iintro ⟨#Hau, #Hlb, #Hpub⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, #Has, #Hreq, #Hreqb, #Hcca, -⟩
  iunfold srvAuthLeaseLb at Hlb
  icases Hlb with ⟨%au, #Has2, #Hall⟩
  icombine Has Has2 gives %Heq
  subst Heq
  iexists st, cca
  iframe Has Hreq Hreqb Hcca
  iapply Hall $$ Hpub

/-- **The checks' own errors**: `auth.ErrUserEmpty` and `auth.ErrAuthOldRevision`, `errors.New`
errors (the auth package's facts). -/
theorem leaseCheckErrs [_root_.Perennial.errors.Assumptions]
    [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.auth.ErrUserEmpty ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e)) ∗
      (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e)) := by
  iintro #Hpkg
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HUE, -, -, #HOR, -⟩
  iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HUE HOR
  isplitl
  · iapply errVarLeaf_get
    iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HUE
  · iapply errVarLeaf_get
    iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HOR

/-- **A leaf's walk** (pure): an error that is not `target`, whose `Is` answers `false` and which
unwraps to nothing, under exact relations, does not answer `true`. -/
theorem isWalk_leaf_not_true {I : GoInterfaceOk → Bool → Prop}
    {U : GoInterfaceOk → List GoInterface → Prop} {target : GoInterface} {ii : GoInterfaceOk}
    (hex : exactRels I U) (hI : I ii false) (hU : U ii []) (hne : GoInterface.ok ii ≠ target) :
    ¬ _root_.Perennial.errors.IsWalk true I U target (GoInterface.ok ii) true := by
  intro h
  cases h with
  | eq _ heq => exact hne heq
  | is _ hI' => exact absurd (hex.1 _ _ _ hI hI') (by decide)
  | hit _ _ hU' hcs => rw [hex.2 _ _ _ hU' hU] at hcs; cases hcs
  | miss _ _ _ _ hes => cases hes

/-- A leaf error's node of a walk tree: its `Is` answers `false`, its `Unwrap` nothing. -/
theorem errorWalkNode_leaf (S : GoInterface → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoInterface → Prop) (target : GoInterface) (ii : GoInterfaceOk)
    (hl : errLeaf ii) :
    _root_.Perennial.errors.errorWalkNode (GF := GF) S I U target ii ⊢ ⌜I ii false ∧ U ii []⌝ := by
  obtain ⟨-, ⟨-, hU1, hU2⟩, hIs⟩ := hl
  unfold _root_.Perennial.errors.errorWalkNode
  simp only [hIs, hU1, hU2, ↓reduceIte]
  iintro ⟨%h1, %h2⟩
  ipureintro; exact ⟨h1, h2⟩

/-- **`errors.Is` of a leaf error and another error is false** (`errIsTrue` refuted): Go's
`errors.New` errors are leaves (`errLeaf`), so the walk answers `true` only at the target itself. -/
theorem errIsTrue_leaf_ne (e1 e : GoInterfaceOk) (hl : errLeaf e1) (hne : e1 ≠ e) :
    errIsTrue (GF := GF) (GoInterface.ok e1) (GoInterface.ok e) ⊢ False := by
  iunfold errIsTrue
  iintro ⟨%S, %I, %U, #Ht, %H⟩
  obtain ⟨hS, hex, hw⟩ := H
  ihave Hn := Ht $$ %e1 %hS
  ihave %hIU := errorWalkNode_leaf S I U _ e1 hl $$ Hn
  exfalso
  exact isWalk_leaf_not_true hex hIU.1 hIU.2 (fun h => hne (GoInterface.ok.inj h)) hw

/-- `errors.Is(nil, target)` is false for a non-nil target. -/
theorem errIsTrue_nil (e : GoInterfaceOk) :
    errIsTrue (GF := GF) GoInterface.nil (GoInterface.ok e) ⊢ False := by
  iunfold errIsTrue
  iintro ⟨%S, %I, %U, -, %H⟩
  obtain ⟨-, -, hw⟩ := H
  exfalso
  cases hw with
  | nilSkip _ h => cases h

/-- **An auth package error is not `lease.ErrLeaseNotFound`, as `errors.Is` sees it** (the
lease-expiry plan's E3): `nil` or one of the auth package's error variables (`authErrVarIs`), a leaf
holding an error other than `ErrLeaseNotFound`'s (the variables' message cells: "lease not found" is
none of the auth package's messages). -/
theorem authErrVarIs_not_leaseNotFound (err : GoInterface) (e : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ authErrVarIs err ∗
      globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e ∗
      errIsTrue err (GoInterface.ok e) ⊢ False := by
  iintro ⟨#Hap, #Hlp, #Hv, #He, Hi⟩
  iunfold authErrVarIs at Hv
  icases Hv with (%Hnil | ⟨%g, %e1, %Hg, #Hge, %He1⟩)
  · subst Hnil; iapply errIsTrue_nil e $$ Hi
  subst He1
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hap
  icases Hai with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #AUC⟩
  ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hlp
  icases Hli with ⟨-, -, -, -, -, -, -, #CLNF, -⟩
  ihave #Hall := EtcdGrove.errVarApart_cells go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound
    go!"lease not found" go_etcd_io.etcd.server.v3.auth.authErrMsgs
    (go_etcd_io.etcd.server.v3.auth.authErrMsgs_ne_of _ (by decide)) $$ CLNF AUC
  ihave #Hap2 := Hall $$ %g %Hg.1
  iunfold errVarApart at Hap2
  icases Hap2 with ⟨%e2, %e3, #H2, #H3, %Hne⟩
  icombine He H2 gives %h2
  icombine Hge H3 gives %h3
  cases h2; cases h3
  iapply errIsTrue_leaf_ne e1 e Hg.2 (fun h => Hne h.symm) $$ Hi

/-- `authErrVarIs_not_leaseNotFound` as the lease rows' not-found clause takes it: anything follows
from `errors.Is(err, ErrLeaseNotFound)` of an auth package error. -/
theorem authErrVarIs_leaseNotFound_absurd (err : GoInterface) (P : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ authErrVarIs err ⊢
      □ (∀ e : GoInterfaceOk,
        globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e -∗
        errIsTrue err (GoInterface.ok e) -∗ P) := by
  iintro ⟨#Hap, #Hlp, #Hv⟩ !> %e #He Hi
  iexfalso
  iapply authErrVarIs_not_leaseNotFound err e $$ [$Hap $Hlp $Hv $He $Hi]

open Iris.ProofMode in
/-- `IsAuthEnabled` answers `true` (from an index) only in a mode that may refuse (the lease-grant
plan's (F3): the lease checks fail only with auth on). -/
theorem enabledVerdictFrom_true_isOn (M : auth.AuthMode) (n : Nat) :
    auth.enabledVerdictFrom (GF := GF) M n true ⊢ ⌜M.isOn = true⌝ := by
  cases M
  · unfold auth.enabledVerdictFrom; iintro %H; cases H
  · iintro -; ipureintro; rfl
  · iintro -; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
