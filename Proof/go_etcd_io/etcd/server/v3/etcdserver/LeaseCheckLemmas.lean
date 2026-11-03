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
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hreqb, #Hcca, -⟩
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

end proof

end EtcdGrove
end Perennial
