/-
**The auth store's methods the lease checks call, no older than a reader's lower bound** (moved from
`LeaseCheck.lean` by the lease-src plan, 2026-11-02, `notes/lease-src-plan.md`, so that the auth
store's construction can state them: `authStoreLbM`, `StoreLatest.lean`). Lean-first (no Rocq
counterpart).

- `adminVerdictFrom M n info err`: `IsAdminPermitted`'s verdict no older than `n` (the auth
  package's `auth.adminVerdictFrom`).
- `permCheck2Lb`: `IsPutPermitted`'s at a lower bound (`permCheck3Lb`'s two-argument twin).
- `isAuthStoreLeaseLb st RD M n` (persistent): `IsAuthEnabled`, `Revision`, `IsAdminPermitted`,
  `IsPutPermitted`, `IsRangePermitted`, each at states no older than `n`;
  `isAuthStoreLeaseLb_of_authInv`: the real store's, of its invariant, from the five `specLb`s.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb
public import Proof.go_etcd_io.etcd.server.v3.auth.FreshAdmin

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`IsAdminPermitted`'s verdict no older than the index `n`** in the mode `M` (persistent): the auth
package's (`auth.adminVerdictFrom`, `IsAdminPermitted.specLb`'s; this definition's own body until the
lease-src plan, 2026-11-02): in `on γa`, a passed check's principal an admin at a state recorded at an
index at least `n`; with auth off, a pass. -/
def adminVerdictFrom (M : auth.AuthMode) (n : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (err : GoInterface) : IProp GF :=
  auth.adminVerdictFrom M n info err

instance adminVerdictFrom_persistent (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (err : GoInterface) :
    Persistent (adminVerdictFrom (GF := GF) M n info err) := by
  unfold adminVerdictFrom; infer_instance

/-- **`permCheck2` no older than a lower bound**: `IsPutPermitted(authInfo, key)`'s verdict at states
no older than `n`, for a caller with the reader resource `RD`. -/
def permCheck2Lb (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode) (n : Nat)
    (op : auth.PermType) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ authApplyErrIs err ∗
        auth.permVerdictFrom M n info k [] op err }}))

/-- **The auth store's methods the lease checks call, no older than a reader's lower bound `n`**
(persistent): `IsAuthEnabled`, `Revision` and `IsAdminPermitted` with their verdicts at states no
older than `n`, and the permission checks `IsPutPermitted` and `IsRangePermitted` at such states. -/
def isAuthStoreLeaseLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (n : Nat) :
    IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
        {{ (b : Bool), RET #b; RD ∗ auth.enabledVerdictFrom M n b }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"Revision" ai.v)) (Val #()))
        {{ (x : w64), RET #x; auth.revisionVerdictFrom M n x }}) ∗
    □ (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
      {{ a ↦{dq} info ∗ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
      {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
          adminVerdictFrom M n info err }}) ∗
    permCheck2Lb ai go!"IsPutPermitted" RD M n .write ∗
    apply.permCheck3Lb ai go!"IsRangePermitted" RD M n .read)

instance isAuthStoreLeaseLb_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (n : Nat) : Persistent (isAuthStoreLeaseLb st RD M n) := by
  unfold isAuthStoreLeaseLb permCheck2Lb apply.permCheck3Lb; infer_instance

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The real store's lease checks at a lower bound, of its invariant** (as
`apply.isAuthStoreRangeLb_of_authInv`, from the five methods' `specLb`s). -/
theorem isAuthStoreLeaseLb_of_authInv
    (hEn : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (hRev : auth.authStore.Revision.specLb (GF := GF))
    (hAdmin : auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.specLb (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.specLb (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ∗
      auth.authPubLbM M n ⊢
      isAuthStoreLeaseLb (auth.authIface st) (auth.authRd st R M) M n := by
  sorry

end proofs

end EtcdGrove
end Perennial
