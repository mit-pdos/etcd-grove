/-
`concurrency.Mutex.tryAcquire(ctx)` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
`InvMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`m.tryAcquire(ctx)`**, from any state, knowing etcd has reached `lo`: `myKey` becomes a key
under the prefix (`fmt.Sprintf("%s%x", pfx, lease)`); then the transaction (`acquireTxn`): an
error (with `myKey` written), or a response at a revision `r ≥ lo` (`acquireResp`: etcd's state at
`r` has `myKey` with create revision `myRev`, and `Responses[1]` lists the first-created key under
the prefix in that state), `myRev` being the response's revision if the key was created, its
create revision otherwise. -/
abbrev Mutex.tryAcquire.spec : Prop :=
  ∀ (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : MutexSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s γ client id pfx ∗ mutexState m st ∗
      context.isContext ctx cs ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"tryAcquire")) (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ key : GoString, mutexState m { st with key := key }) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (rev r : w64) (hdr : Loc),
        mutexState m { st with key := key, rev := rev } ∗ etcdReached r ∗
        acquireResp resp pfx key rev r hdr ∗
        ⌜pfx <+: key ∧ sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z rev ∧ sint.Z rev ≤ sint.Z r ∧
          sint.Z r < 2 ^ 63 - 1⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
