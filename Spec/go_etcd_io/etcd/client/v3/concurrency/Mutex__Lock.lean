/-
`concurrency.Mutex.Lock(ctx)` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
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

/-- **`m.Lock(ctx)`**, from any state, for a cancelable context (`waitDelete`'s `WithCancel`
takes one: Perennial's `wp_WithCancel`), knowing etcd has reached `lo`:
* `nil`: at a revision `R ≥ lo` (the header `hdr` the mutex keeps), the mutex's key `key` (under
  the prefix), created at `rev`, holds the lock (`lockedAt pfx key rev R`) — **or** `key` was
  deleted and re-created since `rev` (`keyRecreated`): `Lock`'s last check only asks that `key`
  exist, so another `Mutex` of the same session on the same prefix (which shares the key)
  unlocking and locking again in between makes `Lock` return `nil` without the lock (see
  `notes/STATUS.md`, "Mutex: mutual exclusion");
* `ErrSessionExpired`: the key is absent at some `R ≥ lo`;
* any other error, in some state (the mutex may have deleted its key, `Unlock`). -/
abbrev Mutex.Lock.spec : Prop :=
  ∀ (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : MutexSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s γ client id pfx ∗ mutexState m st ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Lock")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (rev R : w64) (hdr : Loc),
        mutexState m ⟨key, rev, hdr⟩ ∗ hdrRevAt hdr R ∗ etcdReached R ∗
        (lockedAt pfx key rev R ∨ keyRecreated pfx key rev R) ∗
        ⌜pfx <+: key ∧ sint.Z lo ≤ sint.Z R⌝) ∨
      (isPkgErr ErrSessionExpired err ∗ ∃ (st' : MutexSt) (R : w64), mutexState m st' ∗
        etcdReached R ∗ etcdAbsent pfx st'.key R ∗ ⌜pfx <+: st'.key ∧ sint.Z lo ≤ sint.Z R⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ st' : MutexSt, mutexState m st') }}

end spec

end concurrency
end EtcdGrove
end Perennial
