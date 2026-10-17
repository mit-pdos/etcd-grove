/-
`concurrency.Mutex.Rev()` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`m.Rev()`** (etcd#18779): `myRev`, the create revision of the key the mutex last acquired
or tried to acquire (`-1` before any, and after `Unlock` or `TryLock`'s `ErrLocked`). After `Lock`
or `TryLock` returns `nil`, it is the create revision `rev` of their ownership fact (`lockedAt` or
`keyRecreated`), the fencing token of `lockFloor_later` (`InvMutex.lean`). Not synchronized: the
caller owns `mutexState`, as for every `Mutex` method. After an error of `Lock` (`ErrSessionExpired`,
a failed transaction) it can be a positive, stale create revision of a key the mutex does not hold
(`Mutex.Lock.spec`'s `∃ st'`). -/
abbrev Mutex.Rev.spec : Prop :=
  ∀ (m : Loc) (st : MutexSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ mutexState m st }}
    (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Rev")) (Val #()))
  {{ RET #st.rev; mutexState m st }}

end spec

end concurrency
end EtcdGrove
end Perennial
