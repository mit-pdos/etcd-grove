/-
`concurrency.NewLocker(s, pfx)` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`NewLocker(s, pfx)`**: a `sync.Locker` wrapping (`lockerMutex`) a new mutex on `pfx + "/"`
(`NewMutex`). Its `Lock` and `Unlock` panic on any error of `Mutex.Lock`/`Unlock`, which every
client call allows (`lockerMutex.Lock.spec`, `lockerMutex.Unlock.spec`: a panic outcome). -/
abbrev NewLocker.spec : Prop :=
  ∀ (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s γ client id ∗
      isEtcdMutexClient client (pfx ++ go!"/") }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewLocker)) (Val #s)) (Val #pfx))
  {{ (l : GoInterface), RET #l; ∃ (lm m : Loc),
      ⌜l = interface.mkOk (go.GoType.PointerType lockerMutex.ty) #lm⌝ ∗
      structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗
      isMutex m s γ client id (pfx ++ go!"/") ∗ mutexState m MutexSt.init }}

end spec

end concurrency
end EtcdGrove
end Perennial
