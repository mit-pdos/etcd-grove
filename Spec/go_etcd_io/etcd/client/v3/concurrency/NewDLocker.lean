/-
`concurrency.NewDLocker(s, pfx)` (`client/v3/concurrency/mutex.go`, etcd#18779). Lean-first (no Rocq
counterpart); see `InvMutex.lean`.
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

/-- **`NewDLocker(s, pfx)`**: `NewLocker`'s result (`NewLocker.spec`), as a `DLocker`: the same
`lockerMutex` wrapping a new mutex on `pfx + "/"`, so `Lock`/`Unlock` are `lockerMutex.Lock.spec`/
`Unlock.spec` (panic on any error) and `Rev` is `lockerMutex.Rev.spec`. The interface value's
dynamic type is `*lockerMutex` (the conversion to `DLocker` keeps it). -/
abbrev NewDLocker.spec : Prop :=
  ∀ (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s γ client id ∗
      isEtcdMutexClient client (pfx ++ go!"/") }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewDLocker)) (Val #s)) (Val #pfx))
  {{ (l : GoInterface), RET #l; ∃ (lm m : Loc),
      ⌜l = interface.mkOk (go.GoType.PointerType lockerMutex.ty) #lm⌝ ∗
      structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗
      isMutex m s γ client id (pfx ++ go!"/") ∗ mutexState m MutexSt.init }}

end spec

end concurrency
end EtcdGrove
end Perennial
