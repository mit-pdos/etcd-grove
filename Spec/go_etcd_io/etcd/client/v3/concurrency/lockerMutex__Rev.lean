/-
`concurrency.lockerMutex.Rev()` (`client/v3/concurrency/mutex.go`, etcd#18779): the method
`Rev` of `*lockerMutex` promoted from its embedded `*Mutex`, which `NewDLocker`'s `DLocker`
calls. Lean-first (no Rocq counterpart); see `InvMutex.lean`.
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

/-- **`lm.Rev()`** (`NewDLocker`'s `DLocker`): `Mutex.Rev` of the wrapped mutex `m`, its
`myRev`. After `lm.Lock()` returns (`lockerMutex.Lock.spec`'s non-panic outcome) it is the
create revision of the lock's ownership fact, the fencing token (`lockFloor_later`). -/
abbrev lockerMutex.Rev.spec : Prop :=
  ∀ (lm m : Loc) (st : MutexSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗
      structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗ mutexState m st }}
    (App (Val (lm @!! go.GoType.PointerType lockerMutex.ty @!! go!"Rev")) (Val #()))
  {{ RET #st.rev; structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗ mutexState m st }}

end spec

end concurrency
end EtcdGrove
end Perennial
