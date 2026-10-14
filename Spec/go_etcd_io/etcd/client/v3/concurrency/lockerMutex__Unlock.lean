/-
`concurrency.lockerMutex.Unlock()` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
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

/-- **`lm.Unlock()`** (`NewLocker`'s `sync.Locker`): `Mutex.Unlock(client.Ctx())` on the wrapped
mutex `m`, knowing etcd has reached `lo`: `Mutex.Unlock`'s `nil` case (the key absent at some
`R ≥ lo`, the mutex released); or, on any error (`ErrLockReleased` for a mutex without a key, or
a client error), the panic `panic(err)`, with the mutex unchanged. -/
abbrev lockerMutex.Unlock.spec : Prop :=
  ∀ (lm m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : MutexSt)
    (cctx : GoInterfaceOk) (ccs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗
      structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗ isMutex m s γ client id pfx ∗ mutexState m st ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" client ↦□ GoInterface.ok cctx ∗
      context.isContext cctx ccs ∗ etcdReached lo }}
    (App (Val (lm @!! go.GoType.PointerType lockerMutex.ty @!! go!"Unlock")) (Val #()))
  {{ (r : val), RET r; structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗
      ((⌜r = #()⌝ ∗ ∃ R : w64, mutexState m (MutexSt.released st.hdr) ∗
        etcdReached R ∗ etcdAbsent pfx st.key R ∗
        ⌜¬ st.noKey ∧ pfx <+: st.key ∧ sint.Z lo ≤ sint.Z R⌝) ∨
      (∃ err : GoInterface, ⌜err ≠ GoInterface.nil ∧ r = PanicV #err⌝ ∗ mutexState m st)) }}

end spec

end concurrency
end EtcdGrove
end Perennial
