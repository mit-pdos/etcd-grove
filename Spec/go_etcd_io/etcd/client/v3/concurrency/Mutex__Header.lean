/-
`concurrency.Mutex.Header()` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
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

/-- **`m.Header()`**: `hdr` (the header of the response that acquired the lock, `hdrRevAt` in
`TryLock`'s and `Lock`'s postconditions). -/
abbrev Mutex.Header.spec : Prop :=
  ∀ (m : Loc) (st : MutexSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ mutexState m st }}
    (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Header")) (Val #()))
  {{ RET #st.hdr; mutexState m st }}

end spec

end concurrency
end EtcdGrove
end Perennial
