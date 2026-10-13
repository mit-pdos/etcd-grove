/-
`SetScheduledCompact` (`store.go`) (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `SetScheduledCompact(tx, value)`, `value ≥ 0`: its own critical section of the batch lock
(`LockInsideApply`, which runs the post-lock hook `f` on the caller's `Pre`: `{P ∗ Pre} f() {Q}`),
`UnsafeSetScheduledCompact`, `Unlock`; the caller's update, with the lock's resource `W` (the store updates
its record of the meta key there), before the `Unlock`: `Q ∗ W ={⊤}=∗ P ∗ W ∗ Post`. -/
abbrev mvcc.SetScheduledCompact.spec : Prop :=
  ∀ (bt : GoInterfaceOk) (View : Qp → mvcc.Bucket → IProp GF) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Locked : mvcc.Puts → IProp GF) (P : IProp GF) (f : val) (value : w64)
    (Pre Q Post : IProp GF),
  0 ≤ sint.Z value →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.batchTxSpec bt View Del W Dep Locked P f ∗ Pre ∗
      □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗ (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetScheduledCompact)) (Val #(GoInterface.ok bt)))
      (Val #value))
  {{ RET #(); Post }}

end spec

end EtcdGrove
end Perennial
