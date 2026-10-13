/-
`UnsafeSetScheduledCompact` (`store.go`) (2026-10-13, unit 5a).
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

/-- `UnsafeSetScheduledCompact(tx, value)` under the batch lock (`Locked l`), `value ≥ 0`: its `UnsafePut` of
`RevToBytes(Revision{Main: value})` at the compaction key (the store's record of the key,
`metaCompact`, is its own: the caller updates it). -/
abbrev mvcc.UnsafeSetScheduledCompact.spec : Prop :=
  ∀ (bt : GoInterfaceOk) (View : Qp → mvcc.Bucket → IProp GF) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Locked : mvcc.Puts → IProp GF) (P : IProp GF) (f : val) (l : mvcc.Puts)
    (value : w64),
  0 ≤ sint.Z value →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.batchTxSpec bt View Del W Dep Locked P f ∗ Locked l }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetScheduledCompact)) (Val #(GoInterface.ok bt)))
      (Val #value))
  {{ RET #(); Locked l }}

end spec

end EtcdGrove
end Perennial
