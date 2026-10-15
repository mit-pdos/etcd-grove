/-
`UnsafeReadScheduledCompact` (`store.go`): the meta key `scheduledCompactRev` (2026-10-13, unit 5a).
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

/-- `UnsafeReadScheduledCompact(tx)` over a reader of the `Meta` bucket's compaction keys (`metaReadSpec`: what the
store wrote there, `RevToBytes(Revision{Main: x})`, `x ≥ 0`; which one is not modelled): the main
revision read and `true`, or `0` and `false` (none). -/
abbrev mvcc.UnsafeReadScheduledCompact.spec : Prop :=
  ∀ (rt : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ □ mvcc.metaReadSpec rt }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact)) (Val #(GoInterface.ok rt)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found);
      ⌜(found = true → 0 ≤ sint.Z x) ∧ (found = false → x = W64 0)⌝ }}

end spec

end EtcdGrove
end Perennial
