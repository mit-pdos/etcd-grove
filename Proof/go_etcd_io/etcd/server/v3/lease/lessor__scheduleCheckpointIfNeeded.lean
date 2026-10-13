/-
The trust boundary: `(*lessor).scheduleCheckpointIfNeeded` (names only: its
`int64(le.checkpointInterval.Seconds())`, a float-to-integer conversion, which Perennial's
semantics does not step; and `heap.Push` onto the checkpoint heap, `zap` logging).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

axiom lease.lessor.scheduleCheckpointIfNeeded.wp_proof :
  lease.lessor.scheduleCheckpointIfNeeded.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
