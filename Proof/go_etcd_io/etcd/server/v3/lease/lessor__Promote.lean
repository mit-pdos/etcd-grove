/-
The trust boundary: `(*lessor).Promote` (names only: float arithmetic and the float-to-integer
conversion `time.Duration(rateDelay)`, which Perennial's semantics does not step; `sort.Sort`
over `Remaining()`, which read-locks each lease's `expiryMu`, a reader slot the lessor's
invariant does not keep).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Promote

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

axiom lease.lessor.Promote.wp_proof : lease.lessor.Promote.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
