/-
The trust boundary: `(*lessor).Demote` (translated with its body, not proved: its
`close(le.demotec)` needs the channel's close right, which the lessor's invariant does not keep
(only `Demote` closes `demotec`, which `Promote`, itself assumed, makes); the rest (the leases'
`forever`, the fresh heap and notifier) is in the invariant).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Demote

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

axiom lease.lessor.Demote.wp_proof : lease.lessor.Demote.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
