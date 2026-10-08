/-
`reflect.DeepEqual`: Go reflection, not modelled; see the spec.
-/
import EtcdGrove.Raft.Spec.reflect_DeepEqual

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an
assumption under `#print axioms`. Go reflection is outside what Goose models; see the
spec for the reading of `reflect/deepequal.go` it encodes. -/
axiom reflect.DeepEqual.wp_proof : reflect.DeepEqual.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
