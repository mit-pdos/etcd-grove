/-
`reflect.DeepEqual` on bbolt's page-id sets: Go reflection, not modelled; see the spec.
-/
module
public import Spec.reflect.DeepEqualPgidSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- **Trust boundary**: an `axiom`, so that it counts as an assumption under `#print axioms`.
Go reflection is outside what Goose models; see the spec for the reading of
`reflect/deepequal.go` it encodes. -/
axiom reflect.DeepEqual.wp_proof : reflect.DeepEqual.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial
