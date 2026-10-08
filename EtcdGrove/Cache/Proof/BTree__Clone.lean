/-
`(*BTree[T]).Clone()`: a method of the names-only btree package; see the spec.
-/
import EtcdGrove.Cache.Spec.BTree__Clone

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an
assumption under `#print axioms`. `k8s.io/utils/third_party/forked/golang/btree` is
translated names-only (no bodies); the spec states what its documentation says. -/
axiom btree.BTree.Clone.wp_proof : btree.BTree.Clone.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
