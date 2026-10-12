/-
The trust boundary: `Spec/go_etcd_io/bbolt/Tx__Commit_kv.lean` (bbolt is names-only here).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Commit_kv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

axiom bbolt.Tx.Commit_kv.wp_proof : bbolt.Tx.Commit_kv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
