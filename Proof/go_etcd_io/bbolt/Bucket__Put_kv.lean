module

public import Spec.go_etcd_io.bbolt.Bucket__Put_kv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The trust boundary (stage S1 left it an axiom: the spec file's header says why). -/
axiom bbolt.Bucket.Put_kv.wp_proof : bbolt.Bucket.Put_kv.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
