/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__ForEachBucket_w.lean`: not yet (U6, `notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.ForEachBucket_w.wp_proof : Bucket.ForEachBucket_w.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
