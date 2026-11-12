/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__ForEachBucket_r.lean`: U6c's `ForEachBucket_rP`'s
(the same statement; `notes/bbolt-proof-plan.md`, the maintainer's queue item D).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_r
public import Proof.go_etcd_io.bbolt.Bucket__ForEachBucket_rP

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

theorem Bucket.ForEachBucket_r.wp_proof
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hfst : Cursor.first_r.spec (GF := GF) (hG := hG))
    (hnx : Cursor.next_r.spec (GF := GF) (hG := hG)) :
    Bucket.ForEachBucket_r.spec (GF := GF) (hG := hG) :=
  Bucket.ForEachBucket_rP.wp_proof hcur hfst hnx

end proof

end bbolt
end EtcdGrove
end Perennial
