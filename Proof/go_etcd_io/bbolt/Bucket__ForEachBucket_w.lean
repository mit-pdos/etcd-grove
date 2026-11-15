/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__ForEachBucket_w.lean`: `Read/WFeb`'s
`Bucket.ForEachBucket_w.wp_proof'`, over the specs of `Bucket.Cursor` and the writer cursor moves.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_w
public import Proof.go_etcd_io.bbolt.Read.WFeb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.ForEachBucket_w.wp_proof
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hfst : Cursor.first_w.specQ (GF := GF) (hG := hG))
    (hnx : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hnxe : Cursor.next_we.specQ (GF := GF) (hG := hG)) :
    Bucket.ForEachBucket_w.spec (GF := GF) (hG := hG) :=
  Bucket.ForEachBucket_w.wp_proof' hcur hfst hnx hnxe

end proof

end bbolt
end EtcdGrove
end Perennial
