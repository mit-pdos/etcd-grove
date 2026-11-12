/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Put.lean` (U7k, `notes/bbolt-proof-plan.md`): a write
transaction's `Put`, `Write/PutWp`'s `wp_writer`. Its premise `hD1` (`gensOK`'s third clause,
maintainer 14) is discharged by `Inv/Tx`'s `gensOK_handle_bktLoc` (`gensOK`'s third clause).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Put
public import Proof.go_etcd_io.bbolt.Write.PutWp
public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Put.wp_proof (hclone : cloneBytes.spec (GF := GF) (hG := hG))
    (hcur : ∀ [HasExt osFsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : ∀ [HasExt osFsExt], Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hnode : ∀ [HasExt osFsExt], Cursor.node.spec (GF := GF) (hG := hG))
    (hput : ∀ [HasExt osFsExt], node.put.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Bucket.Put.spec (GF := GF) (hG := hG) := by
  intro _ tx γ T b n m key value kb vb dk
  exact Write.Bucket.Put.wp_writer hclone hcur hseek hnode hput hEq tx γ T b n m key value kb vb dk
    (fun X h => gensOK_handle_bktLoc T X h)

end proof

end bbolt
end EtcdGrove
end Perennial
