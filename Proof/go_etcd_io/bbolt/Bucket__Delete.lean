/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Delete.lean` (U7k, `notes/bbolt-proof-plan.md`): a
write transaction's `Delete`, `Write/DelWp`'s `wp_writer`. Its premise `hD1` (`gensOK`'s third
clause, maintainer 14) is discharged by `Inv/Tx`'s
`gensOK_handle_bktLoc` (`gensOK`'s third clause).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Delete
public import Proof.go_etcd_io.bbolt.Write.DelWp
public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Delete.wp_proof
    (hcur : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hnode : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Cursor.node.spec (GF := GF) (hG := hG))
    (hdel : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], node.del.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Bucket.Delete.spec (GF := GF) (hG := hG) := by
  intro _ _ _ tx γ T b n m key kb dk own
  exact Write.Bucket.Delete.wp_writer hcur hseek hnode hdel hEq tx γ T b n m key kb dk own
    (fun X h => gensOK_handle_bktLoc T X h)

end proof

end bbolt
end EtcdGrove
end Perennial
