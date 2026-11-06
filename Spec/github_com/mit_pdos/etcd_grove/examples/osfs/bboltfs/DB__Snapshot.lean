/- Lean-first (no Rocq counterpart). `db.Snapshot()` (`examples/osfs/bboltfs/minibolt.go`, tx.go's `WriteTo`): as `Get` (`DB__Get.lean`, the thread token and the committer's token too), what the copy's root page holds, read with the racing `ReadAt` (`os.File.ReadAt.specRacy`, over the committed pages' discarded bytes, `pageIs`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.Snapshot.spec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t : Nat) (o : Option (Nat × Nat)),
  {{ isDB (GF := GF) γ db ∗ threadTok ∗ dbLast (GF := GF) γ t ∗
      dbOwnerOpt (GF := GF) γ o }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Snapshot")) (Val #()))
  {{ (txid v : w64) (has : Bool) (err : GoInterface), RET (PairV (PairV (PairV #txid #v) #has) #err);
      threadTok ∗ dbOwnerOpt (GF := GF) γ o ∗
      ((⌜err = interface.nil ∧ t ≤ txid.toNat ∧ ∀ x, o = some x → txid.toNat = x.1⌝ ∗ dbLast (GF := GF) γ txid.toNat ∗
          dbTx (GF := GF) γ txid.toNat (if has then some v else none)) ∨
       ⌜err ≠ interface.nil⌝) }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
