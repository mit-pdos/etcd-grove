/- Lean-first (no Rocq counterpart). `db.Get()` (`examples/bboltfs/minibolt.go`), a read transaction through the mapping, with a reader token (`dbReader`) and a lower bound `t` of the current txid: on success, a txid at least `t` and what its root page holds (`dbTx`: `has` and `v`); on an error, the handle failed. A client that commits `txid` as transaction `txid`'s value gets `valueOk`. NOT PROVABLE for the code as it is: `issues/bbolt-failed-remap-nil-meta-panic.md`. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.Get.spec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t : Nat),
  {{ isDB (GF := GF) γ db ∗ dbReader (GF := GF) γ db ∗ dbLast (GF := GF) γ t }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Get")) (Val #()))
  {{ (txid v : w64) (has : Bool) (err : GoInterface), RET (PairV (PairV (PairV #txid #v) #has) #err);
      dbReader (GF := GF) γ db ∗
      ((⌜err = interface.nil ∧ t ≤ txid.toNat⌝ ∗ dbLast (GF := GF) γ txid.toNat ∗
          dbTx (GF := GF) γ txid.toNat (if has then some v else none)) ∨
       (⌜err ≠ interface.nil⌝ ∗ dbFailed (GF := GF) γ)) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
