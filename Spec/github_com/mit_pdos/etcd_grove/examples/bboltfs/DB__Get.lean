/- Lean-first (no Rocq counterpart). `db.Get()` (`examples/bboltfs/minibolt.go`), a read transaction through the mapping, with a reader token (`dbReader`) and a lower bound `t` of the current txid: on success, a txid at least `t` and what its root page holds (`dbTx`: `has` and `v`), and, if the caller holds the committer's token at `t'` (`dbOwnerOpt γ (some (t', n))`, given back), the txid is `t'`; on an error, nothing (an error is just an error: no client needs more). The client's predicate holds of what it reads (`dbTx`, `γ.vp`). -/
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
  ∀ (γ : DBNames) (db : Loc) (t : Nat) (o : Option (Nat × Nat)),
  {{ isDB (GF := GF) γ db ∗ dbReader (GF := GF) γ db ∗ dbLast (GF := GF) γ t ∗
      dbOwnerOpt (GF := GF) γ o }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Get")) (Val #()))
  {{ (txid v : w64) (has : Bool) (err : GoInterface), RET (PairV (PairV (PairV #txid #v) #has) #err);
      dbReader (GF := GF) γ db ∗ dbOwnerOpt (GF := GF) γ o ∗
      ((⌜err = interface.nil ∧ t ≤ txid.toNat ∧ ∀ x, o = some x → txid.toNat = x.1⌝ ∗ dbLast (GF := GF) γ txid.toNat ∗
          dbTx (GF := GF) γ txid.toNat (if has then some v else none)) ∨
       ⌜err ≠ interface.nil⌝) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
