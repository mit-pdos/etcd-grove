/- Lean-first (no Rocq counterpart). `db.Commit(v)` (`examples/bboltfs/minibolt.go`), a write transaction, with the committer's token (`dbOwner γ t n`: the current txid `t`, the high water mark `n`, small enough that the next mapping is at most 1 TiB): on success, transaction `t + 1` is current and its root page holds `v`; on an error, the handle failed (`dbFailed`). -/
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
abbrev DB.Commit.spec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t n : Nat) (v : w64),
  t + 1 < 2 ^ 64 → (n + 3) * 4096 ≤ 2 ^ 40 →
  {{ isDB (GF := GF) γ db ∗ dbOwner (GF := GF) γ t n }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Commit")) (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ dbOwner (GF := GF) γ (t + 1) (n + 1) ∗
          dbTx (GF := GF) γ (t + 1) (some v) ∗ dbLast (GF := GF) γ (t + 1)) ∨
      (⌜err ≠ interface.nil⌝ ∗ dbFailed (GF := GF) γ) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
