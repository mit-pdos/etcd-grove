/- Lean-first (no Rocq counterpart). `db.Commit(v)`'s crash-aware spec: `DB.Commit.spec`
(`DB__Commit.lean`) for an open database over the crash invariant of its file (`isDBC`,
`DBCrash.lean`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DBCrash

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
abbrev DB.Commit.specCrash : Prop :=
  ∀ (γ : DBNames) (γc : GName) (db : Loc) (t n : Nat) (v : w64),
  t + 1 < 2 ^ 64 → (n + 2) * 4096 ≤ 2 ^ 30 → γ.vp (t + 1) (some v) →
  {{ isDBC (GF := GF) γ γc db ∗ dbOwner (GF := GF) γ t n }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Commit")) (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ dbOwner (GF := GF) γ (t + 1) (n + 1) ∗
          dbTx (GF := GF) γ (t + 1) (some v) ∗ dbLast (GF := GF) γ (t + 1)) ∨
      (⌜err ≠ interface.nil⌝ ∗ dbFailed (GF := GF) γ ∗ dbOwner (GF := GF) γ t 0) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
