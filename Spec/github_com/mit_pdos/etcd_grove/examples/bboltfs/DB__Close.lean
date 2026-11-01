/- Lean-first (no Rocq counterpart). `db.Close()` (`examples/bboltfs/minibolt.go`, db.go's `Close`): all three locks, unmap, unlock the file, close it. It takes every reader token and the committer's token: nothing may use the handle afterwards (the locks' resources then hold no mapping and no open file). -/
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
abbrev DB.Close.spec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t n : Nat),
  {{ isDB (GF := GF) γ db ∗ dbOwner (GF := GF) γ t n ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        dbReader (GF := GF) γ db) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end bboltfs
end EtcdGrove
end Perennial
