/-
`os.Stat(p)` of a strict ancestor of a root (`/`, or `/c₁/…/cₖ` above a root `/c₁/…/cₙ`, `k < n`): the
environment makes it an existing directory (`GooseLang/Ext/Fs/Impl.lean`, "the roots and their ancestors
are existing directories throughout"), but the model's `stat` opens `p` with the extension's `Open`, which
is stuck off the roots' trees (`OsState.TreePath`). So this triple (any result, nothing changed) is **not
provable against the current model**: a hypothesis of `fileutil.TouchDirAll`'s proof, whose `Exist` loop
climbs above the root when `Stat` of the root fails (any errno, in the model). Model finding (W4, sixth
session, `notes/wal-fsext-plan.md`): `model.stat` should answer at `PathKind` `0` with no step, as
`MkdirAll`'s model does [user]. Lean-first.
-/
module

public import LinuxFs.Proof.os.Base
public import GooseLang.Ext.Fs.TreeShared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- **The path of the first components `l`**: `/` for none, `/c₁/…/cₖ` otherwise. -/
def os.ancPath (l : List GoString) : GoString := if l = [] then [slashB] else joinPath [] l

/-- **`p` is a strict ancestor of a root of `R`**: `/c₁/…/cₖ` (or `/`) for a root `/c₁/…/cₙ`, `k < n`. -/
def os.AboveRoot (R : Roots) (p : GoString) : Prop :=
  ∃ (rcs : List GoString) (j0 : Ino) (k : Nat), (joinPath [] rcs, j0) ∈ R ∧ k < rcs.length ∧
    p = os.ancPath (rcs.take k)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.Stat.specAboveRoot : Prop :=
  ∀ (p : GoString) (R : Roots) (qc : Qp),
  os.AboveRoot R p →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osCallPerm qc }}
    (App (Val (@! os.Stat)) (Val #p))
  {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osCallPerm qc }}

end spec

end EtcdGrove
end Perennial
