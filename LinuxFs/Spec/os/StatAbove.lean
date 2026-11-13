/-
`os.Stat(p)` of a strict ancestor of a root (`/`, or `/c₁/…/cₖ` above a root `/c₁/…/cₙ`, `k < n`): any
result, nothing changed. The environment makes such a path an existing directory
(`GooseLang/Ext/Fs/Impl.lean`, "the roots and their ancestors are existing directories throughout"),
and `model.stat` answers there with no extension step but the query `PathKind` (`2`: `model.statAbove`,
2026-11-13, pending the user's review; `notes/wal-fsext-models-review.md`, "Above-root Stat/Open").
`fileutil.TouchDirAll`'s `Exist` loop climbs above the root when `Stat` of the root fails. Proved in
`LinuxFs/Proof/os/StatAbove.lean` (`os.Stat.wp_proofAboveRoot`). Lean-first.
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
