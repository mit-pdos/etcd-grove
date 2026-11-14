/-
`os.MkdirAll(d/b, perm)` (this repository's `os`, part `LinuxFs`) of a name already holding a directory,
in the tree's shared mode (`GooseLang/Ext/Fs/TreeShared.lean`): what `fileutil.TouchDirAll` meets when
its `Exist(d/b)` failed (a `Stat` error) on a leftover directory (`wal.Create`'s `nm.tmp`). The model
(`TrustedCode/os.lean`, `MkdirAll.impl`) asks `PathKind` (`d/b` is below a root), `Stat`s `d/b` (a
directory: `nil` if `IsDir`, else `ENOTDIR`; or an error), and after a `Stat` error runs `MkdirAll(d)`
(no change), then `Mkdir(d/b)`, which fails with no effect (the name is taken), then `Lstat(d/b)`.

* `os.MkdirAll.specDirS`: `b` holds the directory `J` (a fraction of the claim on `b`, a fraction of
  the spine to `d`, any fraction of the call permission): no effect, `nil` or an error.

Proved in `Proof/os/MkdirAllDir.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.os.MkdirAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.MkdirAll.specDirS : Prop :=
  ∀ (d b : GoString) (perm : w32) (R : Roots) (j J : Ino) (qd qn : Qp) (h : NamesH) (qc : Qp),
  NameOk b → h.cur !! b = some (.dir J) →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own qn) h }}
    (App (App (Val (@! os.MkdirAll)) (Val #(child d b))) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own qn) h }}

end spec

end EtcdGrove
end Perennial
