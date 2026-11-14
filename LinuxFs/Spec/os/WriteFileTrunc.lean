/-
`os.WriteFile(d/b, data, perm)` (file.go:939; translated, over the trusted `OpenFile`, `Write`, `Close`)
of an empty `data`, for a name `b` holding the regular file `i`, in the tree's shared mode: what
`fileutil.IsDirWriteable`'s probe meets when `dir/.touch` is a leftover (a crash between its create and
its remove). `OpenFile(d/b, O_WRONLY|O_CREATE|O_TRUNC, perm)` of the existing file
(`os.OpenFile.wp_truncS`: no claim changes, the file truncated, which needs its `OsMeta` and bytes,
`trFile`), the empty `Write` (no effect), `Close`.

* `os.WriteFile.specTruncS`: a fraction of a claim on names containing `b`, the file held whole
  (`trFile i False`, what a truncation keeps); no claim changes, the file still held whole.

Proved in `LinuxFs/Proof/os/WriteFileTrunc.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.os.OpenFileTruncS

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
abbrev os.WriteFile.specTruncS : Prop :=
  ∀ (d b : GoString) (sl : GoSlice) (dqs : DFrac) (perm : w32) (R : Roots) (j i : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp),
  NameOk b → N.Mem b → h.cur !! b = some (.file i) →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h ∗
      trFile i False ∗ sl ↦*{dqs} ([] : List w8) }}
    (App (App (App (Val (@! os.WriteFile)) (Val #(child d b))) (Val #sl)) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h ∗
      trFile i False ∗ sl ↦*{dqs} ([] : List w8) }}

end spec

end EtcdGrove
end Perennial
