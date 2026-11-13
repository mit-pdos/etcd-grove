/-
`os.WriteFile(d/b, data, perm)` (file.go:939; translated, over the trusted `OpenFile`, `Write`,
`Close`) of an empty `data`, in the tree's shared mode, for a name `b` holding nothing whose claim
the caller holds whole: `OpenFile(d/b, O_WRONLY|O_CREATE|O_TRUNC, perm)` (`os.OpenFile.specCreateTruncS`
with the trivial update), the empty `Write` (no effect), `Close`. Outcome `o` the create's
(`crOut`); a success has created the file. What `fileutil.IsDirWriteable`'s probe `dir/.touch` needs.
Proved in `LinuxFs/Proof/os/WriteFile.lean`. Lean-first (W4).
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
abbrev os.WriteFile.specEmptyS : Prop :=
  ∀ (d b : GoString) (sl : GoSlice) (dqs : DFrac) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac)
    (h : NamesH) (qc : Qp),
  NameOk b → h.cur !! b = none →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own 1) h ∗ sl ↦*{dqs} ([] : List w8) }}
    (App (App (App (Val (@! os.WriteFile)) (Val #(child d b))) (Val #sl)) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm qc ∗ sl ↦*{dqs} ([] : List w8) ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ crOut j b h (DFrac.own 1) o }}

end spec

end EtcdGrove
end Perennial
