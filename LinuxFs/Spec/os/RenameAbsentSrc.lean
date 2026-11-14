/-
`os.Rename(d/bs, d/bt)` **with an absent source** (`fsExt`; the model `LinuxFs/TrustedCode/os.lean`,
`Rename.impl`): with the source `bs` absent in a fraction of a claim on `d`'s names holding both
names, the rename fails (a `*LinkError`: the target's `lstat` found a directory, then Go reports the
source's `lstat` error; or `rename(2)` returned `ENOENT`, `EINTR` retried) and changes nothing.
`renameWALUnlock`'s second rename after a first one that took effect and returned an error (W4 of
`notes/wal-fsext-plan.md`, ledger 2026-11-14). Proved in `LinuxFs/Proof/os/RenameAbsentSrc.lean`.
Lean-first.
-/
module

public import LinuxFs.Spec.os.Rename

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
abbrev os.Rename.specAbsentSrc : Prop :=
  ∀ (d bs bt : GoString) (j : Ino) (N : NameSet) (R : Roots) (qd : Qp) (dqn : DFrac) (h : NamesH)
    (qc : Qp),
  NameOk bs → NameOk bt → N.Mem bs → N.Mem bt → h.cur !! bs = none →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ osCallPerm qc ∗
      osNames j N dqn h }}
    (App (App (Val (@! os.Rename)) (Val #(child d bs))) (Val #(child d bt)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm qc ∗
      osNames j N dqn h ∗ ⌜err ≠ interface.nil ∧ os.renameErrOk err⌝ }}

end spec

end EtcdGrove
end Perennial
