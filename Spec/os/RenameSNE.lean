/-
`os.Rename(oldpath, newpath)` in the tree's shared mode **with no error** (S5, 2026-11-18,
`notes/bbolt-integration-plan.md`): under the premise that the steps on every path have no I/O
error where a success exists (`NoIoErr Sio`, every path covered), a rename of the file `d/bs`
(inode `i`) onto `d'/bt` (a file or nothing), the two names in two claims of distinct keys held
whole, returns `nil` with the rename done: the source's entry gone, the target's the file `i`.
(`os.Rename.specFileS` with no atomic update and no error: the model's `LstatDir` of a target
that is no directory, then one `rename(2)`, which has a success, so returns 0.) Proved in
`Proof/os/RenameSNE.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.RenameS
public import GooseLang.Ext.Fs.NoErrSpecsRename

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
abbrev os.Rename.specFileSNE : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ p, Sio.path p) →
  ∀ (d bs d' bt : GoString) (j j' i : Ino) (N N' : NameSet) (R : Roots) (dq dq' : DFrac)
    (h h' : NamesH) (qc : Qp),
  NameOk bs → NameOk bt → N.Mem bs → N'.Mem bt → (j, N) ≠ (j', N') →
  h.cur !! bs = some (.file i) → (∀ J, h'.cur !! bt ≠ some (.dir J)) →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osPathS R d' dq' j' ∗ osCallPerm qc ∗
      osNames j N (DFrac.own 1) h ∗ osNames j' N' (DFrac.own 1) h' }}
    (App (App (Val (@! os.Rename)) (Val #(child d bs))) (Val #(child d' bt)))
  {{ RET #interface.nil; osPathS R d dq j ∗ osPathS R d' dq' j' ∗ osCallPerm qc ∗
      ∃ h1 h2 : NamesH, ⌜h1.cur = GMap.delete bs h.cur ∧ h2.cur = <[bt := .file i]> h'.cur⌝ ∗
        osNames j N (DFrac.own 1) h1 ∗ osNames j' N' (DFrac.own 1) h2 }}

end spec

end EtcdGrove
end Perennial
