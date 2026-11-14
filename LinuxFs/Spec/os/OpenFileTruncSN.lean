/-
`os.OpenFile(d/b, flag, perm)`, `flag` with `O_CREATE` and `O_TRUNC`, of an absent name `b` of a claim
on any names `N` containing it (this repository's `os`, part `LinuxFs`): `Spec/os/OpenFileTruncS.lean`'s
`specCreateTruncSnc` with the claim generalized from `.only [b]` (the WAL's `Repair` creates
`<segment>.wal.broken` in the WAL directory's claim on all names but the pipeline's, and joins that
claim's halves at the open's atomic update; `notes/wal-fsext-plan.md`, W7-W12 log, ninth session).
Proved in `Proof/os/OpenFileTruncSN.lean`, over `wp_osOpenCreateSN` (`GooseLang/Ext/Fs/TreeSharedCreateN.lean`)
and `wp_osOpenTruncS`. Lean-first (no Rocq counterpart).
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

/-- The claim on `N ∋ b` after an outcome, with fraction `dq` (`crOut` of a claim on any names). -/
def crOutN (j : Ino) (N : NameSet) (b : GoString) (h : NamesH) (dq : DFrac) :
    Option (Nat × Nat × Ino) → IProp GF
  | none => osNames j N dq h
  | some (x, s, i) => iprop(⌜h.cur !! b = none ∧ h.next ≤ s⌝ ∗ osLogged x (crEnt j b i s) ∗
      osNames j N dq (h.log x (crEnt j b i s) (<[b := .file i]> h.cur)))

/-- `specCreateTruncSnc` over a claim on any names `N` containing `b`. -/
abbrev os.OpenFile.specCreateTruncSncN : Prop :=
  ∀ (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (q r qc : Qp) (Q : Option (Nat × Nat × Ino) → IProp GF),
  OpenFlagsOk (flag ||| W64 0x80000).toNat → (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1 →
  (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 1 →
  NameOk b → N.Mem b → h.cur !! b = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j N (DFrac.own q) h ∗
      osAUnc (osNames j N (DFrac.own r) h) (crOutN j N b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, Q o ∗ crOutN j N b h (DFrac.own q) o ∗ crTr (err = interface.nil) o ∗
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }}

end spec

end EtcdGrove
end Perennial
