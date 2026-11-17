/-
`os.OpenFile(d/b, flag, perm)` in the tree's shared mode, `flag` with `O_CREATE` and without
`O_TRUNC`, `b` a file or nothing, **with no error of the environment** (session S3d): `specCreateS`
(`Spec/os/OpenFileS.lean`) over a semantics whose steps satisfy `NoIoErr` and `NoMapLockErr` on the
path `d/b` (`Sio.path`). Every attempt either succeeds or, with no free fd, fails with `EINTR`, which
the model retries (`NoMapLockErr`'s clause on `open`: out of descriptors the call does not return): so
it returns a fresh `*os.File`, never an error. Proved in `Proof/os/OpenFileSNoErr.lean`, over
`wp_osOpenCreateSNE` and `wp_osOpenFileSNE` (`GooseLang/Ext/Fs/NoErrSpecsOpenFile.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.OpenFileS
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
abbrev os.OpenFile.specCreateSNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]
    (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH)
    (q r qc : Qp) (Q : Option (Nat × Nat × Ino) → IProp GF),
  Sio.path (child d b) →
  OpenFlagsOk (flag ||| W64 0x80000).toNat → (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1 →
  (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 →
  NameOk b → (∀ J, h.cur !! b ≠ some (.dir J)) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, Q o ∗ crOut j b h (DFrac.own q) o ∗ crMeta o ∗
        ∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
          os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
          osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000)) }}

end spec

end EtcdGrove
end Perennial
