/-
`os.Rename(d/bs, d/bt)` of a directory onto a name holding anything (this repository's `os`, part
`LinuxFs`; the tree's shared mode): the WAL's `cleanupWAL` renames its directory to `nm.broken.<time>`,
which may hold a leftover (`notes/wal-fsext-plan.md`, W4 log, twenty-seventh session).
`os.Rename.specDirS` (`Rename.lean`) needs the target absent.

The model (`TrustedCode/os.lean`) first `lstat`s the target (`LstatDir`): a directory there (as the
`lstat` reports it) makes Go return a `LinkError` (`EEXIST`, or the `lstat` of the source's error)
with no `rename(2)`: then the atomic update is given back unused, with the caller's fraction. Else
`rename(2)`, `EINTR` retried: its outcome is `specDirS`'s, of the operation
`.rename j bs j bt (.dir J) old` (`old := h.cur !! bt`), and a logged outcome found the target
nothing or a directory (`RenTgtOk`, recorded in `renDirOutA`: the model replaces only an empty
directory; onto a file or a non-empty directory the call fails with no effect). Proved in
`Proof/os/RenameAny.lean` over `Fs.wp_osRenameDirAnyS`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.PkgInit
public import Spec.os.RenameS
public import Spec.fmt.ErrorOk
public import GooseLang.Ext.Fs.TreeSharedRenameAny

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The entry of a directory rename onto `old`, by a call begun at `s`. -/
def renDirEntA (j : Ino) (bs bt : GoString) (J : Ino) (old : Option Node) (s : Nat) : LogEntry :=
  ⟨.rename j bs j bt (.dir J) old, s⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The claim of a directory rename onto whatever `bt` holds, after an outcome, with fraction `dq`; the
call began at least at `lb`; a logged outcome found the target nothing or a directory. -/
def renDirOutA (j J : Ino) (N : NameSet) (bs bt : GoString) (h : NamesH) (dq : DFrac) (lb : Nat)
    (o : Option (Nat × Nat)) : IProp GF :=
  iprop(⌜o.isSome → RenTgtOk (h.cur !! bt)⌝ ∗ logOut lb (renDirEntA j bs bt J (h.cur !! bt)) o ∗
    claimOut j N dq h (renDirEntA j bs bt J (h.cur !! bt))
      (restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur))) o)

/-- See the file header. -/
abbrev os.Rename.specDirAnySnc : Prop :=
  ∀ (d bs bt : GoString) (j J : Ino) (N : NameSet) (R : Roots) (qd : Qp) (h : NamesH)
    (q r : Qp) (lb : Nat) (Q : Option (Nat × Nat) → IProp GF),
  NameOk bs → NameOk bt → N.Mem bs → N.Mem bt → bs ≠ bt →
  h.cur !! bs = some (.dir J) → q + r = 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) 1 ∗
      osLogLb lb ∗ osNames j N (DFrac.own q) h ∗
      osAUnc (osNames j N (DFrac.own r) h) (renDirOutA j J N bs bt h (DFrac.own r) lb) Q }}
    (App (App (Val (@! os.Rename)) (Val #(child d bs))) (Val #(child d bt)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) 1 ∗
      fmtErrorOkOrNil err ∗
      ((⌜err ≠ interface.nil ∧ os.renameErrOk err⌝ ∗ osNames j N (DFrac.own q) h ∗
          osAUnc (osNames j N (DFrac.own r) h) (renDirOutA j J N bs bt h (DFrac.own r) lb) Q) ∨
        ∃ o, ⌜(err = interface.nil → o.isSome) ∧ os.renameErrOk err⌝ ∗ Q o ∗
          renDirOutA j J N bs bt h (DFrac.own q) lb o) }}

end spec

end EtcdGrove
end Perennial

end
