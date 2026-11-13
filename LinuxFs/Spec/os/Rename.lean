/-
`os.Rename(oldpath, newpath)` (this repository's `os`, part `LinuxFs`) in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`, review finding M1): logically
atomic. The model (`TrustedCode/os.lean`) is an `lstat` of the new name (`LstatDir`), then
`rename(2)` (the extension's `Rename`), each after its own `CallBegin`, retried on `EINTR`. The
caller holds a fraction of each claim the rename writes, the atomic update the rest (a crash
invariant typically holds it): the update commits at the step that logs the rename, or at the
step that returns the call's error with no effect; an `EINTR` with no effect aborts it. A rename
that took effect and returned `EINTR` is retried; the retry finds the source gone (the caller's
fraction keeps it so) and fails: the error is non-nil, the outcome the logged one.

* `os.Rename.specFileS`: the file `d/bs` (inode `i`) onto `d'/bt` (a file or nothing), the names in
  two claims of distinct keys (the WAL's cut: `N.tmp`'s claim and the directory's). Outcome
  `some (x, s)`: the entry `x`, by a call begun at `s` after both claims' last change.
* `os.Rename.specDirS`: the directory `d/bs` (inode `J`) to the free name `d/bt`, both in one
  claim, with the whole call permission (no other call in flight; the WAL's `Create` and
  `cleanupWAL`).

Each returns the caller's fractions as the outcome left them. Proved in `Proof/os/Rename.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The entry of a file rename by a call begun at `s`. -/
def renFileEnt (j : Ino) (bs : GoString) (j' : Ino) (bt : GoString) (i : Ino) (h' : NamesH)
    (s : Nat) : LogEntry :=
  ⟨.rename j bs j' bt (.file i) (h'.cur !! bt), s⟩

/-- The entry of a directory rename by a call begun at `s`. -/
def renDirEnt (j : Ino) (bs bt : GoString) (J : Ino) (s : Nat) : LogEntry :=
  ⟨.rename j bs j bt (.dir J) none, s⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The two claims of a file rename after an outcome, with fractions `dq1`, `dq2`. -/
def renFileOut (j j' i : Ino) (N N' : NameSet) (bs bt : GoString) (h h' : NamesH)
    (dq1 dq2 : DFrac) (o : Option (Nat × Nat)) : IProp GF :=
  iprop(logOut (max h.next h'.next) (renFileEnt j bs j' bt i h') o ∗
    claimOut j N dq1 h (renFileEnt j bs j' bt i h') (GMap.delete bs h.cur) o ∗
    claimOut j' N' dq2 h' (renFileEnt j bs j' bt i h') (<[bt := .file i]> h'.cur) o)

/-- See the file header. -/
abbrev os.Rename.specFileS : Prop :=
  ∀ (d bs d' bt : GoString) (j j' i : Ino) (N N' : NameSet) (R : Roots) (dq dq' : DFrac)
    (h h' : NamesH) (q1 r1 q2 r2 qc : Qp) (Q : Option (Nat × Nat) → IProp GF),
  NameOk bs → NameOk bt → N.Mem bs → N'.Mem bt → (j, N) ≠ (j', N') →
  h.cur !! bs = some (.file i) → (∀ J, h'.cur !! bt ≠ some (.dir J)) →
  q1 + r1 = 1 → q2 + r2 = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osPathS R d' dq' j' ∗ osCallPerm qc ∗
      osNames j N (DFrac.own q1) h ∗ osNames j' N' (DFrac.own q2) h' ∗
      osAU iprop(osNames j N (DFrac.own r1) h ∗ osNames j' N' (DFrac.own r2) h')
        (renFileOut j j' i N N' bs bt h h' (DFrac.own r1) (DFrac.own r2)) Q }}
    (App (App (Val (@! os.Rename)) (Val #(child d bs))) (Val #(child d' bt)))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osPathS R d' dq' j' ∗ osCallPerm qc ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗
        renFileOut j j' i N N' bs bt h h' (DFrac.own q1) (DFrac.own q2) o }}

/-- The claim of a directory rename after an outcome, with fraction `dq`. -/
def renDirOut (j J : Ino) (N : NameSet) (bs bt : GoString) (h : NamesH) (dq : DFrac)
    (o : Option (Nat × Nat)) : IProp GF :=
  iprop(logOut 0 (renDirEnt j bs bt J) o ∗
    claimOut j N dq h (renDirEnt j bs bt J)
      (restrictN N (<[bt := .dir J]> (GMap.delete bs h.cur))) o)

/-- See the file header. -/
abbrev os.Rename.specDirS : Prop :=
  ∀ (d bs bt : GoString) (j J : Ino) (N : NameSet) (R : Roots) (qd : Qp) (h : NamesH)
    (q r : Qp) (Q : Option (Nat × Nat) → IProp GF),
  NameOk bs → NameOk bt → N.Mem bs → N.Mem bt → bs ≠ bt →
  h.cur !! bs = some (.dir J) → h.cur !! bt = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ osCallPerm 1 ∗
      osNames j N (DFrac.own q) h ∗
      osAU (osNames j N (DFrac.own r) h) (renDirOut j J N bs bt h (DFrac.own r)) Q }}
    (App (App (Val (@! os.Rename)) (Val #(child d bs))) (Val #(child d bt)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm 1 ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ renDirOut j J N bs bt h (DFrac.own q) o }}

end spec

end EtcdGrove
end Perennial
