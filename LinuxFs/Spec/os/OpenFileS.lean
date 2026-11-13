/-
`os.OpenFile(d/b, O_RDWR|O_CREATE, perm)` (this repository's `os`, part `LinuxFs`) in the tree's
shared mode (`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`, review finding
M1): logically atomic. The model (`TrustedCode/os.lean`) is the extension's `Open` with
`O_CLOEXEC` added, each attempt after its own `CallBegin`, retried on `EINTR`. The caller holds a
fraction of the claim on `b` (`.only [b]`), the atomic update the rest: it commits at the step
that creates the file (outcome `some (x, s, i)`: the `create` logged at `x` by a call begun at `s`,
the new inode `i`) or at the step that ends the call with no effect (`none`: the file existed, or an
error); an `EINTR` with no effect aborts it. An attempt that created the file and returned `EINTR`
is retried, and opens the file it made. The new file's `OsMeta` (empty) goes to the caller.

* `os.OpenFile.specCreateS`: `b` holds a file or nothing in `d`'s directory `j`. On success a
  fresh `*os.File` on a fresh fd, readable and writable, on the file the outcome left at `b`.

Proved in `Proof/os/OpenFileS.lean`, over `Proof/os/SharedExt.lean`'s `wp_osOpenFileS` (not yet
proved). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The entry of a create of `b` in `j`, the inode `i`, by a call begun at `s`. -/
def crEnt (j : Ino) (b : GoString) (i : Ino) (s : Nat) : LogEntry := ⟨.create j b i, s⟩

/-- The inode at `b` after an outcome. -/
def crIno (b : GoString) (h : NamesH) : Option (Nat × Nat × Ino) → Ino → Prop
  | none, i' => h.cur !! b = some (.file i')
  | some (_, _, i), i' => i' = i

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The claim on `b` after an outcome, with fraction `dq`. -/
def crOut (j : Ino) (b : GoString) (h : NamesH) (dq : DFrac) : Option (Nat × Nat × Ino) → IProp GF
  | none => osNames j (.only [b]) dq h
  | some (x, s, i) => iprop(⌜h.cur !! b = none ∧ h.next ≤ s⌝ ∗ osLogged x (crEnt j b i s) ∗
      osNames j (.only [b]) dq (h.log x (crEnt j b i s) (<[b := .file i]> h.cur)))

/-- The new file's `OsMeta` after an outcome. -/
def crMeta : Option (Nat × Nat × Ino) → IProp GF
  | none => iprop(emp)
  | some (_, _, i) => osMeta i (DFrac.own 1) newMeta

/-- See the file header. -/
abbrev os.OpenFile.specCreateS : Prop :=
  ∀ (d b : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH) (q r qc : Qp)
    (Q : Option (Nat × Nat × Ino) → IProp GF),
  NameOk b → (∀ J, h.cur !! b ≠ some (.dir J)) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, Q o ∗ crOut j b h (DFrac.own q) o ∗ crMeta o ∗
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝) }}

end spec

end EtcdGrove
end Perennial
