/-
`os.Remove(name)` (this repository's `os`, part `LinuxFs`) of a file, in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`, review finding M1): logically
atomic. The model (`TrustedCode/os.lean`) is `unlink(2)` (the extension's `Unlink`), then, if it
failed, `rmdir(2)` (`Rmdir`), each attempt after its own `CallBegin`, each retried on `EINTR`. The
caller holds a fraction of the claim on the name (`.only [b]`), the atomic update the rest: it
commits at the step that logs the unlink, or at the unlink attempt that ends the call with an error
and no effect; an `EINTR` with no effect aborts it. After the unlink took effect and returned
`EINTR`, the retry finds the name gone (the caller's fraction keeps it so) and fails, as the
`rmdir` that follows: the error is non-nil, the outcome the logged one.

* `os.Remove.specFileS`: `d/b` holds the file `i`. Outcome `some (x, s)`: the unlink logged at `x`
  by a call begun at `s`, after the claim's last change; `none`: no effect, and the error non-nil.

Proved in `Proof/os/Remove.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The entry of an unlink of the file `i` at `b` in `j`, by a call begun at `s`. -/
def rmFileEnt (j : Ino) (b : GoString) (i : Ino) (s : Nat) : LogEntry :=
  ⟨.remove j b (.file i), s⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The claim on `b` after an unlink's outcome, with fraction `dq`. -/
def rmFileOut (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (dq : DFrac)
    (o : Option (Nat × Nat)) : IProp GF :=
  iprop(logOut h.next (rmFileEnt j b i) o ∗
    claimOut j (.only [b]) dq h (rmFileEnt j b i) (restrictN (.only [b]) (GMap.delete b h.cur)) o)

/-- See the file header. -/
abbrev os.Remove.specFileS : Prop :=
  ∀ (d b : GoString) (j i : Ino) (R : Roots) (dq : DFrac) (h : NamesH) (q r qc : Qp)
    (Q : Option (Nat × Nat) → IProp GF),
  NameOk b → h.cur !! b = some (.file i) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (rmFileOut j b i h (DFrac.own r)) Q }}
    (App (Val (@! os.Remove)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ rmFileOut j b i h (DFrac.own q) o }}

/-- `specFileS` with `osAUnc` (`Proof/os/SharedAu.lean`): its opening gets the generation's
`notCrashed`, so a client can open an invariant with a crash branch (the WAL's `walInv`) at it; it
gives `specFileS` (`osAU_osAUnc`). -/
abbrev os.Remove.specFileSnc : Prop :=
  ∀ (d b : GoString) (j i : Ino) (R : Roots) (dq : DFrac) (h : NamesH) (q r qc : Qp)
    (Q : Option (Nat × Nat) → IProp GF),
  NameOk b → h.cur !! b = some (.file i) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAUnc (osNames j (.only [b]) (DFrac.own r) h) (rmFileOut j b i h (DFrac.own r)) Q }}
    (App (Val (@! os.Remove)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ rmFileOut j b i h (DFrac.own q) o }}

end spec

end EtcdGrove
end Perennial
