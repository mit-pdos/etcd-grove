/-
`os.Mkdir(name, perm)` (this repository's `os`, part `LinuxFs`) in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`, review finding M1): logically
atomic. The model (`TrustedCode/os.lean`) is `mkdir(2)` (the extension's `Mkdir`), each attempt
after its own `CallBegin`, retried on `EINTR`. A directory operation needs the whole call
permission (no other call in flight; `DirOpExcl`). The caller holds a fraction of the claim on
the name (`.only [b]`), the atomic update the rest: it commits at the step that logs the `mkdir`,
or at the step that ends the call with an error and no effect; an `EINTR` with no effect aborts it.
After the `mkdir` took effect and returned `EINTR`, the retry finds the name taken (the caller's
fraction keeps it so) and fails: the error is non-nil, the outcome the logged one.

* `os.Mkdir.specS`: `d/b` is free. Outcome `some (x, s, J)`: the `mkdir` of the new directory `J`
  logged at `x` by a call begun at `s`; the caller also gets the new directory's claim on all its
  names (whole, empty, `hJ.next = x + 1`). `none`: no effect, and the error non-nil.

Proved in `Proof/os/Mkdir.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The entry of a `mkdir` of the directory `J` at `b` in `j`, by a call begun at `s`. -/
def mkEnt (j : Ino) (b : GoString) (J : Ino) (s : Nat) : LogEntry := ⟨.mkdir j b J, s⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The claim on `b` after a `mkdir`'s outcome, with fraction `dq`. -/
def mkOut (j : Ino) (b : GoString) (h : NamesH) (dq : DFrac) : Option (Nat × Nat × Ino) → IProp GF
  | none => osNames j (.only [b]) dq h
  | some (x, s, J) => iprop(osLogged x (mkEnt j b J s) ∗
      osNames j (.only [b]) dq (h.log x (mkEnt j b J s) (<[b := .dir J]> h.cur)))

/-- The new directory's claim after a `mkdir`'s outcome. -/
def mkNew : Option (Nat × Nat × Ino) → IProp GF
  | none => iprop(emp)
  | some (x, _, J) => iprop(∃ hJ, osNames J (.except []) (DFrac.own 1) hJ ∗
      ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝)

/-- See the file header. -/
abbrev os.Mkdir.specS : Prop :=
  ∀ (d b : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH) (q r : Qp)
    (Q : Option (Nat × Nat × Ino) → IProp GF),
  NameOk b → h.cur !! b = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm 1 ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (mkOut j b h (DFrac.own r)) Q }}
    (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm 1 ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ mkOut j b h (DFrac.own q) o ∗ mkNew o }}

/-- `specS` with `osAUnc` (`Proof/os/SharedAu.lean`): its opening gets the generation's
`notCrashed`, so a client can open an invariant with a crash branch (the WAL's `walInv`) at it; it
gives `specS` (`osAU_osAUnc`). -/
abbrev os.Mkdir.specSnc : Prop :=
  ∀ (d b : GoString) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH) (q r : Qp)
    (Q : Option (Nat × Nat × Ino) → IProp GF),
  NameOk b → h.cur !! b = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm 1 ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAUnc (osNames j (.only [b]) (DFrac.own r) h) (mkOut j b h (DFrac.own r)) Q }}
    (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm 1 ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ mkOut j b h (DFrac.own q) o ∗ mkNew o }}

end spec

end EtcdGrove
end Perennial
