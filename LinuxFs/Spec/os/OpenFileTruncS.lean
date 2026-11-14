/-
`os.OpenFile(d/b, flag, perm)`, `flag` with `O_CREATE` and `O_TRUNC` (the WAL's `filePipeline.alloc`,
`O_CREATE|O_TRUNC|O_WRONLY` of `N.tmp`), of an absent name (this repository's `os`, part `LinuxFs`),
in the tree's shared mode (`GooseLang/Ext/Fs/TreeShared.lean`): logically atomic, as
`os.OpenFile.specCreateS` (`Spec/os/OpenFileS.lean`). The atomic update commits at the step that
creates the file (outcome `some (x, s, i)`) or at the step that ends the call with an error and no
effect (`none`); an `EINTR` with no effect aborts it. An attempt that created the file and returned
`EINTR` is retried, and the retry truncates the file it made (`wp_osOpenTruncS`), which changes
only the file's data.

* `os.OpenFile.specCreateTruncS`: `b` holds nothing in `d`'s directory `j`. The new file goes to the
  caller as `trFile i P`: its `OsMeta` whole, its bytes, the client's halves of its mapped cells,
  and on success (`P`: the error is nil) its size 0.

Proved in `Proof/os/OpenFileTruncS.lean`, over `wp_osOpenCreateS'` and `wp_osOpenTruncS`
(`GooseLang/Ext/Fs/TreeSharedTrunc.lean`). The open of a name holding a file with `O_TRUNC` (a
leftover `N.tmp`) changes no claim: a plain triple, `os.OpenFile.wp_truncS` in the same proof file.
Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.os.OpenFileS
public import GooseLang.Ext.Fs.TreeSharedTrunc

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

/-- The file `i`, held whole by its owner: its `OsMeta`, its bytes, the client's halves of its
mapped cells (none: the file is not mapped, `m.maps = ∅`, as a file this process created and never
mmapped; a truncation keeps the mappings); its size 0 if `P`; no sync without its bytes (`OsMeta.cut`
none) and a crash's lower size bound at most the size (a new file's `newMeta`; a truncation to 0 sets
it to 0). What an `O_TRUNC` open takes and gives. -/
def trFile (i : Ino) (P : Prop) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
    osBytes i 0 (DFrac.own 1) xs ∗ mcellsAny (GF := GF) m.maps 0 m.size ∗
    ⌜xs.length = m.size ∧ (P → m.size = 0) ∧ m.maps = ∅ ∧ m.cut = none ∧ m.lo ≤ m.size⌝)

/-- The new file after an outcome. -/
def crTr (P : Prop) : Option (Nat × Nat × Ino) → IProp GF
  | none => iprop(emp)
  | some (_, _, i) => trFile i P

/-- See the file header. -/
abbrev os.OpenFile.specCreateTruncS : Prop :=
  ∀ (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH)
    (q r qc : Qp) (Q : Option (Nat × Nat × Ino) → IProp GF),
  OpenFlagsOk (flag ||| W64 0x80000).toNat → (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1 →
  (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 1 →
  NameOk b → h.cur !! b = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, Q o ∗ crOut j b h (DFrac.own q) o ∗ crTr (err = interface.nil) o ∗
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }}

/-- `specCreateTruncS` with `osAUnc` (`Proof/os/SharedAu.lean`): its opening gets the generation's
`notCrashed`, so a client can open an invariant with a crash branch (the WAL's `walInv`) at it; it
gives `specCreateTruncS` (`osAU_osAUnc`). -/
abbrev os.OpenFile.specCreateTruncSnc : Prop :=
  ∀ (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH)
    (q r qc : Qp) (Q : Option (Nat × Nat × Ino) → IProp GF),
  OpenFlagsOk (flag ||| W64 0x80000).toNat → (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1 →
  (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 1 →
  NameOk b → h.cur !! b = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAUnc (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ o, Q o ∗ crOut j b h (DFrac.own q) o ∗ crTr (err = interface.nil) o ∗
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }}

end spec

end EtcdGrove
end Perennial
