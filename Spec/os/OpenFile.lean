/-
`os.OpenFile(path, O_RDWR|O_CREATE, perm)` (this repository's `os`, project `bboltfs`), as
minibolt and the walfs examples open their files. The model (`TrustedCode/os.lean`) is the
extension's `Open` with `O_CLOEXEC` added, each attempt after its own `CallBegin`, retried on
`EINTR`; the path is resolved in the directory tree (`lookupH`, over the caller's history `V` and
roots `R`).

* `os.OpenFile.spec`: the path names a file, of inode `i`; with a fraction of the history, which
  comes back unchanged. On success a fresh `*os.File` on a fresh fd (non-negative, which `Truncate`
  needs), readable and writable, on `i`; on failure `nil` and a non-nil error.
* `os.OpenFile.specCreate`: the path is `d/b`, nothing there, `d` a directory `j`; with the whole
  history (the open may create). On success a new file of a fresh inode `i`, named `b` in `j` (its
  `create` logged), with its `OsMeta` (`newMeta`: empty, zeros past its size) and the fd; on failure
  `nil` and a non-nil error, and the file may have been created.

Proved in `Proof/os/OpenFile.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.OpenFile.spec : Prop :=
  ∀ (path : GoString) (perm : w32) (q : Qp) (R : Roots) (V : Hist) (i : Ino),
  lookupH R V path = some (.file i) →
  {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osTree (DFrac.own q) R V ∗
      ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd path (DFrac.own 1) ∗
          osFd fd (DFrac.own 1) ⟨i, true, true⟩) ∨
       ⌜err ≠ interface.nil ∧ f = null⌝) }}

/-- See the file header. -/
abbrev os.OpenFile.specCreate : Prop :=
  ∀ (d b : GoString) (perm : w32) (R : Roots) (V : Hist) (j : Ino),
  NameOk b → lookupH R V d = some (.dir j) → lookupH R V (child d b) = none →
  {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own 1) R V }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      (∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗
          osTree (DFrac.own 1) R (V.push ⟨.create j b i, V.2.length⟩) ∗
          osMeta i (DFrac.own 1) newMeta ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
          osFd fd (DFrac.own 1) ⟨i, true, true⟩) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗ (osTree (DFrac.own 1) R V ∨ ∃ i : Ino,
          osTree (DFrac.own 1) R (V.push ⟨.create j b i, V.2.length⟩) ∗
          osMeta i (DFrac.own 1) newMeta)) }}

end spec

end EtcdGrove
end Perennial
