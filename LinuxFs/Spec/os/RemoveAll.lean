/-
`os.RemoveAll(path)` (this repository's `os`, part `LinuxFs`) in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`, "Implementation log,
`os.RemoveAll`"), for the WAL's uses (`wal.go`'s `Create`: `RemoveAll(dir.tmp)` of a leftover
temporary directory, and the deferred one; `renameWAL`: `RemoveAll(dir)`, a no-op when `dir` is
absent). The model (`TrustedCode/os.lean`, `RemoveAll.impl`, `model.removeAllFrom`) holds a guard
call for the whole call (`CallBegin` at the start, `LstatDir` at the end), unlinks then `rmdir`s the
path, and on a directory opens the parent and runs `removeAllFrom`: passes, an arbitrary number of
them, each reading the directory's names and removing each (recursively: a file entry is
`unlink`ed), then an `rmdir`.

Plain triples, no atomic update: the removal is not one step (each `unlink` of an entry logs), and
the WAL's uses need none. `dir.tmp` is the program's before `Create` publishes it (its claims whole,
`walAreaRes`), not under the WAL's crash invariant; `dir` is absent when `renameWAL` removes it
(nothing logged, the claim's fraction suffices).

* `os.RemoveAll.specAbsentS`: `d/b`, `b` absent (a fraction of its claim, any fraction of the call
  permission): nothing changes; the error is `nil` or `fmtErrorOk`.
* `os.RemoveAll.specDirS`: `d/b` holds the directory `J` whose entries are all files (the whole
  claims on `b` and on `J`'s names, the whole call permission): `rmAllOut`, what the model allows:
  some of `J`'s files removed (its claim's entries a part of what they were), and `b` either as it
  was or its `rmdir` logged, after which `J` is empty. The error says nothing of which: the
  extension's failures may return any errno with no effect, `ENOENT` included, which `RemoveAll`
  takes for success (`nil` with `b` still there), and the last `rmdir` may fail after the files are
  gone. The error is `nil` or `fmtErrorOk`. Not covered: a directory holding subdirectories (the
  recursion below one level), and `b` a file.

Proved in `Proof/os/RemoveAll.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.SharedAu
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The entry of an `rmdir` of the directory `J` at `b` in `j`, by a call begun at `s`. -/
def rmDirEnt (j : Ino) (b : GoString) (J : Ino) (s : Nat) : LogEntry :=
  ⟨.remove j b (.dir J), s⟩

/-- Every entry of the names `e` is a file. -/
def FilesOnly (e : Ents) : Prop := ∀ c n, e !! c = some n → ∃ i, n = .file i

/-- The entries `e'` are some of `e`'s. -/
def EntsSub (e' e : Ents) : Prop := ∀ c n, e' !! c = some n → e !! c = some n

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- **After `RemoveAll(d/b)` of the directory `J`** (`b` in `j`, the claims' histories `h`, `hJ`
before): the whole claims on `b` and on `J`'s names; `J`'s entries some of what they were; `b` as it
was, or its `rmdir` logged (at `x`, by a call begun at `s`), `J` then empty. -/
def rmAllOut (j : Ino) (b : GoString) (J : Ino) (h hJ : NamesH) : IProp GF :=
  iprop(∃ (h' hJ' : NamesH), osNames j (.only [b]) (DFrac.own 1) h' ∗
    osNames J (.except []) (DFrac.own 1) hJ' ∗ ⌜EntsSub hJ'.cur hJ.cur⌝ ∗
    (⌜h' = h⌝ ∨ ∃ x s, osLogged x (rmDirEnt j b J s) ∗
      ⌜h' = h.log x (rmDirEnt j b J s) (restrictN (.only [b]) (GMap.delete b h.cur)) ∧
        hJ'.cur = ∅⌝))

/-- See the file header. -/
abbrev os.RemoveAll.specAbsentS : Prop :=
  ∀ (d b : GoString) (j : Ino) (R : Roots) (qd : Qp) (dqn : DFrac) (h : NamesH) (qc : Qp),
  NameOk b → h.cur !! b = none →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j (.only [b]) dqn h ∗ osCallPerm qc }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osNames j (.only [b]) dqn h ∗
      osCallPerm qc ∗ fmtErrorOkOrNil err }}

/-- See the file header. -/
abbrev os.RemoveAll.specDirS : Prop :=
  ∀ (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp) (h hJ : NamesH),
  NameOk b → h.cur !! b = some (.dir J) → FilesOnly hJ.cur →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
      osCallPerm 1 }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm 1 ∗
      rmAllOut j b J h hJ ∗ fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
