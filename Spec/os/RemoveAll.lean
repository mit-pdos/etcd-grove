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
* `os.RemoveAll.specSubS` (step 2 (D) of `notes/wal-units/tester.md`'s handoffs): `d/b` holding
  anything (nothing, a file, or a directory with any subtree), with the whole claims `cl` of every
  directory under it (`SubCover`), among which no cycle (`ClRanked`), the whole claim on `b` and
  the whole call permission: the claims back, each holding some of the entries it held (`ClsSub`),
  and `b` as it was or gone (`EntsSub`); the error `nil` or `fmtErrorOk`. The error says nothing of
  which (as for `specDirS`), unless the file system does not fail on `d/b` and on `d`
  (`FsNoErrAt`, `GooseLang/Ext/Fs/NoErrRemoveSteps.lean`): then `nil` only with `b` gone (wal-safe,
  2026-11-22, design (FNE): every `nil` exit of the model is an `unlink`/`rmdir` of `d/b` answering 0
  or `ENOENT`, the parent's `open` answering `ENOENT`, or a read of `d/b` answering `ENOENT`; with
  `d/b` and `d` covered, each happens only with `b` gone).

Proved in `Proof/os/RemoveAll.lean` (`specSubS`: `Proof/os/RemoveAllSub.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.PkgInit
public import Proof.os.SharedAu
public import Spec.fmt.ErrorOk
public import GooseLang.Ext.Fs.NoErrRemoveSteps

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

/-- **`J'` is a directory under `J` through the claims `cl`**: each step a name of a directory whose
whole claim (`except []`) is in `cl` holding the next directory. (Moved from the WAL's `CreateDefs`.) -/
inductive ClReach (cl : List Claim) : Ino → Ino → Prop
  | refl (J : Ino) : ClReach cl J J
  | step (J J' J'' : Ino) (h : NamesH) (b : GoString) :
      (J, NameSet.except [], h) ∈ cl → h.cur !! b = some (.dir J') → ClReach cl J' J'' →
      ClReach cl J J''

/-- **The claims `cl` cover the subtree of the entry `e`**: every directory under it has its whole
claim in `cl`. (Moved from the WAL's `CreateDefs`.) -/
def SubCover (cl : List Claim) (e : Option Node) : Prop :=
  ∀ J, e = some (.dir J) → ∀ J', ClReach cl J J' → ∃ h, (J', NameSet.except [], h) ∈ cl

/-- **The claims `cl` hold no cycle**: a rank on directories that grows along every entry of a claim
of `cl` naming a directory. (A tree's directories have one, their depth; `RemoveAll`'s recursion
needs it to know that a directory below another is not that one.) -/
def ClRanked (cl : List Claim) : Prop :=
  ∃ rk : Ino → Nat, ∀ c ∈ cl, ∀ x K, c.2.2.cur !! x = some (.dir K) → rk c.1 < rk K

/-- What a claim is on: its directory and names. -/
def clKey (c : Claim) : Ino × NameSet := (c.1, c.2.1)

/-- **`cl'` is `cl` after removals**: the same claims in the same order (directories and names), each
holding some of the entries it held. -/
def ClsSub : List Claim → List Claim → Prop
  | [], [] => True
  | c' :: cl', c :: cl => clKey c' = clKey c ∧ EntsSub c'.2.2.cur c.2.2.cur ∧ ClsSub cl' cl
  | _, _ => False

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j (.only [b]) dqn h ∗ osCallPerm (callKey R d) qc }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osNames j (.only [b]) dqn h ∗
      osCallPerm (callKey R d) qc ∗ fmtErrorOkOrNil err }}

/-- See the file header. -/
abbrev os.RemoveAll.specDirS : Prop :=
  ∀ (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp) (h hJ : NamesH),
  NameOk b → h.cur !! b = some (.dir J) → FilesOnly hJ.cur →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
      osCallPerm (callKey R d) 1 }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) 1 ∗
      rmAllOut j b J h hJ ∗ fmtErrorOkOrNil err }}

/-- The whole claims `cl`. -/
def osClaimsW (cl : List Claim) : IProp GF :=
  iprop([∗list] c ∈ cl, osNames c.1 c.2.1 (DFrac.own 1) c.2.2)

/-- See the file header. -/
abbrev os.RemoveAll.specSubS : Prop :=
  ∀ (d b : GoString) (j : Ino) (R : Roots) (qd : Qp) (h : NamesH) (cl : List Claim),
  NameOk b → SubCover cl (h.cur !! b) → ClRanked cl →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j (.only [b]) (DFrac.own 1) h ∗ osClaimsW cl ∗ osCallPerm (callKey R d) 1 }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) 1 ∗
      (∃ (h' : NamesH) (cl' : List Claim), osNames j (.only [b]) (DFrac.own 1) h' ∗ osClaimsW cl' ∗
        ⌜EntsSub h'.cur h.cur ∧ ClsSub cl' cl ∧
          (err = interface.nil → FsNoErrAt (child d b) → FsNoErrAt d → h'.cur !! b = none)⌝) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
