/- Lean-first (no Rocq counterpart). `Open(path)` (`examples/osfs/bboltfs/minibolt.go`): opens (or creates) the database at `path`, given the file there as `dbFile` describes it, whose current transaction is `t`, holding `vo`: no file, or a file of whole bytes that `fileOk` accepts (`dbFresh`: `init` lays out a file shorter than four pages or with no valid meta, at transaction 1 with no value; otherwise its current meta is read), or what a `Close` gives back (`dbStored`: committed pages as discarded `pageIs`, the meta pages clean, the current root page holding `vo`). Either way no mapping of the file, and no byte lost by a failed sync (`ok`). The client also gives `pkgFacts` (for the package's `isPkgInit`, see `DB.lean`). The client also gives the predicate `vp` the transactions' values must satisfy (`dbTx`, `Commit`), which `vo` does. On success, an open database (`isDB`) on `path` (`db.path`, which `Close` gives back) at transaction `t` holding `vo` (`dbTx`), whose predicate is `vp`, its committer token at `t` and the high water mark `n`, a lower bound of the txid. `isDB` holds the pool of `mmaplock`'s reader slots, which `Open` builds (with `threadBound GF ≤ 2 ^ 30`, `ThreadBoundLe`): a reader brings its thread token (`Get`, `Snapshot`). On an error, the file is closed, and its `OsMeta` is that of the path after an open (it may have been created); its bytes are lost to the caller (a crash proof would keep them).

The database file lives in the directory tree: `path` is `d/b`, `d` a directory of the tree
`(R, V)`, of which the caller gives the whole history (the open may create the file); the history
comes back, with the create logged if it made the file, and the database's file is the one the
path then names (`γ.ino`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section pure
variable [GooseExts]

/-- The current transaction of a fresh file of bytes `xs` once opened, its value, and the high
water mark: a file of four pages or more with a valid meta (an open database's, by `fileOk`) is at
its current meta, whose root page holds the value; any other file is laid out by `init`, at
transaction 1 with no value and high water mark 4. -/
def freshTx (xs : List (w8 × Bool)) : Nat × Option w64 × Nat :=
  let mp := (xs.map Prod.fst).take 8192
  if 4 * 4096 ≤ xs.length ∧ (metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1)) then
    ((curMeta mp).txid'.toNat, pageVal (((xs.map Prod.fst).drop (4096 * curRoot mp)).take 4096),
      curPgid mp)
  else (1, none, 4)

/-- The facts of a stored database (`dbStored`): the whole `OsMeta` `m`, the meta pages' bytes
`mxc` (clean, an open database's `mp`), the bytes `tail` from the high water mark on; at least
four pages and at most 1 GiB (as an open database keeps it), no mapping, no byte lost by a failed sync. -/
def storedOk (m : OsMeta) (mp : List w8) (mxc tail : List (w8 × Bool)) : Prop :=
  mxc.map Prod.fst = mp ∧ (∀ x ∈ mxc, x.2 = true) ∧ metaPagesOk mp ∧
    4096 * curPgid mp ≤ m.size ∧ tail.length = m.size - 4096 * curPgid mp ∧
    m.ok = true ∧ m.maps = ∅ ∧ 4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 30

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- The bytes `xs` of a fresh file (of `OsMeta` `m`): whole, at most 1 GiB, accepted by `fileOk`,
at transaction `t` holding `vo`, high water mark `n` (`freshTx`), no mapping, no lost byte. -/
def FreshOk (m : OsMeta) (xs : List (w8 × Bool)) (t : Nat) (vo : Option w64) (n : Nat) : Prop :=
  xs.length = m.size ∧ m.maps = ∅ ∧ m.ok = true ∧ m.size ≤ 2 ^ 30 ∧ fileOk xs ∧
    freshTx xs = (t, vo, n)

/-- No file at the path `p` of the tree `(R, V)`, at transaction 1 with no value (`freshTx []`), or
a file there of inode `i` whose whole bytes `xs` are `FreshOk`. -/
def dbFresh (R : Roots) (V : Hist) (p : GoString) (t : Nat) (vo : Option w64) (n : Nat) : IProp GF :=
  iprop((⌜lookupH R V p = none ∧ freshTx [] = (t, vo, n)⌝) ∨
    ∃ (i : Ino) (m : OsMeta) (xs : List (w8 × Bool)), ⌜lookupH R V p = some (.file i)⌝ ∗
      osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes (GF := GF) i 0 (DFrac.own 1) xs ∗
      ⌜FreshOk m xs t vo n⌝)

/-- A stored database, the file of inode `i` (as `Close` leaves it, `dbClosed`) at transaction `t`
holding `vo`, high water mark `n`, besides its `OsMeta` `m`: the meta pages' bytes, the committed
pages (`pageIs`), the current root page holding `vo`, and the bytes from the high water mark on
(`storedOk`). -/
def dbStoredAt (i : Ino) (t : Nat) (vo : Option w64) (n : Nat) (m : OsMeta) : IProp GF :=
  iprop(∃ (mp : List w8) (mxc tail : List (w8 × Bool)) (B : List w8),
    osBytes (GF := GF) i 0 (DFrac.own 1) mxc ∗
    ([∗list] r ∈ List.range' 2 (curPgid mp - 2), ∃ B', pageIs (GF := GF) i r B') ∗
    osBytes (GF := GF) i (4096 * curPgid mp) (DFrac.own 1) tail ∗
    pageIs (GF := GF) i (curRoot mp) B ∗
    ⌜storedOk m mp mxc tail ∧ (curMeta mp).txid'.toNat = t ∧ pageVal B = vo ∧ curPgid mp = n⌝)

/-- A stored database, the file of inode `i`, with the whole of its `OsMeta` (`dbStoredAt`). -/
def dbStored (i : Ino) (t : Nat) (vo : Option w64) (n : Nat) : IProp GF :=
  iprop(∃ m : OsMeta, osMeta (GF := GF) i (DFrac.own 1) m ∗ dbStoredAt (GF := GF) i t vo n m)

/-- The file `Open` opens at the path `p` of the tree `(R, V)`, at transaction `t` holding `vo`,
high water mark `n` (see the file header). -/
def dbFile (R : Roots) (V : Hist) (p : GoString) (t : Nat) (vo : Option w64) (n : Nat) : IProp GF :=
  iprop(dbFresh (GF := GF) R V p t vo n ∨
    ∃ i : Ino, ⌜lookupH R V p = some (.file i)⌝ ∗ dbStored (GF := GF) i t vo n)

/-- What a failed `Open` leaves at the path `p` of the tree `(R, V)`: the file of inode `i` there
(it may have been created), with its `OsMeta`, or nothing. -/
def openFail (R : Roots) (V : Hist) (p : GoString) : IProp GF :=
  iprop((∃ (i : Ino) (m : OsMeta), ⌜lookupH R V p = some (.file i)⌝ ∗
    osMeta (GF := GF) i (DFrac.own 1) m) ∨ ⌜lookupH R V p = none⌝)

/-- See the file header. -/
abbrev Open.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (d b : GoString) (R : Roots) (V : Hist) (j : Ino) (t : Nat)
    (vo : Option w64) (n : Nat) (vp : Nat → Option w64 → Prop),
  RootsOk R → NameOk b → lookupH R V d = some (.dir j) → vp t vo →
  {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own 1) R V ∗
      dbFile (GF := GF) R V (child d b) t vo n }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Open)) (Val #(child d b)))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); ∃ V' : Hist,
      osTree (DFrac.own 1) R V' ∗
      ((⌜err = interface.nil⌝ ∗ ∃ γ : DBNames, ⌜γ.vp = vp ∧ lookupH R V' (child d b) = some (.file γ.ino) ∧
          lookupH R V' d = some (.dir j)⌝ ∗
          isDB (GF := GF) γ db ∗ db.[DB, go!"path"] ↦□ (child d b) ∗ dbOwner (GF := GF) γ t n ∗
          dbLast (GF := GF) γ t ∗ dbTx (GF := GF) γ t vo) ∨
      (⌜err ≠ interface.nil ∧ db = null⌝ ∗ openFail (GF := GF) R V' (child d b))) }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
