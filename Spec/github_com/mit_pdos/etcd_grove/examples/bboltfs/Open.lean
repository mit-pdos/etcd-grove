/- Lean-first (no Rocq counterpart). `Open(path)` (`examples/bboltfs/minibolt.go`): opens (or creates) the database at `path`, given the file there as `dbFile` describes it, whose current transaction is `t`, holding `vo`: no file, or a file of whole bytes that `fileOk` accepts (`dbFresh`: `init` lays out a file shorter than four pages or with no valid meta, at transaction 1 with no value; otherwise its current meta is read), or what a `Close` gives back (`dbStored`: committed pages as discarded `pageIs`, the meta pages clean, the current root page holding `vo`). Either way no mapping of the file, and no byte lost by a failed sync (`ok`). The client also gives `pkgFacts` (for the package's `isPkgInit`, see `DB.lean`). On success, an open database (`isDB`) at transaction `t` holding `vo` (`dbTx`), its committer token at `t` and the high water mark, a lower bound of the txid, and every reader token. On an error, the file is closed, and its `OsMeta` is that of the path after an open (it may have been created); its bytes are lost to the caller (a crash proof would keep them). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- The current transaction of a fresh file of bytes `xs` once opened, and its value: a file of
four pages or more with a valid meta (an open database's, by `fileOk`) is at its current meta,
whose root page holds the value; any other file is laid out by `init`, at transaction 1 with no
value. -/
def freshTx (xs : List (w8 × Bool)) : Nat × Option w64 :=
  let mp := (xs.map Prod.fst).take 8192
  if 4 * 4096 ≤ xs.length ∧ (metaValid (fileMeta mp 0) ∨ metaValid (fileMeta mp 1)) then
    ((curMeta mp).txid'.toNat, pageVal (((xs.map Prod.fst).drop (4096 * curRoot mp)).take 4096))
  else (1, none)

/-- The facts of a stored database (`dbStored`): the whole `OsMeta` `m`, the meta pages' bytes
`mxc` (clean, an open database's `mp`), the bytes `tail` from the high water mark on; at least
four pages and at most 1 TiB (`mmap`'s bound), no mapping, no byte lost by a failed sync. -/
def storedOk (m : OsMeta) (mp : List w8) (mxc tail : List (w8 × Bool)) : Prop :=
  mxc.map Prod.fst = mp ∧ (∀ x ∈ mxc, x.2 = true) ∧ metaPagesOk mp ∧
    4096 * curPgid mp ≤ m.size ∧ tail.length = m.size - 4096 * curPgid mp ∧
    m.ok = true ∧ m.maps = ∅ ∧ 4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 40

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- No file at `p`, or a file of whole bytes `xs` that `fileOk` accepts, at most 1 GiB, at
transaction `t` holding `vo` (`freshTx`). -/
def dbFresh (p : GoString) (t : Nat) (vo : Option w64) : IProp GF :=
  iprop(∃ (mo : Option OsMeta) (xs : List (w8 × Bool)),
    osMeta (GF := GF) p (DFrac.own 1) mo ∗
    (match mo with
     | none => emp
     | some _ => osBytes (GF := GF) p 0 (DFrac.own 1) xs) ∗
    ⌜(mo = none → xs = []) ∧
      (∀ m, mo = some m → xs.length = m.size ∧ m.maps = ∅ ∧ m.ok = true ∧ m.size ≤ 2 ^ 30 ∧
        fileOk xs) ∧
      freshTx xs = (t, vo)⌝)

/-- A stored database at `p` (as `Close` leaves it, `dbClosed`) at transaction `t` holding `vo`,
besides its `OsMeta` `m`: the meta pages' bytes, the committed pages (`pageIs`), the current root
page holding `vo`, and the bytes from the high water mark on (`storedOk`). -/
def dbStoredAt (p : GoString) (t : Nat) (vo : Option w64) (m : OsMeta) : IProp GF :=
  iprop(∃ (mp : List w8) (mxc tail : List (w8 × Bool)) (B : List w8),
    osBytes (GF := GF) p 0 (DFrac.own 1) mxc ∗
    ([∗list] r ∈ List.range' 2 (curPgid mp - 2), ∃ B', pageIs (GF := GF) p r B') ∗
    osBytes (GF := GF) p (4096 * curPgid mp) (DFrac.own 1) tail ∗
    pageIs (GF := GF) p (curRoot mp) B ∗
    ⌜storedOk m mp mxc tail ∧ (curMeta mp).txid'.toNat = t ∧ pageVal B = vo⌝)

/-- A stored database at `p`, with the whole of its `OsMeta` (`dbStoredAt`). -/
def dbStored (p : GoString) (t : Nat) (vo : Option w64) : IProp GF :=
  iprop(∃ m : OsMeta, osMeta (GF := GF) p (DFrac.own 1) (some m) ∗ dbStoredAt (GF := GF) p t vo m)

/-- The file `Open` opens, at transaction `t` holding `vo` (see the file header). -/
def dbFile (p : GoString) (t : Nat) (vo : Option w64) : IProp GF :=
  iprop(dbFresh (GF := GF) p t vo ∨ dbStored (GF := GF) p t vo)

/-- See the file header. -/
abbrev Open.spec : Prop :=
  ∀ (path : GoString) (t : Nat) (vo : Option w64),
  {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ dbFile (GF := GF) path t vo }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.Open)) (Val #path))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err);
      (⌜err = interface.nil⌝ ∗ ∃ (γ : DBNames) (n : Nat),
          isDB (GF := GF) γ db ∗ dbOwner (GF := GF) γ t n ∗ dbLast (GF := GF) γ t ∗
          dbTx (GF := GF) γ t vo ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            dbReader (GF := GF) γ db)) ∨
      (⌜err ≠ interface.nil ∧ db = null⌝ ∗ ∃ mo', osMeta (GF := GF) path (DFrac.own 1) mo') }}

end spec

end bboltfs
end EtcdGrove
end Perennial
