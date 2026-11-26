/- Lean-first (no Rocq counterpart).

# C-I1: bbolt's file after a power loss, at the backend's interface (proved)

The crash record `dbCrashKeep γ i0 Dl Dn` of the open database `γ` (its file the inode `i0`, its committed
data `Dn`, the data `Dl` its file falls back to if the commit that made `Dn` did not reach the disk) and
the hole `dbCrashHole` it leaves while its half is lent to `Tx.Commit`'s update, defined as bbolt's
sealed crash record (`Spec/go_etcd_io/bbolt/ApiCrash.lean`: `boltCrashRec`, `boltCrashHole`) under
`onFs`; and the six laws of it, theorems from bbolt's crash proof over the file extension:
`dbCrashKeep_new` (a record from a fresh write transaction, under `dbOpts`), `_take`, `_putSame`,
`_putStep` (the half lent for one update and put back at the same or the next version), `_close`, and
`dbCrash` (after a power loss, the inode holds `Dl` or `Dn`, every byte durable: `bbolt.fileHoldsMDur`).

**What it rests on.** The crash premise `BoltCrashWhole` (`dbCrash`'s `hQ`, one definition,
`Spec/go_etcd_io/bbolt/CrashPremise.lean`: a torn meta page that validates is one change's, FNV-64a
collision aside), `dbOpts`'s producer (the axiom `storage.OpenBackend`, `DbOpts.lean`), and the file
extension's crash semantics. A record exists only for a database past `Open` (`init`'s window is outside
it: `issues/bbolt-init-not-crash-safe.md`). Reviews of the laws' statements:
`notes/axiom-review/c-i1-bbolt-crash.md`, `c-i1-takeput.md`, `c-i1-nopath.md`, `c-i1-monotone.md`.

**Statements.** Each law is the former interim axiom's text, except `dbCrash`, which takes
`[sem : go.Semantics]` at the old generation's context (the record is over `onFs`, which needs it) and
concludes `fileHoldsMDur` (`bbolt.fileHoldsMDur_holds` gives the axiom's `fileHoldsM`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DbOpts
public import Spec.go_etcd_io.bbolt.ApiCrash
public import Spec.go_etcd_io.bbolt.CrashPremise
public import GooseLang.Ext.Fs.CrashTok

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode

/-- (C-I1) **The crash premise** (`dbCrash`'s `hQ`): bbolt's `BoltCrashWhole`
(`Spec/go_etcd_io/bbolt/CrashPremise.lean`, which states it and its evidence; one definition). The
checksum bytes are as of a change no later than the fields' (review `notes/axiom-review/c-i1-monotone.md`). -/
abbrev BoltCrashWhole (I : Fs.Ino → Prop) (st st' : Fs.OsState) : Prop :=
  bbolt.BoltCrashWhole I st st'

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- (C-I1) **The crash record of the open database `γ`, whose file is the inode `i0`** (exclusive): its
committed data `Dn` (with the commit invariant's half) and the data `Dl` its file falls back to; it claims
no name (`notes/axiom-review/c-i1-nopath.md`). bbolt's `boltCrashRec` at the program's file-extension
instances. -/
def dbCrashKeep [hG : HeapGS hlc GF] [sem : go.Semantics] (γ : DBNames) (i0 : Fs.Ino) (Dl Dn : Data) : IProp GF :=
  onFs (GF := GF) iprop(bbolt.boltCrashRec γ i0 Dl Dn)

/-- (C-I1) **The record with its half lent at version `ν`** (`dbCrashKeep_take`), for one update of
`Tx.Commit`: bbolt's `boltCrashHole`. -/
def dbCrashHole [hG : HeapGS hlc GF] [sem : go.Semantics] (γ : DBNames) (i0 : Fs.Ino) (Dl Dn : Data) (ν : Nat) :
    IProp GF :=
  onFs (GF := GF) iprop(bbolt.boltCrashHole γ i0 Dl Dn ν)

end preds

section laws
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- (C-I1) **The half lent for `Tx.Commit`'s update**: the half at its version `ν`, and the hole that
remembers `ν`. -/
theorem dbCrashKeep_take [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) :
    dbCrashKeep (GF := GF) γ i0 Dl Dn ⊢ ∃ ν, dbHalfV γ Dn ν ∗ dbCrashHole γ i0 Dl Dn ν := by
  unfold dbCrashKeep dbCrashHole dbHalfV onFs
  split
  · rename_i c _
    letI := c.S; letI := c.ok; letI := c.has
    exact bbolt.boltCrashRec_take γ i0 Dl Dn
  · iintro %h; exact h.elim

/-- (C-I1) **The half back unchanged** (the update aborted): the same version, so no commit took
place. -/
theorem dbCrashKeep_putSame [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) (ν : Nat) :
    dbCrashHole (GF := GF) γ i0 Dl Dn ν ∗ dbHalfV γ Dn ν ⊢ dbCrashKeep γ i0 Dl Dn := by
  unfold dbCrashKeep dbCrashHole dbHalfV onFs
  split
  · rename_i c _
    letI := c.S; letI := c.ok; letI := c.has
    exact bbolt.boltCrashRec_putSame γ i0 Dl Dn ν
  · iintro ⟨%h, -⟩; exact h.elim

open Classical in
/-- (C-I1) **The half back after one commit** (`Tx.Commit.spec`'s update giving the data `S` at version
`ν + 1`): exactly one commit took place, from `Dn`; the fallback becomes `Dn` (or stays `Dl` when the
commit kept the data). -/
theorem dbCrashKeep_putStep [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (ν : Nat) :
    dbCrashHole (GF := GF) γ i0 Dl Dn ν ∗ dbHalfV γ S (ν + 1) ⊢
      dbCrashKeep γ i0 (if S = Dn then Dl else Dn) S := by
  unfold dbCrashKeep dbCrashHole dbHalfV onFs
  split
  · rename_i c _
    letI := c.S; letI := c.ok; letI := c.has
    exact bbolt.boltCrashRec_putStep γ i0 Dl Dn S ν
  · iintro ⟨%h, -⟩; exact h.elim

/-- (C-I1) **A crash record from a fresh write transaction**: with the database opened syncing
(`dbOpts`), its file the inode `i0` (`boltIno`), the commit invariant's half at the committed data `D`
and a live write transaction begun at `D`, the record at `(D, D)` (crash mode is on for every database
`Open` accepts, `bbolt.crashMode_on`; the writer carries the committed version's `synced` fact). -/
theorem dbCrashKeep_new [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (D : Data) (tx : Loc) :
    ⊢ dbOpts (hlc := HasLC.hasLC) (GF := GF) γ -∗ onFs (GF := GF) iprop(bbolt.boltIno γ i0) -∗
      dbHalf γ D -∗ txLive tx γ 1 (bbolt.TxView.wr D) ==∗
      dbCrashKeep γ i0 D D ∗ txLive tx γ 1 (bbolt.TxView.wr D) := by
  unfold dbOpts dbOptsRaw dbCrashKeep dbHalf txLive onFs
  split
  · rename_i c _
    letI := c.S; letI := c.ok; letI := c.has
    obtain ⟨Sio, hino, hpath, hs1, hs2⟩ := c.ne.ok
    have hfs : Fs.FsNoErr := Fs.fsNoErr_of Sio hino hpath
    iintro #Hsy #Hino Hh Ht
    imodintro
    iapply bbolt.boltCrashRec_new hfs γ i0 D tx $$ [Hh Ht]
    iframe; iframe #
  · iintro #H
    iexfalso; iexact H

/-- The record's half. -/
theorem dbCrashKeep_dbHalf [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) : dbCrashKeep (GF := GF) γ i0 Dl Dn ⊢ dbHalf γ Dn := by
  unfold dbCrashKeep dbHalf onFs
  split
  · rename_i c _
    letI := c.S; letI := c.ok; letI := c.has
    exact bbolt.boltCrashRec_close γ i0 Dl Dn
  · exact .rfl

/-- (C-I1) **The record closed**, holding a live write transaction begun at the committed `Dn`: the
half back (to close the database), and the transaction. -/
theorem dbCrashKeep_close [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (G : GoString → Nat) (tx : Loc) :
    dbCrashKeep γ i0 Dl Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G) ⊢
      dbHalf γ Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G) :=
  sep_mono_left (dbCrashKeep_dbHalf γ i0 Dl Dn)

/-- (C-I1) **bbolt's file after a power loss**: under the crash premise `BoltCrashWhole` for the
database's inode `i0`, from the old generation's record `(i0, Dl, Dn)`, its `crashed`, and the file
system's crash rest (with the files `Dx` other crash lemmas took, not `i0`) of a crash whose durable tree
still names `i0` (`Named`): the inode `i0` holds `Dl` or `Dn` at the new generation, whole, with its
txid's receipt, every byte durable and its size settled (`bbolt.fileHoldsMDur`), and the crash rest with
`i0` taken. The mask holds bbolt's crash invariant's namespace (`hE`). From bbolt's
`boltCrashRec_crash`, the record's instances being the program's (`HasExt.sem_eq`). -/
theorem dbCrash [S : ExtSemantics Fs.fsExt] [ok : Fs.FsSemOk] [has : HasExt Fs.fsExt] [G : GooseGlobalGS HasLC.hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF)
    [sem : @go.Semantics _ L.goose_go_local_context _] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data)
    (hQ : ∀ st st', Q st st' → BoltCrashWhole (· = i0) st st')
    (Dx : List Fs.Ino) (hi : i0 ∉ Dx) (V' : Fs.Hist) (hN : Fs.Named V'.now i0) (E : CoPset)
    (hE : (↑(bbolt.crashN γ.ns) : CoPset) ⊆ E := by simp) :
    ⊢ dbCrashKeep (hG := ⟨G, L⟩) γ i0 Dl Dn -∗ crashed (hC := L.goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) Dx false V' ={E}=∗
      ∃ D' : Data, ⌜D' = Dl ∨ D' = Dn⌝ ∗
        bbolt.fileHoldsMDur (hG := ⟨G, L'⟩) i0 D' ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) (i0 :: Dx) false V' := by
  unfold dbCrashKeep onFs
  split
  · rename_i c _
    obtain ⟨cS, cok, chas, -, -, -⟩ := c
    have e : cS = S := chas.sem_eq.symm.trans has.sem_eq
    subst e
    iintro H -
    iapply bbolt.boltCrashRec_crash Q L L' γ i0 Dl Dn hQ Dx hi V' hN E hE $$ H
  · iintro %h; exact h.elim

end laws

end backend
end EtcdGrove
end Perennial
