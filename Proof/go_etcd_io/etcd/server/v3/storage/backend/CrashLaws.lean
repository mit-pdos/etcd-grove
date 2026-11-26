/- Lean-first (no Rocq counterpart).

# C-I1's laws as theorems (W3 of `plans/bbolt-crash-plan.md`; in progress)

`CrashInterim.lean`'s opaque `dbCrashKeep`/`dbCrashHole` as definitions over bbolt's sealed crash record
(`Spec/go_etcd_io/bbolt/ApiCrash.lean`: `boltCrashRec`, `boltCrashHole`), and its laws proved with their
statements unchanged (namespace `backend.crashLaws`, so that the text is the axioms'; the swap moves
them into `backend` and deletes the axioms). Done: `dbCrashKeep_take`, `_putSame`, `_putStep`,
`_close`, `_new` (with the axiom's text since W7: crash mode is on for every file `Open` accepts, whose
meta tails `fileOK` gives) and `dbCrash` (the crash invariant's crash lemma `csInvIR_crash_keep`, the
version agreement and the crashed file's receipt). **Statement issue**: the definitions are over
`onFs`, which needs `go.Semantics` (`FsCtx`'s field facts mention `GoSemanticsFunctions`); the
opaque `dbCrashKeep` takes none, and `dbCrash`'s statement has none in scope, so `dbCrash` needs
`[sem : go.Semantics]` added (its one caller, `MemberCrash.lean`, has it).
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
namespace crashLaws

open Iris Iris.BI Iris.ProofMode

/-- (C-I1) The crash premise (as in `CrashInterim.lean`). -/
abbrev BoltCrashWhole (I : Fs.Ino → Prop) (st st' : Fs.OsState) : Prop :=
  bbolt.BoltCrashWhole I st st'

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- (C-I1) **The crash record of the open database `γ`, whose file is the inode `i0`**: bbolt's
`boltCrashRec` at the program's file-extension instances. -/
def dbCrashKeep [hG : HeapGS hlc GF] [sem : go.Semantics] (γ : DBNames) (i0 : Fs.Ino) (Dl Dn : Data) : IProp GF :=
  onFs (GF := GF) iprop(bbolt.boltCrashRec γ i0 Dl Dn)

/-- (C-I1) **The record with its half lent at version `ν`**: bbolt's `boltCrashHole`. -/
def dbCrashHole [hG : HeapGS hlc GF] [sem : go.Semantics] (γ : DBNames) (i0 : Fs.Ino) (Dl Dn : Data) (ν : Nat) :
    IProp GF :=
  onFs (GF := GF) iprop(bbolt.boltCrashHole γ i0 Dl Dn ν)

end preds

section laws
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

theorem dbCrashKeep_take [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) :
    dbCrashKeep (GF := GF) γ i0 Dl Dn ⊢ ∃ ν, dbHalfV γ Dn ν ∗ dbCrashHole γ i0 Dl Dn ν := by
  unfold dbCrashKeep dbCrashHole dbHalfV onFs
  split
  · rename_i c _
    letI := c.S; letI := c.ok; letI := c.has
    exact bbolt.boltCrashRec_take γ i0 Dl Dn
  · iintro %h; exact h.elim

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

/-- (C-I1, `dbCrashKeep_new`) **A crash record from a fresh write transaction** (crash mode is on,
`bbolt.crashMode_on`). -/
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

theorem dbCrashKeep_close [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (G : GoString → Nat) (tx : Loc) :
    dbCrashKeep γ i0 Dl Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G) ⊢
      dbHalf γ Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G) :=
  sep_mono_left (dbCrashKeep_dbHalf γ i0 Dl Dn)

/-- (C-I1, `dbCrash`) **bbolt's file after a power loss** (the axiom's statement, with
`[sem : go.Semantics]` among its binders, at the old generation's local context `L`: the record is
over `onFs`, which needs it; approved for the swap): from bbolt's `boltCrashRec_crash`, the record's instances being the program's
(`HasExt.sem_eq`). -/
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
        bbolt.fileHoldsM (hG := ⟨G, L'⟩) i0 D' ∗
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

end crashLaws
end backend
end EtcdGrove
end Perennial
