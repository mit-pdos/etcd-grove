/- Lean-first (no Rocq counterpart).

# C-I1's laws as theorems (W3 of `plans/bbolt-crash-plan.md`; in progress)

`CrashInterim.lean`'s opaque `dbCrashKeep`/`dbCrashHole` as definitions over bbolt's sealed crash record
(`Spec/go_etcd_io/bbolt/ApiCrash.lean`: `boltCrashRec`, `boltCrashHole`), and its laws proved with their
statements unchanged (namespace `backend.crashLaws`, so that the text is the axioms'; the swap moves
them into `backend` and deletes the axioms). Done: `dbCrashKeep_take`, `_putSame`, `_putStep`,
`_close`. Open: `_new` (needs the writer's synced mark in `boltTx`, and `bbolt.TailsZeroOnOpen`, its
one extra hypothesis) and `dbCrash` (the crash invariant's crash lemma `csInvIR_crash_keep`, the
version agreement and the crashed file's receipt). **Statement issue**: the definitions are over
`onFs`, which needs `go.Semantics` (`FsCtx`'s field facts mention `GoSemanticsFunctions`); the
opaque `dbCrashKeep` takes none, and `dbCrash`'s statement has none in scope, so `dbCrash` needs
`[sem : go.Semantics]` added (its one caller, `MemberCrash.lean`, has it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DbOpts
public import Spec.go_etcd_io.bbolt.ApiCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend
namespace crashLaws

open Iris Iris.BI Iris.ProofMode

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

end laws

end crashLaws
end backend
end EtcdGrove
end Perennial
