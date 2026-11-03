/-
**The WAL, as the server uses it** (a trust-boundary API, 2026-11-03; approved by the user after
three review rounds, a `spec-reviewer` twice and the `axiom` skill: `notes/decisions.md`, "The WAL's
API"). Lean-first.

The contract over a `serverstorage.Storage` `st` writing the WAL `storage.walOf st`
(`isWalStorage`, sealed, one law per operation), and an opened WAL (`walOpened`, what `bootstrap`'s
contract gives). Its vocabulary (the records and their model, a directory's state, the purge's
right) is `storage/WalRecs.lean`.

NOT YET IN USE: R2b-1's next stage puts `isWalStorage` in place of today's `isRNWal`
(`InvRaftNode.lean`) in `NewStorage`'s contract (`rnNewStorageOk`), and `walOpened` in `bootstrap`'s
(`bootOk`), with the durability invariant the raft loop and the apply thread keep
(`InvWal.lean`), as the user approved (2026-11-03): (1) `NewStorage`'s contract gives this one;
(2) `bootstrap`'s first start takes `walDirFresh` and gives `walOpened … walFresh` and
`walPurgeRight`, the restart takes `walFiles` and gives `walOpened … σ` and `walPurgeRight` (scope:
`ForceNewCluster` off); (3) `srvFiles` is `∃ cid, walFiles (config.walDirOf dd "") id cid σ ∗` the
backend file; (4) `storage.Release` takes `walBaseLb`; (5) `purgeFile` takes and returns
`walPurgeRight`; (6) the examples' members start with their WAL directories fresh.

**What the WAL is to the server.** The server writes raft's durable state through a
`serverstorage.Storage` over a `*wal.WAL`: `Save(hs, ents)`, `SaveSnap(snap)` (the raft loop for a
received snapshot, the apply thread for its own), `Sync`, `Close` (the raft loop's `onStop`),
`Release` (after a snapshot; the server's purge then removes the WAL files no lock keeps). A
restart's `bootstrap` opens the WAL at its snapshot record of the highest index at or below the
saved commit and reads it back (`ReadAll`). **Out of the API:** `MinimalEtcdVersion` (a downgrade's
check), `wal.Repair` (a torn write, never left by `Close`), `UnsafeNoFsync` (one process).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The WAL contract** (sealed; trust boundary: names-only `serverstorage` and `wal`): the
storage `st`, an interface value, over the WAL `storage.walOf st`. Its operations are the laws
below. -/
@[no_expose] def isWalStorage (st : GoInterface) : IProp GF :=
  letI w := storage.walOf st
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryModel) (Q Qf : IProp GF),
      {{ storage.walOpen w q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
          (AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗ ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSave σ hs.toM (es.map EntryModel.toM)), COMM Q }> ∧
           AU <{ ∃∃ (σ : StorContents), walRecs w σ }> @ ⊤, ∅
             <{ ∃ σ' : StorContents, walRecs w σ', COMM Qf }>) }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Qf)) }}) ∗
    □ (∀ (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (Q : IProp GF),
      {{ storage.walOpen w q ∗ sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ ∗
                ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSaveSnap σ md), COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}) ∗
    □ (∀ q : Qp, {{ storage.walOpen w q }} (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen w q }}) ∗
    □ (∀ (σ : StorContents) (id cid : w64),
      {{ storage.walOpen w 1 ∗ walRecs w σ ∗ walMetaIs w id cid ∗ walPurgeRight (walDirOf w) ∗
          ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ walFiles (walDirOf w) id cid σ) ∨
          ⌜¬ storage.walCloseOk⌝ }}))

instance isWalStorage_persistent (st : GoInterface) : Persistent (isWalStorage (GF := GF) st) := by
  unfold isWalStorage; infer_instance

/-- The storage is an interface value (spec review 2: what the laws' `si` is). -/
theorem isWalStorage_ok (st : GoInterface) :
    isWalStorage (GF := GF) st ⊢ ⌜∃ si : GoInterfaceOk, st = GoInterface.ok si⌝ := by
  unfold isWalStorage
  iintro ⟨%si, %Heq, -⟩
  ipureintro; exact ⟨si, Heq⟩

/-- **The WAL's operations** (the contract's laws: a client uses these, not `isWalStorage`'s body).
`Save`: the records saved, or on an error some records (the raft loop then calls `lg.Fatal`,
which never returns). -/
theorem walSave_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
    (es : List EntryModel) (Q Qf : IProp GF) :
    isWalStorage st ⊢
      {{ storage.walOpen (storage.walOf st) q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
          (AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ ∗
                ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs (storage.walOf st) (walSave σ hs.toM (es.map EntryModel.toM)),
              COMM Q }> ∧
           AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ }> @ ⊤, ∅
             <{ ∃ σ' : StorContents, walRecs (storage.walOf st) σ', COMM Qf }>) }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Qf)) }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, #HS, -, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %q %hp %hs %sl %esL %es %Q %Qf
  iexact HS

/-- `SaveSnap`: the snapshot record saved (or the environment failed: the apply thread panics on an
error, the raft loop calls `lg.Fatal`; `walSaveOk`, already in `diskOk`). -/
theorem walSaveSnap_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (Q : IProp GF) :
    isWalStorage st ⊢
      {{ storage.walOpen (storage.walOf st) q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ ∗
                ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }>
            @ ⊤, ∅ <{ walRecs (storage.walOf st) (walSaveSnap σ md), COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, -, #HS, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %q %sn %mp %dq %dq' %md %Q
  iexact HS

/-- `Sync`. -/
theorem walSync_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) :
    isWalStorage (GF := GF) st ⊢
      {{ storage.walOpen (storage.walOf st) q }}
        (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, -, -, #HS, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %q
  iexact HS

/-- `Close`: the WAL's files hold its records and metadata (or the environment failed). -/
theorem walClose_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (σ : StorContents) (id cid : w64) :
    isWalStorage (GF := GF) st ⊢
      {{ storage.walOpen (storage.walOf st) 1 ∗ walRecs (storage.walOf st) σ ∗
          walMetaIs (storage.walOf st) id cid ∗ walPurgeRight (walDirOf (storage.walOf st)) ∗
          ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ walFiles (walDirOf (storage.walOf st)) id cid σ) ∨
          ⌜¬ storage.walCloseOk⌝ }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, -, -, -, #HC⟩
  rw [hst] at Heq; cases Heq
  ispecialize HC $$ %σ %id %cid
  iexact HC

/-- **An opened WAL** (what `bootstrap`'s contract gives: a first start's `wal.Create(dir,
metadata)` at `walFresh`, a restart's `wal.Open` + `ReadAll` of the files `walFiles dir id cid σ` at
`σ`): open, read (`walReady`, what `NewStorage` needs), its records `σ`, its metadata the member's,
in the directory `dir`. -/
def walOpened (w : Loc) (dir : GoString) (id cid : w64) (σ : StorContents) : IProp GF :=
  iprop(storage.walOpen w 1 ∗ walRecs w σ ∗ walMetaIs w id cid ∗
    ⌜storage.walReady w ∧ walDirOf w = dir⌝)

/-- `walOpened`'s parts (its intro is the definition's; this is what a client uses). -/
theorem walOpened_elim (w : Loc) (dir : GoString) (id cid : w64) (σ : StorContents) :
    walOpened (GF := GF) w dir id cid σ ⊢
      storage.walOpen w 1 ∗ walRecs w σ ∗ walMetaIs w id cid ∗
        ⌜storage.walReady w ∧ walDirOf w = dir⌝ := by
  unfold walOpened; iintro H; iexact H

/-! ### The WAL's slots in the boot hub

(2026-11-03, the first slots of the convention the user approved: `notes/spec-first-plan.md`, "The
slot convention".) `bootstrap`'s contract, `bootOk` and `NewServer.spec` name the WAL only through
these, sealed: a change to what the WAL takes or gives at boot changes their bodies and laws, not
the hub's text. No `wal.bootCfg` (the WAL places no condition on the configuration); `wal.Names`
and `wal.srvInv` come with the raft loop's durability invariant (R2b-1 stages 3c/4). -/

/-- **What a caller of `bootstrap` (through `NewServer`) hands the WAL**: the configuration's WAL
directory (`cfg.WALDir()`) fresh, a first start's (from program start, `startRights`). -/
@[no_expose] def wal.bootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(walDirFresh (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'))

/-- `wal.bootRes`'s intro: a configuration whose data directory is `d` and dedicated WAL
directory `w` takes the token of `config.walDirOf d w`. -/
theorem wal.bootRes_intro (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (d w : GoString)
    (hd : cfg.DataDir' = d) (hw : cfg.DedicatedWALDir' = w) :
    walDirFresh (GF := GF) (config.walDirOf d w) ⊢ wal.bootRes cfg := by
  unfold wal.bootRes; subst hd; subst hw; iintro H; iexact H

/-- **What `bootstrap` gives the WAL** (its contract's `bootOk`): the new WAL `w` opened in the
configuration's WAL directory with the member's metadata and no records (`walOpened … walFresh`),
and the right to close it with its files kept (the purge's, `walPurgeRight`). -/
@[no_expose] def wal.bootOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) : IProp GF :=
  iprop(walOpened w (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir') id cid walFresh ∗
    walPurgeRight (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'))

/-- **What the server takes from `wal.bootOk`** (narrow: the slot convention's elimination laws
give what their consumers take, never the slot's body; R2b-1 stage 3c, 2026-11-03, replacing
`wal.bootOk_storage`): the WAL's durability allocated over the fresh records (`rnDur_alloc`: the
invariant, the raft loop's view at the start and its "not failed" token, the stop's claim, the apply
thread's token, the handed log's lower bound), and what `NewStorage` and `Close` take: the open
token, whole, the WAL read, its metadata and the purge's right. -/
theorem wal.bootOk_start (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) :
    wal.bootOk (GF := GF) cfg id cid w ⊢
      |={⊤}=> ∃ ν : WalNames, rnDurInv ν w ∗ ghostVar ν.view (1 : Qp).half walView0 ∗
        token ν.ok ∗ token ν.stop ∗ token ν.app ∗ walCommitLb ν [] ∗
        storage.walOpen w 1 ∗ ⌜storage.walReady w⌝ ∗ walMetaIs w id cid ∗
        walPurgeRight (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir') := by
  unfold wal.bootOk
  iintro ⟨Hw, Hp⟩
  icases walOpened_elim _ _ _ _ _ $$ Hw with ⟨Ho, Hr, Hm, %Hrd⟩
  imod rnDur_alloc w $$ Hr with ⟨%ν, #Hinv, Hv, Hok, Hst, Hap, #Hlb⟩
  imodintro
  iexists ν
  iframe Hinv Hv Hok Hst Hap Hlb Ho Hm Hp
  ipureintro; exact Hrd.1

end defs

end EtcdGrove
end Perennial
