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
(2) `bootstrap`'s first start takes the member's fresh areas (`wal.bootRes`; `dataDirFresh` until
2026-11-24) and gives `walOpened … walFresh` and
`walPurgeRight`, the restart takes `walFiles` and gives `walOpened … σ` and `walPurgeRight` (scope:
`ForceNewCluster` off); (3) `srvFiles` is `∃ cid, walFiles` of the WAL directory (since wal-link P2 the dedicated `srvWalDirOf dd`) `∗` the
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
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsH
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWal
public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseSnapDBs

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

/-- **A reader token of the storage `st`'s lock, over the open WAL `h`** (wal-link L3, 2026-11-19; exclusive):
`serverstorage`'s `Save`, `SaveSnap`, `Sync` and `Release` hold the storage's read lock (`storage.go:62-98`),
so each caller holds a reader token; `NewStorage` hands two (the raft loop's and the apply thread's:
`rnNewStorageOk`). -/
def walStorRd (st : GoInterface) (h : WalH GF) : IProp GF :=
  iprop(∃ p : Loc,
    ⌜st = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p⌝ ∗
    storage.storageRd p h.w)

/-- **What `Save` takes of an entry content `c`, into a WAL of flag `sized`** (wal-link L3): valid unknown
fields, a non-empty encoding below layer 1's record bound `2 ^ 40` (what the server's codec writes as the
wrap `walEntW c`, `walEntInW`), at `sized` of bounded size (`entSizeOk`), and an index below the largest
(layer 1's `Save` premise; raft's room `σ.last ≤ 2^61-1` gives it). -/
def walSaveEntOk (sized : Bool) (c : EntryC) : Prop :=
  ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 40 ∧ (sized = true → entSizeOk c) ∧
    uint.nat c.model.Index' < 2 ^ 64 - 1

/-- **The WAL contract** (sealed; proved, wal-link L3, 2026-11-19: `rnNewStorageOk` from `NewStorage` and the
storage's specs over the real WAL): the storage `st`, an interface value, over the open WAL `h` and the
snapshotter `ss`. Its operations are the laws below (`walSaveSized_spec`, `walSaveSnap_spec`, `walSync_spec`,
`walRelease_spec`, `walClose_spec`). Every law takes a share of the WAL (`storage.walOpen h q`, the whole for
`Close`) and, but `Close`, a reader token of the storage's lock (`walStorRd`); the records move by an atomic
update at the WAL's client mask (`WalFs.walAuMask`); no I/O error arm (every inode is in the run's
no-I/O-error set, `h.cov`). `Save` saves frozen entry contents (`entRoC`, `walSaveEntOk`) after raft's
canonical hard state (`hsOptC`), or (fork fix 0009, approved by the user 2026-11-19) refuses a batch whose
`proto.Size`s plus 64 each pass `MaxSaveBatchBytes` before it commits anything (the share, the token and the
update back); `SaveSnap` a frozen metadata whose record bytes are the canonical ones (`walSnapCanon`, F2) and
gives the synced record's witness (`walSnapRec`), which `Release` takes; `Close` leaves the WAL's files
(`walFiles`). The storage is a `*storage` over the snapshotter `ss` (its field `s`: what ties the
snapshotter to the storage, `isWalStorage_ss_agree`, as `rnStorageOf` did until wal-link L3). -/
@[no_expose] def isWalStorage (st : GoInterface) (h : WalH GF) (ss : Loc) : IProp GF :=
  iprop((∃ p : Loc,
      ⌜st = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"s" p ↦□ ss) ∗
    ∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (sized : Bool) (q : Qp) (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc)
        (cs : List EntryC) (Q : WalHist → IProp GF),
      {{ storage.walOpen h q ∗ walStorRd st h ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
          ([∗list] l; c ∈ esL; cs, entRoC l c) ∗ ⌜∀ c ∈ cs, walSaveEntOk sized c⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ ∃ Hs : WalHist, Q Hs ∗
            (⌜walMustSync Hs hs (cs.map EntryC.model)⌝ -∗
              (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)))) ∨
          (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < (cs.map (fun c => entrySize c + 64)).sum⌝ ∗
            storage.walOpen h q ∗ walStorRd st h ∗
            AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                  ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
              @ WalFs.walAuMask, ∅
              <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                  (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }>) }}) ∗
    □ (∀ (sized : Bool) (q : Qp) (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al : Bool)
        (Q : WalHist → IProp GF),
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
          ⌜m.index.isSome ∧ m.term.isSome ∧ storage.metaWalC m = walSnapCanon m.model al⌝ ∗
          ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗
          ⌜uint.nat m.model.Index' < 2 ^ 64 - 1 ∧ (walSrvMr.encSnap m.model al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSaveSnap σ m.model) (Hs ++ [WalOpG.snap m.model al]) sized,
              COMM Q Hs }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          ∃ Hs : WalHist, Q Hs ∗ (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)) ∗
            walSnapRec h Hs.length m.model }}) ∗
    □ (∀ q : Qp, {{ storage.walOpen h q ∗ walStorRd st h }}
        (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗ walStorRd st h }}) ∗
    □ (∀ (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (sd : GoString) (γd : GName)
        (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF) (i : Nat) (m : SnapshotMetadataM)
        (Q : IProp GF),
      ⌜m.Index' = md.Index'⌝ -∗
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
          snap.isSnapshotter ss sd ∗ snapDirInvH sd γd img Rm ∗
          □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) ∗
          walSnapRec h i m ∗
          AU <{ ∃∃ (σ : StorContents) (s : Bool), walRecs h σ s }> @ WalFs.walAuMask, ∅
            <{ walRecs h σ s, COMM Q }> }}
        (App (Val #(methods si.ty go!"Release" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗ Q ∗
          ⌜err = GoInterface.nil ∨ ¬ snap.dirReadOk ss⌝ }}) ∗
    □ (∀ (sized : Bool) (σ : StorContents) (id cid : w64),
      {{ storage.walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ walFiles h.toWalA id cid σ sized }}))

instance isWalStorage_persistent (st : GoInterface) (h : WalH GF) (ss : Loc) :
    Persistent (isWalStorage (GF := GF) st h ss) := by
  unfold isWalStorage; infer_instance

/-- **The WAL contract from its five laws** (wal-link L3): each law, under a persistent context `R` (the storage's
facts, `rnNewStorageOk_holds`), gives the contract. -/
theorem isWalStorage_intro (R : IProp GF) [Persistent R] (st : GoInterface) (h : WalH GF) (ss : Loc)
    (si : GoInterfaceOk) (hst : st = GoInterface.ok si) (p : Loc)
    (hp : st = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p)
    (hss : R ⊢ structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"s" p ↦□ ss)
    (hSave : ∀ (sized : Bool) (q : Qp) (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc)
        (cs : List EntryC) (Q : WalHist → IProp GF), R ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
          ([∗list] l; c ∈ esL; cs, entRoC l c) ∗ ⌜∀ c ∈ cs, walSaveEntOk sized c⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ ∃ Hs : WalHist, Q Hs ∗
            (⌜walMustSync Hs hs (cs.map EntryC.model)⌝ -∗
              (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)))) ∨
          (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < (cs.map (fun c => entrySize c + 64)).sum⌝ ∗
            storage.walOpen h q ∗ walStorRd st h ∗
            AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                  ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
              @ WalFs.walAuMask, ∅
              <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                  (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }>) }})
    (hSnap : ∀ (sized : Bool) (q : Qp) (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al : Bool)
        (Q : WalHist → IProp GF), R ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
          ⌜m.index.isSome ∧ m.term.isSome ∧ storage.metaWalC m = walSnapCanon m.model al⌝ ∗
          ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗
          ⌜uint.nat m.model.Index' < 2 ^ 64 - 1 ∧ (walSrvMr.encSnap m.model al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSaveSnap σ m.model) (Hs ++ [WalOpG.snap m.model al]) sized,
              COMM Q Hs }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          ∃ Hs : WalHist, Q Hs ∗ (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)) ∗
            walSnapRec h Hs.length m.model }})
    (hSync : ∀ q : Qp, R ⊢
      {{ storage.walOpen h q ∗ walStorRd st h }}
        (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗ walStorRd st h }})
    (hRel : ∀ (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (sd : GoString) (γd : GName)
        (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF) (i : Nat) (m : SnapshotMetadataM)
        (Q : IProp GF), R ⊢
      ⌜m.Index' = md.Index'⌝ -∗
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
          snap.isSnapshotter ss sd ∗ snapDirInvH sd γd img Rm ∗
          □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) ∗
          walSnapRec h i m ∗
          AU <{ ∃∃ (σ : StorContents) (s : Bool), walRecs h σ s }> @ WalFs.walAuMask, ∅
            <{ walRecs h σ s, COMM Q }> }}
        (App (Val #(methods si.ty go!"Release" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗ Q ∗
          ⌜err = GoInterface.nil ∨ ¬ snap.dirReadOk ss⌝ }})
    (hClose : ∀ (sized : Bool) (σ : StorContents) (id cid : w64), R ⊢
      {{ storage.walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ walFiles h.toWalA id cid σ sized }}) :
    R ⊢ isWalStorage st h ss := by
  unfold isWalStorage
  iintro #HR
  isplitr
  · iexists p
    isplitr
    · ipureintro; exact hp
    iapply hss; iexact HR
  iexists si
  isplitr
  · ipureintro; exact hst
  isplitr
  · iintro !>
    iintro %sized %q %hp %hs %sl %esL %cs %Q
    iapply (hSave sized q hp hs sl esL cs Q)
    iexact HR
  isplitr
  · iintro !>
    iintro %sized %q %sn %mp %dq %m %al %Q
    iapply (hSnap sized q sn mp dq m al Q)
    iexact HR
  isplitr
  · iintro !>
    iintro %q
    iapply (hSync q)
    iexact HR
  isplitr
  · iintro !>
    iintro %q %sn %mp %dq %dq' %md %sd %γd %img %Rm %i %m %Q
    iapply (hRel q sn mp dq dq' md sd γd img Rm i m Q)
    iexact HR
  iintro !>
  iintro %sized %σ %id %cid
  iapply (hClose sized σ id cid)
  iexact HR

/-- The storage is an interface value (spec review 2: what the laws' `si` is). -/
theorem isWalStorage_ok (st : GoInterface) (h : WalH GF) (ss : Loc) :
    isWalStorage (GF := GF) st h ss ⊢ ⌜∃ si : GoInterfaceOk, st = GoInterface.ok si⌝ := by
  unfold isWalStorage
  iintro ⟨-, %si, %Heq, -⟩
  ipureintro; exact ⟨si, Heq⟩

/-- (wal-link L3) **The storage is a `*storage`** (what `rnStorageOf` said until then). -/
theorem isWalStorage_ptr (st : GoInterface) (h : WalH GF) (ss : Loc) :
    isWalStorage (GF := GF) st h ss ⊢
      ⌜∃ p : Loc, st = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p⌝ := by
  unfold isWalStorage
  iintro ⟨⟨%p, %Heq, -⟩, -⟩
  ipureintro; exact ⟨p, Heq⟩

/-- **The snapshotter is the storage's** (wal-link L3): two contracts of one storage name one snapshotter. -/
theorem isWalStorage_ss_agree (st : GoInterface) (h h' : WalH GF) (ss ss' : Loc) :
    isWalStorage (GF := GF) st h ss ∗ isWalStorage st h' ss' ⊢ ⌜ss = ss'⌝ := by
  unfold isWalStorage
  iintro ⟨⟨⟨%p, %Hp, #Hs⟩, -⟩, ⟨⟨%p', %Hp', #Hs'⟩, -⟩⟩
  have hpp : p' = p := by
    rw [Hp] at Hp'
    exact (go.intoVal_inj ((interface_mkOk_inj _ _ _ _).1 Hp').2).symm
  subst hpp
  icombine Hs Hs' gives %Heq
  ipureintro
  first | exact Heq | exact Heq.2

/-- (raft-entsize §5; wal-link L3) **`Save`** (the contract's law): the entries as objects frozen at contents
the WAL can write (`walSaveEntOk`), the records saved. -/
theorem walSaveSized_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (sized : Bool) (q : Qp) (hp : Loc) (hs : HardStateM) (sl : GoSlice)
    (esL : List Loc) (cs : List EntryC) (Q : WalHist → IProp GF) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
          ([∗list] l; c ∈ esL; cs, entRoC l c) ∗ ⌜∀ c ∈ cs, walSaveEntOk sized c⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ ∃ Hs : WalHist, Q Hs ∗
            (⌜walMustSync Hs hs (cs.map EntryC.model)⌝ -∗
              (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)))) ∨
          (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < (cs.map (fun c => entrySize c + 64)).sum⌝ ∗
            storage.walOpen h q ∗ walStorRd st h ∗
            AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                  ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
              @ WalFs.walAuMask, ∅
              <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                  (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }>) }} := by
  unfold isWalStorage
  iintro ⟨-, %si', %Heq, #HS, -, -, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %sized %q %hp %hs %sl %esL %cs %Q
  iexact HS

/-- (out_size C3, 2026-11-12) **The entry objects `esL` are frozen at contents of bounded size
holding `es`** (persistent): what a sized WAL `Save` (`walSaveSized_spec`) and the sized storage's
`Append` (`isRNMemStor`) take; a `Ready`'s entries are so in the server's cluster, which bounds
proposed data (`readyEnts_sized`). (wal-link L3) With what the WAL's codec needs of each content
(`walSaveEntOk true`). -/
def rnEntsSized (esL : List Loc) (es : List EntryModel) : IProp GF :=
  iprop(∃ cs : List EntryC, ([∗list] l;c ∈ esL;cs, entRoC l c) ∗
    ⌜cs.map EntryC.model = es.map EntryModel.toM ∧ ∀ c ∈ cs, entSizeOk c⌝)

instance rnEntsSized_persistent (esL : List Loc) (es : List EntryModel) :
    Persistent (rnEntsSized (GF := GF) esL es) := by
  unfold rnEntsSized; infer_instance

/-- The sized objects as `entsROz true` (`isRNMemStor`'s `Append` premise). -/
theorem rnEntsSized_entsROz (sl : GoSlice) (esL : List Loc) (es : List EntryModel) :
    sl ↦*□ esL ∗ rnEntsSized (GF := GF) esL es ⊢ entsROz true sl (es.map EntryModel.toM) := by
  unfold rnEntsSized
  iintro ⟨#Hs, %cs, #Hb, %Hcs⟩
  unfold entsROz entsPtsZ
  iexists esL
  iframe Hs
  rw [← Hcs.1]
  iapply entsBigC_entsBigZ true esL cs (fun _ => Hcs.2) $$ Hb

/-- (wal-link L3, 2026-11-19) **What `Save` takes of each entry content, from the batch's facts**: valid unknown
fields (`entRoC`'s), bounded size (`entSizeOk`), and, from a `Save` step of the records `σ` (`WalSaveOk`: the
first index past `σ.b`, the indices consecutive) and the batch's bound (`2^61`, `rnFits`), an index in
`[1, 2^61)`: a non-empty encoding (the index set) below the largest index. -/
theorem walSaveEntOk_of (cs : List EntryC) (es : List EntryM) (σ : StorContents)
    (hcs : cs.map EntryC.model = es) (hok : WalSaveOk σ es)
    (hfit : ∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ 2 ^ 61)
    (huf : ∀ c ∈ cs, ufWire entrySchema c.uf) (hsz : ∀ c ∈ cs, entSizeOk c) :
    ∀ c ∈ cs, walSaveEntOk true c := by
  intro c hc
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hc
  have hjl : j < cs.length := (List.getElem?_eq_some_iff.1 hj).1
  have hej : es[j]? = some c.model := by rw [← hcs, List.getElem?_map, hj]; rfl
  have hlen : es.length = cs.length := by rw [← hcs, List.length_map]
  obtain ⟨e0, h0⟩ : ∃ e0, es.head? = some e0 := by
    cases hes : es with
    | nil => rw [hes] at hlen; simp at hlen; omega
    | cons a _ => exact ⟨a, rfl⟩
  obtain ⟨hb, -, hcon⟩ := hok e0 h0
  have hidx := hcon j c.model hej
  have hf := hfit e0 h0
  have hidx1 : 1 ≤ uint.nat c.model.Index' := by omega
  have hidx2 : uint.nat c.model.Index' < 2 ^ 61 := by
    have : ((uint.nat e0.Index' : Nat) : Int) = uint.Z e0.Index' := by word
    omega
  have hpos : 0 < entrySize c := by
    unfold entrySize optVarintSize
    cases hci : c.index with
    | none =>
      exfalso
      have : uint.nat c.model.Index' = 0 := by unfold EntryC.model; rw [hci]; rfl
      omega
    | some v => simp only [Option.map_some]; omega
  refine ⟨huf c hc, hpos, ?_, fun _ => hsz c hc, by omega⟩
  have := entrySize_lt_of_ok c (hsz c hc)
  omega

/-- (wal-link L3) **The raft loop's sized entries, as `Save` takes them** (`walSaveEntOk_of`). -/
theorem rnEntsSized_walSave (esL : List Loc) (es : List EntryModel) (σ : StorContents)
    (hok : WalSaveOk σ (es.map EntryModel.toM))
    (hfit : ∀ e0, es.head? = some e0 → uint.Z e0.index + (es.length : Int) ≤ 2 ^ 61) :
    rnEntsSized (GF := GF) esL es ⊢
      ∃ cs : List EntryC, ([∗list] l;c ∈ esL;cs, entRoC l c) ∗
        ⌜cs.map EntryC.model = es.map EntryModel.toM ∧ ∀ c ∈ cs, walSaveEntOk true c⌝ := by
  unfold rnEntsSized
  iintro ⟨%cs, #Hb, %Hcs⟩
  ihave %huf := entsRoC_uf esL cs $$ Hb
  iexists cs
  iframe Hb
  ipureintro
  refine ⟨Hcs.1, walSaveEntOk_of cs _ σ Hcs.1 hok ?_ huf Hcs.2⟩
  intro e0 h0
  cases hes : es with
  | nil => rw [hes] at h0; simp at h0
  | cons a t =>
    rw [hes] at h0; simp only [List.map_cons, List.head?_cons, Option.some.injEq] at h0
    subst h0
    have := hfit a (by rw [hes]; rfl)
    simpa [hes, EntryModel.toM] using this

/-- (out_size C3, MAJ-2) **The raft loop's `Save` into its sized WAL** (`walSaveSized_spec` over
`rnEntsSized`): the entries' objects at sized contents, the records staying sized. (wal-link L3) With the
codec's facts of each content (`walSaveEntOk true`'s other conjuncts: raft's `ufWire` and room). -/
theorem walSaveRn_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc)
    (es : List EntryModel) (Q : WalHist → IProp GF) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
          (∃ cs : List EntryC, ([∗list] l;c ∈ esL;cs, entRoC l c) ∗
            ⌜cs.map EntryC.model = es.map EntryModel.toM ∧ ∀ c ∈ cs, walSaveEntOk true c⌝) ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs true ∗
                ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSave σ hs (es.map EntryModel.toM))
                (Hs ++ [WalOpG.save hs (es.map EntryModel.toM)]) true, COMM Q Hs }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ ∃ Hs : WalHist, Q Hs ∗
            (⌜walMustSync Hs hs (es.map EntryModel.toM)⌝ -∗
              (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)))) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h) }} := by
  iintro #Hw
  iintro !> %Φ ⟨Ho, Hr, Hh, #Hsl, ⟨%cs, #Hb, %Hcs⟩, HAU⟩ HΦ
  ihave #HS := walSaveSized_spec st h ss si hst true q hp hs sl esL cs Q $$ Hw
  rw [← Hcs.1]
  iapply HS $$ [Ho Hr Hh HAU]
  · iframe Ho Hr Hh Hsl Hb HAU
    ipureintro; exact Hcs.2
  iintro %err !> Hpost
  iapply HΦ
  icases Hpost with (Hok | ⟨⟨%Herr, -⟩, Ho, Hr, -⟩)
  · ileft; iexact Hok
  · iright; iframe Ho Hr; ipureintro; exact Herr

/-- (P5) **`walSaveRn_spec` over the records without their history** (the caller's update independent of
the history, `walRecs_au_toH`; the refusal's update dropped: the loop panics there). -/
theorem walSaveRnR_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc)
    (es : List EntryModel) (Q : IProp GF) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
          (∃ cs : List EntryC, ([∗list] l;c ∈ esL;cs, entRoC l c) ∗
            ⌜cs.map EntryC.model = es.map EntryModel.toM ∧ ∀ c ∈ cs, walSaveEntOk true c⌝) ∗
          AU <{ ∃∃ (σ : StorContents), walRecs h σ true ∗ ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ WalFs.walAuMask, ∅ <{ walRecs h (walSave σ hs (es.map EntryModel.toM)) true, COMM Q }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ Q) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ True) }} := by
  have hc := walRecs_au_toH h true (fun σ => WalSaveOk σ (es.map EntryModel.toM))
    (fun σ => walSave σ hs (es.map EntryModel.toM)) (WalOpG.save hs (es.map EntryModel.toM))
    WalFs.walAuMask Q
  iintro #Hw
  iintro !> %Φ ⟨Ho, Hr, Hh, #Hsl, Hcs, HAU⟩ HΦ
  ihave HAU := hc $$ HAU
  ihave #HS := walSaveRn_spec st h ss si hst q hp hs sl esL es (fun _ => Q) $$ Hw
  iapply HS $$ [Ho Hr Hh Hcs HAU]
  · iframe Ho Hr Hh Hsl Hcs HAU
  iintro %err !> Hpost
  iapply HΦ
  icases Hpost with (⟨%He, Ho, Hr, %Hs, HQ, -⟩ | ⟨%Herr, Ho, Hr⟩)
  · ileft; iframe Ho Hr HQ; ipureintro; exact He
  · iright; iframe Ho Hr; ipureintro; exact Herr

/-- (P5) **`SaveSnap`** (the contract's law) over the records with their history: the snapshot record
appended at the history `Hs`, synced, its witness (`walSnapRec`). -/
theorem walSaveSnapH_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al : Bool)
    (Q : WalHist → IProp GF) (sized : Bool := false) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
          ⌜m.index.isSome ∧ m.term.isSome ∧ storage.metaWalC m = walSnapCanon m.model al⌝ ∗
          ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗
          ⌜uint.nat m.model.Index' < 2 ^ 64 - 1 ∧ (walSrvMr.encSnap m.model al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSaveSnap σ m.model) (Hs ++ [WalOpG.snap m.model al]) sized,
              COMM Q Hs }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          ∃ Hs : WalHist, Q Hs ∗ (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)) ∗
            walSnapRec h Hs.length m.model }} := by
  unfold isWalStorage
  iintro ⟨-, %si', %Heq, -, #HS, -, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %sized %q %sn %mp %dq %m %al %Q
  iexact HS

/-- **`SaveSnap`** (the contract's law, over the records without their history: `walSaveSnapH_spec`
with `walRecs_au_toH`): the snapshot record saved, synced, its witness (`walSnapRec`). -/
theorem walSaveSnap_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al : Bool) (Q : IProp GF)
    (sized : Bool := false) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
          ⌜m.index.isSome ∧ m.term.isSome ∧ storage.metaWalC m = walSnapCanon m.model al⌝ ∗
          ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗
          ⌜uint.nat m.model.Index' < 2 ^ 64 - 1 ∧ (walSrvMr.encSnap m.model al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ (σ : StorContents), walRecs h σ sized ∗
                ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅ <{ walRecs h (walSaveSnap σ m.model) sized, COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ Q ∗
          ∃ i : Nat, walSnapRec h i m.model }} := by
  have hc := walRecs_au_toH h sized (fun σ => uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term')
    (fun σ => walSaveSnap σ m.model) (WalOpG.snap m.model al) WalFs.walAuMask Q
  iintro #Hw
  iintro !> %Φ ⟨Ho, Hr, Hsn, #Hm, %h1, %h2, %h3, HAU⟩ HΦ
  ihave HAU := hc $$ HAU
  ihave #HS := walSaveSnapH_spec st h ss si hst q sn mp dq m al (fun _ => Q) sized $$ Hw
  iapply HS $$ [Ho Hr Hsn HAU]
  · iframe Ho Hr Hsn Hm HAU
    ipureintro; exact ⟨h1, h2, h3⟩
  iintro %err !> ⟨%He, Ho, Hr, Hsn, %Hs, HQ, -, #Hrec⟩
  iapply HΦ
  iframe Ho Hr Hsn HQ
  isplitr
  · ipureintro; exact He
  iexists Hs.length
  iexact Hrec

/-- **`Sync`** (the contract's law). -/
theorem walSync_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) :
    isWalStorage (GF := GF) st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h }}
        (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗ walStorRd st h }} := by
  unfold isWalStorage
  iintro ⟨-, %si', %Heq, -, -, #HS, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %q
  iexact HS

/-- **`Release`** (the contract's law; until wal-link L3 the trusted `storage.Release.spec` on the concrete
storage, with `walBaseLb`): at a snapshot `md` whose index is a synced snapshot record's (`walSnapRec`, from
`SaveSnap`'s law), the WAL's locks below it released (the records unchanged: an atomic update that reads
them) and the snapshotter's older `.snap.db` files removed; `nil`, or the snapshot directory's listing
failed. -/
theorem walRelease_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM)
    (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF) (i : Nat)
    (m : SnapshotMetadataM) (Q : IProp GF) (hm : m.Index' = md.Index') :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
          snap.isSnapshotter ss sd ∗ snapDirInvH sd γd img Rm ∗
          □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) ∗
          walSnapRec h i m ∗
          AU <{ ∃∃ (σ : StorContents) (s : Bool), walRecs h σ s }> @ WalFs.walAuMask, ∅
            <{ walRecs h σ s, COMM Q }> }}
        (App (Val #(methods si.ty go!"Release" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗ Q ∗
          ⌜err = GoInterface.nil ∨ ¬ snap.dirReadOk ss⌝ }} := by
  unfold isWalStorage
  iintro ⟨-, %si', %Heq, -, -, -, #HR, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HR $$ %q %sn %mp %dq %dq' %md %sd %γd %img %Rm %i %m %Q
  iapply HR
  ipureintro; exact hm

/-- **`Close`** (the contract's law): the WAL's files hold its records and metadata. -/
theorem walClose_spec (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (σ : StorContents) (id cid : w64) (sized : Bool := false) :
    isWalStorage (GF := GF) st h ss ⊢
      {{ storage.walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ walFiles h.toWalA id cid σ sized }} := by
  unfold isWalStorage
  iintro ⟨-, %si', %Heq, -, -, -, -, #HC⟩
  rw [hst] at Heq; cases Heq
  ispecialize HC $$ %sized %σ %id %cid
  iexact HC

/-- **`serverstorage.NewStorage(lg, w, ss)`** (translated, wal-link L2): over the open WAL `h` at `w = h.w`
(the WAL `bootstrap` opened and read: `wal.bootOk`'s, `wal.restartOk`'s) and the snapshotter `ss`, the storage
`st` meets the WAL contract (`isWalStorage st h ss`), with two reader tokens of its lock (`walStorRd`: the raft
loop's and the apply thread's). (wal-link L3, 2026-11-19: proved, `rnNewStorageOk_holds`, from `NewStorage`'s
and the storage methods' specs over the real WAL; until then a premise of every closed theorem, over a WAL
location with the opaque `walReady w` and `walOf st = w`, and the snapshotter's opaque `storageSnap`.) -/
def rnNewStorageOk : IProp GF :=
  iprop(□ ∀ (lg ss : Loc) (sd : GoString) (h : WalH GF), {{ snap.isSnapshotter ss sd }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewStorage)) (Val #lg)) (Val #h.w))
      (Val #ss))
    {{ (st : GoInterface), RET #st; isWalStorage st h ss ∗ walStorRd st h ∗ walStorRd st h }})

instance rnNewStorageOk_persistent : Persistent (rnNewStorageOk (GF := GF)) := by
  unfold rnNewStorageOk; infer_instance

/-- **`NewStorage`'s contract as a law** (wal-item3, 2026-11-21; the import tiers' "a proof takes a linked
lemma as a law"): given the storage package's initialization, `rnNewStorageOk`. `rnNewStorageOk_law_holds`
(`RnNewStorageLinked.lean`) proves it under `os`'s `fileStat`/`file` field assumptions (the WAL's), and
`bootstrappedRaft.newRaftNode`'s proof takes it (wal-nostorageok, 2026-11-21: until then its spec's premise
`rnNewStorageOk`, and every closed theorem's; those now take the two field-assumption classes instead). The
semantic hypothesis `UntypedRuneSemantics` it also took went with Perennial `04b42a139` (2026-11-21). -/
abbrev rnNewStorageOk.law : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ⊢ rnNewStorageOk (GF := GF)

/-- **An opened WAL** (what `bootstrap`'s contract gives: a first start's `wal.Create(dir, metadata)` at
`walFresh`, a restart's `wal.Open` + `ReadAll` of the files `walFiles` at `σ`): open (its whole share), its
records `σ`, its metadata the member's, in the directory `dir`. (wal-link L3: over the open WAL `h`; until
then over a location with an opaque readiness, `walReady`, and directory, `walDirOf`.)

(raft-entsize §5, [r3g], 2026-11-09) **`sized`** (default `false`): the records' flag (`walRecs`'s). -/
def walOpened (h : WalH GF) (dir : GoString) (id cid : w64) (σ : StorContents) (sized : Bool := false) :
    IProp GF :=
  iprop(storage.walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ ⌜h.dir = dir⌝)

/-- `walOpened`'s parts (its intro is the definition's; this is what a client uses). -/
theorem walOpened_elim (h : WalH GF) (dir : GoString) (id cid : w64) (σ : StorContents)
    (sized : Bool := false) :
    walOpened (GF := GF) h dir id cid σ sized ⊢
      storage.walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ ⌜h.dir = dir⌝ := by
  unfold walOpened; iintro H; iexact H

/-- (P5, 2026-11-25) **`walOpened` with the records' history** (`walRecsH`): what `wal.Create` and a
restart's `ReadAll` leave, for the crash-aware durability invariant's allocation (`rnDurK_alloc`). -/
def walOpenedH (h : WalH GF) (dir : GoString) (id cid : w64) (σ : StorContents) (Hs : WalHist)
    (sized : Bool := false) : IProp GF :=
  iprop(storage.walOpen h 1 ∗ walRecsH h σ Hs sized ∗ walMetaIs h id cid ∗ ⌜h.dir = dir⌝)

/-- `walOpenedH`'s parts. -/
theorem walOpenedH_elim (h : WalH GF) (dir : GoString) (id cid : w64) (σ : StorContents) (Hs : WalHist)
    (sized : Bool := false) :
    walOpenedH (GF := GF) h dir id cid σ Hs sized ⊢
      storage.walOpen h 1 ∗ walRecsH h σ Hs sized ∗ walMetaIs h id cid ∗ ⌜h.dir = dir⌝ := by
  unfold walOpenedH; iintro H; iexact H

/-- `walOpenedH` forgets the history. -/
theorem walOpenedH_walOpened (h : WalH GF) (dir : GoString) (id cid : w64) (σ : StorContents)
    (Hs : WalHist) (sized : Bool := false) :
    walOpenedH (GF := GF) h dir id cid σ Hs sized ⊢ walOpened h dir id cid σ sized := by
  unfold walOpenedH walOpened
  iintro ⟨Ho, Hr, Hm, %Hd⟩
  iframe Ho Hm
  isplitl [Hr]
  · iapply walRecsH_walRecs; iexact Hr
  · ipureintro; exact Hd

/-! ### The WAL's slots in the boot hub

(2026-11-03, the first slots of the convention the user approved: `notes/spec-first-plan.md`, "The
slot convention".) `bootstrap`'s contract, `bootOk` and `NewServer.spec` name the WAL only through
these, sealed: a change to what the WAL takes or gives at boot changes their bodies and laws, not
the hub's text. No `wal.bootCfg` (the WAL places no condition on the configuration); `wal.Names`
and `wal.srvInv` come with the raft loop's durability invariant (R2b-1 stages 3c/4). -/

/-- **What a caller of `bootstrap` (through `NewServer`) hands the WAL and the backend**: the
configuration's dedicated WAL directory the member's (`srvWalDirOf`, under the member's `fsExt` root
`walAreaOf`), and that WAL area fresh (`walAreaFresh`: what `wal.Create` takes of it, no WAL in the
directory; allocated at adequacy, `lib/etcdstart/WalAreas.lean`), with the data directory a root of its
own, empty, wholly the caller's (`dataAreaFresh`, in `memberAreasFresh` with the WAL area; 2026-11-19,
approved by the user via etcd-grove-03, `notes/datadir-relative-unsat.md`): what the backend's and the
snapshots' file claims `bootOk` gives are made of. (Sweep repairs 1, W3/W4, 2026-11-07: until then the
WAL directory's `walDirFresh`, which said nothing of the backend file a first start opens; wal-link P2,
2026-11-19: until then no dedicated WAL directory, the WAL in the data directory.) (2026-11-24, approved
for `putget_safe`, `notes/putget-dist-plan.md` §12: a deletion of trust) It no longer takes
the axiomatized token `dataDirFresh cfg.DataDir'` (the data directory absent or empty, so no backend
file at `config.backendPathOf`): `dataAreaFresh cfg.DataDir'` already says it, as a claim on every name
of the directory, none of which names an entry (`dataAreaFresh`'s definition, `storage/WalAreaFresh.lean`:
the caller's whole names claim on `d`'s root with `∀ b, h.cur !! b = none`, which the shared mode's
invariant keeps coherent with the tree), held whole by the caller, so no other thread can create one;
the token added nothing a faithful `bootstrap` needs. -/
@[no_expose] def wal.bootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(⌜cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir'⌝ ∗ memberAreasFresh cfg.DataDir')

/-- `wal.bootRes`'s intro: a configuration whose data directory is `d` and whose dedicated WAL
directory is `d`'s takes the fresh areas of `d`. -/
theorem wal.bootRes_intro (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (d : GoString)
    (hd : cfg.DataDir' = d) (hw : cfg.DedicatedWALDir' = srvWalDirOf d) :
    memberAreasFresh (GF := GF) d ⊢ wal.bootRes cfg := by
  unfold wal.bootRes; subst hd; iintro Ha; iframe Ha; ipureintro; exact hw

/-- **`wal.bootRes` is the dedicated WAL directory's equation and the member's fresh areas** (since
2026-11-24 no data directory's token, `dataDirFresh`) (claim #34, 2026-11-23): the slot's body as a law, so that `bootstrap`'s
file-system laws (`BootFsLaws.lean`), which split the data area, need no `import all` of this sealed
module. It says what the slot is made of; the WAL's sealed records (`WalRecs`) are not involved. -/
theorem wal.bootRes_iff (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    wal.bootRes (GF := GF) cfg ⊣⊢
      ⌜cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir'⌝ ∗ memberAreasFresh cfg.DataDir' := by
  unfold wal.bootRes; exact .rfl

/-- **What `bootstrap` gives the WAL** (its contract's `bootOk`): the new WAL `w` opened in the
configuration's WAL directory with the member's metadata and no records (`walOpened … walFresh`),
and the right to close it with its files kept (the purge's, `walPurgeRight`). (raft-entsize §5,
[r3g], 2026-11-09) Sized (`true`): `wal.Create` writes the metadata, an empty snapshot record and no
entry record, so every entry record (none) is of a content of bounded size. (wal-fsfix2, 2026-11-20, approved
by the user via etcd-grove-03) The open WAL's area (`WalA`, `h.toWalA`; a faithful `bootstrap` hands on
`walAreaFresh`'s, though the post ties only `h.dir` to it) carries, besides the
no-I/O-error instance, the no-lock-error one (`satL`: its files' `flock` calls succeed whenever they can), the
WAL directory's `Fs.DirFits` (`fits`) and every path below it covered by path (`covP`: there `NoIoErr`'s path clauses apply, an `open`, `rename`,
`mkdir`, `unlink` or `rmdir` that can succeed does and a failing `unlink`/`rmdir` gives Linux's errno, `PathErrno`;
and `NoMapLockErr`'s `open` clause with no free fd). Old → new: covered by `NoIoErr` by inode only → also by `NoMapLockErr`, and by path in its
directory, which fits. -/
@[no_expose] def wal.bootOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) : IProp GF :=
  iprop(∃ h : WalH GF, ⌜h.w = w⌝ ∗
    walOpenedH h cfg.DedicatedWALDir' id cid walFresh [] true ∗ walPurgeRight h)

/-- **`wal.bootOk`'s intro** (claim #34 stage 4, 2026-11-25): the WAL `wal.Create` opened in the
configuration's WAL directory (`wal.Create.specSrv`'s post), as `bootstrapNewWAL` hands it on. -/
theorem wal.bootOk_intro (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) :
    (∃ h : WalH GF, ⌜h.w = w⌝ ∗ walOpenedH h cfg.DedicatedWALDir' id cid walFresh [] true ∗
        walPurgeRight h) ⊢ wal.bootOk (GF := GF) cfg id cid w := by
  unfold wal.bootOk; exact .rfl

/-- **What the server takes from `wal.bootOk`** (narrow: the slot convention's elimination laws
give what their consumers take, never the slot's body; R2b-1 stage 3c, 2026-11-03, replacing
`wal.bootOk_storage`): the open WAL `h` at `w` (wal-link L3), the WAL's durability allocated over the
fresh records (`rnDur_alloc`: the invariant, the raft loop's view at the start and its "not failed" token,
the stop's claim, the apply thread's token, the handed log's lower bound), and what `NewStorage` and
`Close` take: the open WAL's whole share, its metadata and the purge's right. -/
theorem wal.bootOk_start (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (cl : Cluster) :
    wal.bootOk (GF := GF) cfg id cid w ⊢
      |={⊤}=> ∃ (h : WalH GF) (ν : WalNames GF), ⌜h.w = w⌝ ∗ rnDurInv cl ν h ∗
        ghostVar ν.view (1 : Qp).half walView0 ∗
        token ν.ok ∗ token ν.stop ∗ token ν.app ∗ walCommitLb ν [] ∗
        storage.walOpen h 1 ∗ walMetaIs h id cid ∗ walPurgeRight h ∗
        -- (2026-11-04, R2b-3d) the WAL's directory, the configuration's (the stop image's `srvFiles`)
        ⌜h.dir = cfg.DedicatedWALDir'⌝ := by
  unfold wal.bootOk
  iintro ⟨%h, %Hw, Hwo, Hp⟩
  icases walOpenedH_elim _ _ _ _ _ _ _ $$ Hwo with ⟨Ho, Hr, Hm, %Hd⟩
  ihave Hr := walRecsH_walRecs h _ _ _ $$ Hr
  imod rnDur_alloc cl h $$ Hr with ⟨%ν, #Hinv, Hv, Hok, Hst, Hap, #Hlb⟩
  imodintro
  iexists h, ν
  iframe Hinv Hv Hok Hst Hap Hlb Ho Hm Hp
  ipureintro; exact ⟨Hw, Hd⟩

/-- **The WAL's slot in the stopped member's image** (R2d review F7, 2026-11-06; DRAFT; the slot
convention, `notes/spec-first-plan.md`, "The slot convention": the WAL's facts move into their slot
as the WAL next changes the hub, which the certificate does). Sealed; `wal.stopImage_intro` builds
it. The WAL's records `σ` hold the node's durable state `S` (`StorageHolds`, what `RestartNode`'s
update checks); their snapshot is at or below the backend's consistent index `i` and `i` at or below
their commit (etcd's order: a snapshot is of the applied state; and the raft loop, which hands a
batch to the apply thread before it saves the batch's `HardState` (`r.applyc <- ap`,
`server/etcdserver/raft.go:240`, before `r.storage.Save(rd.HardState, …)`, `:264`, at the pin
`673da07c8`), finishes that `Save` before it can observe `stopped`; `r.stop()` waits for the loop to
end (`:425-435`), and the stop commits the backend after it (`s.r.stop()` then `s.Cleanup()`,
`server.go:831-833`): so the order holds at a graceful stop, not at every instant); the first so
that `bootstrap` keeps the backend file; and their snapshot certificate (`walSnapCert`, Q14 (a)): at index `0`, or their snapshot, of no data at their base, valid; (restart S6) a committed log reaching their base, which `S`'s log agrees with.

**Margin.** The certificate is of the records' snapshot. `bootstrap` replaces that snapshot's
`ConfState` by the backend's at `i` (`bootstrap.go:107-115`, `buildConfStateFromV3store`) before
the restarted storage applies it, so it certifies the restarted storage's snapshot only when the
two conf states agree: in a static cluster (HS2's caveat (ii), `notes/restart-plan.md`). -/
@[no_expose] def wal.stopImage (cl : Cluster) (S : RaftState) (σ : StorContents) (i : w64) :
    IProp GF :=
  iprop(⌜StorageHolds S σ ∧ σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit⌝ ∗ walSnapCert cl σ ∗
    -- (restart S6, 2026-11-13; S1's, r2db §4.1) a committed log reaching the records' base, which
    -- the durable state's log agrees with (`raftNode.stop`'s `DurAgrees`): for `wal.restartOk_start`
    (∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝))

/-- `wal.stopImage`'s intro, from the stop's facts. -/
theorem wal.stopImage_intro (cl : Cluster) (S : RaftState) (σ : StorContents) (i : w64)
    (hS : StorageHolds S σ) (hb : σ.b ≤ uint.nat i) (hc : uint.nat i ≤ σ.commit) :
    walSnapCert (GF := GF) cl σ ∗
        (∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝) ⊢
      wal.stopImage cl S σ i := by
  unfold wal.stopImage; iintro ⟨H, Hl⟩; iframe H Hl; ipureintro; exact ⟨hS, hb, hc⟩

/-- `wal.stopImage`'s elimination: the stop's facts, the snapshot certificate (the Freeze 1
review's F5, for its R2d' consumer, the restart's `bootstrap`) and the committed log the durable
state agrees with (restart S6). -/
theorem wal.stopImage_elim (cl : Cluster) (S : RaftState) (σ : StorContents) (i : w64) :
    wal.stopImage (GF := GF) cl S σ i ⊢
      ⌜StorageHolds S σ ∧ σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit⌝ ∗ walSnapCert cl σ ∗
        (∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝) := by
  unfold wal.stopImage; iintro H; iexact H

/-! ### The WAL's slot in a restart's boot hub

(Restart S6, 2026-11-13; D2, approved by the user via etcd-grove-81, 2026-11-12;
`notes/wal-crash-handoff/restart-wal-interface.md` §2, §5.) What a restart's `bootstrap` gives the
WAL, sealed: the restart proofs use only its two laws (`wal.restartOk_facts`, `wal.restartOk_start`),
so that the crash-model WAL (C6, the WAL collaborator's) can replace the body and re-prove the laws
without touching them. -/

/-- **What a restart's read of the WAL returns, as facts of the records `σ`** (the interface's
I1-I4; pure): the entries consecutive from the base (I1, the history model's `walEntsWf`); the last index within raft's
room (I2, `σ.last ≤ 2^61 - 1`); the base at or below the commit and the commit at or below the last
index (I3: raft's `loadState` panics otherwise, `raft.go`'s "commit is out of range"); and (I4) either
the fresh base `(0, 0)` with no snapshot record, or a data-less snapshot record at the base
(`walSnapAtBase`'s form; both written out here, as `storage/WalHistLemmas.lean` states them: this
module does not import the history model). I4 gives `NodeStartSpecR`'s snapshot-term premise (F3, `walReadFacts_F3`).
I4 does not give `bootstrappedWAL.MemoryStorage.spec`'s premise that a base at index `0` has term
`0` (F2's third clause): the WAL model's `walSaveSnap` at index `0` sets the snapshot's term, any term
(`storage/WalRecs.lean`), so only the server's history (no `SaveSnap` at index `0`: `snapshot`'s
`0 < ai`, raft's snapshots past its commit) excludes it (CP2 review, minor (b)). **Trusted, not
checked** (CP2 review, minor (a)): `bootstrap` never checks these facts, and the stop's image does not
carry them all (I2); they are the WAL interface's promise, inside the trusted restart contract's
`bootOkR`, to be discharged by the WAL collaborator's crash-model spec (C6). -/
def walReadFacts (σ : StorContents) : Prop :=
  (∀ (j : Nat) (e : EntryM), σ.ents[j]? = some e → uint.nat e.Index' = σ.b + 1 + j) ∧
    σ.last ≤ 2 ^ 61 - 1 ∧ σ.b ≤ σ.commit ∧ σ.commit ≤ σ.last ∧
    ((σ.snap = none ∧ σ.base = entryID.mk (W64 0) (W64 0)) ∨
      ∃ m, σ.snap = some (SnapshotM.mk [] m) ∧ σ.base = entryID.mk m.Term' m.Index')

/-- I4 gives F3: a snapshot record's term is the base's. -/
theorem walReadFacts_F3 (σ : StorContents) (h : walReadFacts σ) :
    ∀ m' : SnapshotMetadataM, σ.snap = some (SnapshotM.mk [] m') → m'.Term' = σ.base.term' := by
  intro m' hm
  rcases h.2.2.2.2 with ⟨hn, -⟩ | ⟨m, hs, hb⟩
  · rw [hn] at hm; cases hm
  · rw [hs] at hm; cases hm; rw [hb]

/-- `DurAgrees` passes to a prefix of the committed log. -/
theorem durAgrees_prefix (S : RaftState) (l l' : List LogEntry) (hp : l <+: l')
    (h : DurAgrees S l') : DurAgrees S l := by
  intro i e hi he
  obtain ⟨t, rfl⟩ := hp
  exact h i e hi (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 he).1]; exact he)

/-- **What a restart's `bootstrap` gives the WAL** (its contract's `bootOkR`; D2): `wal.Open` and
`ReadAll` of the stopped member's files (`srvFiles`' `walFiles`) leave the WAL `w` open in the
configuration's WAL directory, read (`walReady`), its records exactly `σ`, sized (the files' flag,
`walFiles … true`, kept: no `walRecs_unsize` on the restart path), with the member's metadata
(`id`, `cid`), and the right to close it with its files kept (`walPurgeRight`); and `σ` meets I1-I4
(`walReadFacts`). The graceful model's body: what `walFiles` describes, read back (the files of one
process's graceful stop). C6 replaces it by the crash model's (`ReadAll`'s post, `walCrashKeeps` and
the server's history invariant) and re-proves the two laws. -/
@[no_expose] def wal.restartOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) : IProp GF :=
  iprop((∃ (h : WalH GF) (Hs : WalHist), ⌜h.w = w⌝ ∗
      walOpenedH h cfg.DedicatedWALDir' id cid σ Hs true ∗ walPurgeRight h ∗
      -- (P5, 2026-11-25, approved by coordinator-E on #50) `ReadAll`'s history facts: every record
      -- synced, the indices within raft's room, and each prefix's (eager) fold with its commit at or
      -- below its last index (`walCommitLeFrom walFresh`, which gives the reader's `walCommitLe`)
      (letI := h.W; WalFs.walSyncedLb h.dir Hs.length) ∗
      ⌜walIdxLe (2 ^ 61 - 1) Hs ∧ walCommitLeFrom walFresh Hs⌝) ∗
    ⌜walReadFacts σ⌝)

/-- **The read's pure facts** (I1-I4; the slot kept). -/
theorem wal.restartOk_facts (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) :
    wal.restartOk (GF := GF) cfg id cid w σ ⊢ wal.restartOk cfg id cid w σ ∗ ⌜walReadFacts σ⌝ := by
  unfold wal.restartOk
  iintro ⟨Hw, %Hf⟩
  iframe Hw
  ipureintro; exact ⟨Hf, Hf⟩

/-- **What the restarted server takes from `wal.restartOk`** (`wal.bootOk_start`'s restart form):
the open WAL `h` at `w`, the WAL's durability allocated at the restart's view `⟨S, σ.hs, none, l₀⟩`, for the
durable state `S` the stopped member's image holds (`wal.stopImage`: `StorageHolds S σ`, the records'
certificate, a committed log the durable log agrees with) and a committed log `l₀` reaching the records'
base (`rnDur_alloc_view`, `viewOk_restart`; `DurAgrees S l₀` by prefix); the image's WAL slot given back;
and what `NewStorage` and `Close` take, as at a first start. -/
theorem wal.restartOk_start (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) (cl : Cluster) (S : RaftState) (i : w64) (l₀ : List LogEntry)
    (hl : l₀.length = σ.b) :
    wal.restartOk (GF := GF) cfg id cid w σ ∗ wal.stopImage cl S σ i ∗ isCommittedLogLb cl l₀ ⊢
      |={⊤}=> ∃ (h : WalH GF) (ν : WalNames GF), ⌜h.w = w⌝ ∗ rnDurInv cl ν h ∗
        ghostVar ν.view (1 : Qp).half (⟨S, σ.hs, none, l₀⟩ : WalView) ∗
        token ν.ok ∗ token ν.stop ∗ token ν.app ∗ walCommitLb ν l₀ ∗
        wal.stopImage cl S σ i ∗
        storage.walOpen h 1 ∗ walMetaIs h id cid ∗ walPurgeRight h ∗
        ⌜h.dir = cfg.DedicatedWALDir'⌝ := by
  unfold wal.restartOk
  iintro ⟨⟨⟨%h, %Hs0, %Hw, Hwo, Hp, -, -⟩, %Hf⟩, Hsi, #Hl0⟩
  ihave Hwo := walOpenedH_walOpened _ _ _ _ _ _ _ $$ Hwo
  icases wal.stopImage_elim cl S σ i $$ Hsi with ⟨%Hs, #Hcert, ⟨%l', #Hl', %Hl'b, %Hag⟩⟩
  icases isCommittedLogLb_agree cl l₀ l' $$ [$Hl0 $Hl'] with %Hpre
  have hpre : l₀ <+: l' := by
    rcases Hpre with h | h
    · exact h
    · have := h.length_le
      have heq : l' = l₀ := h.eq_of_length (by omega)
      rw [heq]; exact List.prefix_refl _
  have hag0 : DurAgrees S l₀ := durAgrees_prefix S l₀ l' hpre Hag
  have hv : ViewOk ⟨S, σ.hs, none, l₀⟩ σ :=
    viewOk_restart S σ l₀ Hs.1 (by omega) (by rw [hl]; exact Hf.2.2.1) hag0
  icases walOpened_elim _ _ _ _ _ _ $$ Hwo with ⟨Ho, Hr, Hm, %Hd⟩
  imod rnDur_alloc_view cl h σ _ hv rfl $$ [Hr Hcert] with ⟨%ν, #Hinv, Hv, Hok, Hst, Hap, #Hlb⟩
  · iframe Hr Hcert
  ihave Hsi2 := wal.stopImage_intro cl S σ i Hs.1 Hs.2.1 Hs.2.2 $$ [Hcert Hl']
  · iframe Hcert
    iexists l'
    iframe Hl'
    ipureintro; exact ⟨Hl'b, Hag⟩
  imodintro
  iexists h, ν
  iframe Hinv Hv Hok Hst Hap Hlb Hsi2 Ho Hm Hp
  ipureintro; exact ⟨Hw, Hd⟩


/-- (P5, 2026-11-25) **What a first start's crash-aware durability takes from `wal.bootOk`**: the open WAL
`h` at `w`, its records with their (empty) history (`rnDurK_alloc`'s), the empty prefix synced, and what
`NewStorage` and `Close` take. -/
theorem wal.bootOk_startK (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64) (w : Loc) :
    wal.bootOk (GF := GF) cfg id cid w ⊢
      ∃ h : WalH GF, ⌜h.w = w⌝ ∗ walRecsH h walFresh [] true ∗
        (letI := h.W; WalFs.walSyncedLb h.dir 0) ∗
        storage.walOpen h 1 ∗ walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜h.dir = cfg.DedicatedWALDir'⌝ := by
  unfold wal.bootOk
  iintro ⟨%h, %Hw, Hwo, Hp⟩
  icases walOpenedH_elim _ _ _ _ _ _ _ $$ Hwo with ⟨Ho, Hr, Hm, %Hd⟩
  icases walRecsH_synced0 h _ _ _ $$ Hr with ⟨Hr, #Hsy⟩
  iexists h
  iframe Hr Hsy Ho Hm Hp
  ipureintro; exact ⟨Hw, Hd⟩

/-- (P5, 2026-11-25) **What a restart's crash-aware durability takes from `wal.restartOk`**: the open WAL
`h` at `w`, its records `σ` with their history `Hs` (the fold of `Hs`), the whole history synced, its
index and commit bounds, the read's facts, and what `NewStorage` and `Close` take. -/
theorem wal.restartOk_startK (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) :
    wal.restartOk (GF := GF) cfg id cid w σ ⊢
      ∃ (h : WalH GF) (Hs : WalHist), ⌜h.w = w⌝ ∗ walRecsH h σ Hs true ∗
        (letI := h.W; WalFs.walSyncedLb h.dir Hs.length) ∗
        ⌜walIdxLe (2 ^ 61 - 1) Hs ∧ walCommitLeFrom walFresh Hs ∧
          walFoldChkFrom walFresh Hs = some σ ∧ walReadFacts σ⌝ ∗
        storage.walOpen h 1 ∗ walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜h.dir = cfg.DedicatedWALDir'⌝ := by
  unfold wal.restartOk
  iintro ⟨⟨%h, %Hs, %Hw, Hwo, Hp, #Hsy, %Hb⟩, %Hf⟩
  icases walOpenedH_elim _ _ _ _ _ _ _ $$ Hwo with ⟨Ho, Hr, Hm, %Hd⟩
  icases walRecsH_fold h _ _ _ $$ Hr with ⟨Hr, %Hfo⟩
  iexists h, Hs
  iframe Hr Hsy Ho Hm Hp
  ipureintro; exact ⟨Hw, ⟨Hb.1, Hb.2, Hfo, Hf⟩, Hd⟩

end defs

end EtcdGrove
end Perennial
