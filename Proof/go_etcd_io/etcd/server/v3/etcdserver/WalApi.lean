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
(2) `bootstrap`'s first start takes `dataDirFresh` (`wal.bootRes`) and gives `walOpened … walFresh` and
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

/-- **What `Save` takes of the entries' objects `esL` saved as the models `es`, in a WAL of flag
`sized`** (raft-entsize §5, [r3g], 2026-11-09): unsized, today's `entriesAt esL es`; sized, each
object frozen at a wire content (`entRoC`) whose model is the saved entry's and whose size is
bounded (`entSizeOk`), which `saveEntry` writes as `MustMarshalMessage(e)` of that object
(`wal.go:1072-1078` at the pin `0b50f0426`). -/
def walSaveEnts (sized : Bool) (esL : List Loc) (es : List EntryM) : IProp GF :=
  if sized then
    iprop(∃ cs : List EntryC, ([∗list] l; c ∈ esL; cs, entRoC l c) ∗
      ⌜cs.map EntryC.model = es ∧ ∀ c ∈ cs, entSizeOk c⌝)
  else iprop(∃ es' : List EntryModel, entriesAt esL es' ∗ ⌜es'.map EntryModel.toM = es⌝)

/-- **The WAL contract** (sealed; trust boundary: names-only `serverstorage` and `wal`): the
storage `st`, an interface value, over the WAL `storage.walOf st`. Its operations are the laws
below.

(raft-entsize §5, [r3g], 2026-11-09) The `Save` and `Close` laws are over the records' flag
`sized` (`walRecs`'s). `Save` at `sized = true` takes the entries as objects frozen at contents
of bounded size (`walSaveEnts`): `serverstorage`'s `Save` calls `wal.Save(st, ents)`, which writes
each entry record as `pbutil.MustMarshalMessage(ents[i])` (`saveEntry`, `wal.go:1072-1078` at the
pin `0b50f0426`, from `Save`'s loop, `:1112`), so the record's bytes are the encoding of
the saved object's content, and the flag stays `true`. At `sized = false`, today's premise
(`entriesAt`). A failed `Save` commits no update and leaves the flag as it was (`walRecs`'s
docstring: the flag speaks of successful saves only). `SaveSnap` (the axiom review's W1) only drops
entries (`walSaveSnap`), so it keeps the flag. `Close` writes no record: the files keep the flag
(`walFiles … sized`). -/
@[no_expose] def isWalStorage (st : GoInterface) : IProp GF :=
  letI w := storage.walOf st
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (sized : Bool) (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
        (es : List EntryM) (Q : IProp GF),
      {{ storage.walOpen w q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ walSaveEnts sized esL es ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ sized ∗ ⌜WalSaveOk σ es⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSave σ hs.toM es) sized, COMM Q }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}) ∗
    □ (∀ (sized : Bool) (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM)
        (Q : IProp GF),
      {{ storage.walOpen w q ∗ sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs w σ sized ∗
                ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }>
            @ ⊤, ∅ <{ walRecs w (walSaveSnap σ md) sized, COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen w q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }}) ∗
    □ (∀ q : Qp, {{ storage.walOpen w q }} (App (Val #(methods si.ty go!"Sync" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen w q }}) ∗
    □ (∀ (sized : Bool) (σ : StorContents) (id cid : w64),
      {{ storage.walOpen w 1 ∗ walRecs w σ sized ∗ walMetaIs w id cid ∗
          walPurgeRight (walDirOf w) ∗ ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ walFiles (walDirOf w) id cid σ sized) ∨
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
`Save`: the records saved, or the environment failed (the raft loop then calls `lg.Fatal`;
`walSaveOk`, in `diskOk`, as for `SaveSnap` and `Close`). (2026-11-03, R2b-1 stage 5, the user's
choice: until then on an error some records, a second atomic update; with records unknown after a
failed `Save`, the apply thread's own `SaveSnap` could not show its precondition.) -/
theorem walSave_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
    (es : List EntryModel) (Q : IProp GF) :
    isWalStorage st ⊢
      {{ storage.walOpen (storage.walOf st) q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
          AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ ∗
                ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs (storage.walOf st) (walSave σ hs.toM (es.map EntryModel.toM)),
              COMM Q }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, #HS, -, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %false %q %hp %hs %sl %esL %(es.map EntryModel.toM) %Q
  iintro !> %Φ ⟨Ho, Hh, #Hsl, He, HAU⟩ HΦ
  iapply HS $$ [Ho Hh He HAU] HΦ
  iframe Ho Hh Hsl HAU
  simp only [walSaveEnts, Bool.false_eq_true, ↓reduceIte]
  iexists es
  iframe He
  ipureintro; rfl

/-- (raft-entsize §5, [r3g], 2026-11-09) **`Save` into a sized WAL**: the entries as objects frozen
at contents of bounded size whose models are the saved entries (`walSaveEnts true`); the records
stay sized. -/
theorem walSaveSized_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
    (cs : List EntryC) (Q : IProp GF) :
    isWalStorage st ⊢
      {{ storage.walOpen (storage.walOf st) q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗
          ([∗list] l; c ∈ esL; cs, entRoC l c) ∗ ⌜∀ c ∈ cs, entSizeOk c⌝ ∗
          AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ true ∗
                ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
            @ ⊤, ∅ <{ walRecs (storage.walOf st) (walSave σ hs.toM (cs.map EntryC.model)) true,
              COMM Q }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, #HS, -, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %true %q %hp %hs %sl %esL %(cs.map EntryC.model) %Q
  iintro !> %Φ ⟨Ho, Hh, #Hsl, He, %Hsz, HAU⟩ HΦ
  iapply HS $$ [Ho Hh He HAU] HΦ
  iframe Ho Hh Hsl HAU
  simp only [walSaveEnts, ↓reduceIte]
  iexists cs
  iframe He
  ipureintro; exact ⟨rfl, Hsz⟩

/-- (out_size C3, 2026-11-12) **The entry objects `esL` are frozen at contents of bounded size
holding `es`** (persistent): what a sized WAL `Save` (`walSaveSized_spec`) and the sized storage's
`Append` (`isRNMemStor`) take; a `Ready`'s entries are so in the server's cluster, which bounds
proposed data (`readyEnts_sized`). -/
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

/-- (out_size C3, MAJ-2) **The raft loop's `Save` into its sized WAL** (`walSaveSized_spec` over
`rnEntsSized`): the entries' objects at sized contents, the records staying sized. -/
theorem walSaveRn_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) (hp : Loc) (hs : HardStateModel) (sl : GoSlice) (esL : List Loc)
    (es : List EntryModel) (Q : IProp GF) :
    isWalStorage st ⊢
      {{ storage.walOpen (storage.walOf st) q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗
          rnEntsSized esL es ∗
          AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ true ∗
                ⌜WalSaveOk σ (es.map EntryModel.toM)⌝ }>
            @ ⊤, ∅ <{ walRecs (storage.walOf st) (walSave σ hs.toM (es.map EntryModel.toM)) true,
              COMM Q }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }} := by
  iintro #Hw
  iintro !> %Φ ⟨Ho, Hh, #Hsl, #Hsz, HAU⟩ HΦ
  unfold rnEntsSized
  icases Hsz with ⟨%cs, #Hb, %Hcs⟩
  ihave #HS := walSaveSized_spec st si hst q hp hs sl esL cs Q $$ Hw
  rw [← Hcs.1]
  iapply HS $$ [Ho Hh HAU] HΦ
  iframe Ho Hh Hsl Hb HAU
  ipureintro; exact Hcs.2

/-- `SaveSnap`: the snapshot record saved (or the environment failed: the apply thread panics on an
error, the raft loop calls `lg.Fatal`; `walSaveOk`, already in `diskOk`). -/
theorem walSaveSnap_spec (st : GoInterface) (si : GoInterfaceOk) (hst : st = GoInterface.ok si)
    (q : Qp) (sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (Q : IProp GF)
    (sized : Bool := false) :
    isWalStorage st ⊢
      {{ storage.walOpen (storage.walOf st) q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          AU <{ ∃∃ (σ : StorContents), walRecs (storage.walOf st) σ sized ∗
                ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }>
            @ ⊤, ∅ <{ walRecs (storage.walOf st) (walSaveSnap σ md) sized, COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen (storage.walOf st) q ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smPtsV mp dq' md ∗
          ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ storage.walSaveOk⌝) }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, -, #HS, -, -⟩
  rw [hst] at Heq; cases Heq
  ispecialize HS $$ %sized %q %sn %mp %dq %dq' %md %Q
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
    (σ : StorContents) (id cid : w64) (sized : Bool := false) :
    isWalStorage (GF := GF) st ⊢
      {{ storage.walOpen (storage.walOf st) 1 ∗ walRecs (storage.walOf st) σ sized ∗
          walMetaIs (storage.walOf st) id cid ∗ walPurgeRight (walDirOf (storage.walOf st)) ∗
          ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods si.ty go!"Close" si.v)) (Val #()))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ walFiles (walDirOf (storage.walOf st)) id cid σ sized) ∨
          ⌜¬ storage.walCloseOk⌝ }} := by
  unfold isWalStorage
  iintro ⟨%si', %Heq, -, -, -, #HC⟩
  rw [hst] at Heq; cases Heq
  ispecialize HC $$ %sized %σ %id %cid
  iexact HC

/-- **An opened WAL** (what `bootstrap`'s contract gives: a first start's `wal.Create(dir,
metadata)` at `walFresh`, a restart's `wal.Open` + `ReadAll` of the files `walFiles dir id cid σ` at
`σ`): open, read (`walReady`, what `NewStorage` needs), its records `σ`, its metadata the member's,
in the directory `dir`.

(raft-entsize §5, [r3g], 2026-11-09) **`sized`** (default `false`): the records' flag (`walRecs`'s).
`wal.Create` writes no entry record, so a first start's WAL is sized (`wal.bootOk`: `true`). A
restart's would carry its files' flag (`walFiles … sized`) with, at `true`, the replayed entries'
contents (`ReadAll`'s decoding and `D2`): deferred to the restart contract's work. -/
def walOpened (w : Loc) (dir : GoString) (id cid : w64) (σ : StorContents) (sized : Bool := false) :
    IProp GF :=
  iprop(storage.walOpen w 1 ∗ walRecs w σ sized ∗ walMetaIs w id cid ∗
    ⌜storage.walReady w ∧ walDirOf w = dir⌝)

/-- `walOpened`'s parts (its intro is the definition's; this is what a client uses). -/
theorem walOpened_elim (w : Loc) (dir : GoString) (id cid : w64) (σ : StorContents)
    (sized : Bool := false) :
    walOpened (GF := GF) w dir id cid σ sized ⊢
      storage.walOpen w 1 ∗ walRecs w σ sized ∗ walMetaIs w id cid ∗
        ⌜storage.walReady w ∧ walDirOf w = dir⌝ := by
  unfold walOpened; iintro H; iexact H

/-! ### The WAL's slots in the boot hub

(2026-11-03, the first slots of the convention the user approved: `notes/spec-first-plan.md`, "The
slot convention".) `bootstrap`'s contract, `bootOk` and `NewServer.spec` name the WAL only through
these, sealed: a change to what the WAL takes or gives at boot changes their bodies and laws, not
the hub's text. No `wal.bootCfg` (the WAL places no condition on the configuration); `wal.Names`
and `wal.srvInv` come with the raft loop's durability invariant (R2b-1 stages 3c/4). -/

/-- **What a caller of `bootstrap` (through `NewServer`) hands the WAL and the backend**: the
configuration's data directory fresh, a first start's (no WAL, no backend file; from program
start, `startRights`), with no dedicated WAL directory: the scope in which the data directory holds
the WAL, every starter's configuration. (Sweep repairs 1, W3/W4, 2026-11-07: until then the WAL
directory's `walDirFresh`, which said nothing of the backend file a first start opens.) -/
@[no_expose] def wal.bootRes (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : IProp GF :=
  iprop(dataDirFresh cfg.DataDir' ∗ ⌜cfg.DedicatedWALDir' = go!""⌝)

/-- `wal.bootRes`'s intro: a configuration whose data directory is `d`, with no dedicated WAL
directory, takes `d`'s token. -/
theorem wal.bootRes_intro (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (d : GoString)
    (hd : cfg.DataDir' = d) (hw : cfg.DedicatedWALDir' = go!"") :
    dataDirFresh (GF := GF) d ⊢ wal.bootRes cfg := by
  unfold wal.bootRes; subst hd; iintro H; iframe H; ipureintro; exact hw

/-- **What `bootstrap` gives the WAL** (its contract's `bootOk`): the new WAL `w` opened in the
configuration's WAL directory with the member's metadata and no records (`walOpened … walFresh`),
and the right to close it with its files kept (the purge's, `walPurgeRight`). (raft-entsize §5,
[r3g], 2026-11-09) Sized (`true`): `wal.Create` writes the metadata, an empty snapshot record and no
entry record, so every entry record (none) is of a content of bounded size. -/
@[no_expose] def wal.bootOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) : IProp GF :=
  iprop(walOpened w (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir') id cid walFresh true ∗
    walPurgeRight (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'))

/-- **What the server takes from `wal.bootOk`** (narrow: the slot convention's elimination laws
give what their consumers take, never the slot's body; R2b-1 stage 3c, 2026-11-03, replacing
`wal.bootOk_storage`): the WAL's durability allocated over the fresh records (`rnDur_alloc`: the
invariant, the raft loop's view at the start and its "not failed" token, the stop's claim, the apply
thread's token, the handed log's lower bound), and what `NewStorage` and `Close` take: the open
token, whole, the WAL read, its metadata and the purge's right. -/
theorem wal.bootOk_start (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (cl : Cluster) :
    wal.bootOk (GF := GF) cfg id cid w ⊢
      |={⊤}=> ∃ ν : WalNames, rnDurInv cl ν w ∗ ghostVar ν.view (1 : Qp).half walView0 ∗
        token ν.ok ∗ token ν.stop ∗ token ν.app ∗ walCommitLb ν [] ∗
        storage.walOpen w 1 ∗ ⌜storage.walReady w⌝ ∗ walMetaIs w id cid ∗
        walPurgeRight (walDirOf w) ∗
        -- (2026-11-04, R2b-3d) the WAL's directory, the configuration's (the stop image's `srvFiles`)
        ⌜walDirOf w = config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'⌝ := by
  unfold wal.bootOk
  iintro ⟨Hw, Hp⟩
  icases walOpened_elim _ _ _ _ _ _ $$ Hw with ⟨Ho, Hr, Hm, %Hrd⟩
  imod rnDur_alloc cl w $$ Hr with ⟨%ν, #Hinv, Hv, Hok, Hst, Hap, #Hlb⟩
  imodintro
  iexists ν
  rw [Hrd.2]
  iframe Hinv Hv Hok Hst Hap Hlb Ho Hm Hp
  ipureintro; exact ⟨Hrd.1, rfl⟩

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
  iprop(walOpened w (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir') id cid σ true ∗
    walPurgeRight (config.walDirOf cfg.DataDir' cfg.DedicatedWALDir') ∗ ⌜walReadFacts σ⌝)

/-- **The read's pure facts** (I1-I4; the slot kept). -/
theorem wal.restartOk_facts (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) :
    wal.restartOk (GF := GF) cfg id cid w σ ⊢ wal.restartOk cfg id cid w σ ∗ ⌜walReadFacts σ⌝ := by
  unfold wal.restartOk
  iintro ⟨Hw, Hp, %Hf⟩
  iframe Hw Hp
  ipureintro; exact ⟨Hf, Hf⟩

/-- **What the restarted server takes from `wal.restartOk`** (`wal.bootOk_start`'s restart form):
the WAL's durability allocated at the restart's view `⟨S, σ.hs, none, l₀⟩`, for the durable state `S`
the stopped member's image holds (`wal.stopImage`: `StorageHolds S σ`, the records' certificate, a
committed log the durable log agrees with) and a committed log `l₀` reaching the records' base
(`rnDur_alloc_view`, `viewOk_restart`; `DurAgrees S l₀` by prefix); the image's WAL slot given back;
and what `NewStorage` and `Close` take, as at a first start. -/
theorem wal.restartOk_start (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) (cl : Cluster) (S : RaftState) (i : w64) (l₀ : List LogEntry)
    (hl : l₀.length = σ.b) :
    wal.restartOk (GF := GF) cfg id cid w σ ∗ wal.stopImage cl S σ i ∗ isCommittedLogLb cl l₀ ⊢
      |={⊤}=> ∃ ν : WalNames, rnDurInv cl ν w ∗
        ghostVar ν.view (1 : Qp).half (⟨S, σ.hs, none, l₀⟩ : WalView) ∗
        token ν.ok ∗ token ν.stop ∗ token ν.app ∗ walCommitLb ν l₀ ∗
        wal.stopImage cl S σ i ∗
        storage.walOpen w 1 ∗ ⌜storage.walReady w⌝ ∗ walMetaIs w id cid ∗
        walPurgeRight (walDirOf w) ∗
        ⌜walDirOf w = config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'⌝ := by
  unfold wal.restartOk
  iintro ⟨⟨Hw, Hp, %Hf⟩, Hsi, #Hl0⟩
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
  icases walOpened_elim _ _ _ _ _ _ $$ Hw with ⟨Ho, Hr, Hm, %Hrd⟩
  imod rnDur_alloc_view cl w σ _ hv rfl $$ [Hr Hcert] with ⟨%ν, #Hinv, Hv, Hok, Hst, Hap, #Hlb⟩
  · iframe Hr Hcert
  ihave Hsi2 := wal.stopImage_intro cl S σ i Hs.1 Hs.2.1 Hs.2.2 $$ [Hcert Hl']
  · iframe Hcert
    iexists l'
    iframe Hl'
    ipureintro; exact ⟨Hl'b, Hag⟩
  imodintro
  iexists ν
  rw [Hrd.2]
  iframe Hinv Hv Hok Hst Hap Hlb Hsi2 Ho Hm Hp
  ipureintro; exact ⟨Hrd.1, rfl⟩


end defs

end EtcdGrove
end Perennial
