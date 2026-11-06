/-
**A member's stop and restart: the server's vocabulary, drafted** (the restart plan's R2a,
2026-11-02, `notes/restart-plan.md`). Lean-first (no Rocq counterpart).

R2a states what the example (`examples/etcd/restart`) needs of the server at a stop and a restart, over
the predicates named here. Their content is the later sub-steps' (R2a: `opaque` placeholders; since
defined: the stop's in R2b-2 and R2c, the image in R2c).

* `srvStopRight s E γ ρ id dd` (exclusive): the right to stop the server `s` (apply environment
  `E`) of member `id` of the cluster `γ`, started at the request names `ρ` (`HardStop`). R2b-2 (2026-11-02): defined, the
  stop channel (at the stop request, `srvStopReq`, R2c-2), `done` with the image escrowed
  (`srvDoneInv`) and the escrow's claim; `Start` gives it (`start` makes the channels, at the
  slot's `DataDir` field, `srvStop.dataDirField`). Sealed (R2c review F5): its law for clients is
  `srvStopRight_dd`. (Until R2b-2 opaque and `NewServer`'s, without `ρ`.)
* `srvDiskImage γ ρ id dd` (exclusive): member `id`'s data directory, as its last incarnation's stop
  left it, that incarnation's request names `ρ` recorded: raft's hard state, log and last snapshot
  record (the WAL), the backend's buckets at its consistent index, the member and cluster ids. R2c
  (L2): the ghost image handed from one incarnation to the next; graceful stops only (the plan's
  Q4). It holds what the restarted member's `NewServer` takes of the ghost state in place of a
  first start's `memberBoot` (`examples/lib/etcdstart/Defs.lean`): the node API's restart token in place
  of `nodeBoot` (R2e, raft's restart from a durable state), the cluster's invariants at the
  recorded names. (R2c, 2026-11-02: no id state. A restart makes its incarnation's id share anew,
  at a fresh incarnation key, `idutil/Incarnations.lean`'s `idIncarnation_alloc`, with its new
  store's floor `srvFloorFact E₀'` as the key's claim facts; the ids' freshness across incarnations
  is the trusted `Next`'s assumption, `nonissues/etcd-request-id-restart-reuse.md`.) R2c and R2d split it between the image and
  `NewServer`'s restart premise. (2026-11-02, `Run`'s glue: until then a separate `srvRestartBoot`
  bundle the example supplied; the restarted member's own names, its wait registry and its store's
  index, are new, so the server allocates them, not the example.)
* `restartNames ρ ρ'` (pure, defined): the restarted incarnation's names `ρ'` agree with the stopped
  one's `ρ` on what the rest of the cluster and its clients see: raft's names, the KV state's ghost
  variable (`etcdKV`, the clients' invariants), the KV model of the committed log, the cluster's
  map of issued request ids and the member's id prefix. Its other names are its own. (Once the
  id state is keyed by incarnation, R2c, the agreement is on the cluster's id maps and the prefix,
  and the key is the one `idIncarnation_alloc` gives.)
* `bootstrapRestartContract cfg U γ id ctxs N dir`: `bootstrap`'s contract on a data directory that
  holds member `id`'s image (`bootstrapContract`'s restart case, L3): with the image, an error or
  the record of a restart (`bootOk`'s restart case). R2c.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Spec.go_etcd_io.raft.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **The files of a stopped member's data directory hold `σ` and `D`** (made of the two closes'
trust-boundary tokens; DRAFT R2c, defined in R2b-3c): the WAL in `<dd>/member/wal` reads back (`ReadAll` from its newest
valid snapshot record: of the highest index at or below the last hard state's commit,
`wal.ValidSnapshotEntries`, `newestSnapshotEntry`, `bootstrap.go:437-462`; 2026-11-03, the final
whole-`bootOk` review: until then "its last snapshot record", which Go does not read when the apply
loop's snapshot record follows a newer received one, and which did not exclude `recoverSnapshot`'s
panic, `bootstrap.go:482`) as the records `σ` -- the snapshot record at `σ.b`, the hard state `σ.hs`, the
entries `σ.ents` -- and the bbolt file at `<dd>/member/snap/db` holds `D`; the WAL's metadata names the member `id`
(R2c review, second tier 1: `bootOkR`'s `cv.ID' = id` comes from it). (2026-11-04, R2b-3c part 2b:
defined, as `WalApi.lean`'s plan (3) says: the closed WAL's files in the configuration's WAL
directory with no dedicated one, `walFiles`, and the bbolt file, `fileHolds`, the two closes'
outputs.) Exclusivity per directory
(two tokens of one directory) is not stated: an open question for R2b, which makes it. Made by the stop's
closes (R2b: `wal.Close`, `backend.Close`, axioms at the trust boundary, from what the server's
`Save`s and the backend's commits wrote), consumed by `bootstrap`'s restart contract. A graceful
stop in the same process: every write is visible to the next open, synced or not (the plan's
Q4). -/
def srvFiles (dd : GoString) (id : w64) (σ : StorContents) (D : backend.Data) : IProp GF :=
  iprop((∃ cid : w64, walFiles (config.walDirOf dd "") id cid σ) ∗
    backend.fileHolds (config.backendPathOf dd) D)

/-- **`cs` is a conf state `buildConfStateFromV3store` builds from the `members` bucket of `D`**
(R2c's draft opaque `v3ConfState`, defined 2026-11-04, the restart plan's R2b-3d gap 3; R2c review
F4: from the bucket, not the in-memory members): the bucket's entries are those of some members
`ms` with distinct ids, each under its id's key with its JSON (`memberKey mm.id ↦ memberEnc mm`, the
shape `membersDecode` states and the apply thread writes; `MustReadMembersFromBackend` unmarshals
each value back to its member). `cs`'s voters are the non-learners' ids and its learners the
learners', in any order (Go ranges over a map), with no joint state. A relation, not a
function, because of that order. -/
def v3ConfStateIs (D : backend.Data) (cs : ConfStateM) : Prop :=
  ∃ ms : List apply.MemberM,
    (∀ k v, ((D.lookup go!"members").getD ∅).lookup k = some v ↔
      ∃ mm ∈ ms, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm) ∧
    (ms.map (·.id)).Nodup ∧
    cs.Voters' ≡ₚ (ms.filter (fun mm => !mm.isLearner)).map (·.id) ∧
    cs.Learners' ≡ₚ (ms.filter (·.isLearner)).map (·.id) ∧
    cs.VotersOutgoing' = [] ∧ cs.LearnersNext' = [] ∧ cs.AutoLeave' = false

/-- **Member `id`'s data directory as its last stop left it, at that incarnation's request names
`ρ`** (DRAFT, R2c; see the file header and `notes/restart-plan.md`, "R2c: the image's content"):
- raft's part (the WAL): the id vacant (`node.Stop`'s `nodeVacant`), the node's durable state
  `S` (`raftState`, which the stopped raft loop held), and the WAL's records `σ` holding it
  (`StorageHolds`, what `RestartNode`'s update checks);
- the backend's part (the bbolt file): `D` is the image of a committed prefix `A` of the server's
  log through the consistent index `i` (`imageAt`, the snapshot path's certificate, `dbImage`'s
  content at the stopped incarnation's names), its stored term `t` (`metaIs`);
- between them: the WAL's snapshot at or below the backend's index, the backend's index at or
  below the WAL's commit (etcd's order: a snapshot is of the applied state, an entry is applied
  after the `Save` of its commit), so that `bootstrap` keeps the file (`recoverSnapshot` opens a
  `.snap.db` only when the file's index is below the snapshot's);
- the configuration point raft restarts with: `bootstrap` replaces the WAL snapshot's `ConfState`
  by the backend's (`buildConfStateFromV3store`, `v3ConfStateIs`): every conf state it can build is the
  membership at `i`; `RestartNode` takes any point from the storage's base to its commit;
- the bootstrap log applied (`γ.cl.bootLen ≤ i`; R2c review F4, a scope restriction: a member
  stopped before its first `Ready` was applied would restart with an empty members bucket, which
  etcd copes with and these statements do not; `restart3`'s stop must provide it);
- the storage registry's authority (R2c review F3: the restart registers its new `MemoryStorage`
  in the same registry, `restartNames` keeping raft's names), handed back by the stop;
- the files holding `σ` and `D` (`srvFiles`) and the backend file's directory entry (`pathOwn`,
  which a first start's `bootOk` gives and the stop returns), in the directory `dd` the right to
  stop records (`srvStopRight`; R2c review F2). (R2c review F5: the KV names' `c0` is `0`, as
  `restModel (W64 0)` reads the image's buckets.)

(#7-cmp's Freeze, 2026-11-02, the user's approval: `imageAt` restated in place, by the KV names'
compaction mode at records of the committed log's compaction revision. **Open, the restart path's
(RESTART-RCPT, `notes/image-cmp-plan.md`):** in compaction mode a restart restores the image, whose
`restoreRcptM` needs the image's KV log's receipt `⧖ (logCh (kvModel ρ.rd.kv A))`, which `dbImage`
carries and this predicate does not yet.) -/
def srvDiskImage (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) : IProp GF :=
  iprop(∃ (S : RaftState) (σ : StorContents) (i : w64) (A : List EntryModel)
      (D : backend.Data) (m : Membership) (M : GMap Loc MemStorNamesRec),
    nodeVacant γ.cl id ∗ raftState γ.cl id S ∗ ⌜StorageHolds S σ⌝ ∗
    ⌜ρ.rd.raft.raft = γ ∧ ρ.rd.kv.c0 = W64 0⌝ ∗ srvRLogLb ρ.rd.raft A ∗
    ⌜uint.Z i = uint.Z ρ.rd.raft.ai0 + A.length ∧
      imageAt ρ.rd.kv γ.boot i (ρ.rd.raft.pre ++ A) A D⌝ ∗
    ⌜σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit ∧ γ.cl.bootLen ≤ uint.nat i⌝ ∗
    confAt γ.cl (uint.nat i) m ∗ ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝ ∗
    -- (R2d, Q14 (a), 2026-11-06; DRAFT) the WAL records' snapshot certificate: at index `0`, or
    -- their snapshot (of no data, at their base) valid, what the restart's `MemoryStorage` attaches
    -- with (`restartStorage`)
    walSnapCert γ.cl σ ∗
    (letI : MemStorReg GF := ⟨γ.reg⟩; memStorRegAuth M) ∗
    srvFiles dd id σ D ∗ backend.pathOwn (config.backendPathOf dd))

/-- The image records the raft names it is at (`ρ.rd.raft.raft = γ`). -/
theorem srvDiskImage_raft (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) :
    srvDiskImage (GF := GF) γ ρ id dd ⊢ ⌜ρ.rd.raft.raft = γ⌝ ∗ srvDiskImage γ ρ id dd := by
  refine (persistent_entails_left ?_).trans sep_comm.1
  unfold srvDiskImage
  iintro ⟨%S, %σ, %i, %A, %D, %m, %M, -, -, -, %Hρ, -⟩
  ipureintro; exact Hρ.1

/-- **The server `s`'s data directory is `dd`, its WAL in it** (persistent; R2b-2): the
configuration's `DataDir` field is `dd` and its `DedicatedWALDir` field empty, so that the WAL is
`<dd>/member/wal` (`ServerConfig.WALDir`), as `srvFiles` says. Per field (as the snapshot path's
`srvSnapRes`): `start` writes other fields of `Cfg` (`SnapshotCount`, ...), whose whole struct is
read-only only after it (R2b-2 review F1: a read-only points-to of the whole `Cfg` contradicted
`memberBuilt`'s ownership of those fields). `NewServer` gives it, and `Start`'s stop right names
`dd` (R2c review F2). -/
def srvDataDir (s : Loc) (dd : GoString) : IProp GF :=
  iprop(srvCfgFieldAddr s go!"DataDir" ↦□ dd ∗
    srvCfgFieldAddr s go!"DedicatedWALDir" ↦□ (go!"" : GoString))

instance srvDataDir_persistent (s : Loc) (dd : GoString) :
    Persistent (srvDataDir (GF := GF) s dd) := by
  unfold srvDataDir; infer_instance

/-- **The server at the request names `ρ` has applied the cluster's bootstrap log** (persistent;
R2b-2 review F2): an applied-index lower bound (`appliedAtLeast`, what `AppliedIndex()` returns) at
least the bootstrap log's length. What a stop request carries (`srvStopRight`'s stop bag): the image
needs `bootLen ≤ i` (R2c review F4), and `run`, shut down by a request sent right after `Start`,
could not give it otherwise. `restart3`'s `stop` gets it by waiting on `AppliedIndex()`. -/
def srvBootApplied (ρ : ReqNames) : IProp GF :=
  iprop(∃ v : w64, appliedAtLeast ρ.rd v ∗ ⌜ρ.rd.raft.raft.boot.length ≤ uint.nat v⌝)

instance srvBootApplied_persistent (ρ : ReqNames) : Persistent (srvBootApplied (GF := GF) ρ) := by
  unfold srvBootApplied; infer_instance

/-- **The boot evidence from an applied index** (R2c review F4): an index the server applied at
least, past the bootstrap log. -/
theorem srvBootApplied_of_applied (ρ : ReqNames) (v : w64)
    (h : ρ.rd.raft.raft.boot.length ≤ uint.nat v) :
    appliedAtLeast ρ.rd v ⊢ srvBootApplied (GF := GF) ρ := by
  unfold srvBootApplied
  iintro H
  iexists v
  iframe H
  ipureintro; exact h

/-- A reader's view of the server holds the applied index's invariant (`AppliedIndex()`'s
premise). -/
theorem isServerRead_applied (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    isServerRead (GF := GF) s E γr ⊢ srvAppliedInv s E γr := by
  iintro #H
  iunfold isServerRead at H
  icases H with ⟨%v, H⟩
  iunfold srvReadFieldsAt at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hai, -⟩
  iexact Hai

/-- The namespace of the stopped server's escrowed image (R2b-2). -/
def srvStopN : Namespace := nroot.@"srvStop"

/-- **What `done`'s close announces** (DRAFT, R2b-2; `notes/restart-plan.md`, "R2b: the stop"):
the image of member `id`'s data directory `dd` at the names `ρ` (`srvDiskImage`), escrowed for the
holder of the claim `c` (the stop right's): `run`'s deferred shutdown puts the image in before it
closes `done`; the claim's holder takes it out, once. -/
def srvDoneInv (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) (c : GName) : IProp GF :=
  inv srvStopN iprop(srvDiskImage γ ρ id dd ∨ token c)

instance srvDoneInv_persistent (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString)
    (c : GName) : Persistent (srvDoneInv (GF := GF) γ ρ id dd c) := by
  unfold srvDoneInv; infer_instance

/-- **The stop's scope** (2026-11-05, the restart plan's R2c-2; the user's Q2 (b)): the
configurations whose server `run`'s deferred shutdown can stop with an image: auth off (with auth
on, `Cleanup`'s auth closer is the apply thread's, not threaded; and a restart's image after
`AuthEnable` is the open gap H) and no compaction mode (`apply.cmpOwn` is both what `kv.Close`
takes and what the image's observation reads; and the image lacks the compaction-mode receipt,
RESTART-RCPT). No compactor follows from the latter (`NewServer` makes one only in compaction mode,
`srvStop.censusPart`). Carried in the stop request (`srvStopReq`), not in `run`'s precondition, so
that every started server's `run` has one spec. -/
def srvStop.scope (E : apply.AEnv GF) : Prop := E.authOn = false ∧ E.cmp = false

/-- **The stop's serving readers** (R2c-4): the store readers a member's serving stocks hold (the
API's and the watch server's, `64 + 64`), which the stop request returns for the backend's `Close`
(`storeReaders_retire`); named here, by the stop's owner, so that a client of the stop request names
no count (`etc/bounds-check.py`). -/
abbrev srvStopReaders (E : apply.AEnv GF) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate (64 + 64) (), mvcc.storeReader E.s E.γ)

/-- **A stop request** (2026-11-05, R2c-2; what `HardStop` sends on `s.stop` and `run` receives):
evidence that the server at the request names `ρ` applied the bootstrap log (`srvBootApplied`,
R2b-2 review F2), the stop's scope at the server's apply environment `E` (`srvStop.scope`), and the
server's data directory `dd` with no dedicated WAL directory (`srvDataDir`, which the image names:
the scope's other half), and (R2c-4, F-e) the store's readers of the serving stocks the server no
longer uses (`srvServeBuilt`'s 64 request readers and `srvWatchReaders`' 64 watch readers,
`mvcc.watchReader_storeReader`): with the slot's and the apply thread's, every reader of the store,
for the backend's `Close` (gap 4's census); the sender stopped serving first. Until R2c-2 the
request carried only `srvBootApplied ρ`, and `run.specStop` took the scope as premises; until R2c-4
the readers were `run.specStop`'s (`srvShutdownPre`), which a serving member cannot give at its
start. -/
def srvStopReq (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (dd : GoString) : IProp GF :=
  iprop(srvBootApplied ρ ∗ ⌜srvStop.scope E⌝ ∗ srvDataDir s dd ∗ srvStopReaders E)

/-- The stop request names only the request names' read side (`ρ.rd`): the same at the wait
registry `start` makes (R2c-4). -/
theorem srvStopReq_wait (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (w : GName) (dd : GoString) :
    srvStopReq (GF := GF) s E { ρ with wait := w } dd = srvStopReq s E ρ dd := rfl

/-- **A stop request made** (R2c review F4): the boot evidence, the scope, the data directory and
the serving readers. -/
theorem srvStopReq_intro (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (dd : GoString)
    (hsc : srvStop.scope E) :
    srvBootApplied ρ ∗ srvDataDir s dd ∗ srvStopReaders E ⊢ srvStopReq (GF := GF) s E ρ dd := by
  unfold srvStopReq
  iintro ⟨#Hb, #Hdd, Hr⟩
  iframe Hb Hdd Hr
  ipureintro; exact hsc

/-- The escrow names only the request names' read side (`ρ.rd`) (R2c-4). -/
theorem srvDoneInv_wait (γ : SrvRaft) (ρ : ReqNames) (w : GName) (id : w64) (dd : GoString)
    (c : GName) : srvDoneInv (GF := GF) γ { ρ with wait := w } id dd c = srvDoneInv γ ρ id dd c :=
  rfl

/-- **The right to stop the started server `s`** (R2b-2; defined in R2c-2; see the file header): `s.stop` (a
channel a stop request is sent on, `srvStopReq` at the server's apply environment `E`: R2c-2; until
then the request carried `srvBootApplied ρ` only; `run` receives it), and
`s.done`, whose close announces the image escrowed for the claim `c` (`srvDoneInv`), with the claim.
`start` makes both channels, so `Start` gives the right (R2b-2: until then `NewServer`, in the
draft). The data directory `dd` is the configuration's `DataDir` (R2c review F2; R2c-2: the right
records the field, so that a holder who knows the directory, `srvDataDir`, learns `dd`). Sealed (R2c
review F5, 2026-11-06; round 2's N2): a client sees the name and its law `srvStopRight_dd`; the
package's two proofs that make and open it, `start`'s and `HardStop`'s, `import all` this module
(`etc/import-all.txt`). -/
@[no_expose] def srvStopRight (s : Loc) (E : apply.AEnv GF) (γ : SrvRaft) (ρ : ReqNames) (id : w64)
    (dd : GoString) : IProp GF :=
  iprop(∃ (stc dnc : Loc) (γst γd : ChanNames) (c : GName),
    srvStopAddr s ↦□ stc ∗ isChanBag γst stc (V := Unit) (fun _ => srvStopReq s E ρ dd) ∗
    srvDoneAddr s ↦□ dnc ∗ ownBroadcastChan dnc γd (srvDoneInv γ ρ id dd c) .Unknown ∗
    token c ∗ srvCfgFieldAddr s go!"DataDir" ↦□ dd)

/-- The stop right's data directory is the server's (`srvDataDir`'s). -/
theorem srvStopRight_dd (s : Loc) (E : apply.AEnv GF) (γ : SrvRaft) (ρ : ReqNames) (id : w64)
    (dd dd' : GoString) :
    srvStopRight (GF := GF) s E γ ρ id dd ∗ srvDataDir s dd' ⊢
      ⌜dd = dd'⌝ ∗ srvStopRight s E γ ρ id dd := by
  unfold srvStopRight srvDataDir
  iintro ⟨⟨%stc, %dnc, %γst, %γd, %c, #Hs, #Hb, #Hd, Hdn, Hc, #Hdd⟩, #Hdd', -⟩
  icombine Hdd Hdd' gives %Heq
  isplitr
  · ipureintro; exact Heq
  iexists stc, dnc, γst, γd, c
  iframe Hs Hb Hd Hdn Hc Hdd

/-- (R2b-2's draft; defined 2026-11-05, R2b-3d stage 5b) **What `Cleanup` closes besides the apply
thread's resources**: the server's auth store with its `Close` (`authCloseOk`, `NewAuthStore`'s
with auth off, the user's decision: `notes/axiom-review/auth-close.md`), what `Cleanup`'s closer is
(`authCloser` at no resource). Auth off only, `restart3`'s mode: with auth on, the closer is the
apply thread's, at the token provider's admin share (`authCloser_of_inv`). (The lessor's stop right
is in the stop's slot, `srvStop.keep`; the KV store's closer and the backend's come back from the apply thread through
`sched.Stop`'s last job's post, R2b-2 review F3.) -/
def srvCleanupOwn (s : Loc) : IProp GF :=
  iprop(∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗ authCloseOk stl)

instance srvCleanupOwn_persistent (s : Loc) : Persistent (srvCleanupOwn (GF := GF) s) := by
  unfold srvCleanupOwn; infer_instance

/-- (2026-11-05, R2b-3d gap 4) **The store's readers `NewServer` keeps for the stop**: of the
`rdStockN - nJobRd` readers `NewStore` gives, all but the watch loops' (`wsLoopN`), the request
goroutines' and the watch service's run slots' (64 each, `memberUp`'s serving stocks), the
compactor's, the storage version monitor's and the apply thread's retired ones, and the apply
thread's own (`apply.kvOwn`). Until then `NewServer` dropped them. With every other reader,
`storeReaders_retire` and `storeRTs_shares` give the backend's `Close` the stock's shares of its
open token, as `NewServer`'s own error path does (R-D1). -/
abbrev srvKeepRdN (γst : mvcc.StoreNames) : Nat :=
  backend.rdStockN - mvcc.nJobRd γst.kb - mvcc.wsLoopN - 64 - 64 - 1 - 1 - 1 - 1

end defs

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **The `MemoryStorage` `bootstrappedWAL.MemoryStorage` rebuilds** (opaque, DRAFT R2c, R2d's to
define): `NewMemoryStorage`, then `ApplySnapshot` of the WAL's snapshot record at `σ.b` with the
conf state `cs`, `SetHardState(σ.hs)`, `Append(σ.ents)`. R2d defines it in raft's storage
vocabulary (`memLog`, `memEnd`, `memStorMeta`, `memStorFresh` at the snapshot) and proves from it
`RestartNode`'s `restartStorage`, as kvdurable's `kd_restartStorage`. -/
opaque memStorRestarted (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM) :
    IProp GF

/-- **The real backend's batch-lock resource, as a restart's `bootstrap` leaves it** (2026-11-03,
the whole-`bootOk` review, T1-B, option B3): `mvcc.lateWB`'s arms, the unregistered one with the
client's halves of the backend's exact ghosts at some values (`backend.pvckOwn`), not the empty ones
of a first start (`pvckEmpty`, false here: the `Key` bucket holds the stopped member's revisions,
and after a compaction its compaction keys are set; measured, `etc/spec-test/bootstrap/`). A
restart's `NewStore` (R2d) learns the values under the lock. Nothing on the restart path uses it
yet: `lateWD`, `KBReal.snap`, `kbBoot` take a backend `bootstrap` opened to carry `lateWB`, so R2d
merges the two (B1: `lateWB`'s arm at `pvckOwn`, `NewStore` deriving `pvckEmpty` by agreement) when
the two contracts merge. -/
def lateWBR (gx : GName) (γB : backend.BNames) : IProp GF :=
  iprop((dghostVar gx (DFrac.own (1 : Qp).half) (none : Option (Loc × mvcc.StoreNames)) ∗
      backend.pvckOwn γB) ∨ mvcc.lateWR gx)

/-- **The bootstrapped record of a restart** (DRAFT, R2c; `bootOk`'s restart case, L3): `bootOk`
with the changes marked `[R2c]`: no peers (so `RestartNode`), the storage rebuilt from the WAL's
records `σ` (`memStorRestarted`), the cluster's members recovered from the image's buckets at its
committed log `L`, the consistent index loaded at the image's `i` (`γA.m0`, `ciApplying`), the
backend file's data the image `D` (no fresh file's facts: `HD`, `HDr`, `HmEmpty` gone), the
batch lock's resource `lateWBR` (2026-11-03, the whole-`bootOk` review, T1-B: until then `lateWB`,
whose unregistered arm, an empty `Key` bucket, a restart does not meet). Kept as a first start's:
the remotes (`Hrms0`: `bootstrapClusterWithWAL` sets none either), the directory's members (a
static cluster, the plan's scope: the restart contract's premise). (2026-11-03, the whole-`bootOk`
review: the write-back stock `bootLeft N`, the hooks stated once, as `bootOk`.) -/
def bootOkR (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : SrvRaft) (id : w64)
    (N : Nat) (dir : w64 → List GoString) (σ : StorContents) (i : w64) (L : List EntryModel)
    (D : backend.Data) (M : GMap Loc MemStorNamesRec) (b : Loc) : IProp GF :=
  iprop(∃ (bs : bootstrappedServer) (sto : bootstrappedStorage) (bk : bootstrappedBackend)
      (bw : bootstrappedWAL) (bc : bootstrappedCluster) (bv : bootstrappedRaft) (cv : Config)
      (lok : GoInterfaceOk) (γs : MemStorNames) (pv : List Peer) (ps : List w64)
      (rms : List Loc) (cid : w64) (cil : Loc) (γA : ApplyNames)
      (d : mvcc.KBReal),
    -- the records
    "Hb" ∷ b ↦ bs ∗ "Hsto" ∷ bs.storage' ↦ sto ∗ "Hbk" ∷ sto.backend' ↦ bk ∗
    "Hbw" ∷ sto.wal' ↦ bw ∗ "Hbc" ∷ bs.cluster' ↦ bc ∗ "Hbv" ∷ bs.raft' ↦ bv ∗
    -- (the keep-alive stage's K7, 2026-11-01, the user's decision) the peers' round tripper a
    -- `*http.Transport` (`bootstrap`'s `prt`, from `rafthttp.NewRoundTripper`, `bootstrap.go:72`:
    -- `transport.NewTimeoutTransport`'s), which `NewServer` stores in `peerRt` and `LeaseRenew`
    -- forwards a follower's renewal through (`srvPeerRt`)
    "%Hprt" ∷ ⌜∃ t : Loc, bs.prt' =
      GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.net.http.Transport.ty, #t⟩⌝ ∗
    -- (2026-10-31, `notes/axiom-review/savesnap.md`) the WAL read (`bootstrapWAL`'s `ReadAll`),
    -- which `NewStorage`'s contract takes
    "%HwalR" ∷ ⌜storage.walReady bw.w'⌝ ∗
    -- (2026-10-31, the user's decision) and its open token, whole: the WAL `bootstrap` opened is the
    -- server's (`storage.walOpen`; the raft loop's `Save`s and `Close`, the apply thread's `SaveSnap`)
    "Hwalo" ∷ storage.walOpen bw.w' 1 ∗
    -- (D22 S-i, 2026-10-19) the snapshotter (`bootstrapSnapshot`'s `snap.New(lg, cfg.SnapDir())`,
    -- its fields set once), which the transport's snapshot handler and `applySnapshot` use
    "#Hss" ∷ snap.isSnapshotter bs.ss' ∗
    -- `b.raft`: the raft configuration (as `bootOk`'s, but `RestartNode`'s path: no peers)
    -- (2026-11-03, S2: until then `heartbeat ≠ 0`) the heartbeat as Go computes it
    -- (`bootstrap.go:574`, wrapping)
    "%Hraft" ∷ ⌜bv.lg' ≠ null ∧ bv.heartbeat' = cfg.TickMs' * W64 1000000 ∧
      ConfigValid cv ∧ cv.Logger' = interface.ok lok ∧
      cv.Storage' = memStorIface bv.storage' ∧
      sint.Z cv.MaxInflightMsgs' < 2 ^ 62 ∧
      cv.DisableProposalForwarding' = false ∧ cv.ReadOnlyOption' = W64 0 ∧
      cv.DisableConfChangeValidation' = false ∧
      (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) ∧
      cv.AsyncStorageWrites' = false ∧ cv.Applied' = W64 0 ∧
      cv.ID' = id ∧
      -- [R2c] no peers: `bootstrapRaftFromWAL` sets none, so `newRaftNode` calls `RestartNode`
      -- (`len(b.peers) == 0`); `ps` is the cluster's members (`Hmembers`), not peers
      pv = [] ∧ ps ≠ [] ∧ ps.Nodup ∧ W64 0 ∉ ps ∧
      cv.ID' ∈ ps ∧ γ.vs = ps ∧ srvBootLogOk ps γ.boot⌝ ∗
    "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
    "#Hreg" ∷ memStorReg bv.storage' γs ∗
    -- (D19r (B), 2026-10-18) the registry's authority, given empty, back with the new storage
    -- [R2c] (review F3) the registry's authority given at `M`, back with the new storage, a
    -- location not registered before
    "Hrauth" ∷ memStorRegAuth (GMap.insert bv.storage' γs.tuple M) ∗ "%HMn" ∷ ⌜M !! bv.storage' = none⌝ ∗
    -- the storage's lock
    "#Hmlock" ∷ memStorLock bv.storage' γs ∗
    -- [R2c] the storage `bootstrappedWAL.MemoryStorage` rebuilds from the WAL's records `σ`
    -- (`ApplySnapshot` of the WAL snapshot with the backend's `ConfState`, `SetHardState`,
    -- `Append`), in place of the fresh storage's tokens; R2d derives `RestartNode`'s
    -- `restartStorage` from it, as kvdurable's `kd_restartStorage`
    "Hrest" ∷ (∃ cs : ConfStateM, ⌜v3ConfStateIs D cs⌝ ∗ memStorRestarted bv.storage' γs σ cs) ∗
    "Hpeers" ∷ bv.peers' ↦* pv ∗
    -- the cluster
    "#Hcl" ∷ rnClusterOk bc.cl' ∗ "#Hrc" ∷ membership.isRaftCluster bc.cl' ∗
    "#Hcid" ∷ membership.clusterCid bc.cl' cid ∗ "%Hid" ∷ ⌜bc.nodeID' = id⌝ ∗
    -- (D43 M5e, 2026-10-26, the user's decision) its logger, read-only, not nil
    -- (`bootstrapClusterWithWAL`'s `NewCluster` sets `lg` from the configuration's logger): what
    -- `AddMember` and `RemoveMember` log through, `applyConfChange`'s
    "#Hclg" ∷ (∃ lgc : Loc, membership.rcLgAddr bc.cl' ↦□ lgc ∗ ⌜lgc ≠ null⌝) ∗
    -- (audit B4a, 2026-10-18) its `versionChanged` field, owned (the cluster not yet shared):
    -- `NewServer`'s `SetVersionChangedNotifier` writes it without the lock, and the cluster's
    -- apply contract `Hisc` (whose `SetVersion` reads it) is for after, the field read-only
    "Hvcn" ∷ (∃ v : Loc, membership.rcVersionChangedAddr bc.cl' ↦ v) ∗
    "#Hrms" ∷ bc.remotes' ↦*□ rms ∗ "#Hrmsi" ∷ ([∗list] m ∈ rms, memberRO dir m) ∗
    -- no remotes: `bootstrapClusterWithWAL` sets none (`bootstrap.go:430-433`), so `NewServer`
    -- calls `AddRemote` never
    "%Hrms0" ∷ ⌜rms = []⌝ ∗
    -- (2026-11-03, the final whole-`bootOk` review's M2: until then `Hdirps`, a fact of the
    -- caller's `dir` and `γ.vs`; a restart's `NewServer`, when one is stated, will take it as a premise, `rafthttp.bootCfg`)
    -- (D21 M2, 2026-10-19) the members' records name each member's own URLs (`dir`, D21b's
    -- deployment fact): `Members()` returns members whose peer URLs are the directory's;
    -- (2026-10-24, rafthttp stage 6d) raft's peers, in order (both sorted by id: `Members()`'s
    -- `MembersByID`, `bootstrapRaftFromCluster`'s peers from `MemberIDs()`)
    "#Hmembers" ∷ □ (∀ Φ : val → IProp GF,
      (∀ (sl : GoSlice) (ms : List (Loc × w64)), ⌜ms.map Prod.snd = ps⌝ -∗
        sl ↦* ms.map Prod.fst -∗ ([∗list] p ∈ ms, memberDirIs dir p.1 p.2) -∗ Φ #sl) -∗
      WP (App (Val (bc.cl' @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members"))
        (Val #())) {{ Φ }}) ∗
    -- the cluster's contracts (unit N4, 2026-10-17): the lessor's (`Version()`), and the apply
    -- package's at the backend's batch lock and any frozen hook (its writes: one write-back
    -- each, `membershipBackend`'s `LockInsideApply`/`Unlock`, as the stores', D14f); (D22,
    -- 2026-10-23: the backend over every bucket) its writes' effect on the tracked buckets and
    -- its in-memory members (`srvRestOwn`), `SetDowngradeInfo` with the write right
    -- (`srvRestRW`)
    "#Hclok" ∷ lease.clusterOk (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty) #bc.cl') ∗
    -- (srvBuildGap's rows, 2026-10-17) its `Version()` monotone, for `start`'s
    -- `clusterVersionOk`
    "#Hcvm" ∷ (∃ γcv : GName, clusterVersionMono bc.cl' γcv) ∗
    -- (D22 receiver epochs, S7e, 2026-10-23) on whichever backend its `be` field names, which
    -- `bootstrap` set to the boot backend and gives owned (`clusterBeOn`: no lock guards it, the
    -- apply thread is its only user); until then for the boot backend's batch lock only
    "#Hisc" ∷ clusterApplyOk bc.cl' ∗
    "HclBe" ∷ clusterBeOn bc.cl' d.be ∗
    -- [R2c] the cluster's in-memory members, recovered from the backend's buckets (`Finalize`'s `cl.Recover`), the image's
    -- members at its committed log `L` (`bkRestAt`), in place of the boot log's
    "Hmem" ∷ membership.clusterMem bc.cl' (restModel (W64 0) γ.boot L).mem ∗
    -- the consistent index and the apply protocol
    "%Hci" ∷ ⌜bk.ci' = ciIface cil⌝ ∗
    "#HisCI" ∷ isCI cil γA.ci ∗ "#Hcons" ∷ inv applyN (consInv γA) ∗
    -- (D43 M5e, 2026-10-26, the user's decision) the backend's hooks, as `NewBackendHooks(cfg.Logger,
    -- ci)` makes them (`bootstrapBackend`, `bootstrap.go:258`): the server's `s.beHooks`, whose
    -- `SetConfState` `applyConfChange` calls, and (D22 J1a) which the snapshot path's
    -- `OpenSnapshotBackend` installs on each new backend (stated once, 2026-11-03)
    "#Hbh" ∷ (∃ lgh : Loc, storage.isBackendHooks bk.beHooks'
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #cil⟩
      lgh) ∗
    -- (2026-11-01: `consInv_alloc`'s state, processed through the stored index `γA.m0.1`; until
    -- then `⟨0, 0, 0, false⟩`, a hidden copy of the literal)
    "Hthr" ∷ applyThread γA ⟨W64 0, γA.m0.1, W64 0, false⟩ ∗
    -- (R2c review, F1: the applying index and term are the apply loop's own fields, which
    -- `NewConsistentIndex` leaves at 0 and `SetBackend` does not set: as on a first start)
    "Happ" ∷ ciApplying cil (W64 0) (W64 0) ∗ "Hown" ∷ ciOwner cil bk.be' ∗
    -- the boot backend's meta reads: `#HmetaSnap`'s output at the boot open (`boot_create`,
    -- `SnapApplyOpen.lean`: from the fresh keys and payment rights inside `OpenBackend`'s `openPre`,
    -- with `Hm0`), which `bootstrap`, names-only, does not let `NewServer` derive
    "#Hmeta" ∷ isMetaBackend bk.be' (⊤ \ ↑applyN) (readView γA) ∗
    -- (J8a-4, 2026-11-01, the user's decision: `notes/decisions.md`, "J8a-4") the meta reads of a
    -- backend the apply thread opens (`applySnapshot`'s `OpenSnapshotBackend`) at the protocol's
    -- names `π`, over an image whose meta keys are `π.m0`, at its fresh keys and payment rights
    -- (they come back): what `applySnapshot.specSnap` takes
    "#HmetaSnap" ∷ □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
        ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
        backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
        backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
        □ ∀ (W : IProp GF) (b : Loc),
          backend.isBackend γB P W (batchLockInv (γA.withPh π) (metaTM γB P)) b -∗
          isMetaBackend (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
            (readView (γA.withPh π))) ∗
    -- the backend of the real instance, with the server's hooks (2026-11-01, J8a-1, approved: and
    -- its parameters `newBackend` configures, well-formed with the batch limit `openLimit cfg`, as
    -- `OpenSnapshotBackend`'s `openPre` requires of a snapshot's backend)
    "%Hbe" ∷ ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be ∧
      mvcc.bridgeParams d.P ∧ ciKeys d.P ∧ storage.hooksParams d.P ∧
      d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧
      -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook
      -- keys: what a revocation's deletions from it take (`mvcc.storeRb`)
      mvcc.leaseParams d.P ∧
      -- (2026-11-02, the backend-auth-split stage, item E of the approved restatements) the alarm
      -- and auth buckets in the table (schema's `Alarm`, `Auth`, `AuthUsers`, `AuthRoles`, of
      -- `MustCreateBackendBuckets`' `AllBuckets`): what `NewAlarmStore` and `NewAuthStore` take of
      -- the buckets they create, so that they are among the backend's ghost names
      d.P.has mvcc.alarmBI ∧ d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧
      d.P.has mvcc.authRolesBI⌝ ∗
    -- (2026-11-02, the user's approval, branch `snap-window`) the backend's hooks are the server's
    -- `s.beHooks` (`bootstrapBackend`'s `OpenBackend(cfg, beHooks)`: `bcfg.Hooks = hooks`, which
    -- `New` stores in `b.hooks`): what the merged snapshot's window needs of its commit
    "#HhkAt" ∷ backend.hooksAt d.be (storage.hooksIface bk.beHooks') ∗

    -- (the integration with `construct`, 2026-10-17) what `backend.New` gives (item 6's
    -- `newPostK`, at the server's batch-lock resources: its hooks the server's, so its
    -- `isBackend` names the apply protocol's batch lock), over the image's data `D`, the stopped
    -- file; (2026-11-03, the whole-`bootOk` review) `N + 7` write-back tokens and the open token
    -- (`bootLeft`, A), the batch lock's resource `lateWBR` (T1-B); and what `bootstrap` adds: the
    -- store's registration right, `keySized`
    "Hnew" ∷ backend.newPostK d.γB d.P (fun γB => lateWBR d.gx γB)
      (fun γB => batchLockInv γA (metaTM γB d.P)) (bootLeft N) d.be D ∗
    -- [R2c] the file is the image (`srvDiskImage`), at the consistent index `i`
    -- (2026-11-01, the user's decision, "bootOk's boot metadata") the boot data's meta keys are the
    -- protocol's initial ones: the consistent index and term stored in `D`'s `Meta` bucket are
    -- `γA.m0` (what `#Hmeta`'s reads return and `batchLockInv γA`'s mirror starts at; a restart's
    -- `D` holds the last commit's)
    "%Hm0" ∷ ⌜metaIs D γA.m0 ∧ γA.m0.1 = i⌝ ∗
    -- (D22 J1a, 2026-10-26: of every backend at these parameters, for the snapshot path's backends;
    -- until then of `d` only) the Key bucket's size bound (no bbolt file holds `2 ^ 62` keys)
    "#Hsz" ∷ □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗
    "Hlate" ∷ mvcc.lateReg d.gx ∗
    -- (D22 S-j2, 2026-10-20; an environment assumption the user approved, "D22's environment
    -- assumptions approved") the backend file's directory entry is the server's: nothing else
    -- creates, renames or deletes a file at `<DataDir>/member/snap/db`. `applySnapshot`'s
    -- `storage.OpenSnapshotBackend` renames a received image onto it (`os.Rename`'s axiom takes it)
    "Hpath" ∷ backend.pathOwn (config.backendPathOf cfg.DataDir'))
    -- (R-D1, 2026-11-04) no row for the error paths' close: `bootstrappedServer.Close` is
    -- translated and proved (`bootstrappedServer.Close.spec`, one-shot: it takes the backend's whole
    -- open token), and `NewServer`'s proof reassembles what it takes; until then the opaque
    -- `"#Hclose" ∷ □ {{ True }} b.Close() {{ True }}`, false (a second call panics)


/-- **`bootstrap`'s contract on a stopped member's data directory** (DRAFT, R2c; L3; a premise, as
`bootstrapContract`): with the configuration's URLs, the storage registry's authority, and the
directory's files holding the WAL's records `σ` and the backend's data `D` (`srvFiles`, its path's
entry `pathOwn`) of an image (`imageAt` at `L`, the index `i` between the WAL's snapshot and
commit, the bootstrap log applied), `bootstrap` returns an error, or the record of a restart
(`bootOkR`). (2026-11-03, the whole-`bootOk` review) For the configurations it covers (`bootCfgOk`,
not forcing a new cluster, `bootstrapWALFromSnapshot`'s `ForceNewCluster` rewriting the WAL's log,
`bootstrap.go:628-650`; the WAL in the data directory, `DedicatedWALDir` empty: `cfg.WALDir()`,
`config.go:302-307`, is the dedicated directory when set, while `srvFiles` places the WAL at
`<dd>/member/wal`), a write budget `bootstrap`'s own sessions leave (`N + 7 + bootWB ≤ wbInit`),
and (G, a scope restriction: the restart plan's static cluster) the image's members the boot log's,
at the same peer URLs (what `Members()`, `Hmembers`, reports through `memberDirIs dir`; their names
and client URLs may differ, `publishV3`, `server.go:1828`, updating them once a member has
started). As a first start's, the contract may always return an error, after which `restart3`
does nothing more: it does not promise the restart succeeds (R2c review, second tier 6).
(#7-cmp's Freeze: `imageAt` by the mode, in place; the compaction-mode receipt, RESTART-RCPT, as
`srvDiskImage`'s.) -/
def bootstrapRestartContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) : IProp GF :=
  iprop(□ ∀ (σ : StorContents) (i : w64) (L : List EntryModel) (D : backend.Data)
      (M : GMap Loc MemStorNamesRec),
    ⌜(∃ (γk : KVNames) (A : List EntryModel), γk.c0 = W64 0 ∧ imageAt γk γ.boot i L A D) ∧
      σ.b ≤ uint.nat i ∧ uint.nat i ≤ σ.commit ∧ γ.cl.bootLen ≤ uint.nat i ∧
      bootCfgOk cfg ∧ cfg.ForceNewCluster' = false ∧ cfg.DedicatedWALDir' = (go!"" : GoString) ∧
      -- (2026-11-03, the final whole-`bootOk` review's M1) bbolt opens the backend file (else
      -- `newBackend`'s `lg.Panic`)
      storage.dbOpensOk ∧
      N + 7 + bootWB ≤ backend.wbInit ∧
      (∀ f, ((restModel (W64 0) γ.boot L).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.boot).lookup f).map apply.MemberM.peerURLs)⌝ -∗
    {{ bootCfgRO cfg U ∗ memStorRegAuth M ∗
        srvFiles cfg.DataDir' id σ D ∗ backend.pathOwn (config.backendPathOf cfg.DataDir') }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOkR cfg γ id N dir σ i L D M b }})

end boot

/-- **A restarted incarnation's names agree with the stopped one's where the cluster sees them**
(see the file header): raft's names, the KV names wherever the KV invariant reads them
(`kvCongr`, R2d-1, Q8 (a), 2026-11-06: so the restarted member reuses the cluster's `kvInv`,
`kvInv_restartNames`; until then the state's variable, the model and `c0` only), and the claims'
map and prefix of the request ids. -/
def restartNames [GooseExts] (ρ ρ' : ReqNames) : Prop :=
  ρ'.rd.raft = ρ.rd.raft ∧ kvCongr ρ.rd.kv ρ'.rd.kv ∧
    ρ'.ids.issued = ρ.ids.issued ∧ ρ'.ids.pfx = ρ.ids.pfx

/-- The restarted names' state variable is the stopped one's. -/
theorem restartNames_st [GooseExts] {ρ ρ' : ReqNames} (h : restartNames ρ ρ') :
    ρ'.rd.kv.st = ρ.rd.kv.st := h.2.1.1.symm

/-- The restarted names' KV model is the stopped one's. -/
theorem restartNames_kvModel [GooseExts] {ρ ρ' : ReqNames} (h : restartNames ρ ρ') :
    kvModel ρ'.rd.kv = kvModel ρ.rd.kv := by
  obtain ⟨-, h2, h3, h4, -⟩ := h.2.1
  funext L; unfold kvModel; rw [h2, h3, h4]

section restartKV
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A restarted member reuses the cluster's KV invariant** (R2d-1, Q8 (a), the Scope's easy
probe): `kvInv` reads only the fields `restartNames` keeps (`kvCongr`, `kvInv_congr`). -/
theorem kvInv_restartNames (γs : ServerRaftNames) {ρ ρ' : ReqNames} (h : restartNames ρ ρ') :
    kvInv (GF := GF) γs ρ'.rd.kv = kvInv γs ρ.rd.kv :=
  (kvInv_congr γs _ _ h.2.1).symm

end restartKV

end EtcdGrove
end Perennial
