/-
**The database image's certificate** (D22c (A) as amended by S-0, carried out in D22 S-f,
2026-10-19; `notes/decisions.md`, "D22 S-f carried out"): what a backend image sent with a
`MsgSnap` holds, as a function of the committed log. Lean-first (no Rocq counterpart).

* `bkRestOf L n`, `bkRestAt L D` (pure): the buckets restore reads besides `Key` and `Meta`
  (`lease`, `auth`, `authUsers`, `authRoles`, `members`, `members_removed`, `cluster`, `alarm`:
  `restBuckets`) are, in `D`, what every member's backend holds at the committed log `L` (the raft
  log through the image's index), for the server's workload (no lease, no auth, no alarm request:
  `plainCover`): the lease, alarm and auth users' and roles' buckets empty, the auth bucket the
  boot state `NewAuthStore` leaves (`authRevision = 1`, auth disabled: `authBoot`), and the
  membership buckets `clusterBktOf n L` (opaque: what the membership store writes for the boot
  log's conf changes and the member-attribute and cluster-version requests of `L`, a function of
  `L` in a fresh static cluster: `notes/snapshot-path-s0.md`, part 2, (3), exception 7). Under a
  workload with leases or auth the lease and auth buckets would be a function of `L` only if the
  members agree on `ElectionTicks`, `TickMs` and `checkpointPersist` (exceptions 4-6); not stated.
  `meta`'s `confState`, `term` and `storageVersion` keys are left free (exceptions 1, 3; restore
  reads none of them).
* `imageAt γk i L A D` (pure): `D`'s key view is the KV model of the server's entries `A`
  (`mvcc.keyImage (kvModel γk A)`: the `Key` bucket, no compaction keys), its stored consistent
  index is `i` (`encMeta`, the `meta` key the hook saves) and its stored term some term (its
  value is not specified: restore does not read it, S-0 part 2 (2) (d); that it decodes is what
  names the receiver's consistent-index protocol, `metaIs D (i, t)`), and its other buckets
  `bkRestAt L`, `L` the raft log (`pre ++ A`). (D22 J7b, 2026-10-26) And the KV model is well
  formed as a store's committed log (`mvcc.IdxWf (kvModel γk A) []`: `LogWf'`, fewer than `2 ^ 63`
  revisions and changes per revision), which the sender's store knows of its log (its sole
  writer's certificate, `soleWriter_idxWf`) and restore needs (`restoreLogOk`, with the facts of
  the model a plain log has: `restoreLogOk_kvRaftOf`). The stored term stays some term: the
  consistent index's protocol tracks no term (`InvCindex.lean`), and restore reads none; the
  receiver names its protocol with the image's (`specSnap`'s `tI`, D22 J7b).
* `dbImage γ γk i D` (persistent): of a committed prefix `A` (`srvRLogLb`) of the server's log
  ending at index `i`, the store's part mvcc's `mvccImage` of the KV model's history (strict M1,
  2026-11-06; until then `imageAt`), the server's `imageRestAt` (`imageAt`'s meta and rest-bucket
  clauses). `imageAt` stays for the restart's image (`InvRestart`).
* `srvImage γ i D` (persistent; D22 S-i): `dbImage` at the fresh cluster's start for any KV names
  with `NewServer.spec`'s start values: what a snapshot message carries over the network
  (`srvNet`'s `img`), member-independent.

Who establishes it: the sender (D22 S-h), from `backend.Snapshot`'s observation (`Q`: the `Key`
bucket from the store's view in the batch lock's resource, the stored index from the consistent
index's meta keys in the hooks' resource) for the modeled part, and, for `bkRestAt` and the
compaction keys (in buckets the model does not track), a trust-boundary axiom of the server's
determinism (D22c (A): the apply path writes them as a function of the applied entries, the
workload plain). Who reads it: the receiver (D22 S-j), through `OpenSnapshotBackend`
(`fileHolds` of the file the transport saved, D22 S-i), `mvcc.store.restore` (D22 S-g:
`keyImage`), the `Recover` axioms (`bkRestAt`) and `consistIndex.SetBackend` (the stored index).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestLeased
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode backend go_etcd_io.etcd.server.v3.storage

/-! ## The other buckets -/

/-- The buckets restore reads besides `Key` and `Meta` (`mvcc.restBuckets`). -/
abbrev restBuckets : List GoString := mvcc.restBuckets

/-- **The bucket `n` every member's backend holds at the committed log `L`** (D22, 2026-10-23: a
definition, the rest model's, `InvRest.lean`; until then the boot values and the opaque
`clusterBktOf`), from the start's consistent index `c0` and the boot log `bootLog`. -/
def bkRestOf [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) (n : GoString) :
    Option BktData :=
  (restModel c0 bootLog L).bk.lookup n

/-- **The membership bucket `n` at the committed log `L`** (D22, 2026-10-23: a definition, the
rest model's; until then opaque). -/
abbrev clusterBktOf [GooseExts] (c0 : w64) (bootLog : List EntryM) (n : GoString)
    (L : List EntryModel) : Option BktData :=
  bkRestOf c0 bootLog L n

/-- **`D`'s other buckets are those of the committed log `L`** (see the file header). -/
def bkRestAt [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) (D : Data) :
    Prop :=
  ∀ n ∈ restBuckets, D.lookup n = bkRestOf c0 bootLog L n

/-- **The leased image of a log that grants nothing is the plain one** (the lease-grant plan's
Freeze, amendment (D)): with no live lease, `bkRestAtL`'s records are none. -/
theorem bkRestAt_of_L [GooseExts] {γk : KVNames} {bootLog : List EntryM} {L : List EntryModel}
    {D : Data} (hn : (kvLeases γk L).ids = []) (h : bkRestAtL γk bootLog L D) :
    bkRestAt γk.c0 bootLog L D := by
  obtain ⟨f, -, hf⟩ := h
  intro n hn'
  rw [hf n hn', hn, apply.restLeasesWith_nil]; rfl

/-- **The plain image of a log that grants nothing is the leased one** (`bkRestAt_of_L`'s converse):
with no live lease, `bkRestAtL`'s records are none. -/
theorem bkRestAtL_of_nil [GooseExts] {γk : KVNames} {bootLog : List EntryM} {L : List EntryModel}
    {D : Data} (hn : (kvLeases γk L).ids = []) (h : bkRestAt γk.c0 bootLog L D) :
    bkRestAtL γk bootLog L D := by
  refine ⟨fun _ => W64 0, leaseTTLsGeReq_of_ids_nil hn _, fun n hn' => ?_⟩
  rw [h n hn', hn, apply.restLeasesWith_nil]; rfl

/-! ## The image -/

/-- **`D` is the image at index `i` of the server's entries `A`, the raft log being `L`** (see
the file header). (#7-cmp's Freeze, 2026-11-02, the user's approval) The `Key` bucket and the
compaction records by the KV names' compaction mode (`mvcc.keyImageM γk.cmp`) at records `r` of
the committed log's compaction revision (`r.crev = crevOf γk A`: the store's `compactMainRev` is
the latest compaction applied, which a receiver restores and its apply thread carries on from);
mode off, at a log with no compaction, today's `keyImage` (`imageAt_off`). -/
def imageAt [GooseExts] (γk : KVNames) (bootLog : List EntryM) (i : w64) (L A : List EntryModel)
    (D : Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM γk.cmp (kvModel γk A) r D ∧ r.crev = crevOf γk A) ∧
    dget D schema.metaName schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, dget D schema.metaName schema.termKeyBytes = encMeta t) ∧
    bkRestAtL γk bootLog L D ∧ mvcc.IdxWf (kvModel γk A) []

/-- **Off, at a log with no compaction, the image is `keyImage`'s** (`keyImageM_off`). -/
theorem imageAt_off [GooseExts] (γk : KVNames) (bootLog : List EntryM) (i : w64)
    (L A : List EntryModel) (D : Data) (hcm : γk.cmp = false) :
    imageAt γk bootLog i L A D ↔
      (mvcc.keyImage (kvModel γk A) D ∧ dget D schema.metaName schema.ciKeyBytes = encMeta i ∧
        (∃ t : w64, dget D schema.metaName schema.termKeyBytes = encMeta t) ∧
        bkRestAtL γk bootLog L D ∧ mvcc.IdxWf (kvModel γk A) []) ∧ crevOf γk A = -1 := by
  unfold imageAt
  rw [hcm]
  constructor
  · rintro ⟨⟨r, hk, hc⟩, h2, h3, h4, h5⟩
    obtain ⟨hk', hr⟩ := (mvcc.keyImageM_off _ r D).1 hk
    subst hr
    exact ⟨⟨hk', h2, h3, h4, h5⟩, by rw [← hc, mvcc.CmpRecs.crev_empty]⟩
  · rintro ⟨⟨hk, h2, h3, h4, h5⟩, hc⟩
    exact ⟨⟨mvcc.CmpRecs.empty, (mvcc.keyImageM_off _ _ D).2 ⟨hk, rfl⟩,
      by rw [mvcc.CmpRecs.crev_empty, hc]⟩, h2, h3, h4, h5⟩

/-- `imageAt` reads the KV names through their start values and mode; an image moves to another
mode when, for the mode off, the committed log has no compaction (`keyImageM_mode`). -/
theorem imageAt_kv_congr [GooseExts] {γk γk' : KVNames} {bootLog : List EntryM} {i : w64}
    {L A : List EntryModel} {D : Data}
    (h0 : γk.c0 = γk'.c0) (h1 : γk.ch0 = γk'.ch0) (h2 : γk.log0 = γk'.log0)
    (hc : γk.cmp = true → γk'.cmp = false → crevOf γk A = -1) :
    imageAt γk bootLog i L A D → imageAt γk' bootLog i L A D := by
  have hk : kvModel γk A = kvModel γk' A := by simp only [kvModel, h0, h1, h2]
  have hcr : crevOf γk A = crevOf γk' A := by simp only [crevOf, h0, h1]
  rintro ⟨⟨r, hkI, hr⟩, h2', h3, h4, h5⟩
  have hb : mvcc.LogB (kvModel γk A) := ⟨by have := h5.2.1; omega, h5.2.2.2⟩
  have hl : kvLeases γk L = kvLeases γk' L := by simp only [kvLeases, h0, h1]
  refine ⟨⟨r, ?_, by rw [← hcr]; exact hr⟩, h2', h3,
    by unfold bkRestAtL at h4 ⊢; rw [← hl, ← h0]; exact h4, by rw [← hk]; exact h5⟩
  rw [← hk]
  exact mvcc.keyImageM_mode _ _ _ r D hb hkI (fun h h' => by rw [hr]; exact hc h h')

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The image certificate's server parts** (pure; strict M1, 2026-11-06: the draft's
`imageRestAt`, `notes/mvcc-api-clients/ServerSpecs.lean` §3c, here beside `dbImage`): `imageAt`
without its `Key`-bucket/compaction-records and `IdxWf` conjuncts, which mvcc's `mvccImage` holds:
the stored consistent index `i`, some stored term, the other buckets the committed log `L`'s
leased image (`bkRestAtL`, as `lean`'s `imageAt`: the records of `L`'s live leases in `lease`;
R4, 2026-11-07: until then strict M1's `bkRestAt`, the lease bucket empty, false under
lease-expiry once a lease is live; with none the two agree, `bkRestAt_of_L`/`bkRestAtL_of_nil`). -/
def imageRestAt (γk : KVNames) (bootLog : List EntryM) (i : w64) (L : List EntryModel)
    (D : Data) : Prop :=
  dget D schema.metaName schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, dget D schema.metaName schema.termKeyBytes = encMeta t) ∧
    bkRestAtL γk bootLog L D

/-- **The image's state is one the store reaches, its history short** (pure; strict M1,
2026-11-06): the writer's facts at the sender (`writer_facts`), carried by the certificate to the
receiver, whose `KV.Restore.contract` takes the restored state reachable and whose KV ghost state
jumps under the length bound. -/
def imageStOk (L : mvcc.Log) (c : Int) : Prop :=
  mvcc.api.MvccReachable (srvApi.stAt L c) ∧ L.length + 3 ≤ 2 ^ 63

/-- **`D` is the image of the committed log through index `i`** (persistent; see the file
header): of a committed prefix `A` of the server's log ending at `i`. (Strict M1, 2026-11-06: the
draft's `dbImageA`, `ServerSpecs.lean` §3c, restated in place: the store's part is mvcc's
`mvccImage` of the KV model's history and compaction revision, an unfinished compaction recorded
iff `u`, the history's receipt inside; the sender makes it by `mvccImage_snapshot.law`
(`SnapSendBranch.merged_image`), the receiver opens the snapshot's backend with it
(`dbImageA_open.law`, over `etcdStorage_open.law`); the server's parts `imageRestAt`; and the
image's state reachable and its history short (`imageStOk`, the sender's writer's facts,
`writer_facts`: what the receiver's `KV.Restore.contract` takes of the restored state, in place of
the draft's `kvModel_reachable.law`, a model lemma over the committed log; the image's `IdxWf`
conjunct until then, the sender's store's, played that part). Until then
`imageAt`, over mvcc's internal key image `keyImageM`, with the receipt beside it.) -/
def dbImage (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : Data) : IProp GF :=
  iprop(∃ (A : List EntryModel) (u : Bool), srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageRestAt γk γ.raft.boot i (γ.pre ++ A) D ∧
      imageStOk (kvModel γk A) (crevOf γk A)⌝ ∗
    mvcc.api.mvccImage D (kvModel γk A) (crevOf γk A) u)

instance dbImage_persistent (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : Data) :
    Persistent (dbImage (GF := GF) γ γk i D) := by
  unfold dbImage; infer_instance

/-- **The image certificate a snapshot message carries over the network** (persistent; D22 S-i,
2026-10-19; the server's `NetPayload.img`, `srvNet`): `dbImage` at the fresh cluster's start
(`⟨γ, [], 0⟩`, `NewServer.spec`'s `ρ.rd.raft`) for KV names with the start values `NewServer.spec`
fixes. The KV names differ per member (their ghost names), but `dbImage` reads only the start
values (`kvModel`, `crevOf`): `srvImage_of_dbImage` gives a member's to the network,
`dbImage_of_srvImage` the network's at a member's own names. (Strict M1: no compaction mode, the
store having none.) -/
def srvImage (γ : SrvRaft) (i : w64) (D : Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImage ⟨γ, [], W64 0⟩ γk i D)

instance srvImage_persistent (γ : SrvRaft) (i : w64) (D : Data) :
    Persistent (srvImage (GF := GF) γ i D) := by
  unfold srvImage; infer_instance

/-- `dbImage` reads the KV names through their start values. -/
theorem dbImage_kv_congr {γ : ServerRaftNames} {γk γk' : KVNames} {i : w64} {D : Data}
    (h0 : γk.c0 = γk'.c0) (h1 : γk.ch0 = γk'.ch0) (h2 : γk.log0 = γk'.log0) :
    dbImage (GF := GF) γ γk i D ⊢ dbImage γ γk' i D := by
  have hk : ∀ A, kvModel γk A = kvModel γk' A := by
    intro A; simp only [kvModel, h0, h1, h2]
  have hc : ∀ A, crevOf γk A = crevOf γk' A := by
    intro A; simp only [crevOf, h0, h1]
  iintro H
  iunfold dbImage at H
  iunfold dbImage
  icases H with ⟨%A, %u, #Hlb, %h, #Hr⟩
  iexists A, u
  iframe Hlb
  rw [← hk, ← hc]
  iframe Hr
  ipureintro
  unfold imageRestAt at h ⊢
  obtain ⟨hi, ⟨hci, ht, hrest⟩, hre⟩ := h
  have hl : kvLeases γk (γ.pre ++ A) = kvLeases γk' (γ.pre ++ A) := by
    simp only [kvLeases, h0, h1]
  exact ⟨hi, ⟨hci, ht, by unfold bkRestAtL at hrest ⊢; rw [← hl, ← h0]; exact hrest⟩, hre⟩

/-- A member's image certificate is the network's. -/
theorem srvImage_of_dbImage {γ : SrvRaft} {γk : KVNames} {i : w64} {D : Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    dbImage (GF := GF) ⟨γ, [], W64 0⟩ γk i D ⊢ srvImage γ i D := by
  iintro #H
  iunfold srvImage
  iexists γk
  iframe H
  ipureintro
  exact ⟨h0, h1, h2⟩

/-- **The network's image certificate at a member's names** (the receiver's; strict M1: no mode
to move, the certificate reading only the start values every member shares). -/
theorem dbImage_of_srvImage {γ : SrvRaft} {γk : KVNames} {i : w64} {D : Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    srvImage (GF := GF) γ i D ⊢ dbImage ⟨γ, [], W64 0⟩ γk i D := by
  iintro H
  iunfold srvImage at H
  icases H with ⟨%γk', %h, #H⟩
  obtain ⟨h0', h1', h2'⟩ := h
  iapply (dbImage_kv_congr (γk := γk') (γk' := γk)
    (h0'.trans h0.symm) (h1'.trans h1.symm) (h2'.trans h2.symm)) $$ H

end defs

/-! ## Lemmas -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- An image's lease, alarm and auth buckets are the boot state's (the rest model writes only
`members`, `members_removed` and `cluster`: `restModel_keep`). -/
theorem bkRestAt_boot {c0 : w64} {bootLog : List EntryM} {L : List EntryModel} {D : Data}
    (h : bkRestAt c0 bootLog L D) :
    D.lookup go!"lease" = some ∅ ∧ D.lookup go!"alarm" = some ∅ ∧
      D.lookup go!"auth" = some authBoot ∧ D.lookup go!"authUsers" = some ∅ ∧
      D.lookup go!"authRoles" = some ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by decide), bkRestOf, restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
     simp [restBoot, restBootBk])

/-- The image's stored meta keys are `(i, t)` for some term (`metaIs`, what the consistent
index's protocol names the backend's start with: `ApplyNames.m0`). -/
theorem imageAt_metaIs {γk : KVNames} {bootLog : List EntryM} {i : w64} {L A : List EntryModel}
    {D : Data} (h : imageAt γk bootLog i L A D) : ∃ t : w64, metaIs D (i, t) := by
  obtain ⟨-, hci, ⟨t, ht⟩, -⟩ := h
  exact ⟨t, hci, ht⟩

/-- **The rest buckets of a snapshot's data from its observation** (D22, 2026-10-23): the
tracked buckets `rbData P D` the rest model's at `L` (the apply thread's `rbOwn`, which the
observation agrees with), the tracked buckets the rest buckets. -/
theorem bkRestAt_of_rb {P : BParams} (hRB : ∀ n ∈ restBuckets, P.RB n = true)
    {c0 : w64} {bootLog : List EntryM} {L : List EntryModel} {D : Data}
    (hrb : rbData P D = (restModel c0 bootLog L).bk) : bkRestAt c0 bootLog L D := by
  intro n hn
  have := congrArg (fun r => GMap.lookup r n) hrb
  simp only [rbData_lookup, hRB n hn, ↓reduceIte] at this
  exact this

end lemmas

end EtcdGrove
end Perennial
