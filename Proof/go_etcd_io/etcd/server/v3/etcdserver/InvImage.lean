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
* `dbImage γ γk i D` (persistent): `imageAt` of a committed prefix `A` (`srvRLogLb`) of the
  server's log ending at index `i`.
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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

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
def bkRestOf [FfiSyntax] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) (n : GoString) :
    Option BktData :=
  (restModel c0 bootLog L).bk.lookup n

/-- **The membership bucket `n` at the committed log `L`** (D22, 2026-10-23: a definition, the
rest model's; until then opaque). -/
abbrev clusterBktOf [FfiSyntax] (c0 : w64) (bootLog : List EntryM) (n : GoString)
    (L : List EntryModel) : Option BktData :=
  bkRestOf c0 bootLog L n

/-- **`D`'s other buckets are those of the committed log `L`** (see the file header). -/
def bkRestAt [FfiSyntax] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) (D : Data) :
    Prop :=
  ∀ n ∈ restBuckets, D.lookup n = bkRestOf c0 bootLog L n

/-! ## The image -/

/-- **`D` is the image at index `i` of the server's entries `A`, the raft log being `L`** (see
the file header). -/
def imageAt [FfiSyntax] (γk : KVNames) (bootLog : List EntryM) (i : w64) (L A : List EntryModel)
    (D : Data) : Prop :=
  mvcc.keyImage (kvModel γk A) D ∧ dget D schema.metaName schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, dget D schema.metaName schema.termKeyBytes = encMeta t) ∧
    bkRestAt γk.c0 bootLog L D ∧ mvcc.IdxWf (kvModel γk A) []

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`D` is the image of the committed log through index `i`** (persistent; see the file
header): of a committed prefix `A` of the server's log ending at `i`. -/
def dbImage (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAt γk γ.raft.reBoot i (γ.pre ++ A) A D⌝)

instance dbImage_persistent (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : Data) :
    Persistent (dbImage (GF := GF) γ γk i D) := by
  unfold dbImage; infer_instance

/-- **The image certificate a snapshot message carries over the network** (persistent; D22 S-i,
2026-10-19; the server's `NetPayload.img`, `srvNet`): `dbImage` at the fresh cluster's start
(`⟨γ, [], 0⟩`, `NewServer.spec`'s `ρ.rd.raft`) for KV names with the start values `NewServer.spec`
fixes. The KV names differ per member (their ghost names), but `dbImage` reads only the start
values (`kvModel`): `dbImage_of_srvImage`, `srvImage_of_dbImage` move between a member's and the
network's. -/
def srvImage (γ : RaftNames) (i : w64) (D : Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain false false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImage ⟨γ, [], W64 0⟩ γk i D)

instance srvImage_persistent (γ : RaftNames) (i : w64) (D : Data) :
    Persistent (srvImage (GF := GF) γ i D) := by
  unfold srvImage; infer_instance

/-- `dbImage` reads the KV names only through their start values. -/
theorem dbImage_kv_congr {γ : ServerRaftNames} {γk γk' : KVNames} {i : w64} {D : Data}
    (h0 : γk.c0 = γk'.c0) (h1 : γk.ch0 = γk'.ch0) (h2 : γk.log0 = γk'.log0) :
    dbImage (GF := GF) γ γk i D ⊢ dbImage γ γk' i D := by
  have hk : ∀ A, kvModel γk A = kvModel γk' A := by
    intro A; simp only [kvModel, h0, h1, h2]
  have hc : γk.c0 = γk'.c0 := h0
  iintro H
  iunfold dbImage at H
  iunfold dbImage
  icases H with ⟨%A, #Hlb, %h⟩
  iexists A
  iframe Hlb
  ipureintro
  refine ⟨h.1, ?_⟩
  have h2' := h.2
  unfold imageAt at h2' ⊢
  rw [← hk, ← hc]
  exact h2'

/-- A member's image certificate is the network's. -/
theorem srvImage_of_dbImage {γ : RaftNames} {γk : KVNames} {i : w64} {D : Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    dbImage (GF := GF) ⟨γ, [], W64 0⟩ γk i D ⊢ srvImage γ i D := by
  iintro #H
  iunfold srvImage
  iexists γk
  iframe H
  ipureintro
  exact ⟨h0, h1, h2⟩

/-- The network's image certificate is any member's. -/
theorem dbImage_of_srvImage {γ : RaftNames} {γk : KVNames} {i : w64} {D : Data}
    (h0 : γk.c0 = W64 0) (h1 : γk.ch0 = apply.alarmChain false false false)
    (h2 : γk.log0 = [[], []]) :
    srvImage (GF := GF) γ i D ⊢ dbImage ⟨γ, [], W64 0⟩ γk i D := by
  iintro H
  iunfold srvImage at H
  icases H with ⟨%γk', %h, #H⟩
  obtain ⟨h0', h1', h2'⟩ := h
  iapply (dbImage_kv_congr (h0'.trans h0.symm) (h1'.trans h1.symm) (h2'.trans h2.symm)) $$ H

end defs

/-! ## Lemmas -/

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
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

/-- The readers' view of a backend opened over an image (`newPost`'s `bView`), under the bridge's
parameters, is the `Key` bucket of the image's KV model. -/
theorem imageAt_keyView {P : BParams} (hP : mvcc.bridgeParams P) {γk : KVNames}
    {bootLog : List EntryM} {i : w64} {L A : List EntryModel} {D : Data}
    (h : imageAt γk bootLog i L A D) :
    mvcc.keyView (vData P (D, ⟨∅, W64 0⟩)) (mvcc.bucketMap (kvModel γk A)) :=
  mvcc.keyView_of_keyImage hP h.1

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

/-- The modeled half of an image from a snapshot's observation (`backend.Snapshot.spec`'s `Q`):
the readers' view `sData P D` the `Key` bucket of `kvModel γk A`, the hook's own keys holding the
index `i` and some term and (D22, 2026-10-23) the tracked buckets the rest model's at `L`; no
compaction key given (`bkNoCmp`'s, not modeled). (D22 J7b) The KV model well formed (`hwf`): the
sender's sole writer's (`soleWriter_idxWf`, at the applied log `kvModel γk A`). -/
theorem imageAt_of_snap {P : BParams} (hP : mvcc.bridgeParams P) (hK : ciKeys P)
    (hRB : ∀ n ∈ restBuckets, P.RB n = true)
    {γk : KVNames} {bootLog : List EntryM} {i : w64} {L A : List EntryModel} {D : Data}
    (hv : mvcc.keyView (sData P D) (mvcc.bucketMap (kvModel γk A)))
    (hci : (hkData P D).lookup (schema.metaName, schema.ciKeyBytes) = encMeta i)
    (htm : ∃ t : w64, (hkData P D).lookup (schema.metaName, schema.termKeyBytes) = encMeta t)
    (hcmp : dget D schema.metaName mvcc.schedKeyBytes = none ∧
      dget D schema.metaName mvcc.finKeyBytes = none)
    (hrb : rbData P D = (restModel γk.c0 bootLog L).bk)
    (hwf : mvcc.IdxWf (kvModel γk A) []) : imageAt γk bootLog i L A D := by
  have hrest := bkRestAt_of_rb hRB hrb
  obtain ⟨t, ht⟩ := htm
  rw [hkData_lookup, ciKeys_hk hK (Or.inl rfl)] at hci
  rw [hkData_lookup, ciKeys_hk hK (Or.inr rfl)] at ht
  exact ⟨⟨mvcc.dget_of_keyView hP hv, hcmp⟩, by simpa using hci, ⟨t, by simpa using ht⟩, hrest,
    hwf⟩

end lemmas

end EtcdGrove
end Perennial
