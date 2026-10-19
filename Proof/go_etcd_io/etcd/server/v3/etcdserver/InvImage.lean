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
  `bkRestAt L`, `L` the raft log (`pre ++ A`).
* `dbImage γ γk i D` (persistent): `imageAt` of a committed prefix `A` (`srvRLogLb`) of the
  server's log ending at index `i`.

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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode backend go_etcd_io.etcd.server.v3.storage

/-! ## The other buckets -/

/-- The buckets restore reads besides `Key` and `Meta`. -/
def restBuckets [FfiSyntax] : List GoString :=
  [go!"lease", go!"alarm", go!"auth", go!"authUsers", go!"authRoles", go!"members",
   go!"members_removed", go!"cluster"]

/-- The auth bucket `NewAuthStore` leaves on a fresh backend: the revision `1`
(`commitRevision`), auth disabled (no `authEnabled` key). -/
def authBoot [FfiSyntax] : BktData := GMap.insert go!"authRevision" (u64Be (W64 1)) ∅

/-- **The membership bucket `n` at the committed log `L`** (opaque; see the file header). -/
opaque clusterBktOf [FfiSyntax] (n : GoString) (L : List EntryModel) : Option BktData

/-- **The bucket `n` every member's backend holds at the committed log `L`**, for the server's
workload (see the file header). -/
def bkRestOf [FfiSyntax] (L : List EntryModel) (n : GoString) : Option BktData :=
  if n = go!"auth" then some authBoot
  else if n = go!"lease" ∨ n = go!"alarm" ∨ n = go!"authUsers" ∨ n = go!"authRoles" then some ∅
  else clusterBktOf n L

/-- **`D`'s other buckets are those of the committed log `L`** (see the file header). -/
def bkRestAt [FfiSyntax] (L : List EntryModel) (D : Data) : Prop :=
  ∀ n ∈ restBuckets, D.lookup n = bkRestOf L n

/-! ## The image -/

/-- **`D` is the image at index `i` of the server's entries `A`, the raft log being `L`** (see
the file header). -/
def imageAt [FfiSyntax] (γk : KVNames) (i : w64) (L A : List EntryModel) (D : Data) : Prop :=
  mvcc.keyImage (kvModel γk A) D ∧ dget D schema.metaName schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, dget D schema.metaName schema.termKeyBytes = encMeta t) ∧ bkRestAt L D

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`D` is the image of the committed log through index `i`** (persistent; see the file
header): of a committed prefix `A` of the server's log ending at `i`. -/
def dbImage (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAt γk i (γ.pre ++ A) A D⌝)

instance dbImage_persistent (γ : ServerRaftNames) (γk : KVNames) (i : w64) (D : Data) :
    Persistent (dbImage (GF := GF) γ γk i D) := by
  unfold dbImage; infer_instance

end defs

/-! ## Lemmas -/

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- An image's lease, alarm and auth buckets are the boot state's. -/
theorem bkRestAt_boot {L : List EntryModel} {D : Data} (h : bkRestAt L D) :
    D.lookup go!"lease" = some ∅ ∧ D.lookup go!"alarm" = some ∅ ∧
      D.lookup go!"auth" = some authBoot ∧ D.lookup go!"authUsers" = some ∅ ∧
      D.lookup go!"authRoles" = some ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h _ (by simp [restBuckets])]; simp [bkRestOf]
  · rw [h _ (by simp [restBuckets])]; simp [bkRestOf]
  · rw [h _ (by simp [restBuckets])]; simp [bkRestOf]
  · rw [h _ (by simp [restBuckets])]; simp [bkRestOf]
  · rw [h _ (by simp [restBuckets])]; simp [bkRestOf]

/-- The readers' view of a backend opened over an image (`newPost`'s `bView`), under the bridge's
parameters, is the `Key` bucket of the image's KV model. -/
theorem imageAt_keyView {P : BParams} (hP : mvcc.bridgeParams P) {γk : KVNames}
    {i : w64} {L A : List EntryModel} {D : Data} (h : imageAt γk i L A D) :
    mvcc.keyView (vData P (D, ⟨∅, W64 0⟩)) (mvcc.bucketMap (kvModel γk A)) :=
  mvcc.keyView_of_keyImage hP h.1

/-- The image's stored meta keys are `(i, t)` for some term (`metaIs`, what the consistent
index's protocol names the backend's start with: `ApplyNames.m0`). -/
theorem imageAt_metaIs {γk : KVNames} {i : w64} {L A : List EntryModel} {D : Data}
    (h : imageAt γk i L A D) : ∃ t : w64, metaIs D (i, t) := by
  obtain ⟨-, hci, ⟨t, ht⟩, -⟩ := h
  exact ⟨t, hci, ht⟩

/-- The modeled half of an image from a snapshot's observation (`backend.Snapshot.spec`'s `Q`):
the readers' view `sData P D` the `Key` bucket of `kvModel γk A` and the hook's own keys holding
the index `i` and some term; the unmodeled half (`bkRestAt`, no compaction key) given. -/
theorem imageAt_of_snap {P : BParams} (hP : mvcc.bridgeParams P) (hK : ciKeys P)
    {γk : KVNames} {i : w64} {L A : List EntryModel} {D : Data}
    (hv : mvcc.keyView (sData P D) (mvcc.bucketMap (kvModel γk A)))
    (hci : (hkData P D).lookup (schema.metaName, schema.ciKeyBytes) = encMeta i)
    (htm : ∃ t : w64, (hkData P D).lookup (schema.metaName, schema.termKeyBytes) = encMeta t)
    (hcmp : dget D schema.metaName mvcc.schedKeyBytes = none ∧
      dget D schema.metaName mvcc.finKeyBytes = none)
    (hrest : bkRestAt L D) : imageAt γk i L A D := by
  obtain ⟨t, ht⟩ := htm
  rw [hkData_lookup, ciKeys_hk hK (Or.inl rfl)] at hci
  rw [hkData_lookup, ciKeys_hk hK (Or.inr rfl)] at ht
  exact ⟨⟨mvcc.dget_of_keyView hP hv, hcmp⟩, by simpa using hci, ⟨t, by simpa using ht⟩, hrest⟩

end lemmas

end EtcdGrove
end Perennial
