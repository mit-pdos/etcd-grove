/-
**The mode-`on` image certificate** (the auth-on snapshot plan's Q3 (b) and F8,
`notes/snapshot-auth-on-plan.md`): the auth buckets of a backend's data (`authDataOf`,
`authBucketsAt`), the image of a cluster with auth on (`imageAtOn`, `dbImageOn`, `srvImageOn`, beside
`InvImage.lean`'s mode-off ones), and the certificate in the cluster's mode (`srvImageM`), which the
network carries (`srvNet`, `InvApplyAll.lean`). Moved out of the Draft, `AuthSrv.lean` and
`ServerOn.lean` (`srvAuthSt0`), below `InvApplyAll`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

/-- **The auth state the mode-`on` KV model starts from**: the store's latest at the server's
start (`newAuthStore_boot`: the history `[bootState, bump bootState]`, the revision committed
once). -/
def srvAuthSt0 : auth.AuthState := auth.bump auth.bootState

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The rest buckets after `NewAuthStore` on the buckets `r` (its buckets created, the revision
`1` committed: `NewAuthStore`'s axiom's post). -/
abbrev authBucketsAfter (r : GMap GoString backend.BktData) : GMap GoString backend.BktData :=
  ((r.insert go!"auth" authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅

/-- **The auth buckets of the buckets `r`** (a backend's data, or the tracked view of it,
`backend.rbData P D`): what the decoding `schema.authBucketsAre` reads. -/
def authDataOf (r : GMap GoString backend.BktData) : schema.AuthData :=
  ⟨(r.lookup go!"auth").getD ∅, (r.lookup go!"authUsers").getD ∅,
    (r.lookup go!"authRoles").getD ∅⟩

/-- **The auth buckets of `r` hold the state `st`** (`schema.authBucketsAre` of `authDataOf r`),
its revision a `uint64` (the bucket stores `u64Be (W64 st.revision)`, which alone does not bound
`st.revision`: the read contract's `uint.nat x = st.revision` needs it; review round 1's F2).
(Q3 (b)'s boot form, "empty buckets at the boot state", is not needed: what `NewAuthStore` leaves
holds `bump bootState`, `authBucketsAt_after`, so every image decodes with this one form.) -/
def authBucketsAt (st : auth.AuthState) (r : GMap GoString backend.BktData) : Prop :=
  schema.authBucketsAre st (authDataOf r) ∧ st.revision < 2 ^ 64

/-- **What `NewAuthStore` leaves holds the start's state** `bump bootState` (its buckets created,
the revision `1` committed): so an image taken before any admin entry decodes to `srvAuthSt0`. -/
theorem authBucketsAt_after (r : GMap GoString backend.BktData) :
    authBucketsAt (auth.bump auth.bootState) (authBucketsAfter r) := by
  have hA : ((authBucketsAfter r).lookup go!"auth").getD ∅ = authBoot := by
    simp [authBucketsAfter, GMap.lookup_insert_eq_iff]
  have hU : ((authBucketsAfter r).lookup go!"authUsers").getD ∅ = ∅ := by
    simp [authBucketsAfter, GMap.lookup_insert_eq_iff]
  have hR : ((authBucketsAfter r).lookup go!"authRoles").getD ∅ = ∅ := by
    simp [authBucketsAfter, GMap.lookup_insert_eq_iff]
  unfold authBucketsAt
  refine ⟨?_, by simp [auth.bump, auth.bootState]⟩
  unfold authDataOf schema.authBucketsAre
  rw [hA, hU, hR]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n v h; simp at h
  · intro n v h; simp at h
  · intro v h
    simp [authBoot, schema.authRevisionKey, GMap.lookup_insert_eq_iff] at h
    subst h; exact u64Be_length _
  · simp [schema.enabledOf, authBoot, schema.authEnabledKey, schema.authRevisionKey,
      GMap.lookup_insert_eq_iff, auth.bump, auth.bootState]
  · simp [authBoot, schema.authRevisionKey, GMap.lookup_insert_eq_iff, auth.bump, auth.bootState]
  · intro n; simp [auth.bump, auth.bootState]
  · intro n v h; simp at h
  · intro n; simp [auth.bump, auth.bootState]
  · intro n v h; simp at h

/-- **`D` is the mode-`on` image at index `i` of the server's entries `A`, the raft log being `L`**
(`imageAt` with the model in the mode `on` from the start's auth state `st₀`): the `Key` bucket
`kvModelOn`'s, the meta keys, the rest buckets but the auth ones the rest model's, and the auth
buckets the auth state after `A` (`srvAuthAtLog`). (Rebased on #7-cmp's Freeze, as `imageAt`:) the
`Key` bucket and the compaction records by the KV names' mode at records `r` of the committed log's
compaction revision. -/
def imageAtOn (γk : KVNames) (st₀ : auth.AuthState) (bootLog : List EntryM) (i : w64)
    (L A : List EntryModel) (D : backend.Data) : Prop :=
  (∃ r : mvcc.CmpRecs, mvcc.keyImageM γk.cmp (kvModelOn γk st₀ A) r D ∧ r.crev = crevOf γk A) ∧
    backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta i ∧
    (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
    (∀ n ∈ restBuckets, ¬ auth.authBkts n →
      D.lookup n = bkRestOf γk.c0 bootLog L n) ∧
    authBucketsAt (srvAuthAtLog γk st₀ A) D ∧ mvcc.IdxWf (kvModelOn γk st₀ A) []

/-- `dbImage` in the mode `on` (with `dbImage`'s KV log receipt, #7-cmp's). -/
def dbImageOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (i : w64)
    (D : backend.Data) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z i = uint.Z γ.ai0 + A.length ∧ imageAtOn γk st₀ γ.raft.boot i (γ.pre ++ A) A D⌝ ∗
    ⧖ (mvcc.logCh (kvModelOn γk st₀ A)))

/-- **The image certificate of a cluster with auth on** (Q3 (b); the network's when the cluster
runs auth on, `srvImageM`): `srvImage`'s, the
start's chain the mode `on`'s and the model's start state `srvAuthSt0`. -/
def srvImageOn (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  iprop(∃ γk : KVNames, ⌜γk.c0 = W64 0 ∧ γk.ch0 = apply.alarmChain true false false ∧
    γk.log0 = [[], []]⌝ ∗ dbImageOn ⟨γ, [], W64 0⟩ γk srvAuthSt0 i D)

/-- **The image certificate in the cluster's auth mode** (decision 7; #7-on (b), the user's go-ahead
of 2026-11-03 after review R1's F8): `srvImageOn` when the cluster runs auth on, `srvImage`
otherwise (by `rfl`). Keyed on the **cluster's** mode, not a member's `E.authMode`: the certificate
travels in the cluster's network payload (`srvNet`), which every member's transport and snapshot
directory share. The mode is a field of `SrvRaft` (`authOn`, set by the allocator
`srvLogInv_alloc`, whose callers `NewServerAlloc`/`NewServerAllocOn` know it), and the member's KV
invariant ties it to the member's (`kvInv`: off, `kvInvOn`: on): every member of a cluster runs in
its mode. -/
def srvImageM (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) : IProp GF :=
  match on with
  | true => srvImageOn γ i D
  | false => srvImage γ i D

theorem srvImageM_off (γ : SrvRaft) : srvImageM (GF := GF) false γ = srvImage γ := rfl

instance srvImageM_persistent (on : Bool) (γ : SrvRaft) (i : w64) (D : backend.Data) :
    Persistent (srvImageM (GF := GF) on γ i D) := by
  cases on
  · simp only [srvImageM]; infer_instance
  · simp only [srvImageM]; unfold srvImageOn dbImageOn; infer_instance

theorem srvImageM_on (γ : SrvRaft) : srvImageM (GF := GF) true γ = srvImageOn γ := rfl

end defs

end EtcdGrove
end Perennial
