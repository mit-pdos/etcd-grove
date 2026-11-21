/-
`s.createMergedSnapshotMessage(m, snapt, snapi, confState)` (`snapshot_merge.go`): the merged
snapshot message. Lean-first (no Rocq counterpart); D22 S-h, 2026-10-20 (`notes/decisions.md`, "D22
S-h carried out"); the vocabulary is `InvSnapSend.lean`. (A `True`-postcondition axiom until D19p,
2026-10-18, which removed it as false.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__termAt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The frozen backend has reached at most the apply cursor. Its bytes can be sent with the
current apply metadata, independently of the retained replay terms. -/
abbrev EtcdServer.createMergedSnapshotMessage.specCaughtUp : Prop :=
  ∀ (s ml : Loc) (st : MsgSt) (snapt snapi ci : w64) (terms : GoSlice) (boot cs lg : Loc) (kv be : GoInterface) (dq : DFrac)
    (RC RC' RS RS' : IProp GF) (Qd : backend.Data → IProp GF) (γs : ServerRaftNames),
  uint.Z ci ≤ uint.Z snapi → GMap.size γs.raft.cfg ≤ 2 ^ 20 → st.ents = [] ∧ st.ctx = [] ∧ st.resps = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ zapLoggerOk lg ∗ srvLgReader s ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗
      srvBeAddr s ↦{dq} be ∗ srvBeSnapOk be RS RS' (fun D =>
        iprop(Qd D ∗ ⌜∃ term : w64, metaIs D (ci, term)⌝)) ∗ (RC' -∗ RS) ∗
      msgOwn ml (DFrac.own 1) st ∗ pbMsg go_etcd_io.raft.v3.raftpb.Message ml [] ∗
      epCsVoters γs cs ∗ threadTok }}
    (App (App (App (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"createMergedSnapshotMessage")) (Val #ml)) (Val #snapt)) (Val #snapi)) (Val #cs)) (Val #terms)) (Val #boot))
  {{ (mg : Loc), RET #mg; srvLgReader s ∗ RS' ∗ srvBeAddr s ↦{dq} be ∗ threadTok ∗
      ∃ (rc : GoInterface) (D : backend.Data) (c : ConfStateM),
        mergedMsg mg ml rc ∗ msgOwn ml DFrac.discard (mergedSt st c snapi snapt) ∗
        msgSzC False ml (mergedSt st c snapi snapt) ∗
        csOpt cs DFrac.discard c ∗
        ⌜(c.Voters' ++ c.Learners' ++ c.VotersOutgoing' ++ c.LearnersNext').length ≤ 2 ^ 20⌝ ∗
        backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗ Qd D }}

/-- The IDs and learner bits of a legacy member map determine the configuration
for every permissible map iteration order. -/
def replaySnapshotMembers (γ : ServerRaftNames) (mp : Loc) : IProp GF :=
  iprop(∃ (ptrs : GMap w64 Loc) (memberID : w64 → w64) (learner : w64 → Bool),
    mp ↦$ ptrs ∗
    □ (∀ (k : w64) (p : Loc), ⌜ptrs !! k = some p⌝ -∗
      membership.mIDAddr p ↦□ memberID k ∗ membership.mIsLearnerAddr p ↦□ learner k) ∗
    ⌜∀ keys : List w64, (∀ k, k ∈ keys ↔ (ptrs !! k).isSome) → keys.Nodup →
      confStateIs (.mk ((keys.filter (fun k => !learner k)).map memberID)
        ((keys.filter learner).map memberID) [] [] false) (Membership.simple γ.raft.cfg)⌝)

/-- Recovery from the absent configuration key reads the members in the same
transaction that will be streamed. -/
def replayMemberRead (γs : ServerRaftNames) (D : backend.Data) (lg sp : Loc) (γ : GName) : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ backend.snapOpenQ sp D γ 1 }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadMembers)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp)))
  {{ (mp : Loc), RET (PairV #mp #GoInterface.nil); backend.snapOpenQ sp D γ 1 ∗ replaySnapshotMembers γs mp }}

/-- A modern configuration decodes directly. An absent key makes the frozen
members available to the translated recovery loop. -/
def replayConfigRead (γs : ServerRaftNames) (D : backend.Data) : Prop :=
  ∀ (lg sp : Loc) (γ : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
    isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ backend.snapOpenQ sp D γ 1 }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.UnsafeConfStateFromBackend)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp)))
  {{ (p : Loc), RET #p; backend.snapOpenQ sp D γ 1 ∗
    (if p = null then ⌜replayMemberRead (GF := GF) γs D lg sp γ⌝ else epCsVoters γs p) }}

/-- The term at the durable index is either stored in Meta or supplied by the
immutable log of the job that is sending the snapshot. -/
def replaySnapshotTerm (terms : GoSlice) (ci stored chosen : w64) : IProp GF :=
  if stored = W64 0 then iprop(∃ (runs : List replayTermRun) (r : replayTermRun),
      terms ↦*□ runs ∗ ⌜replayRunAt runs ci = some r ∧ r.term' = chosen⌝)
  else iprop(⌜stored = chosen⌝)

/-- The bootstrap configuration belongs to the initial backend. The sender can
pair it with the immutable Ready's term when that log contains the image index.
An installed backend or an uncovered index uses the frozen metadata instead. -/
def replayImageMetadata (γs : ServerRaftNames) (D : backend.Data) (boot : Loc)
    (terms : GoSlice) (ci stored chosen : w64) : IProp GF :=
  iprop(∃ useBoot : Bool,
    (if boot = null then ⌜useBoot = false⌝ else ∃ runs : List replayTermRun,
      terms ↦*□ runs ∗ ⌜replayRunCovers runs ci = useBoot⌝) ∗
    (if useBoot then epCsVoters γs boot ∗ replaySnapshotTerm terms ci (W64 0) chosen
     else replaySnapshotTerm terms ci stored chosen ∗ ⌜replayConfigRead (GF := GF) γs D⌝))

/-- The sent index, term and configuration describe the backend image in the
restart window and the apply cursor once replay has caught up. -/
abbrev EtcdServer.createMergedSnapshotMessage.spec : Prop :=
  ∀ (s ml : Loc) (st : MsgSt) (snapt snapi ci backendTerm : w64) (terms : GoSlice) (boot cs lg : Loc) (kv be : GoInterface) (dq : DFrac)
    (RC RC' RS RS' : IProp GF) (Qd : backend.Data → IProp GF) (γs : ServerRaftNames),
  GMap.size γs.raft.cfg ≤ 2 ^ 20 → st.ents = [] ∧ st.ctx = [] ∧ st.resps = [] →
  let ahead := uint.Z snapi < uint.Z ci
  let labelIndex := if ahead then ci else snapi
  let labelTerm := if ahead then backendTerm else snapt
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ zapLoggerOk lg ∗ srvLgReader s ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗
      srvBeAddr s ↦{dq} be ∗ srvBeSnapOk be RS RS' (fun D =>
        iprop(Qd D ∗ ∃ stored : w64, ⌜metaIs D (ci, stored)⌝ ∗
          (⌜ahead⌝ -∗ replayImageMetadata γs D boot terms ci stored backendTerm))) ∗ (RC' -∗ RS) ∗
      msgOwn ml (DFrac.own 1) st ∗ pbMsg go_etcd_io.raft.v3.raftpb.Message ml [] ∗
      epCsVoters γs cs ∗ threadTok }}
    (App (App (App (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"createMergedSnapshotMessage")) (Val #ml)) (Val #snapt)) (Val #snapi)) (Val #cs)) (Val #terms)) (Val #boot))
  {{ (mg : Loc), RET #mg; srvLgReader s ∗ RS' ∗ srvBeAddr s ↦{dq} be ∗ threadTok ∗
      ∃ (rc : GoInterface) (D : backend.Data) (c : ConfStateM),
        mergedMsg mg ml rc ∗ msgOwn ml DFrac.discard (mergedSt st c labelIndex labelTerm) ∗
        msgSzC False ml (mergedSt st c labelIndex labelTerm) ∗
        (⌜¬ahead⌝ -∗ csOpt cs DFrac.discard c) ∗ ⌜confStateIs c (Membership.simple γs.raft.cfg)⌝ ∗
        ⌜(c.Voters' ++ c.Learners' ++ c.VotersOutgoing' ++ c.LearnersNext').length ≤ 2 ^ 20⌝ ∗
        backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗ Qd D }}

end spec

end EtcdGrove
end Perennial
