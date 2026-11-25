/- Lean-first (no Rocq counterpart). (2026-11-22, kvraft: drafted with no `.lake`, unchecked.)

`newReplica(id, file, node, storage, kv, applied, cs, index, rafted, tick, stats, send)`
(`examples/raft/kvraft/replica.go`): an incarnation of replica `id` on the node `RestartNode` just started on
`storage`, whose durable file is `file` (the generation's file names `fl`: `durable`'s, the file, its roots, the
writer's variable; the file invariant `kdFileInvK γ id fl`, allocated at the generation's boot with the
writer's other half; the node started from the generation's arm `fl.x`), at the replicated state of the stored snapshot's prefix `ap` (`repOwn`'s fields `kv` and `applied`
given here, their values fitting a reply frame, `MapFits`; the configuration `cs` denoting `m`, `index =
len ap`); raft's applied index at start `rafted`. Its `dmu` lock gets the writer's half at `(S, o)`, the
storage's image at the contents `M` (holding `S`), the file's handle and a share of its call permission;
the node's driver, configuration view and running token go to `run` and the snapshotter (halves). As
kvdurable's, without the stop channels, the crashed flag and `seqs`.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev newReplica.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (n : NodeH) (st sts ms : Loc)
    (γs : MemStorNames) (K : GName) (mK mA csp : Loc) (Kv A : GMap (List w8) (List w8))
    (ap l : List LogEntry) (m : Membership) (cfg : ConfStateM) (ip : Loc) (hs : HardStateM) (S : RaftState)
    (o : Option StorFile) (M : StorFile) (rafted : w64) (tick : time.Duration) (f : GoFunc)
    (fl : KdFileNames) (qc : Qp),
  0 < sint.Z tick → M.hs = hs → KdFileOk M → StorageHolds S (kdContents (some M)) →
  (ap.length : Int) < 2 ^ 61 → uint.nat rafted = l.length →
  (∀ f, o = some f → f = M) → l.length ≤ ap.length →
  uint.nat M.prev ≤ l.length → l.length ≤ uint.nat M.hs.Commit' →
  1 ≤ uint.nat id → uint.nat id ≤ γ.max → GMap.size m.ids < 2 ^ 61 →
  ap.length = uint.nat M.snap.Metadata'.Index' →
  -- (2026-11-22) the starting maps' values fit a reply frame (`repOwn`/`repShared`'s `MapFits`)
  MapFits Kv → MapFits A →
  -- (2026-11-22, decision C) the file
  fl.df.Ok → fl.df.name = kdFileName dir id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ context.isClosedchanInit ∗
      kdCluster γ vs ∗ isStats sts ∗
      Fs.osInv ∗ Fs.osSharedInv fl.fR ∗ DurFs.durInv fl.γd fl.df ∗ kdFileInvK γ id fl ∗
      DurFs.durHandle fl.γd fl.df fl.fR ∗ Fs.osCallPerm (Fs.callKey fl.fR fl.df.d) qc ∗
      nodeArm n γ.r.cluster fl.x ∗
      isNode n γ.r.cluster kdRaftN id ∗
      nodeDriver n γ.r.cluster kdRaftN ⟨kdStorIface st, l, hs, none, K, S, StateFollower⟩ ∗
      nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ ∗
      nodeRunning n γ.r.cluster kdRaftN 1 ∗
      kdStorRec st ms γs ∗ memStorInvP ms γs (kdJ γ.r.cluster K) ∗
      memStorMeta ms γs hs ∗ st.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip M ∗
      kdSnapCert γ M.snap ∗ kdWriter fl S o ∗
      memCompacted γs (uint.nat M.prev) ∗
      memLog γs (uint.nat M.prev + 1) DFrac.discard (M.ents.take (l.length - uint.nat M.prev)) ∗
      raft_kvreconf.frozenTo γs (uint.nat M.prev) l ∗
      memSnapLb γs (uint.nat M.snap.Metadata'.Index') ∗
      mK ↦$ Kv ∗ mA ↦$ A ∗ csOpt csp DFrac.discard cfg ∗ ⌜confStateIs cfg m⌝ ∗
      isCommittedLogLb γ.r.cluster ap ∗ confAt γ.r.cluster ap.length m ∗
      ⌜∀ k, (Kv !! k).getD [] = raft_kvreconf.kvFold (raft_kvreconf.logHist ap) k⌝ ∗
      ⌜raft_kvreconf.AppliedOk A (raft_kvreconf.logHist ap)⌝ ∗ sendSpec γ id f ∗
      ⌜γ.r.cluster.maxData = none⌝ ∗
      ⌜¬ clusterNoSnap γ.r.cluster⌝ }}
    (App (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.newReplica)) (Val #id)) (Val #(kdFileName dir id)))
      (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n.loc))) (Val #st)) (Val #mK)) (Val #mA))
      (Val #csp)) (Val #(W64 ap.length))) (Val #rafted)) (Val #tick)) (Val #sts)) (Val #f))
  {{ (r : Loc), RET #r; (∃ (st' sts' sq' : Loc) (ρ : KdRepNames),
        isReplicaR γ vs dir id r n st' sts' sq' ρ) ∗ repStopper γ vs dir id r }}

end spec

end kvraft
end EtcdGrove
end Perennial
