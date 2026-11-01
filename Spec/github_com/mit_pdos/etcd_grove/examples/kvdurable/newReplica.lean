/- Lean-first (no Rocq counterpart).

`newReplica(id, file, node, storage, kv, applied, cs, index, rafted, tick, stats, seqs, send)`
(kv.go): an incarnation of replica `id` on the node `RestartNode` just started on `storage`, whose
durable file is `file` (its invariant, `kdFileInv`), at the replicated state of the stored
snapshot's prefix `ap` (`repOwn`'s fields `kv` and `applied` given here, the configuration `cs`
denoting `m`, `index = len ap`); raft's applied index at start `rafted`. Its `dmu` lock gets the
writer's half of the file's variable at `(S, o)` and the storage's contents `M` (holding `S`), its
hard state copy; the node's driver (at the storage's key `K`), its configuration view at `(len ap,
m)`, its running token whole (halves to `run` and the snapshotter, the stopper collecting both) go
to the incarnation's goroutines (`run`, `ticker`, `snapshotter`). It returns the running
incarnation with the stopper's share.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev newReplica.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (n st sts sq ms : Loc)
    (γs : MemStorNames) (K : GName) (mK mA csp : Loc) (Kv A : GMap (List w8) (List w8))
    (ap l : List LogEntry) (m : Membership) (cfg : ConfStateM) (hsp : Loc) (hs : HardStateM) (S : RaftState)
    (o : Option StorFile) (M : StorFile) (rafted : w64) (tick : time.Duration) (f : GoFunc),
  0 < sint.Z tick → M.hs = hs → KdFileOk M → StorageHolds S (kdContents (some M)) →
  (ap.length : Int) < 2 ^ 61 → uint.nat rafted = l.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ context.isClosedchanInit ∗
      kdCluster γ vs ∗ isStats sts ∗ isReadSeqs γ sq ∗ kdFileInv γ dir id ∗
      isNode n γ.r.cluster kdRaftN id ∗
      nodeDriver n γ.r.cluster kdRaftN ⟨kdStorIface st, l, hs, none, K, S, StateFollower⟩ ∗
      nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ ∗
      nodeRunning n γ.r.cluster kdRaftN 1 ∗
      kdStorRec st ms γs ∗ memStorInvP ms γs (kdJ γ.r.cluster K) ∗
      memStorMeta ms γs hs ∗ st.[KStorage, go!"hs"] ↦ hsp ∗ hsOpt hsp hs ∗ kdStorView γs M ∗
      kdSnapCert γ M.snap ∗ kdWriter γ id S o ∗
      mK ↦$ Kv ∗ mA ↦$ A ∗ csOpt csp DFrac.discard cfg ∗ ⌜confStateIs cfg m⌝ ∗
      isCommittedLogLb γ.r.cluster ap ∗ confAt γ.r.cluster ap.length m ∗
      ⌜∀ k, (Kv !! k).getD [] = kvreconf.kvFold (kvreconf.logHist ap) k⌝ ∗
      ⌜kvreconf.AppliedOk A (kvreconf.logHist ap)⌝ ∗ sendSpec γ id f }}
    (App (App (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.newReplica)) (Val #id)) (Val #(kdFileName dir id)))
      (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n))) (Val #st)) (Val #mK)) (Val #mA))
      (Val #csp)) (Val #(W64 ap.length))) (Val #rafted)) (Val #tick)) (Val #sts)) (Val #sq)) (Val #f))
  {{ (r : Loc), RET #r; (∃ (n' st' sts' sq' : Loc) (ρ : KdRepNames),
        isReplicaR γ vs dir id r n' st' sts' sq' ρ) ∗ repStop γ vs dir id r }}

end spec

end kvdurable
end EtcdGrove
end Perennial
