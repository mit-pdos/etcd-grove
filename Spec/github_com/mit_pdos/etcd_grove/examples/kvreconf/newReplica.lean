/- Lean-first (no Rocq counterpart).

`newReplica(id, node, storage, cs0, tick, stats, send)` (kv.go): replica `id` on the node just started
(`RestartNode`'s post: its driver, running token and configuration view at the bootstrap voters
`vs`) and its registered storage (`kvrStorRec`, its `MemoryStorage`'s invariant, hard state and no
snapshot stored yet, `memSnapNone`, which it opens for the two writers), at the bootstrap conf state
`cs0` (read-only), ticked every `tick`; `send` its transport. It starts the loop (`run`), the clock
(`ticker`) and the snapshot goroutine (`snapshotter`; kvreconf-snapshot-thread, 2026-10-30) and returns the running replica with the
stopper's share of it (`repStop`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev newReplica.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (n st sts cs0 : Loc) (tick : time.Duration)
    (f : GoFunc) (ms : Loc) (γs : MemStorNames) (hs : HardStateM),
  0 < sint.Z tick → vs.Nodup → (vs.length : Int) < 2 ^ 61 →
  confStateIs (bootCS vs) (Membership.simple (GMap.listToSet vs)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      context.isClosedchanInit ∗ kvrCluster γr vs ∗ isStats sts ∗ isNode n γr.cluster kvrRaftN id ∗
      nodeDriver n γr.cluster kvrRaftN (NodeDriverState.init (kvrStorIface st)) ∗
      nodeRunning n γr.cluster kvrRaftN 1 ∗
      nodeConfig n γr.cluster kvrRaftN ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
      kvrStorRec st ms γs ∗ memStorInvP ms γs (kvrJ γr.cluster id) ∗ memStorMeta ms γs hs ∗
      memSnapNone γs ∗ ownCSM cs0 DFrac.discard (bootCS vs) ∗ sendSpec γr id f ∗
      id ↪[γr.rseq] W64 0 }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.newReplica))
      (Val #id)) (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n))) (Val #st)) (Val #cs0))
      (Val #tick)) (Val #sts)) (Val #f))
  {{ (r : Loc), RET #r; isRep γr vs id r ∗ repStop γr vs r }}

end spec

end kvreconf
end EtcdGrove
end Perennial
