/- Lean-first (no Rocq counterpart).

`newTransport(id, addrs, stats)` (`examples/raft/kvraft/transport.go`): the transport of replica
`id`, whose peers' addresses are the read-only map `addrs` (`M`, its own included and left out):
for every other replica `pid` at `a`, a peer (`isPeer F p pid a`, its queue a fresh bag channel),
given the address's protocols for `pid` (`addrProto a (kvP F pid) (kvQ F pid)`) and its validity.
Its node field is still unset (`Transport.start` sets it).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TransportDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev newTransport.spec : Prop :=
  ∀ (F : KvFacts GF) (id : w64) (am : Loc) (M : GMap w64 GoString) (sts : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      am ↦$□ M ∗
      □ (∀ (pid : w64) (a : GoString), ⌜M !! pid = some a ∧ pid ≠ id⌝ -∗
          addrProto a (kvP F pid) (kvQ F pid) ∗ ⌜addrOk a = true⌝) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.newTransport))
      (Val #id)) (Val #am)) (Val #sts))
  {{ (t : Loc), RET #t;
      t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport, go!"id"] ↦□ id ∗
      t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport, go!"stats"] ↦□ sts ∗
      (∃ v : GoInterface, t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport, go!"node"] ↦ v) ∗
      isPeers F t ∗
      -- (2026-11-24, G5) the stop channel, with its closer (`Transport.stop`'s)
      ∃ (sc : Loc) (γsc : ChanNames), isTransportStop t sc γsc ∗ transportStopper sc γsc }}

end spec

end kvraft
end EtcdGrove
end Perennial
