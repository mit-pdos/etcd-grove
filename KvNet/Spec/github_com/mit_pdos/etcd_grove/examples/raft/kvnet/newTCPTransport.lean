/-
`newTCPTransport(id, addrs, stats)` (`transport.go`, 2026-11-24 G5): TCP's transport (`newTransport`)
as a `peerTransport`: a fresh one of the peer-transport contract (`ptFresh`, `PeerTransport.lean`).
With it, the function value meets `ptCtor` at `tcpAP F` (its premise is `tcpAP`, unfolded).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PeerTransport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev newTCPTransport.spec : Prop :=
  ∀ (F : KvFacts GF) (γ : Cluster) (N : Namespace) (id : w64) (am : Loc) (M : GMap w64 GoString)
    (sts : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ am ↦$□ M ∗ isStats sts ∗
      □ (∀ (pid : w64) (a : GoString), ⌜M !! pid = some a ∧ pid ≠ id⌝ -∗
          addrProto a (kvP F pid) (kvQ F pid) ∗ ⌜addrOk a = true⌝) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newTCPTransport)) (Val #id)) (Val #am)) (Val #sts))
  {{ (tv : GoInterface), RET #tv; ptFresh F γ N id tv }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
