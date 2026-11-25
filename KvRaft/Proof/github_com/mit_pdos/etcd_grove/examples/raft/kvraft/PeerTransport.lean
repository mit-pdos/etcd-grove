/-
# The peer-transport contract (2026-11-24, G5: `notes/kvraft-g5-stop.md`)

A replica's incarnation sends its node's messages through a `peerTransport` (`transport.go`): an
interface with `start(node)`, `Send(ms)` and `stop()`, made per incarnation by a `newPeerTransport`
constructor `f(id, addrs, stats)`. TCP's is `newTCPTransport`. A UDP transport in this package proves
the same contract. What a transport receives it steps through the node (`Node.stepPeer`), so receiving
is not part of the contract. The method calls are on the interface's dynamic value (`methods i.ty`), as
in raft's storage contract (`isStorageP`).

* `ptSend F tv` (persistent): `Send` takes each message, owned, with its fact (`sendElem F m`), and
  only reads the slice: what `run`'s send callback needs (`sendSpec`, from the method value).
* `ptStop tv` (exclusive): `stop()` may be called, once: what `stopIncarnation` spends.
* `ptRunning F tv := ptSend F tv ∗ ptStop tv`: a started transport.
* `ptFresh F γ N id tv` (exclusive): a transport not started yet. `start(n)` on replica `id`'s node
  `n` (`isNode n γ N id`) makes it running.
* `ptCtor F γ N id AP f` (persistent): `f` makes fresh transports of replica `id`, from an address map
  whose other replicas' addresses `a` (of replica `pid`) carry `AP pid a`, and the stats. `AP` is the
  transport's: TCP's is `tcpAP F` (the address's protocols, and it is valid); UDP's its own.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__Send

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- `tv`'s `Send` (see the file header). -/
def ptSend (F : KvFacts GF) (tv : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tv = interface.ok i⌝ ∗
    □ ∀ (msl : GoSlice) (dqs : DFrac) (ms : List Loc),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
          msl ↦*{dqs} ms ∗ [∗list] m ∈ ms, sendElem F m }}
        (App (Val #(methods i.ty go!"Send" i.v)) (Val #msl))
      {{ RET #(); msl ↦*{dqs} ms }})

instance ptSend_persistent F tv : Persistent (ptSend (GF := GF) F tv) := by
  unfold ptSend; infer_instance

/-- `tv`'s `stop`, once (see the file header). -/
def ptStop (tv : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tv = interface.ok i⌝ ∗
    ∀ Φ : val → IProp GF, Φ #() -∗
      WP (App (Val #(methods i.ty go!"stop" i.v)) (Val #())) {{ Φ }})

/-- A started transport (see the file header). -/
def ptRunning (F : KvFacts GF) (tv : GoInterface) : IProp GF :=
  iprop(ptSend F tv ∗ ptStop tv)

/-- A transport of replica `id` not started yet (see the file header). -/
def ptFresh (F : KvFacts GF) (γ : Cluster) (N : Namespace) (id : w64) (tv : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜tv = interface.ok i⌝ ∗
    ∀ (n : NodeH) (Φ : val → IProp GF),
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft -∗
      isNode n γ N id -∗ (ptRunning F tv -∗ Φ #()) -∗
      WP (App (Val #(methods i.ty go!"start" i.v))
        (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n.loc))) {{ Φ }})

/-- TCP's per-address premise: the address's protocols, and it is valid (see the file header). -/
def tcpAP (F : KvFacts GF) (pid : w64) (a : GoString) : IProp GF :=
  iprop(addrProto a (kvP F pid) (kvQ F pid) ∗ ⌜addrOk a = true⌝)

instance tcpAP_persistent F pid a : Persistent (tcpAP (GF := GF) F pid a) := by
  unfold tcpAP; infer_instance

/-- `f` makes fresh transports of replica `id` (see the file header). -/
def ptCtor (F : KvFacts GF) (γ : Cluster) (N : Namespace) (id : w64) (AP : w64 → GoString → IProp GF)
    (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (am : Loc) (M : GMap w64 GoString) (sts : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
        am ↦$□ M ∗ isStats sts ∗
        □ (∀ (pid : w64) (a : GoString), ⌜M !! pid = some a ∧ pid ≠ id⌝ -∗ AP pid a) }}
      (App (App (App (Val #f) (Val #id)) (Val #am)) (Val #sts))
    {{ (tv : GoInterface), RET #tv; ptFresh F γ N id tv }})

instance ptCtor_persistent F γ N id AP f : Persistent (ptCtor (GF := GF) F γ N id AP f) := by
  unfold ptCtor; infer_instance

end defs

end kvraft
end EtcdGrove
end Perennial
