/-
**The server's side of the raft network** (D21 stage M2, 2026-10-19; `notes/decisions.md`, "D21 M2:
the network contract designed"). Lean-first (no Rocq counterpart).

* `srvProcOk γn s`: what `EtcdServer.Process` (and the reports) read of the server `s`, read-only:
  its logger, member id, cluster, stats and its raft wrapper's node with the node's inbound
  methods (`rnStepIfc`), and the network's payload the server's (`srvNet`). `NewServer` has it
  before the transport starts (the wrapper's fields split off early, `rnFixed_split`), which is
  when the transport may start calling `Process`.
* `stepIn_of_recv`: a message the network delivers to the server (`netRecv`) is what the node
  API's `node.Step` takes (`stepIn`; 2026-10-27, until then raft's `stepP`): the sender's
  `sentMsg` and the message's credits (`stepIn_intro`; 2026-10-30, the repair: until then the
  receiver's `NetMsgOk` from the sender's `SentMsgOk` with leader transfer off).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the inbound path reads of the server `s`**, member `id` (persistent; see the file
header), in the network `γn` whose payload is the server's (`srvNet` at the node's cluster), the
cluster's kind (`srvClusterOk`: no snapshot sent, leader transfer off, started from a bootstrap
log; 2026-10-27, the node API's, until then raft's no-snapshot and no-transfer modes). -/
def srvProcOk (γn : NetNames GF) (s : Loc) (id : w64) : IProp GF :=
  iprop(∃ (l c st : Loc) (γ : RNNames),
    srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗ srvMemberIDAddr s ↦□ id ∗ ⌜γ.id = id⌝ ∗
    srvClusterAddr s ↦□ c ∗ membership.isRaftCluster c ∗
    srvStatsAddr s ↦□ st ∗ ⌜st ≠ null⌝ ∗
    rnNodeAddr (srvRAddr s) ↦□ rnNodeIface γ ∗ rnStepIfc γ (rnNodeIface γ) ∗
    srvClusterOk γ.srv ∗ ⌜γn.N = srvNet γ.node⌝)

instance srvProcOk_persistent (γn : NetNames GF) (s : Loc) (id : w64) :
    Persistent (srvProcOk (GF := GF) γn s id) := by
  unfold srvProcOk; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A delivered message is what `node.Step` takes** (see the file header; 2026-10-27: the node
API's `stepIn`; 2026-10-30, the repair: by `stepIn_intro` from the sender's `sentMsg` and the
credits alone, snapshots included): at the node `γ.id` whose network payload is the server's. The
receiver's copy is the message's wire fields with no responses (`netRecv`). -/
theorem stepIn_of_recv (γn : NetNames GF) (γ : RNNames) (HN : γn.N = srvNet γ.node)
    {γd : GName} (ml : Loc) :
    srvClusterOk (GF := GF) γ.srv ∗ netRecv γn γ.id γd ml ⊢
      |==> stepIn γ.node.cl srvClusterN γ.id ml := by
  letI := srvStor (GF := GF) γ.node
  obtain ⟨N, g, dir, r⟩ := γn
  simp only at HN
  subst HN
  iintro ⟨-, Hr⟩
  iunfold netRecv at Hr
  simp only [srvNet]
  icases Hr with ⟨%st, %st', Hm, %Hw, #HP, HO, -⟩
  obtain ⟨⟨Hmsg, Hents, Hsnap, Hctx⟩, Hto, Hrs'⟩ := Hw
  icases HP with ⟨%sid, #Hrm⟩
  have Hst' : st' = ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ := by
    cases st; cases st'; simp_all
  rw [Hst']
  iapply stepIn_intro γ.node.cl srvClusterN γ.id ml sid st Hto
  iframe Hrm Hm HO

end lemmas

end EtcdGrove
end Perennial
