-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/DurableLastFits.lean` (etc/copy-part.py; rerun it, do not edit).
/- A node's durable log ends within its cluster's room (2026-11-27): in a cluster that fits (`readyFits`:
the receipts' bound past the bootstrap log at most `2^61`), a node's durable state's last index is at most
`2^61 - 1`. Its last index has a record (`durPers_lastRec`: the last entry's, or the base's), whose time
receipt (`lastRec_receipt`) is below the receipts' bound (`preceipt_lt`). What a restart's read facts take
(the WAL's I2, `walReadFacts`: etcd's stop, `StopShutdown.lean`). -/
module
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNode
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApi
import RaftNoAx.Proof.go_etcd_io.raft.v3.Protocol.Refinement

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

theorem raftState_lastFits (γ : Cluster) (N : Namespace) (id : w64) (S : RaftState) :
    readyFits (GF := GF) γ N ∗ raftState γ id S ⊢ |==>
      raftState γ id S ∗ ⌜S.last ≤ 2 ^ 61 - 1⌝ := by
  iintro ⟨Hfits, Hstate⟩
  iunfold readyFits at Hfits
  icases Hfits with %Hfit
  iunfold raftState at Hstate
  iunfold ApiImpl.raftStateU at Hstate
  icases Hstate with ⟨Hdur, #Hterm, #Hbudget⟩
  iunfold ownDurGhost at Hdur
  icases Hdur with ⟨%E, Hshares, #Hpers, Hslot, Hi1⟩
  ihave #Hlr := durPers_lastRec _ id S E $$ Hpers
  imod lastRec_receipt _ _ $$ Hlr with Hrc
  ihave %Hrcl := preceipt_lt _ $$ Hrc
  imodintro
  isplitl [Hshares Hslot Hi1]
  · iunfold raftState
    iunfold ApiImpl.raftStateU
    iframe Hterm Hbudget
    iunfold ownDurGhost
    iexists E
    iframe Hshares Hpers Hslot Hi1
  ipureintro
  unfold Cluster.bootLen at Hfit
  unfold RaftState.last
  unfold plogLastIndexZ at Hrcl
  have := uint_nat_eq S.base.index'
  omega
end EtcdGrove
end Perennial
