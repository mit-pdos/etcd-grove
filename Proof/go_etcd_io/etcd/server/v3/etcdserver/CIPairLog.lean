/-
**The server's consistent-index pair predicate from its committed log** (keepfix-d, row 7h, untrusted):
an entry of the server's committed log (`srvRLogLb`) gives `srvCIPair` of its index and term, what the
apply thread supplies to `SetConsistentIndex` (the hook and the deferred advance). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CIPair
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section ghostHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The last entry of a committed prefix is a committed pair** (keepfix-d): with the server's start
index the length of its prefix (`srvRaftLogInv_facts`), the entry `m` closing `L ++ [m]` is the committed
entry at index `m.index`, with term `m.term`. -/
theorem srvRLogLb_ciPair (γ : ServerRaftNames) (L : List EntryModel) (m : EntryModel)
    (hai : uint.Z γ.ai0 = γ.pre.length) :
    srvRLogLb (GF := GF) γ (L ++ [m]) ⊢ srvCIPair γ.raft.cl m.index m.term := by
  unfold srvRLogLb srvCIPair
  iintro ⟨#HL, %hW⟩
  have hm := (hW L.length m (by simp)).1
  have hn : (uint.nat m.index : Int) = uint.Z m.index := by word
  have hidx : uint.nat m.index = γ.pre.length + L.length + 1 := by omega
  iexists (srvLE γ (L ++ [m])), m.toLE
  iframe HL
  ipureintro
  refine ⟨by omega, ?_, rfl⟩
  rw [hidx]
  simp [srvLE]

end ghostHeap

end EtcdGrove
end Perennial
