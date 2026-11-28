/-
**The server's consistent-index pair predicate from its committed log** (keepfix-d, row 7h, untrusted):
an entry of the server's committed log (`srvRLogLb`) gives `srvCIPair` of its index and term, what the
apply thread supplies to `SetConsistentIndex` (the hook and the deferred advance). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CIPair
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.go_etcd_io.raft.v3.DurableLogView

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

/-- (keepfix (c) step 1, G5) **A committed prefix gives a committed pair at each of its indices**: some term. -/
theorem srvRLogLb_ciPairAt (γ : ServerRaftNames) (L : List EntryModel) (k : w64)
    (hk : 0 < uint.nat k ∧ uint.nat k ≤ γ.pre.length + L.length) :
    srvRLogLb (GF := GF) γ L ⊢ ∃ t : w64, srvCIPair γ.raft.cl k t := by
  unfold srvRLogLb srvCIPair
  iintro ⟨#HL, -⟩
  have hl : (srvLE γ L).length = γ.pre.length + L.length := by simp [srvLE]
  obtain ⟨e, he⟩ : ∃ e, (srvLE γ L)[uint.nat k - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  iexists e.term, srvLE γ L, e
  iframe HL
  ipureintro; exact ⟨hk.1, he, rfl⟩

/-- (keepfix (c) step 1, G5) **The committed pair's row at an index within a committed prefix** (the image's
term row, `mergedImgM`'s, what the snapshot window takes). -/
theorem srvRLogLb_ciRow (γ : ServerRaftNames) (L : List EntryModel) (k : w64)
    (hk : uint.nat k ≤ γ.pre.length + L.length) :
    srvRLogLb (GF := GF) γ L ⊢ ∃ tk : w64, □ (⌜k = W64 0⌝ ∨ srvCIPair γ.raft.cl k tk) := by
  iintro #HL
  by_cases h0 : k = W64 0
  · iexists W64 0; iintro !>; ileft; ipureintro; exact h0
  have hpos : 0 < uint.nat k := by
    have hz : uint.Z k ≠ 0 := fun h => h0 (by word)
    have := uint_nat_eq k
    have : (0 : Int) ≤ uint.Z k := by word
    omega
  icases srvRLogLb_ciPairAt γ L k ⟨hpos, hk⟩ $$ HL with ⟨%tk, #Hp⟩
  iexists tk; iintro !>; iright; iexact Hp

/-- (keepfix (c) step 1) **Two committed pairs at one index agree** (committed logs are prefixes of one
another, `isCommittedLogLb_agree`). -/
theorem srvCIPair_agree (cl : Cluster) (k t1 t2 : w64) :
    srvCIPair (GF := GF) cl k t1 ∗ srvCIPair cl k t2 ⊢ ⌜t1 = t2⌝ := by
  unfold srvCIPair
  iintro ⟨⟨%l1, %e1, #H1, %h1⟩, ⟨%l2, %e2, #H2, %h2⟩⟩
  icases isCommittedLogLb_agree cl l1 l2 $$ [$H1 $H2] with %Hag
  ipureintro
  obtain ⟨-, h1l, rfl⟩ := h1
  obtain ⟨-, h2l, rfl⟩ := h2
  rcases Hag with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hb := (List.getElem?_eq_some_iff.1 h1l).1
    rw [List.getElem?_append_left hb, h1l] at h2l
    cases h2l; rfl
  · have hb := (List.getElem?_eq_some_iff.1 h2l).1
    rw [List.getElem?_append_left hb, h2l] at h1l
    cases h1l; rfl

/-- (keepfix (c) step 1, sub-goal 1) **A committed entry's term is not 0, at the server's cluster**: the raft
log invariant's cluster (`srvClusterOk`'s `isCluster`, its bootstrap log non-empty: one entry per voter, and a
voter) through the law `srvTermPos_of_cluster`. -/
theorem srvRaftLogInv_termPos (hTP : srvTermPos_of_cluster.law (GF := GF)) (γ : ServerRaftNames) :
    srvRaftLogInv (GF := GF) γ ⊢ srvTermPos γ.raft.cl := by
  iintro #H
  iunfold srvRaftLogInv at H
  icases H with ⟨-, #Hcl, -, -, -, -, %Hvs⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨#Hc, -, -, -, -, -, -, -, %Hbl, -⟩
  have hpos : 0 < γ.raft.cl.bootLen := by
    rw [Hbl, Hvs.2.2.1.1]; exact List.length_pos_iff.mpr Hvs.1
  iapply (hTP γ.raft.cl hpos)
  iexact Hc

/-- (keepfix (c), step 1, sub-goal 1) **`srvTermPos_of_cluster.law` holds**: a committed entry of a cluster with a
non-empty boot log has a term at least `1` (raft's `isCommittedLogLb_term_pos`). -/
theorem srvTermPos_of_cluster_holds : srvTermPos_of_cluster.law (GF := GF) := by
  intro cl hb
  iintro #Hc
  unfold srvTermPos
  iintro !> %k %t #Hp
  unfold srvCIPair
  icases Hp with ⟨%l, %e, #Hl, %h⟩
  imod isCommittedLogLb_term_pos cl srvClusterN l ⊤ CoPset.subseteq_top hb $$ [$Hc $Hl] with %Hpos
  imodintro
  ipureintro
  obtain ⟨-, he, ht⟩ := h
  have h1 := Hpos e (List.mem_of_getElem? he)
  intro h0
  rw [← ht, h0] at h1
  simp at h1

end ghostHeap

end EtcdGrove
end Perennial
