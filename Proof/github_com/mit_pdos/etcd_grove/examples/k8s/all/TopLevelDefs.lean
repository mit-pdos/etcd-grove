/- Lean-first (no Rocq counterpart).

# `k8s/all`: the definitions its top-level statement is written in

The program the one closed Kubernetes theorem (`k8s_safe_single_process`, `notes/k8s-unified-scope.md`) is about, and
the other definitions its statement names: the ghost-state bundle (the k8s etcd3 driver's, with
iris-lean's non-atomic invariants for porcupine), the read package's metric names, and the two
clusters' addresses and data directories, the store's (`k8s_etcd3N`, `k₁` members) then the
compactor's (`k8s_compactorN`, `k₂` members; `notes/k8s-compactor-n-plan.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

/-- The functors: putget's (the universal camera `AllG` at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state), and iris-lean's non-atomic invariants at slot 11
(porcupine's). Every other slot is the unit functor. -/
def k8sGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses are stated over every
instance of the ghost state whose Go local context is the semantics' own). -/
abbrev k8sHeapAt (hG : HeapGS .hasLC k8sGF) (lctx : GoLocalContext) : HeapGS .hasLC k8sGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **The program**: `k8sall`'s initialization, then `MainChecked(k1, clients, ops, watchers, wops,
n1, k2, n2)` with the two member counts `k₁` (the store's cluster) and `k₂` (the compactor's), the
store's workload and the lengths `n₁`, `n₂` of the two schedules. `MainChecked` returns at once unless
the counts and the workload are in the ranges `Main`'s proof covers (`ParamsOk`), and draws the two
schedules itself (`cluster3.RandomSchedule`; until the pure-premises plan's P5, 2026-11-24, the program
was `Main` with those ranges premises of the statement and the schedules slice literals of given
lists, `schedLit`). -/
def k8sProgram [GoSemanticsFunctions] (k₁ clients ops watchers wops n₁ k₂ n₂ : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.all.initialize' #() ;;
  App (App (App (App (App (App (App (App
    (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.MainChecked))
    (Val #k₁)) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (Val #n₁))
    (Val #k₂)) (Val #n₂)

/-- **The program's addresses**: the store cluster's (`k8s_etcd3N.k8setcd3NAddrs k₁`: its `k₁` members'
peer and client addresses and its bridges'), then the compactor cluster's
(`k8s_compactorN.k8scompactorNAddrs k₂`, likewise). -/
def k8sAddrs (k₁ k₂ : Nat) : List GoString :=
  k8s_etcd3N.k8setcd3NAddrs k₁ ++ k8s_compactorN.k8scompactorNAddrs k₂

/-- **The program's data directories**: the store cluster's `k8setcd3N-i.etcd`, then the compactor
cluster's `k8scompactorN-j.etcd`. -/
def k8sDirs (k₁ k₂ : Nat) : List GoString :=
  k8s_etcd3N.k8setcd3NDirs k₁ ++ k8s_compactorN.k8scompactorNDirs k₂

end adequacy
end EtcdGrove
end Perennial

end

end
