/- Lean-first (no Rocq counterpart).

# `etcd/all`: the definitions its top-level statement is written in

The program the one closed etcd theorem (`etcd_safe`, `notes/etcd-unified-scope.md`) is about, and the
other definitions its statement names: the ghost-state bundle (partition's `linkvGF`, renamed: the
superset of the eleven drivers' used slots), the program's metric names, and the eleven clusters'
addresses and data directories, in the order of the program's parts: KV (txnlinfaultsN's `k₁` members,
partition's three, compactwatch's, compacted's and cache's one each), Auth (authN's `k₂`, authlease's
`k₃`), Lease (leaseN's `k₄`, leasecatchup's three) and Restart (restartN's `k₅`, restart1's one, which
listens on no address).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.SchedLit
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
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

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

/-- The functors: putget's (the universal camera `AllG` at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state), a ghost variable at slot 7, and iris-lean's
non-atomic invariants at slot 11 (porcupine's): partition's `linkvGF`, a superset of the slots every
driver's triple uses (each is GF-polymorphic). Every other slot is the unit functor. -/
def etcdGF : BundledGFunctors := fun i =>
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
abbrev etcdHeapAt (hG : HeapGS .hasLC etcdGF) (lctx : GoLocalContext) : HeapGS .hasLC etcdGF :=
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

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **The program**: `etcdall`'s initialization, then `Main(k1, clients, ops, sched1, nw, nops, sched2,
cnw, cnops, k2, k3, k4, k5)`: the member counts `k₁` (txnlinfaultsN), `k₂` (authN), `k₃` (authlease),
`k₄` (leaseN) and `k₅` (restartN), txnlinfaultsN's workload (`clients`, `ops`) and schedule `steps₁`,
partition's watch workload (`nw`, `nops`) and schedule `steps₂`, cache's workload (`cnw`, `cnops`); the
two schedules built as slice literals (`schedLit`). -/
def etcdProgram [GoSemanticsFunctions] (k₁ : Nat) (clients ops : w64)
    (steps₁ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) (nw nops : w64)
    (steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) (cnw cnops : w64)
    (k₂ k₃ k₄ k₅ : Nat) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.all.initialize' #() ;;
  App (App (App (App (App (App (App (App (App (App (App (App (App
    (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.Main))
    (Val #(W64 (k₁ : Int)))) (Val #clients)) (Val #ops)) (schedLit steps₁))
    (Val #nw)) (Val #nops)) (schedLit steps₂)) (Val #cnw)) (Val #cnops))
    (Val #(W64 (k₂ : Int)))) (Val #(W64 (k₃ : Int)))) (Val #(W64 (k₄ : Int))))
    (Val #(W64 (k₅ : Int)))

/-- The program's addresses: the three members' peer addresses, their client addresses, and the
bridges' addresses (2026-10-21, `notes/client-cut-plan.md`; partition's, moved here unchanged when its closed theorems
retired, 2026-11-21). -/
def linkv3pAddrs : List GoString :=
  [etcd_partition.peerAddr₁, etcd_partition.peerAddr₂, etcd_partition.peerAddr₃,
    etcd_partition.clientAddr₁, etcd_partition.clientAddr₂, etcd_partition.clientAddr₃,
    etcd_partition.bridgeAddr₁, etcd_partition.bridgeAddr₂, etcd_partition.bridgeAddr₃]

/-- The program's addresses: the three members' peer addresses, their client addresses, and the
bridges' addresses (`clusterCfg`'s; leasecatchup's, moved here unchanged when its closed theorem retired,
2026-11-21). -/
def leasecatchupAddrs : List GoString :=
  [etcd_leasecatchup.clusterCfg.Peer1', etcd_leasecatchup.clusterCfg.Peer2',
    etcd_leasecatchup.clusterCfg.Peer3',
    etcd_leasecatchup.clusterCfg.Client1', etcd_leasecatchup.clusterCfg.Client2',
    etcd_leasecatchup.clusterCfg.Client3',
    etcd_leasecatchup.clusterCfg.Bridge1', etcd_leasecatchup.clusterCfg.Bridge2',
    etcd_leasecatchup.clusterCfg.Bridge3']

/-- The members' data directories `<name>.etcd` (sweep repairs 1, W3/W4: until then their WAL directories). -/
def leasecatchupDataDirs : List GoString :=
  [(memberDataDir etcd_leasecatchup.clusterCfg.Name1'),
    (memberDataDir etcd_leasecatchup.clusterCfg.Name2'),
    (memberDataDir etcd_leasecatchup.clusterCfg.Name3')]

/-- **The program's addresses** (those it listens on), cluster by cluster in the parts' order:
txnlinfaultsN's `k₁` members' peer and client addresses and bridges; partition's three members' and
bridges'; compactwatch's, compacted's and cache's client addresses; authN's `k₂`, authlease's `k₃` and
leaseN's `k₄` members' peer and client addresses; leasecatchup's three members' and bridges'; restartN's
`k₅` peer addresses. (restart1 listens on none.) -/
def etcdAddrs (k₁ k₂ k₃ k₄ k₅ : Nat) : List GoString :=
  etcd_txnlinfaultsN.txnlinfaultsNAddrs k₁ ++ linkv3pAddrs ++
    [go!"127.0.0.1:23794", go!"127.0.0.1:23791", go!"127.0.0.1:23873"] ++
    etcd_authN.authNAddrs k₂ ++ etcd_authlease.authleaseAddrs k₃ ++ etcd_leaseN.leaseNAddrs k₄ ++
    leasecatchupAddrs ++ etcd_restartN.restartNAddrs k₅

/-- **The program's data directories**, one per member (`/tmp/etcd-grove-data/<name>.etcd`), in the
order of `etcdAddrs`' clusters, restart1's last. -/
def etcdDirs (k₁ k₂ k₃ k₄ k₅ : Nat) : List GoString :=
  etcd_txnlinfaultsN.txnlinfaultsNDirs k₁ ++
    [memberDataDir etcd_partition.name₁, memberDataDir etcd_partition.name₂,
      memberDataDir etcd_partition.name₃] ++
    [go!"/tmp/etcd-grove-data/compactkv.etcd", go!"/tmp/etcd-grove-data/putgetc.etcd",
      go!"/tmp/etcd-grove-data/cachekv.etcd"] ++
    etcd_authN.authNDirs k₂ ++ etcd_authlease.authleaseDirs k₃ ++ etcd_leaseN.leaseNDirs k₄ ++
    leasecatchupDataDirs ++ etcd_restartN.restartNDirs k₅ ++ [go!"/tmp/etcd-grove-data/restart1.etcd"]

end adequacy
end EtcdGrove
end Perennial

end
