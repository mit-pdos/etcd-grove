/-
# The durable key-value store's shared ghost vocabulary (2026-11-22, kvraft decision B)

The store's ghost names (`KdNames`), its namespaces, and the predicates a machine other than a
replica's states its proofs in: the store's invariant (`rkvInv`, over `opSlot`, `readSlot`,
`kvCore`), what a waiter learns (`waitP`), the history's lower bound (`kvLb`), the read answers
(`readAns`) and the registry of the snapshots made (`kdSnapInv`). Moved out of `Defs.lean`,
statements unchanged, into sections over the global ghost state only (`[AllG GF] [ReceiptGS GF]
[InvGS GF]`: no heap, no Go semantics), as raft's cluster vocabulary is (`notes/raft-cluster-global.md`),
so that kvraft's adequacy can allocate them before any machine runs and its checking client can
hold them on another machine. `Defs.lean` imports it.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Defs
public import KvRaft.Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The namespaces: raft's cluster, the store's invariant, the snapshots' registry, the conf
decisions, the files, the replicas' file invariants, the statistics. -/
def kdRaftN : Namespace := nroot.@"kvdurable_raft"
def kdRkvN : Namespace := nroot.@"kvdurable_rkv"
def kdSnapN : Namespace := nroot.@"kvdurable_snaps"
def kdConfN : Namespace := nroot.@"kvdurable_conf"
def kdFilesN : Namespace := nroot.@"kvdurable_files"
def kdRepN : Namespace := nroot.@"kvdurable_rep"
def kdStatsN : Namespace := nroot.@"kvdurable_stats"

/-- What an operation's atomic update may open (kvreconf's `kvrMask`, and the files'). -/
def kdMask : CoPset :=
  (((((⊤ \ ↑kdRaftN) \ ↑kdRkvN) \ ↑kdSnapN) \ ↑kdConfN) \ ↑kdFilesN) \ ↑kdRepN

/-- **The durable store's ghost names**: kvreconf's (raft's cluster, the store's history, the
minted operations and reads, ...), the files' (`durableFilesInv`), and per replica id the file's
writer variable (`kdWriter`); the map of the current incarnations and the crasher's token
(`curRep`, `crasher`: 2026-11-01, the crasher); the cluster's replica bound `max` (`opts.MaxReplicas`;
2026-11-16, kvraftN: until then the constant `9`). -/
structure KdNames where
  r : raft_kvreconf.RNames
  files : GName
  wr : w64 → GName
  /-- the current incarnation of each started replica (a `ghostMap` from ids to `Loc`s: its
  authority in `clusterLockInv`, at `c.replicas`; its fragments `curRep`) -/
  cur : GName
  /-- the crasher's token (`token`: `crasher`) -/
  crt : GName
  /-- the replicas the cluster may start (`opts.MaxReplicas`): their ids are `1 … max` -/
  max : Nat


section store
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-! ## The store's model (kvreconf's, at kvdurable's namespaces) -/

/-- The client's half of the store's state `m` (kvreconf's `rkvVal`). -/
def rkvVal (γ : KdNames) (m : raft_kvreconf.KVMap) : IProp GF :=
  iprop(∃ H : List (List w8), ghostVar γ.r.val (1 : Qp).half H ∗ ⌜raft_kvreconf.kvFold H = m⌝)

/-- An operation's atomic update over the store's state. -/
def opAu (γ : KdNames) (f : raft_kvreconf.KVMap → raft_kvreconf.KVMap) (k : List w8)
    (Φ : List w8 → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (x : raft_kvreconf.KVMap), rkvVal γ x }> @ kdMask, ∅
    <{ rkvVal γ (f x), COMM Φ (f x k) }>)

/-- An operation's slot. -/
def opSlot (γ : KdNames) (d : List w8) (γp : GName × GName) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γp.1 DFrac.discard Φ ∗
    ( (⌜d ∉ H⌝ ∗ £ 1 ∗ opAu γ (fun x => raft_kvreconf.kvApply x d) (raft_kvreconf.dkey d) Φ)
    ∨ (∃ H0, ⌜H0 ++ [d] <+: H ∧ d ∉ H0⌝ ∗
        (Φ (raft_kvreconf.kvFold (H0 ++ [d]) (raft_kvreconf.dkey d)) ∨ token γp.2)) ))

/-- The timeless part of the store's invariant. -/
def kvCore (γ : KdNames) (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8))
    (RS : GMap w64 w64) (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName))
    (U : GSet (List w8)) : IProp GF :=
  iprop(ownCommittedOps γ.r.cluster ops ∗ ghostVar γ.r.val (1 : Qp).half (raft_kvreconf.logHist ops) ∗
    ownReadCtxs γ.r.cluster U ∗ ghostVar γ.r.opn (1 : Qp).half n ∗
    ghostMapAuth γ.r.mint 1 Mi ∗ ghostMapAuth γ.r.rseq 1 RS ∗ ghostMapAuth γ.r.rmint 1 RMi ∗
    ghostMapAuth γ.r.ops 1 O ∗ ⌜raft_kvreconf.MintOk n Mi RS RMi O U⌝ ∗
    ⌜∀ d, some d ∈ ops.map raft_kvreconf.odOf → raft_kvreconf.MintedOp Mi d⌝ ∗
    ⌜∀ e ∈ ops, e.isConfChange → raft_kvreconf.ConfShaped e⌝)

/-- A read's slot. -/
def readSlot (γ : KdNames) (γΦ : GName) (s : raft_kvreconf.ReadRec) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γΦ DFrac.discard Φ ∗
    ( (⌜∀ H', s.start <+: H' → H' <+: H → s.ans ≠ some (raft_kvreconf.kvFold H' s.key)⌝ ∗ £ 1 ∗
        AU <{ ∃∃ (x : raft_kvreconf.KVMap), rkvVal γ x }> @ kdMask, ∅
          <{ rkvVal γ x, COMM Φ (x s.key) }>)
    ∨ (∃ v, ⌜s.ans = some v⌝ ∗ Φ v) ))

/-- The registry of the reads in flight. -/
def readReg (γ : KdNames) (H : List (List w8)) : IProp GF :=
  iprop(∃ RD : GMap GName raft_kvreconf.ReadRec, ghostMapAuth γ.r.rds 1 RD ∗
    [∗map] γΦ ↦ s ∈ RD, readSlot γ γΦ s H)

def rkvInvBody (γ : KdNames) : IProp GF :=
  iprop(∃ (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
      (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)),
    kvCore γ ops n Mi RS RMi O U ∗
    ([∗map] d ↦ γp ∈ O, opSlot γ d γp (raft_kvreconf.logHist ops)) ∗ readReg γ (raft_kvreconf.logHist ops))

/-- The store's invariant (kvreconf's `rkvInv`). -/
def rkvInv (γ : KdNames) : IProp GF := inv kdRkvN (rkvInvBody γ)

/-- What a waiter learns with the value `v`. -/
def waitP (γ : KdNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γ.r.cluster l ∗ ⌜raft_kvreconf.AnsOk (raft_kvreconf.logHist l) d v⌝)

/-- A lower bound on the store's history (persistent). -/
def kvLb (γ : KdNames) (L : List (List w8)) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γ.r.cluster l ∗ ⌜L = raft_kvreconf.logHist l⌝)

/-- What the applier answers a read of the context `c` with. -/
def readAns (γ : KdNames) (c : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (i : w64) (ap : List LogEntry) (key : List w8),
    readStateOk γ.r.cluster kdRaftN c i ∗ isCommittedLogLb γ.r.cluster ap ∗
    ⌜uint.Z i ≤ (ap.length : Int) ∧ (∃ rp s, raft_kvreconf.decodeReadCtxB c = some (rp, s, key)) ∧
      v = raft_kvreconf.kvFold (raft_kvreconf.logHist ap) key⌝)

/-- What a snapshot the store made promises (kvreconf's `kvrSnapRecOk`). -/
def kdSnapRecOk (γ : KdNames) (s : SnapRec) : IProp GF :=
  iprop(∃ L : List LogEntry, isCommittedLogLb γ.r.cluster L ∗ confAt γ.r.cluster L.length s.conf ∗
    ⌜L.length = s.index ∧ raft_kvreconf.kvSnapOk L s.data ∧ GMap.size s.conf.ids < 2 ^ 61⌝)

/-- The store's registry of the snapshots made (an invariant). -/
def kdSnapInv (γ : KdNames) : IProp GF :=
  inv kdSnapN iprop(∃ S : List SnapRec, ownSnapsMade γ.r.cluster S ∗
    [∗list] s ∈ S, kdSnapRecOk γ s)

end store

end kvraft
end EtcdGrove
end Perennial
