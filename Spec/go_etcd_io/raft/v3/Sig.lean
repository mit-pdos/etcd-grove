/- Lean-first (no Rocq counterpart).

## raft's signature (2026-10-14)

What a client of the raft library may use of its proof, in one place: the specs of the
functions it may call (`raftSig.specs`), the further vocabulary it may name
(`raftSig.vocab`), and the laws of that vocabulary (`raftSig.GhostLaws`, `raftSig.Laws`,
proved by `raftSig.ghostLaws` and `raftSig.laws` in `Proof/go_etcd_io/raft/v3/Sig.lean`).
`notes/decisions.md`, "Package signatures: raft's first".

**The vocabulary** is what the specs and the laws are stated in (the predicates their
statements name: `isNode`, `nodeDriver`, `isCommitted`, `ownRaftGhost`, `ownMemoryStorage`,
...), plus `raftSig.vocab`: the pure model a driver of the network needs (message types)
and the parts of the proposal protocol a client keeps in its own invariants (`cLog`,
`propFresh`). A client may name these, their structures' fields and constructors, the
instances raft declares, and pure theorems about them; it may not name anything else of
raft's, nor unfold a predicate whose body names anything else (its unfolding would).
`etc/api-check.py raft` reports the uses that break this (`etc/api-check.lean`).

**The laws**, in two layers, as raft's proof is: `GhostLaws` over raft's ghost state
alone (`[AllG GF] [InvGS GF]`), for a client's ghost lemmas, and `Laws` at the program
level (`HeapGS`, a `StorageModel`, the package's assumptions). They are what clients use
(the register example, `examples/register`), and what the protocol is for:
* **The committed log** (`isCommitted γ l`, persistent): any two are prefixes of one
  another (`isCommitted_agree`, the safety property raft exists to provide) and it is
  downward closed (`isCommitted_mono`).
* **Allocation**: the ghost state of a new cluster with its commit invariant
  (`ownRaftGhost_alloc`), the term budget (`budget_alloc`), the proposed slices
  (`propDataInv_alloc`); a node's commit invariant (`isNode_commitInv`).
* **Proposals** (`notes/decisions.md`, "The register: TaDa proposals over raft's client
  log"): a committed entry's data (`node_committed_data`, `node_entData_heap`,
  `entDataIs_list_prefix`), the proposer's result (`node_collect`), and a deposited
  datum's fresh token (`deposited_fresh`).
* **The driver**: a `Ready`'s receipt (`node_ready_receive`), the tick credits
  (`tickCred_split`), and `MemoryStorage`'s appends (`memStorage_handout`,
  `memStorage_absorb`, `ownMemoryStorage_bounded`, `ownMemoryStorage_init`).

`raft_election_safety` (two leaders of a term are one node), which stood in for the
non-triviality of the protocol until a client used it, is gone: `isCommitted_agree` is the
property a client uses, and the register's adequacy theorem runs raft in a closed program.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.RawNode__Campaign
public import Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import Spec.go_etcd_io.raft.v3.RawNode__Propose
public import Spec.go_etcd_io.raft.v3.RawNode__Ready
public import Spec.go_etcd_io.raft.v3.RawNode__Step
public import Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Spec.go_etcd_io.raft.v3.MustSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

namespace raftSig

/-! ## The API -/

/-- The specs of the functions a client may call: the exported functions and methods of
package `raft` (the `Node` interface's, through `node`). Their `Link` results (`node.wp_Step`,
...) are the client's to apply, as is the packages' initialization
(`Proof/go_etcd_io/raft/v3/Init.lean`: `wp_initialize'` and the model of `log.New` it
assumes, `log.NewModel`). -/
def specs : List Lean.Name :=
  [``RestartNode.spec, ``node.Propose.spec, ``node.Ready.spec, ``node.Step.spec,
   ``node.Tick.spec, ``node.Advance.spec,
   ``NewMemoryStorage.spec, ``MemoryStorage.Append.spec, ``MemoryStorage.Entries.spec,
   ``MemoryStorage.FirstIndex.spec, ``MemoryStorage.LastIndex.spec,
   ``MemoryStorage.Snapshot.spec, ``MemoryStorage.Term.spec,
   ``NewRawNode.spec, ``RawNode.Advance.spec, ``RawNode.Campaign.spec,
   ``RawNode.HasReady.spec, ``RawNode.Propose.spec, ``RawNode.Ready.spec,
   ``RawNode.Step.spec, ``RawNode.Tick.spec,
   ``IsEmptyHardState.spec, ``IsEmptySnap.spec, ``IsLocalMsg.spec, ``IsLocalMsgTarget.spec,
   ``IsResponseMsg.spec, ``MustSync.spec]

/-- The vocabulary a client may name beyond what the specs and the laws are stated in (see
the file header). -/
def vocab : List Lean.Name :=
  [-- the proposal protocol's client side: the client log the client's update moves, the
   -- fresh tokens it mints, the update it deposits, and an entry's data (`entDataIs` is
   -- transparent: its body is the data's slice and deposit)
   ``cLog, ``propFresh, ``propAu, ``isPropData, ``occStep,
   -- the messages a driver delivers: what `node.Step` asks of one (`stepP`, transparent:
   -- a network message `netP`, a forwarded proposal `fwdP`) and the protocol's view of it
   ``netP, ``fwdP, ``NetMsgOk, ``netStepTypes, ``Msg, ``msgAbs, ``absSnap,
   ``MsgApp, ``MsgAppResp, ``MsgHeartbeat, ``MsgHeartbeatResp, ``MsgProp, ``MsgVote,
   ``MsgVoteResp,
   -- the `Storage` contract a client's storage meets (`isStorage`'s methods)
   ``isStorageWith,
   -- the logger a client passes (`isLogger`)
   ``logMethods]

/-! ## The laws -/

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- The laws of raft's ghost state (see the file header). -/
structure GhostLaws : Prop where
  isCommitted_agree (γ : RaftNames) (l1 l2 : List raftpb.Entry) :
    ⊢ isCommitted (GF := GF) γ l1 -∗ isCommitted γ l2 -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝
  isCommitted_mono (γ : RaftNames) (l1 l2 : List raftpb.Entry) :
    l1 <+: l2 → ⊢ isCommitted (GF := GF) γ l2 -∗ isCommitted γ l1
  ownRaftGhost_alloc (E : CoPset) (cfg ids : GSet w64) :
    W64 0 ∉ ids →
    ⊢ |={E}=> ∃ γ : RaftNames, ⌜γ.reCfg = cfg⌝ ∗ raftCommitInv (GF := GF) γ ∗
        isCommitted γ [] ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhost γ id initPState) ∗
        (cLog γ [] ∗ ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) ∗
          ghostMapAuth γ.reSl 1 (∅ : GMap GoSlice (List w8)))
  entDataIs_list_prefix (γ : RaftNames) (l P : List raftpb.Entry)
    (o oP : List (Option (List w8))) (Hp : l <+: P) :
    ⊢ ([∗list] e;o ∈ l;o, entDataIs (GF := GF) γ e o) -∗
      ([∗list] e;o ∈ P;oP, entDataIs γ e o) -∗ ⌜o <+: oP⌝
  /-- A deposited datum's fresh token is the client's: it is in the map whose authority
  the client holds. -/
  deposited_fresh (γ : RaftNames) (d : List w8) (M : GMap (List w8) Unit) (E : CoPset)
    (HE : ↑raftN ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γ -∗ deposited γ d -∗ ghostMapAuth γ.reFresh 1 M ={E}=∗
      ⌜M.lookup d = some ()⌝ ∗ ghostMapAuth γ.reFresh 1 M

end ghost

section program
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The laws at the program level (see the file header). -/
structure Laws : Prop where
  budget_alloc (N : Nat) (HN : N < 2 ^ 64 - 1) (E : CoPset) :
    ⊢ |={E}=> ∃ bud : BudgetNames, inv budgetN (budgetInv (GF := GF) bud) ∗ tickCred bud N ∗
      termLB bud (W64 0)
  propDataInv_alloc (γ : RaftNames) (E : CoPset) :
    ⊢ ghostMapAuth γ.reSl 1 (∅ : GMap GoSlice (List w8)) ={E}=∗
      inv propDataN (propDataInv (GF := GF) γ)
  tickCred_split (bud : BudgetNames) (a b : Nat) :
    tickCred (GF := GF) bud (a + b) ⊣⊢ tickCred bud a ∗ tickCred bud b
  /-- A node knows its cluster's commit invariant. -/
  isNode_commitInv (γ : NodeNames) (id : w64) (n : Loc) :
    isNode (GF := GF) γ id n ⊢ raftCommitInv γ.raft
  node_collect (γ : NodeNames) (id : w64) (n : Loc) (d : List w8) (γp : GName × GName)
    (Q : List (List w8) → IProp GF) (l : List raftpb.Entry) (ods : List (Option (List w8)))
    (m : Nat) (E : CoPset) (HE : ↑raftN ⊆ E) :
    ods[m]? = some (some d) → d ∉ firstOcc (ods.take m) →
    ⊢ isNode γ id n -∗ isProp γ.raft d γp Q -∗ propTok γp -∗ isCommitted γ.raft l -∗
      ([∗list] e;o ∈ l;ods, entDataIs γ.raft e o) ={E}=∗ ▷ ▷ Q (firstOcc (ods.take m))
  node_committed_data (γ : NodeNames) (id : w64) (n : Loc) (l : List raftpb.Entry)
    (E : CoPset) (HE : ↑raftN ⊆ E) :
    ⊢ isNode γ id n -∗ isCommitted γ.raft l ={E}=∗
      ∃ ods, [∗list] e;o ∈ l;ods, entDataIs (GF := GF) γ.raft e o
  node_entData_heap (γ : NodeNames) (id : w64) (n : Loc) (e : raftpb.Entry)
    (d : List w8) (E : CoPset) (HE : ↑propDataN ⊆ E) :
    ⊢ isNode γ id n -∗ entDataIs γ.raft e (some d) ={E}=∗ e.Data' ↦*□ d
  node_ready_receive (γ : NodeNames) (id : w64) (n ch : Loc) (ds : List raftpb.Entry) :
    {{ isReadyChan γ ch ∗ nodeDriver (GF := GF) γ id n ds }}
      (App (Val (chan.receive Ready.ty)) (Val #ch))
    {{ (rd : Ready), RET (PairV #rd #true);
        ∃ (ce es : List raftpb.Entry) (ms : List raftpb.Message),
          readyData γ rd ds ce es ms ∗ nodeDriverBusy γ id n (ds ++ ce) es }}
  memStorage_absorb (ms : Loc) (γs : MemStorNames) (σ1 σ : StorState)
    (p : List raftpb.Entry) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ1 -∗ memAppendedTok ms γs σ p ==∗
      ⌜σ1 = { σ with pend := p }⌝ ∗ ownMemoryStorage ms γs (storAbsorb σ1)
  memStorage_handout (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (p : List raftpb.Entry) (Hpo : σ.pend = [] ∧ PendOk σ p) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ ==∗
      ownMemoryStorage ms γs { σ with pend := p } ∗ memAppendTok ms γs σ p
  ownMemoryStorage_bounded (ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ -∗
      ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝ ∗
      ownMemoryStorage ms γs σ
  ownMemoryStorage_init (ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ ownMemoryStorage (GF := GF) ms γs σ -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownMemoryStorage ms γs σ

end program

end raftSig

end EtcdGrove
end Perennial
