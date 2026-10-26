/-
# Raft's signature (prototype, 2026-10-26)

The analogue of a Rocq `Module Type`: `RaftSig` names the types and predicates raft's specs are
stated in, **without defining them**, and the laws a client may use of them. A spec of raft's
API is stated over `[S : RaftSig GF]` (`node.Propose.specS`, `node.readyRecv.specS` below), and a
proof outside raft is written against the class, generic in `S`: it can use a predicate only
through the laws here, since nothing defines it in this file and this file imports none of
raft's proofs. Raft's proof provides the instance (`Proof/go_etcd_io/raft/v3/SigImpl.lean`,
`raftSigImpl`: the definitions, and the laws and specs proved at them), as an implementation of
the module type; a closed theorem applies its client's results to that instance, as a functor
is applied.

What the signature states concretely is in `SigBase.lean` (facts about Go values: the context a
call takes, the errors it returns) and in the protobuf records' pure models (`PbModel.lean`:
`EntryM`, `HardStateM`).

The trust base of a spec stated here is this file, `SigBase.lean`, the models and the Go code:
not the definitions of `rLog`, `rLogLb` or `isNode`, which a change to raft's proof may change
freely as long as the laws still hold.

Prototype scope: the committed log (`rLog`, `rLogLb`), proposals (`propReg`, `entData`), the
node, and a `Ready`'s payload as far as the committed log is concerned; `node.Propose` and the
receive on the `Ready` channel. The other specs and the rest of a `Ready` follow the same pattern.
-/
module

public import Spec.go_etcd_io.raft.v3.SigBase
-- what `isPkgInit` means for raft's package (its globals' facts): package facts, not raft's proofs
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.PbModel
public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.FUpd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section sig
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]

/-- **Raft's signature**: abstract names, predicates and their laws. -/
class RaftSig (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] where
  /-- A cluster's ghost names. -/
  Names : Type 1
  /-- A node's ghost names. -/
  NodeNames : Type 1
  /-- The cluster a node belongs to. -/
  raft : NodeNames → Names
  /-- The namespace of the cluster's invariant: a client's update runs outside it. -/
  N : Namespace
  /-- The cluster's invariant. -/
  inv : Names → IProp GF
  inv_persistent : ∀ γ, Persistent (inv γ)
  /-- The node at `n`, of id `id`, running. -/
  isNode : NodeNames → w64 → Loc → IProp GF
  isNode_persistent : ∀ γ id n, Persistent (isNode γ id n)
  isNode_inv : ∀ γ id n, isNode γ id n ⊢ inv (raft γ)

  /-- **The committed log**, the client's (exclusive): what a proposal's update moves. -/
  rLog : Names → List EntryM → IProp GF
  rLog_timeless : ∀ γ L, Timeless (rLog γ L)
  /-- **A lower bound of the committed log** (persistent): what a `Ready` hands out. -/
  rLogLb : Names → List EntryM → IProp GF
  rLogLb_persistent : ∀ γ L, Persistent (rLogLb γ L)
  /-- Lower bounds are prefix-closed. -/
  rLogLb_mono : ∀ γ l1 l2, l1 <+: l2 → rLogLb γ l2 ⊢ rLogLb γ l1
  /-- Any two lower bounds agree: one is a prefix of the other (every node's committed log is
  one log's prefix). -/
  rLogLb_agree : ∀ γ l1 l2, rLogLb γ l1 ∗ rLogLb γ l2 ⊢ ⌜l1 <+: l2 ∨ l2 <+: l1⌝
  /-- The committed log is a lower bound of itself. -/
  rLog_lb : ∀ γ L (E : CoPset), ↑N ⊆ E →
    inv γ ∗ rLog γ L ⊢ |={E}=> rLog γ L ∗ rLogLb γ L

  /-- An entry's data (persistent): `some d` for a client's proposal of `d`, `none` for raft's
  own entries. -/
  entData : Names → EntryM → Option (List w8) → IProp GF
  entData_persistent : ∀ γ e o, Persistent (entData γ e o)
  /-- The right to register the data `d` (once per data). -/
  propFresh : Names → List w8 → IProp GF
  /-- `d` is registered with the result predicate `Q` (persistent). -/
  propReg : Names → List w8 → (List EntryM → IProp GF) → IProp GF
  propReg_persistent : ∀ γ d Q, Persistent (propReg γ d Q)
  prop_register : ∀ γ d Q (E : CoPset), ↑N ⊆ E →
    inv γ ∗ propFresh γ d ⊢ |={E}=> propReg γ d Q
  /-- At a committed occurrence of `d` (at position `m` of a lower bound `L`), the result of the
  log before it. -/
  prop_collect : ∀ γ d (Q : List EntryM → IProp GF) (L : List EntryM) (m : Nat) (e : EntryM)
    (E : CoPset), ↑N ⊆ E → L[m]? = some e →
    inv γ ∗ propReg γ d Q ∗ rLogLb γ L ∗ entData γ e (some d) ⊢ |={E}=> ▷ ▷ □ Q (L.take m)

  /-- The node's `Ready` channel (persistent). -/
  isReadyChan : NodeNames → Loc → IProp GF
  isReadyChan_persistent : ∀ γ ch, Persistent (isReadyChan γ ch)
  /-- The driver's token: the committed log handed out so far `ds`, the hard state last handed
  out `p` (exclusive). -/
  nodeDriver : NodeNames → w64 → Loc → List EntryM → HardStateM → IProp GF
  /-- The driver's token with a `Ready` in hand: handed `ds`, to append `es`, at `p`. -/
  nodeDriverBusy : NodeNames → w64 → Loc → List EntryM → List EntryM → HardStateM → IProp GF
  /-- A `Ready`'s payload, after the committed log `d`: its committed entries `ce`, its entries
  to append `es`, the hard states before and after it. -/
  readyData : NodeNames → Ready → List EntryM → List EntryM → List EntryM → HardStateM →
    HardStateM → IProp GF
  /-- A `Ready`'s committed entries extend the committed log handed out: a lower bound. -/
  readyData_committed : ∀ γ rd d ce es p p',
    readyData γ rd d ce es p p' ⊢ readyData γ rd d ce es p p' ∗ rLogLb (raft γ) (d ++ ce)
  /-- A node that is never handed a snapshot (the specs below are for it). -/
  noSnap : NodeNames → Prop

attribute [instance] RaftSig.inv_persistent RaftSig.isNode_persistent RaftSig.rLog_timeless
  RaftSig.rLogLb_persistent RaftSig.entData_persistent RaftSig.propReg_persistent
  RaftSig.isReadyChan_persistent

end sig

/-! ## The specs, over the signature -/

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Propose`** (`node.Propose.spec`'s statement, over the signature): the data
registered with `Q`, and the client's update of the committed log -- appending an entry of
`data` -- which raft fires at most once, when an entry of the proposal is committed; the error
`nil`, `ErrProposalDropped`, `ErrStopped` or the context's. -/
abbrev node.Propose.specS [S : RaftSig GF] : Prop :=
  ∀ (γ : S.NodeNames) (id : w64) (n : Loc) (data_sl : GoSlice) (data : List w8)
    (Q : List EntryM → IProp GF)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ S.isNode γ id n ∗
      nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗
      ⌜data ≠ []⌝ ∗
      S.propReg (S.raft γ) data Q ∗
      AU <{ ∃∃ (L : List EntryM), S.rLog (S.raft γ) L }> @ ⊤ \ ↑S.N, ∅
         <{ ∀∀ (e : EntryM), S.rLog (S.raft γ) (L ++ [e]) ∗ S.entData (S.raft γ) e (some data) ∗
              ⌜uint.Z e.Index' = (L.length : Int) + 1⌝,
            COMM □ Q L }> }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err; propErr cd err }}

/-- **`node.Ready`**: the node's `Ready` channel. -/
abbrev node.Ready.specS [S : RaftSig GF] : Prop :=
  ∀ (γ : S.NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ S.isNode γ id n }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Ready")) (Val #()))
  {{ (ch : Loc), RET #ch; S.isReadyChan γ ch }}

/-- **Receiving a `Ready`** (`for rd := range n.Ready()`), at a node never handed a snapshot:
with the driver's token at the committed log handed out `ds`, the `Ready`'s payload for `ds`
(`readyData`, whose committed entries extend `ds` to a lower bound of the committed log,
`readyData_committed`) and the token busy with it. -/
abbrev node.readyRecv.specS [S : RaftSig GF] : Prop :=
  ∀ (γ : S.NodeNames) (id : w64) (n ch : Loc) (ds : List EntryM) (p : HardStateM),
  S.noSnap γ →
  {{ S.isReadyChan γ ch ∗ S.nodeDriver γ id n ds p }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true);
      ∃ (ce es : List EntryM) (p' : HardStateM),
        S.readyData γ rd ds ce es p p' ∗ S.nodeDriverBusy γ id n (ds ++ ce) es p' }}

end spec

end EtcdGrove
end Perennial
