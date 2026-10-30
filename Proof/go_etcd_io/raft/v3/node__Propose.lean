/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.node__stepWait
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Perennial.Proof.context
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.LemmasP5NodeErr
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `node.Propose(ctx, data)` (node.go:469)

A proposal of `data` from any goroutine: `stepWait` of a one-entry `MsgProp`, which `run`
steps as `RawNode.Propose` does. Until stage R7a specified for `context.Background()`.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `propErr cd err`: `nodeErr` (`nil`,
raft's `ErrStopped`, the context's once its `Done()` fired) or the proposal's own result from
`run` (`ErrProposalDropped`, ...; non-`nil`).

**Logically atomic (2026-10-10; stage R, 2026-10-14; D21 M6, 2026-10-19; 2026-10-21).** The
full committed log `rLog γ L` (`Protocol/GhostState.lean`) is the client's. Before proposing
`data` the client registers its key `k = entKey (W32 0) data` (the entry's type and bytes,
`entKey`, since 2026-10-27; until then the bytes) with a result predicate `Q`
(`node_prop_register`, a ghost step, once per key, with the fresh token `propFresh`), getting
`propIs γ k Q`. Each proposal of `data` then hands in `propIs γ k Q` and an atomic update
`propAu1 γ k Q` = `AU <{ ∃∃ L, rLog γ L }> @ ⊤ ∖ ↑raftN, ∅ <{ ∀∀ e, rLog γ (L ++ [e]) ∗
entDataIs γ e (some k), COMM □ Q L }>`, which `Propose` deposits in `k`'s slot before the proposal
leaves the node
(`node_propose_ghost`), with a ticket that travels with the proposal. It fires -- a linearization
point -- at most once, at a committed entry holding `data` (the ticket is spent where the
proposal is appended), on whichever node commits it; every committed occurrence of `data` gives
`□ Q` of the log before it (`prop_collect`, from `propIs`). `data` may be proposed any number of
times, each proposal with its own update. An empty `data`
(2026-10-27) is a filler (`Filler`: the same entry as a new leader's), which fires the standing
`noopAu` and takes no update: the client hands in `⌜data = []⌝`. The error (`ErrProposalDropped`, ...) says only
whether this proposal reached a leader; the update stays deposited either way. (Until
2026-10-21 the fresh token went with the first proposal, which returned the handle.)

raft v3.7 (2026-10-16, stage R5): the message is a fresh `*pb.Message` whose one entry holds
`data`'s bytes (D6: `propEntryM data`, the caller's slice frozen, `data_sl ↦*□ data`), on `propc`
(`propP`); until 2026-10-27 the data had to be non-empty (D6: an empty proposal would be a
leader's own entry; it now is one, a filler).
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.Propose.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (data_sl : GoSlice) (data : List w8)
    (Q : List EntryM → IProp GF)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗
      -- (2026-10-27) the proposal tracked under its key `entKey (W32 0) data`, or empty data (a
      -- filler, no update; until then `data ≠ []` was required)
      (⌜data = []⌝ ∨ propArg γ.raft (entKey (W32 0) data) Q) }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err; propErrRaw γ cd err }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The one-entry batch `[]pb.Entry{{Data: data}}`, then `stepWait`. (Raft v3.7, stage R5: the
message is `&pb.Message{Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Data: data}}}`, its entry
allocated by the slice literal (`wp_slice_literal_ex`, as `confChangeToMsg`), holding the frozen
bytes `data_sl ↦*□ data` (D6: `propEntryM data`; `node_propose_ghost`), frozen
(`entOwn_freeze`); the message owned (`msgIn ml 1`); `MsgProp.Enum()` is a new callee. Stage R7a:
any `nodeCtx`, the error `propErr`.) -/
private theorem node.Propose.wp_raw
    (wp_node_stepWait : node.stepWait.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.Propose.specRaw (GF := GF) (hG := hG) := by
  intro γ id n data_sl data Q ctx cd
  wp_start as ⟨#Hnode, #Hctx, #Hdata, Harg⟩
  wp_auto
  -- the proposal's ghost work (2026-10-10): the update deposited (2026-10-27: none for an empty
  -- `data`, a filler)
  imod node_propose_ghost γ id n data Q ⊤ CoPset.subseteq_top $$ Hnode Harg
    with ⟨#Hent, Htk⟩
  rw [show raftpb.MsgProp = #((W32 2 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 2) as %pty Hpty
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #data_sl)])] = 1 := rfl
  simp only [Hsz]
  imod cellRO_alloc $$ Hpty with #cTy
  imod entOwn_of_struct l0 (⟨zero_val _, null, null, null, data_sl, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM data) ⊤ rfl $$ [Hl0] with He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hdata
    msg_nulls
  imod entOwn_freeze $$ He with #He
  wp_auto
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgPtsC_of_struct «$a1_ptr» (⟨zero_val _, pty, null, null, null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) (DFrac.own 1) false [l0] ⟨propMsgM, [propEntryM data], none, [], []⟩ ⊤
      rfl $$ [«$a1» Hsl] with Hm
  · iframe «$a1» Hsl Hnilb
    simp only [propMsgM, show MsgProp = W32 2 from rfl]
    iframe cTy
    msg_nulls
    simp only [Bool.false_eq_true, ↓reduceIte, snapOpt]
    iframe He
    isplitl []; · iapply entsBig_nil
    isplitl []; · iempintro
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  wp_apply wp_node_stepWait γ id n «$a1_ptr» data ctx cd $$ [$Hnode $Hctx Hm $Hent $Htk]
  · simp only [msgIn, show needsCap propMsgM = false from rfl]
    iexact Hm
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iexact Herr

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.Propose.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Propose_impl
    (hP : EtcdGrove.node.Propose.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Propose.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Propose.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.ownCommittedOps
    EtcdGrove.Cluster.dup
  intro n γ N id data_sl data ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, #Hd, Hau⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, #Htab, #Hci, -⟩
  have Hγr := Hf.1
  by_cases Hne : data = []
  · iapply (hP γn id n data_sl data (fun _ => iprop(True)) ctx cd) $$ []
    · iframe Hinit Hrn Hctx Hd
      ileft; ipureintro; exact Hne
    iintro !> %err #Herr
    iapply HΦ
    unfold EtcdGrove.propErrS EtcdGrove.nodeErrS EtcdGrove.nodeStopped
    iapply propErrRaw_propErrS n γ N id γn cd err Hf
    iframe Hrn Htab Herr
  have Hnf : ¬ Filler (W32 0) data := fun h => Hne h.1
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, #Hinv, -⟩
  imod api_key_register γ N ⊤ CoPset.subseteq_top (entKey (W32 0) data) $$ Hci with #Hpi
  ihave Hau1 := api_propAu1_if γ N (W32 0) data Hnf HNs $$ Hinv Hau
  iapply (hP γn id n data_sl data (fun _ => iprop(True)) ctx cd) $$ [Hau1]
  · iframe Hinit Hrn Hctx Hd
    iright
    unfold propArg
    rw [Hγr]
    iframe Hpi Hau1
  iintro !> %err #Herr
  iapply HΦ
  unfold EtcdGrove.propErrS EtcdGrove.nodeErrS EtcdGrove.nodeStopped
  iapply propErrRaw_propErrS n γ N id γn cd err Hf
  iframe Hrn Htab Herr

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Propose.wp_proof
    (wp_node_stepWait : node.stepWait.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.Propose.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Propose_impl (node.Propose.wp_raw wp_node_stepWait wp_MessageType_Enum)

end proof

end EtcdGrove
end Perennial
