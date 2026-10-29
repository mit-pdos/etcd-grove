/- Proof of `Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean`, Lean-first (2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.confChangeToMsg
public import Spec.go_etcd_io.raft.v3.node__Step
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Perennial.Proof.context
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiDyn

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! `node.ProposeConfChange` (node.go), Lean-first (2026-10-13, reconfiguration stage D).

`ProposeConfChange(ctx, cc)` is `msg, err := confChangeToMsg(cc); if err != nil { return err };
return n.Step(ctx, msg)`: the proposal goes on `propc` as a forwarded one (no result channel),
and `run` steps it (`RawNode.ProposeConfChange`'s file header says what that does). The
entry's data is recorded as proposed (`isPropData`, through the node's proposed slices'
invariant, `node_read_register`), which makes the proposal a protocol message (`fwdP`).
Partial correctness: whether the change is appended or refused is not visible.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `nodeErr cd err`: `nil`, raft's
`ErrStopped`, or the context's once its `Done()` fired (`ctxErr`).

raft v3.7 (2026-10-16, stage R5, D6): the entry holds the conf change's bytes, so no recording
(`isPropData`) is needed: the proposal is `fwdP` from `confChangeToMsg`'s owned message
(`msgIn ml 1`), `ccEntsOk_cc`.

**Logically atomic (2026-10-27).** As `node.Propose`: the conf change's entry is a tracked
proposal, keyed by its type and bytes (`entKey`), and the caller hands in `ccPropArg γ.raft o` --
once `o` is marshaled to bytes `bs`, the key's registration (`propIs`) and an update `propAu1` for
it, which `ProposeConfChange` deposits before the proposal leaves the node (`cc_propose_ghost`),
its ticket travelling with the proposal; or nothing, if the entry is a filler (an empty
`ConfChangeV2`). The update fires at most once, when the entry commits, and never if a leader
refuses the change (an empty normal entry, a filler, is appended in its place and the ticket
dropped). Until 2026-10-27 a conf-change entry fired the standing `noopAu`, and the change had to
be one the cluster's policy admits (`CCAllowed`).
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.ProposeConfChange.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (c : GoInterface) (o : ConfChangeIM) (dq : DFrac)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    -- (2026-10-28) the node in the API's cluster `γc`: what the clean `node.Step` takes
    (γc : ApiImpl.Cluster) (N : Namespace),
  ApiImpl.NodeOk γc γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      ApiImpl.isNode n γc N id ∗ nodeCtx ctx cd ∗
      ownConfChangeI c dq (some o) ∗
      -- (2026-10-27) the proposal tracked under its key (`ccPropArg`; until then
      -- `CCAllowed γ.raft o`, a change the cluster's policy admits)
      ccPropArg γ.raft o }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownConfChangeI c dq (some o) ∗ nodeErr cd err }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `confChangeToMsg`, then `Step` of the proposal, forwarded (`fwdP`). (Raft v3.7, stage R5, D6:
the message `msgIn ml 1` from `confChangeToMsg`, its entry `ccEntryM (some o) bs` holding the
bytes, so no recording of the data is needed. 2026-10-27: the proposal tracked under its key,
`cc_propose_ghost`. Stage R7a: any `nodeCtx`, the error
`nodeErr`.) -/
private theorem node.ProposeConfChange.wp_raw
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    node.ProposeConfChange.specRaw (GF := GF) (hG := hG) := by
  intro γ id n c o dq ctx cd γc N HNo
  wp_start as ⟨#Hnode, #HnodeA, #Hctx, Hc, Harg⟩
  wp_auto
  wp_apply wp_confChangeToMsg c (some o) dq $$ [$Hc] as %ml %bs ⟨Hc, Hm, %Hbs⟩
  -- (2026-10-27) the proposal's ghost work: tracked under its key, its ticket on the entry
  ihave #Hcinv := isNode_commitInv γ id n $$ Hnode
  imod cc_propose_ghost γ.raft o bs Hbs $$ Hcinv Harg with ⟨#Hent, Htk⟩
  -- (2026-10-28) the clean `node.Step`: the forwarded proposal is a `stepIn` at every node names of
  -- the cluster, whose `raft` is `γ`'s (`fwdP` reads only it)
  have wpS := wp_node_Step
  unfold EtcdGrove.node.Step.spec EtcdGrove.isNode EtcdGrove.stepIn EtcdGrove.Cluster at wpS
  icases msgPtsC_nn $$ Hm with ⟨%Hnn, Hm⟩
  wp_apply wpS n γc N id ml ctx cd $$ [$HnodeA $Hctx Hm Htk]
  · unfold ApiImpl.stepIn
    isplitr; · ipureintro; exact Hnn
    iintro %γn' %Hok' -
    have Hr : γn'.raft = γ.raft := Hok'.1.trans HNo.1.symm
    unfold stepP
    iright
    unfold fwdP
    rw [Hr]
    iexists ⟨propMsgM, [ccEntryM (some o) bs], none, [], []⟩
    iframe Hm
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · unfold isMessage absMsg absMsgFrom
      isplitr
      · ipureintro
        exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => propData (GF := GF) γ.raft e)).2
      iexact Hent
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ.raft e)).2
    iexact Htk
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iframe Hc
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

/-- `node.ProposeConfChange.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_ProposeConfChange_impl
    (hP : EtcdGrove.node.ProposeConfChange.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ProposeConfChange.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.ownCommittedOps
  intro n γ N id c o dq ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, Hcc, Hau⟩ HΦ
  ihave #HnodeA := Hnode
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, #Hci⟩
  have Hf0 := Hf
  obtain ⟨Hγr, -⟩ := Hf
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, #Hinv, -⟩
  iapply (hP γn id n c o dq ctx cd γ N Hf0) $$ [Hcc Hau]
  · iframe Hinit Hrn HnodeA Hctx Hcc
    unfold ccPropArg
    iintro %bs %Hm
    by_cases Hf : Filler (confChangeEntryType (some o)) bs
    · imodintro; ileft; ipureintro; exact Hf
    imod api_key_register γ N ⊤ CoPset.subseteq_top
      (entKey (confChangeEntryType (some o)) bs) $$ Hci with #Hpi
    ihave Hau1 := au_cc_fix γ N (confChangeEntryType (some o)) o bs Hm Hf $$ Hau
    ihave Hau1 := api_propAu1 γ N (confChangeEntryType (some o)) bs Hf HNs $$ Hinv Hau1
    imodintro
    iright
    iexists (fun _ => iprop(True))
    rw [Hγr]
    iframe Hpi Hau1
  iintro !> %err ⟨Hcc, #Herr⟩
  iapply HΦ
  iframe Hcc Herr

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ProposeConfChange.wp_proof
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    node.ProposeConfChange.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ProposeConfChange_impl (node.ProposeConfChange.wp_raw wp_confChangeToMsg wp_node_Step)

end proof

end EtcdGrove
end Perennial
