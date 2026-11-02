/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Tick
public import Proof.ReceiptTactics
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
import all Proof.go_etcd_io.raft.v3.InvNode
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

## `node.Tick()` (node.go:458)

A tick, for one credit of the term budget (`tickCred`, `InvNode.lean`; since 2026-10-29, stage U7,
a time receipt of one of `Tick`'s own Go steps, not the caller's): the credit goes
into the buffered `tickc` with the tick, or is dropped with it when the channel is full
(the `default` branch, which warns through the raft struct's logger). Callable from any
goroutine.
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.Tick.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Tick")) (Val #()))
  {{ RET #(); True }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The credit goes into `tickc` with the tick (`tickInv`), or is dropped with it; the
`default` branch's warning reads the raft struct's shared fields (`isNodeChan`). -/
private theorem node.Tick.wp_raw : node.Tick.specRaw (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as #Hnode
  ihave #Hnode' := Hnode
  open_node Hnode'
  -- (2026-10-29, stage U7) the tick's credit, a time receipt of a Go step of its own
  repeat (
    fail_if_success wp_bind (App (Val (GoInstruction (StructFieldRef _ _))) (Val _))
    first | wp_pure | wp_load | wp_store | wp_alloc_auto)
  wp_bind (App (Val (GoInstruction (StructFieldRef _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro Hcred -
  iapply wp_value'
  wp_auto_lc 2
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `tickc <- struct{}{}`: the credit with the tick
      simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.tickc',
        γ.tick, ()
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iexact Htickc
      unfold nonblockingSendAu nonblockingSendAuInner
      isplit
      · iinv Htickinv with Hi Hclose
        imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
        unfold tickInv
        icases Hi with ⟨%l, Hoc, Hcr⟩
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        iexists .Buffered l
        iframe Hoc
        simp only
        iintro Hoc
        imod Hmask with -
        imod Hclose $$ [Hoc Hcr Hcred] with -
        · inext
          iexists l ++ [()]
          iframe Hoc
          simp only [List.length_append, List.length_singleton]
          iapply (tickCred_split γ.bud l.length 1).2
          iframe Hcr
          unfold tickCred; iexact Hcred
        imodintro
        wp_auto
        iapply HΦ
        itrivial
      · itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-n.done` (2026-10-29, stage U9a): the node stopped, the tick is dropped
      simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
      iapply blocking_rcv_implies_nonblocking
      iapply node_done_recv_au γ nv.done' _ $$ Hdone
      iintro -
      wp_auto
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`: the warning, through the raft struct's logger
    wp_auto
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlogger
    try wp_auto
    iapply HΦ
    itrivial

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.Tick.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Tick_impl
    (hT : EtcdGrove.node.Tick.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Tick.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Tick.spec EtcdGrove.Cluster EtcdGrove.isNode
  intro n γ N id
  iintro %Φ ⟨#Hinit, #Hnode⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hrn, -⟩
  iapply (hT γn id n) $$ []
  · iframe Hinit Hrn
  iexact HΦ

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Tick.wp_proof :
    node.Tick.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Tick_impl (node.Tick.wp_raw)

end proof

end EtcdGrove
end Perennial
