/- Lean-first (no Rocq counterpart), 2026-10-29 (stage U7). -/
module

public import Spec.go_etcd_io.raft.v3.node__Status
public import Proof.go_etcd_io.raft.v3.InvNodeChan
import all Proof.go_etcd_io.raft.v3.InvNodeChan
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

`Status()` makes an unbuffered reply channel `c` (a handshake carrying `statusOwnRaw`), sends it on
`status` (`statusChP`), and receives `run`'s answer, `getStatus(r)`; or, the node stopped (`done`
closed), returns `Status{}`. -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the header above. -/
private abbrev node.Status.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Status")) (Val #()))
  {{ (st : Status), RET #st; statusOwnRaw st }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem node.Status.wp_raw : node.Status.specRaw (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as #Hnode
  ihave #Hnode' := Hnode
  open_node Hnode'
  wp_auto_lc 3
  wp_apply chan.wp_make1 (V := Status) as %ch %γc ⟨#Hch, %_, Hoc⟩
  imod start_handshake ch (fun st : Status => statusOwnRaw (GF := GF) st) iprop(True) γc
    $$ Hch Hoc with #Hhc
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `n.status <- c`, then `<-c`
    simp only [chan.blockingClausePre]
    iexists GoChan, inferInstance, inferInstance, inferInstance, inferInstance, nv.status',
      γ.status, ch
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isHandshake_isChan $$ Hstatus
    iapply handshake_send_au γ.status nv.status' ch statusChP iprop(True)
      $$ [$Hlc1 $Hlc2 $Hlc3] Hstatus []
    · iunfold statusChP
      iexists γc
      iexact Hhc
    inext
    iintro -
    wp_auto
    wp_bind (App (Val (chan.receive _)) (Val _))
    iapply chan.wp_receive ch γc $$ []
    · iapply isHandshake_isChan $$ Hhc
    iintro ⟨Hl1, Hl2, -, -⟩
    iapply handshake_receive_au γc ch _ iprop(True) _ $$ [$Hl1 $Hl2] Hhc []
    · itrivial
    inext
    iintro %st Hst
    wp_auto
    iapply HΦ
    iexact Hst
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-n.done`: stopped, `Status{}`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
    iapply node_done_recv_au γ nv.done' _ $$ Hdone
    iintro -
    wp_auto
    iapply HΦ
    iunfold statusOwnRaw
    ileft
    ipureintro
    rfl
  iapply BigAndL.bigAndL_nil.2
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

/-- `node.Status.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Status_impl
    (hS : EtcdGrove.node.Status.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Status.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Status.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.statusOwn
  intro n γ N id
  iintro %Φ ⟨#Hinit, #Hnode⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hrn, -⟩
  iapply (hS γn id n) $$ []
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

theorem node.Status.wp_proof : node.Status.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Status_impl node.Status.wp_raw

end proof

end EtcdGrove
end Perennial
