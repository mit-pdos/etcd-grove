/- Lean-first (no Rocq counterpart), 2026-10-29 (stage U9a). -/
module

public import Spec.go_etcd_io.raft.v3.node__Stop
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

`select { case n.stop <- struct{}{}: case <-n.done: return }; <-n.done`: the client's half of
`live` goes to `run` on `stop` (`isNodeChan`'s `Hstop`), which closes `done` once stopped
(`node_done_recv_au`); if `done` fired first, the node had stopped already. -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the header above. -/
private abbrev node.Stop.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeLiveRaw γ 1 }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); nodeStoppedRaw γ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem node.Stop.wp_raw : node.Stop.specRaw (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as ⟨#Hnode, Hlive⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `n.stop <- struct{}{}`: the client's half of `live` to `run`; then `<-n.done`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.stop',
      γ.stop, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isHandshake_isChan $$ Hstop
    iapply handshake_send_au γ.stop nv.stop' () (fun (_ : Unit) => nodeLiveRaw γ 1) iprop(True)
      $$ [$Hlc1 $Hlc2 $Hlc3] Hstop [Hlive]
    · iexact Hlive
    inext
    iintro -
    wp_auto
    wp_apply chan.wp_receive (V := Unit) nv.done' γ.done $$ [] as -
    · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
    iapply node_done_recv_au γ nv.done' _ $$ Hdone
    iintro #Hst
    wp_auto
    iapply HΦ
    iexact Hst
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-n.done`: stopped already
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
    iapply node_done_recv_au γ nv.done' _ $$ Hdone
    iintro #Hst
    wp_auto
    iapply HΦ
    iexact Hst
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

/-- `node.Stop.spec` from the raw triple: the names are `nodeRunning`'s (`isNode`'s are not
needed). -/
private theorem node.wp_Stop_impl
    (hS : EtcdGrove.node.Stop.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Stop.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Stop.spec EtcdGrove.Cluster EtcdGrove.nodeRunning EtcdGrove.nodeStopped
  intro n γ N id
  iintro %Φ ⟨#Hinit, -, Hlive⟩ HΦ
  iunfold nodeRunning at Hlive
  icases Hlive with ⟨%γn, %id1, %Hok, #Hn, #Htb, Hl⟩
  iapply (hS γn id1 n) $$ [Hl]
  · iframe Hinit Hn Hl
  iintro !> #Hst
  iapply HΦ
  unfold nodeStopped
  iexists γn, id1
  iframe Hn Hst
  isplitr
  · ipureintro; exact Hok.1
  iright; iexact Htb

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Stop.wp_proof : node.Stop.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Stop_impl node.Stop.wp_raw

end proof

end EtcdGrove
end Perennial
