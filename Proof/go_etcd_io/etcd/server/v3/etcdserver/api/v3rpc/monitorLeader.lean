/-
Proof of the spec of the same name (the watch slice's unit W-W, 2026-10-15). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.monitorLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__StoppingNotify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.monitorLeader.wp_proof
    (wp_GoAttach : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (wp_StoppingNotify : EtcdServer.StoppingNotify.spec (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG)) :
    v3rpc.monitorLeader.spec (GF := GF) (hG := hG) := by
  intro s ch tm et
  wp_start as ⟨Hgr, Hlg, #Hlead, #Hst, #Hstc, #Htm, #Het⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoInterface) (V := Unit)
    google_golang_org.grpc.ServerStream.ty (go.GoType.StructType [])) as %mp Hmp
  wp_pures
  irename : («$r0_ptr» ↦ (_ : v3rpc.streamsMap) : IProp GF) => Hsm
  iStructNamed Hsm
  imod sync.init_Mutex (v3rpc.streamsMapInv «$r0_ptr») ⊤
    (structFieldRef v3rpc.streamsMap go!"mu" «$r0_ptr») $$ [mu] [streams Hmp] with #Hmu
  · iexact mu
  · inext; iunfold v3rpc.streamsMapInv; iexists mp; iframe
  ipersist s
  ipersist smap
  wp_apply wp_GoAttach s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_auto
    ihave HI : (∃ n : w64, noLeaderCnt_ptr ↦ n) $$ [noLeaderCnt]
    · iexists _; iexact noLeaderCnt
    wp_for HI
    wp_apply wp_StoppingNotify s ch $$ []
    · iframe #
    wp_apply (lc := 2) time.wp_After as %tch %γt #Hbag
    ihave #Hstc' := Hstc
    iunfold stopChan at Hstc'
    icases Hstc' with ⟨%γst, #Hstc'⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γst
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstc'
      iapply stop_chan_receive _ _ _ _ _ $$ Hstc'
      iintro ⟨-, -⟩
      wp_auto
      wp_for_post
      iapply HΦ'
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
      inext
      iintro %tm' -
      wp_auto
      wp_apply wp_Leader s $$ []
      · iframe #
      iintro %l -
      wp_auto
      wp_if_destruct
      · wp_if_destruct
        · wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
          iunfold v3rpc.streamsMapInv at HR
          icases HR with ⟨%mp', Hf, Hm'⟩
          wp_auto
          wp_apply (wp_map_for_range (K := GoInterface) (V := Unit) (fun _ _ => iprop(True)) _
            google_golang_org.grpc.ServerStream.ty (go.GoType.StructType []) mp' ∅ (DFrac.own 1))
            $$ Hm'
          iintro %keys %Hkeys
          isplitr
          · itrivial
          isplitr
          · iintro !> %i %key %v %Hiv
            exfalso
            simp at Hiv
          iintro - -
          wp_apply (wp_map_make1 (K := GoInterface) (V := Unit)
            google_golang_org.grpc.ServerStream.ty (go.GoType.StructType [])) as %mp'' Hmp''
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hf Hmp'']
          · inext; iunfold v3rpc.streamsMapInv; iexists mp''; iframe
          wp_for_post
          iframe
          iexists _
          iframe
        · wp_for_post
          iframe
          iexists _
          iframe
      · wp_for_post
        iframe
        iexists _
        iframe
    iapply BigAndL.bigAndL_nil.2
    itrivial
  iapply HΦ
  iframe Hgr Hlg
  iunfold v3rpc.streamsMapIs
  iexact Hmu

end proof

end EtcdGrove
end Perennial
