/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewWatchFromWatchClient.lean` (the watch slice's unit
W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewWatchFromWatchClient
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem NewWatchFromWatchClient.wp_proof
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG)) :
    NewWatchFromWatchClient.spec (GF := GF) (hG := hG) := by
  intro V c callSl vs
  wp_start as ⟨#Hf, %Hc, #Hco, #Hvs, #Hok, #Hlg, %Hbd⟩
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := Loc) as %mS HS
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hwnn⟩
  iStructNamed «$r0»
  ipersist remote
  simp only [decide_eq_false Hc]
  wp_auto
  ipersist callOpts
  iapply wp_fupd
  wp_apply wp_GetLogger c $$ [] as %lg %Hlg0
  · iframe #
  ipersist lg
  imod sync.init_Mutex (watcherMu { V with lg := lg } «$r0_ptr» callSl) ⊤
    (watcherF «$r0_ptr» go!"mu") $$ mu [streams HS] with #Hmu
  · inext
    unfold watcherMu
    iexists mS
    iframe streams
    iright
    iexists ∅
    iframe HS
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iapply HΦ
  iexists «$r0_ptr», lg
  isplitr
  · ipureintro; rfl
  unfold isClientWatcherCore
  iexists callSl, vs
  iframe #
  isplitr
  · ipureintro; exact Hwnn
  ipureintro; exact ⟨Hlg0, Hbd⟩

end proof

end EtcdGrove
end Perennial
