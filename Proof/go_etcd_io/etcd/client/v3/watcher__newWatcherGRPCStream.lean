/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcher__newWatcherGRPCStream.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__newWatcherGRPCStream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__run
public import Spec.go_etcd_io.etcd.client.v3.streamKeyFromCtx
public import Spec.context.WithCancelValCtx
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [ctx_sem : context.Assumptions]

set_option maxHeartbeats 0 in
theorem watcher.newWatcherGRPCStream.wp_proof
    (wp_WithCancel : context.WithCancelValCtx.spec (GF := GF) (hG := hG))
    (wp_key : streamKeyFromCtx.spec (GF := GF) (hG := hG))
    (wp_run : watchGRPCStream.run.spec (GF := GF) (hG := hG)) :
    watcher.newWatcherGRPCStream.spec (GF := GF) (hG := hG) := by
  intro V w inctx cs
  wp_start as ⟨#Hw, #Hin, %Hb⟩
  ihave #Hw' := Hw
  iunfold isClientWatcher at Hw'
  icases Hw' with ⟨%callSl, %vs, %Hwnn, #Hrem, #Hco, #Hvs, #Hok, #Hlg, #Hmu, #Hf, %Hlgb⟩
  obtain ⟨Hlgnn, -⟩ := Hlgb
  wp_auto
  wp_alloc vcp as Hvc
  ipersist Hvc
  wp_apply wp_WithCancel vcp inctx cs $$ [] as %cx %γc %cancel ⟨#Hcspec, #Hcx, %Hmd⟩
  · iframe #
  wp_apply wp_key inctx cs $$ []
  · iframe #
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %m0 Hm0
  wp_apply chan.wp_make1 (V := Loc) as %respc %γresp ⟨#Hrespc, %-, Hrespo⟩
  wp_apply chan.wp_make1 (V := GoInterface) as %reqc %γreq ⟨#Hreqc, %-, Hreqo⟩
  wp_apply chan.wp_make1 (V := Unit) as %donec %γdone ⟨#Hdonec, %-, Hdoneo⟩
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %errc %γerr ⟨#Herrc, %Hcap, Herro⟩
  · ipureintro; word
  wp_apply chan.wp_make1 (V := Loc) as %closingc %γcl ⟨#Hclc, %-, Hclo⟩
  wp_apply chan.wp_make1 (V := Unit) as %resumec %γrc ⟨#Hrcc, %-, Hrco⟩
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hgnn⟩
  iStructNamed «$r0»
  ipersist owner
  ipersist remote
  ipersist callOpts
  ipersist ctx
  ipersist ctxKey
  ipersist cancel
  ipersist reqc
  ipersist respc
  ipersist donec
  ipersist errc
  ipersist closingc
  ipersist lg
  imod wgsWg_init _ Hb $$ wg with Hadder
  imod start_bag (reqP V (streamKeyOf (metadata.outgoingOf (GoInterface.ok cx)))) _ reqc γreq
    (by trivial) $$ Hreqc Hreqo with #Hbreq
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit) with ⟨%γws, Hws⟩
  -- (D25) `respc`'s SPSC over every epoch of `run`, the epochs' mono list
  imod mono_list_own_alloc (GF := GF) ([] : List EpInfo) with ⟨%γep, Hep, -⟩
  imod start_sspsc (V := Loc) respc (respcE V γep) (fun _ => iprop(False)) γresp $$ Hrespc
    Hrespo with ⟨%γr, #Hsp, Hprod, Hcons⟩
  imod start_bag (errP γr γep) _ errc γerr (by trivial) $$ Herrc Herro with #Hberr
  -- (D25) the generations of `resumec`
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γend, Hgen, -⟩
  let G : WgsPrm GF := ⟨«$r0_ptr», w, cx, { Values := ∅, Deadline := none, Done_gn := γc, PDone := iprop(True) }, γc, cancel, streamKeyOf (metadata.outgoingOf (GoInterface.ok inctx)), reqc, γreq, respc, donec, γdone, errc, γerr, closingc, γcl, γws, γr, γep, γend⟩
  imod start_bag (closingP V G) _ closingc γcl (by trivial) $$ Hclc Hclo with #Hbcl
  imod alloc_broadcast_chan (E := ⊤) (closeErrPub «$r0_ptr») γdone donec $$ Hdonec Hdoneo with Hdb
  icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hdb with ⟨Hdb, #Hdbu⟩
  imod alloc_broadcast_chan (E := ⊤) (monoNatLbOwn γend 1) γrc resumec $$ Hrcc Hrco with Hrcb
  ihave #HG : isWGS V G callSl $$ []
  · unfold isWGS
    iframe #
    ipureintro; exact ⟨Hgnn, Hlgnn⟩
  wp_apply wp_fork_tok_body $$ [Hm0 Hprod Hcons Hep substreams resuming resumec closeErr Hadder Hdb Hrcb Hws
    Hgen]
  · iintro Htok
    wp_apply wp_run V G callSl m0 slice.nil resumec γrc
      $$ [Hm0 Hprod Hcons Hep substreams resuming resumec closeErr Hadder Hdb Hrcb Hws Htok Hgen] as Htok
    · iframe #
      iframe
      isplitr
      · unfold sliceOwn
        isplitr
        · iapply ownSlice_nil
        iapply ownSliceCap_nil
      unfold wgAdder
      iexact Hadder
    (try wp_auto)
    first | iexact Htok | (iframe Htok; ipureintro; simp) | (iframe Htok; ipureintro; decide)
  iapply HΦ
  iexists G, callSl
  iframe #
  ipureintro; exact ⟨⟨rfl, rfl⟩, Hmd, rfl⟩

end proof

end EtcdGrove
end Perennial
