/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__connectionForContext.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__connectionForContext
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

private theorem ownMap_not_nil {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] (mref : Loc) (dq : DFrac) (m : GMap K V) :
    (mref ↦${dq} m : IProp GF) ⊢ ⌜mref ≠ map.nil⌝ := by
  rw [ownMap_unseal]; unfold ownMapDef; simp only [named]
  iintro ⟨%mv, %mp, Hown, -⟩
  ihave %Hnn := heapPointsto_non_null _ _ _ $$ Hown
  ipureintro; exact Hnn

theorem Client.connectionForContext.wp_proof
    (wp_channelKeyForRequest : channelKeyForRequest.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    Client.connectionForContext.spec (GF := GF) (hG := hG) := by
  intro cl mu mref dq chs ctx o
  wp_start as ⟨Hmu, Hrw, #Hctx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave Hi : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, -, -, -, ⟨%eCNF, #Hcnf, #HcnfE⟩, -⟩
  wp_auto
  wp_apply wp_channelKeyForRequest ctx o $$ [$Hctx] as %k %Hk
  subst Hk
  wp_apply sync.RWMutex.wp_RLock mu (clientPoolInv cl mref chs) $$ [$Hsync $Hrw] as ⟨Hrlk, HP⟩
  iunfold clientPoolInv at HP
  icases HP with ⟨Hchf, Hm⟩
  ihave %Hmnn := ownMap_not_nil mref (DFrac.own sync.rfrac) chs $$ Hm
  wp_auto
  wp_apply (wp_map_lookup1 go.string go_etcd_io.etcd.client.v3.channel.ty mref chs
    (clientv3.reqChannelKey o) (DFrac.own sync.rfrac)) $$ Hm as Hm
  wp_apply sync.RWMutex.wp_RUnlock mu (clientPoolInv cl mref chs) $$ [$Hsync $Hrlk Hchf Hm] as Hrw
  · unfold clientPoolInv; iframe
  rw [decide_eq_false Hmnn]
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %err ⟨-, #Herr⟩
    · iframe #; fmt_args_ok; iright; ileft
      unfold go_etcd_io.etcd.cache.v3.errorStringSpec fmt.stringMethodSpec at *
      iexact HcnfE
    iapply HΦ
    iframe Hmu Hrw
    have hconn : poolConnFor chs o = null := Hif
    simp only [hconn, ↓reduceIte]
    isplitr
    · ipureintro; trivial
    iexists err
    isplitr
    · ipureintro; rfl
    unfold go_etcd_io.etcd.cache.v3.errorStringSpec fmt.stringMethodSpec at *
    iexact Herr
  · iapply HΦ
    iframe Hmu Hrw
    have hconn : poolConnFor chs o ≠ null := Hif
    simp only [hconn, ↓reduceIte]
    ipureintro; trivial

theorem Client.connectionForContext_closed.wp_proof
    (wp_channelKeyForRequest : channelKeyForRequest.spec (GF := GF) (hG := hG))
    (wp_closedErr : Client.connectionPoolClosedError.spec (GF := GF) (hG := hG)) :
    Client.connectionForContext_closed.spec (GF := GF) (hG := hG) := by
  intro cl mu dq0 dq1 ci cd st ctx o
  wp_start as ⟨Hmu, Hrw, Hcctx, #Hce, Hst, #Hctx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_channelKeyForRequest ctx o $$ [$Hctx] as %k %Hk
  subst Hk
  wp_apply sync.RWMutex.wp_RLock mu (clientPoolClosedInv cl) $$ [$Hsync $Hrw] as ⟨Hrlk, HP⟩
  iunfold clientPoolClosedInv at HP
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock mu (clientPoolClosedInv cl) $$ [$Hsync $Hrlk HP] as Hrw
  · unfold clientPoolClosedInv; iexact HP
  wp_apply wp_closedErr cl dq1 ci cd st $$ [$Hcctx $Hce $Hst] as %err ⟨Hcctx, %Herr, #Hse, Hcell⟩
  iapply HΦ
  iframe Hmu Hrw Hcctx Hse Hcell
  ipureintro
  exact ⟨rfl, Herr.1, Herr.2⟩

end proof

end EtcdGrove
end Perennial
