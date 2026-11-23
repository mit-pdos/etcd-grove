/-
Proof of `Spec/go_etcd_io/etcd/api/v3/mvccpb/Event_EventType__StringPtr.lean`, over the trusted model of
protoc-gen-go's `Event_EventType.String` (`TrustedCode/go_etcd_io/etcd/api/v3/mvccpb.lean`,
etcd-grove#39, 2026-11-23): the lookup in `Event_EventType_name`, which `mvccpb`'s package fact holds
read-only (`mvccpb.eventTypeNames`), else `strconv.Itoa`; the call through the pointer reads `*l`
(goose's `ptr_String_unfold`). (Until 2026-11-23 a trust-boundary axiom, T5-f over the pointer
receiver, approved by the user 2026-11-15 via etcd-grove-81, `notes/k8s-7f5a-draft.md` §11.5.)
-/
module

public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event_EventType__StringPtr
public import Spec.strconv.Itoa

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.mvccpb.Assumptions]

theorem mvccpb.Event_EventType.StringPtr.wp_proof
    (hItoa : strconv.Itoa.spec (GF := GF) (hG := hG)) :
    mvccpb.Event_EventType.StringPtr.spec (GF := GF) (hG := hG) := by
  intro l t
  wp_start as #Hl
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave Hfact : (go_etcd_io.etcd.cache.v3.mvccpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hfact with ⟨%m, #Hg, #Hm⟩
  -- the trusted model names the translation's type and table by their names
  have hty : (go_etcd_io.etcd.api.v3.mvccpb.model.Event_EventType : go.GoType) =
      go_etcd_io.etcd.api.v3.mvccpb.Event_EventType.ty := by with_unfolding_all rfl
  have hnm : (go_etcd_io.etcd.api.v3.mvccpb.model.Event_EventType_name : GoString) =
      go_etcd_io.etcd.api.v3.mvccpb.Event_EventType_name := by with_unfolding_all rfl
  wp_auto
  -- the value method's resolution (`go.int32` is not an interface: a local instance, as in
  -- `kvdurable/getEntry.lean`)
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_auto
  wp_method_call
  wp_call
  unfold go_etcd_io.etcd.api.v3.mvccpb.Event_EventType.String.impl
  simp only [hty, hnm]
  wp_auto
  -- the table kept opaque (`wp_auto`'s `simp` would compute its lookups)
  generalize go_etcd_io.etcd.cache.v3.mvccpb.eventTypeNames = M
  cases hk : M !! t with
  | some s =>
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string m M t DFrac.discard)
      $$ Hm as -
    rw [hk]
    simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  | none =>
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string m M t DFrac.discard)
      $$ Hm as -
    rw [hk]
    simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    wp_auto
    wp_apply hItoa $$ Hsc as %str %Hstr
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
