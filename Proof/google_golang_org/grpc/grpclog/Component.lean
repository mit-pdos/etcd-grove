/-
Proof of `Spec/google_golang_org/grpc/grpclog/Component.lean` over the real body (phase7-inits batch 2,
2026-11-25): the lookup in `cache` and, on a miss, the new `componentData` stored there, with the map
taken out of `grpclog`'s init-time invariant (`initInv_acc`) for the call. Lean-first.
-/
module

public import Spec.google_golang_org.grpc.grpclog.Component
public import Proof.google_golang_org.grpc.internal.Hooks

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
variable [package_sem : google_golang_org.grpc.grpclog.Assumptions]

theorem grpclog.Component.wp_proof : grpclog.Component.spec (GF := GF) (hG := hG) := by
  intro name g σ0
  wp_start as ⟨#Hinit, Hown⟩
  ihave #Hf : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.grpclog.grpclogInit (hG := hG) : IProp GF) $$ [Hinit]
  · iapply isPkgInit_access $$ Hinit
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.grpclog.grpclogInit
  icases Hf with ⟨%m, %γI, #Hcache, #Hinv⟩
  unfold EtcdGrove.ownInitLb
  icases Hown with ⟨%σ, Hg, #Hok, %Hle⟩
  iapply fupd_wp
  imod (grpcInternal.initInv_acc _ ⊤ CoPset.subseteq_top _ γI σ) $$ Hinv Hg with ⟨⟨%M, Hm⟩, Hback⟩
  imodintro
  iapply wp_fupd
  wp_func_call; wp_call
  wp_auto
  wp_apply (wp_map_lookup2 go.string (go.GoType.PointerType google_golang_org.grpc.grpclog.componentData.ty)
    m M name _) $$ Hm as Hm
  wp_auto
  cases h : M !! name with
  | some p =>
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    imod Hback $$ [Hm] with Hg
    · iexists M; iexact Hm
    imodintro
    iapply HΦ
    isplitl [Hg]
    · iexists σ; iframe Hg Hok; ipureintro; exact Hle
    ipureintro; exact ⟨p, rfl⟩
  | none =>
    simp only [Option.isSome_none, _root_.decide_false, Option.getD_none]
    wp_auto
    wp_apply (wp_mapInsert go.string m M name _) $$ Hm as Hm
    wp_auto
    imod Hback $$ [Hm] with Hg
    · iexists _; iexact Hm
    imodintro
    iapply HΦ
    isplitl [Hg]
    · iexists σ; iframe Hg Hok; ipureintro; exact Hle
    ipureintro; exact ⟨_, rfl⟩

end proof

end EtcdGrove
end Perennial
