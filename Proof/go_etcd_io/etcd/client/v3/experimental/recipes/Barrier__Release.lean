/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Barrier__Release.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Barrier__Release
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem Barrier.Release.wp_proof : Barrier.Release.spec (GF := GF) (hG := hG) := by
  intro b client key lo
  wp_start as ⟨#Hb, #Hlo⟩
  iunfold isBarrier at Hb
  icases Hb with ⟨#Hbc, #Hbx, #Hbk, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  iunfold isRecipesKV at Hkv
  icases Hkv with ⟨-, -, #HDel, -⟩
  wp_auto
  ihave #Hnil := concurrency.optsAt_nil (GF := GF)
  iunfold isEtcdDeleteKVTodo at HDel
  obtain ⟨hkk, hke⟩ := concurrency.deleteOp_fields key
  wp_apply HDel $$ %key %slice.nil %([] : List (OpFull → OpFull)) %lo [$Hnil $Hlo] as %resp %err #Hres
  · ipureintro
    refine ⟨concurrency.deleteOp_not_panics key, ?_⟩
    rw [hkk, hke]; exact concurrency.keyRangeUnder_key key key (List.prefix_refl key)
  iunfold deleteResult at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s, #Hr, %Hrr, #Hts⟩)
  · (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact Hne
  · subst Heq
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr
    isplitl
    · iapply concurrency.deleteTxn_absent $$ Hts
    ipureintro; exact Hrr.1

end proof

end recipes
end EtcdGrove
end Perennial
