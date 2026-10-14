/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/PriorityQueue__Enqueue.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.PriorityQueue__Enqueue
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV

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

theorem PriorityQueue.Enqueue.wp_proof (hNSK : newSequentialKV.spec (GF := GF) (hG := hG)) :
    PriorityQueue.Enqueue.spec (GF := GF) (hG := hG) := by
  intro q client key val pr lo
  wp_start as ⟨#Hq, #Hlo⟩
  iunfold isPriorityQueue at Hq
  icases Hq with ⟨#Hqc, -, #Hqk, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hfmt $Hargs] as %pfx ⟨Hargs, %Hpfx⟩
  case wf =>
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    exact .cons_string _ _ (.cons_int _ _ _ (_root_.Perennial.fmt.IntArgValue.uint16 pr) .nil)
  rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at Hpfx
  simp only [List.set_cons_succ, List.set_cons_zero] at Hpfx
  have Hpfx' := _root_.Perennial.fmt.SprintfOut.str_05d_uint16 (key ++ go!"/") pr pfx Hpfx
  subst Hpfx'
  (try wp_auto)
  wp_apply hNSK kv [] _ val lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro; exact ⟨List.nil_prefix, List.nil_prefix⟩
  icases Hres with (⟨%Heq, %k, %g, %r, -, #Hr, #Hc, %Hrr⟩ | %Hne)
  · subst Heq
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists k, g, r
    iframe Hr Hc
    ipureintro; exact ⟨Hrr.1, Hrr.2.1, Hrr.2.2.1⟩
  · (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact Hne.1

end proof

end recipes
end EtcdGrove
end Perennial
