/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewStore.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewStore
public import Spec.k8s_io.client_go.tools.cache.NewThreadSafeStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem NewStore.wp_proof
    (wp_NewTS : NewThreadSafeStore.spec (GF := GF) (hG := hG)) :
    NewStore.spec (GF := GF) (hG := hG) := by
  intro OK Fam kf opts dq
  wp_start as Hopts
  ihave %Hol := ownSlice_len $$ Hopts
  wp_auto
  have hlen : opts.len = W64 0 := by simp at Hol; word
  ihave HI : (i_ptr ↦ W64 0 : IProp GF) $$ [i]
  · iexact i
  wp_for HI
  wp_if_destruct
  · exfalso; rw [hlen] at Hif; exact absurd Hif (by decide)
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoFunc) ([] : List GoFunc)
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := GoFunc) go.string IndexFunc.ty as %im Him
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := Loc) go.string
    index.ty as %ip Hip
  (try wp_auto)
  wp_apply (wp_NewTS OK Fam im ip ∅ ∅ _) $$ [$Him $Hip $Htsl]
  · unfold fnsOk
    isplitr
    · ipureintro; intro n; simp [GMap.fmap_empty, GMap.mem_iff, GMap.lookup_empty]
    iapply BigSepM.bigSepM_empty.2; itrivial
  iintro %ts ⟨%γ, #Hts, Hst, Hrds⟩
  iStructNamed «$r0»
  ipersist keyFunc
  ipersist transformer
  wp_pures
  wp_load
  wp_pures
  wp_store
  ipersist cacheStorage
  wp_auto
  iapply HΦ
  iexists ts, γ
  iframe
  iunfold isCache
  iframe #

end proof

end cache
end EtcdGrove
end Perennial
