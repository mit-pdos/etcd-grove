/-
Proof of `Spec/newClonedSnapshot.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newClonedSnapshot
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newClonedSnapshot.wp_proof
    (wp_Clone : btree.BTree.Clone.spec (GF := GF) (hG := hG)) :
    newClonedSnapshot.spec (GF := GF) (hG := hG) := by
  intro rev t m
  wp_start as ⟨Ht, #Hkvs, %Hsorted⟩
  wp_auto
  wp_apply wp_Clone $$ [$Ht] as %t2 ⟨Ht, Ht2⟩
  · ipureintro; exact kvLess_swo
  imod ownBTree_persist _ _ _ _ _ _ $$ Ht2 with #Ht2
  wp_alloc p as Hp
  ipersist Hp
  wp_auto
  iapply HΦ
  iframe Ht
  unfold snapIs
  iexists t2
  iframe Hp Ht2 Hkvs
  ipureintro; exact Hsorted

end proof

end EtcdGrove
end Perennial
