/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/unsafeForEach.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeForEach
public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvr
public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvw
public import Spec.go_etcd_io.bbolt.Bucket__ForEach_kvr
public import Spec.go_etcd_io.bbolt.Bucket__ForEach_kvw

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions]

private theorem bktEnts_bktOf_none {D : Data} {n : GoString} (h : D.lookup n = none) :
    bktEnts (bktOf D n) = [] := by
  unfold bktOf bktEnts; rw [h]; simp [GMap.toList_empty]

theorem backend.unsafeForEach.wp_proof
    (hBr : bbolt.Tx.Bucket_kvr.spec (GF := GF) (hG := hG))
    (hBw : bbolt.Tx.Bucket_kvw.spec (GF := GF) (hG := hG))
    (hFr : bbolt.Bucket.ForEach_kvr.spec (GF := GF) (hG := hG))
    (hFw : bbolt.Bucket.ForEach_kvw.spec (GF := GF) (hG := hG)) :
    backend.unsafeForEach.spec (GF := GF) (hG := hG) := by
  intro tx sd bk bi fn I E
  wp_start as ⟨Hown, #Hbk, HI, #Hf⟩
  unfold isBucket
  icases Hbk with ⟨%bo, %Hbo, #-, #HName, #-⟩
  subst Hbo
  wp_auto
  wp_apply HName as %ns #Hns
  cases sd with
  | rd q D =>
    simp only [feOwn, FeSide.data, FeSide.q] at *
    icases Hown with ⟨Hlive, #Hsnap, Hst⟩
    wp_apply (hBr tx q D ns bi.name DFrac.discard) $$ [$Hlive $Hsnap $Hst $Hns]
      as %b ⟨Hlive, Hst, -, Hbr⟩
    icases Hbr with (%Hn | ⟨%m, %Hm, #Hrb⟩)
    · obtain ⟨Hn, rfl⟩ := Hn
      wp_auto
      iapply HΦ
      iframe; iframe #
      ileft
      rw [bktEnts_bktOf_none Hn]
      iframe
      ipureintro; rfl
    obtain ⟨Hm, Hnn⟩ := Hm
    have hbm : bktOf D bi.name = m := by unfold bktOf; rw [Hm]; rfl
    rw [hbm]
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply (hFr tx b q (bktEnts m) fn I E) $$ [$Hrb $Hst $Hlive $HI $Hf] as %err ⟨Hst, Hlive, Hres⟩
    iapply HΦ
    iframe; iframe #
  | wr γ D S G =>
    simp only [feOwn, FeSide.data, FeSide.q] at *
    wp_apply (hBw tx γ D S G ns bi.name DFrac.discard) $$ [$Hown $Hns] as %b ⟨Hown, -, Hbr⟩
    icases Hbr with (%Hn | ⟨%Hn, #Hwb⟩)
    · obtain ⟨Hn, rfl⟩ := Hn
      wp_auto
      iapply HΦ
      iframe
      ileft
      rw [bktEnts_bktOf_none Hn]
      iframe
      ipureintro; rfl
    obtain ⟨Hn, Hnn⟩ := Hn
    obtain ⟨m, Hm⟩ : ∃ m, S.lookup bi.name = some m := Option.ne_none_iff_exists'.mp Hn
    have hbm : bktOf S bi.name = m := by unfold bktOf; rw [Hm]; rfl
    rw [hbm]
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply (hFw tx γ D S G b bi.name (G bi.name) m fn I E rfl Hm) $$ [$Hown $Hwb $HI $Hf]
      as %err ⟨Hown, Hres⟩
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
