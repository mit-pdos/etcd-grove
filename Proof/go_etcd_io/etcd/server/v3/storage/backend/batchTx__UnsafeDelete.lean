/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeDelete.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDelete
public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvw
public import Spec.go_etcd_io.bbolt.Bucket__Delete_kv
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Stack
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTx.UnsafeDelete.wp_proof
    (hBucket : bbolt.Tx.Bucket_kvw.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hStack : zap.Stack.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hDelete : bbolt.Bucket.Delete_kv.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeDelete.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t st bk bi key kb dk
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, Hkey⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db, %lg, %h, #Hbe, #Hlg, %Hlgn, #-, #-, #-, #-, #-, %HP⟩
  · iframe #
  unfold btW
  icases Hw with ⟨Htx, Hpend, Hwtx⟩
  unfold isBucket
  icases Hbk with ⟨%bo, %Hbo, #-, #HName, #-⟩
  subst Hbo
  wp_auto
  wp_apply HName as %ns #Hns
  wp_apply (hBucket st.tx γ.db st.C st.S ns bi.name DFrac.discard) $$ [$Hwtx $Hns] as %bkt ⟨Hwtx, -, Hbr⟩
  icases Hbr with (%Hn | ⟨%Hn, #Hwb⟩)
  · obtain ⟨Hn, Hnil⟩ := Hn
    subst Hnil
    wp_auto
    wp_apply hStringer as %f1 -
    wp_apply hStack as %f2 -
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply hFatal lg $$ [] as %v Hf
    · ipureintro; exact Hlgn
    iexfalso
    iexact Hf
  obtain ⟨Hn, Hnn⟩ := Hn
  obtain ⟨m, Hm⟩ : ∃ m, st.S.lookup bi.name = some m := Option.ne_none_iff_exists'.mp Hn
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply (hDelete st.tx γ.db st.C st.S bkt bi.name m key kb dk Hm)
    $$ [$Hwtx $Hwb $Hkey] as ⟨Hwtx, Hkey⟩
  iapply HΦ
  unfold BSess.del bktOf
  rw [Hm]
  iframe

end proof

end EtcdGrove
end Perennial
