/- Snapshot reads use the open bbolt read transaction even after the writer commits. -/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__UnsafeRange
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.SnapshotBboltRead
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeRange
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.snapshot.UnsafeRange.wp_proof
    (hBucket : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG))
    (hCursor : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Cursor.spec (GF := GF) (hG := hG))
    (hur : backend.unsafeRange.spec (GF := GF) (hG := hG)) :
    backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG) := by
  replace hBucket := bbolt.kvGlue_Tx__Bucket_kvr hBucket
  replace hCursor := bbolt.kvGlue_Bucket__Cursor_kvr hCursor
  intro sp tx γ γd D q bk bi key endKey kb eb dk de limit
  wp_start as ⟨#Ha, Hl, #Hb, Hk, He⟩
  iunfold snapAt at Ha
  icases Ha with ⟨%sc, %dc, %γsc, %γdc, #Htx, -⟩
  iunfold isBucket at Hb
  icases Hb with ⟨%bo, %hbo, -, #Hname, -⟩
  subst bk
  (try wp_auto)
  wp_apply Hname as %name #Hname'
  wp_apply (hBucket tx γd q D) $$ [$Hl $Hname'] as %bucket ⟨Hl, -, #Hr⟩
  icases Hr with (⟨%hm, %hn⟩ | ⟨%m, ⟨%hm, %hn⟩, #Hbkt⟩)
  · subst bucket
    wp_auto
    iapply HΦ
    iframe Hl Hk He
    simp only [hm, Option.map_none, Option.getD_none]
    unfold kvsOutRd
    iexists ([] : List GoSlice), ([] : List GoSlice)
    simp only [List.map_nil]
    repeat' first | iapply ownSlice_nil | iapply ownSliceCap_nil | iapply rdSlices_nil | isplitr
  · wp_if_destruct
    · exact absurd rfl hn
    wp_apply (hCursor tx γd q D bucket bi.name m hm) $$ [$Hbkt $Hl] as %c ⟨Hcur, Hl⟩
    wp_apply (hur tx c γd (bbolt.TxView.ro D) (bktEnts m) none q key endKey kb eb dk de limit)
      $$ [$Hcur $Hl $Hk $He] as %keys %vals ⟨-, Hl, Hk, He, Hout⟩
    iapply HΦ
    simp only [hm, Option.map_some, Option.getD_some]
    iframe

end proof
end EtcdGrove
end Perennial
