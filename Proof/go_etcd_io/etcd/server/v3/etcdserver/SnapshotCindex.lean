/- Read the consistent index and term from the bbolt transaction that backs a merged snapshot. -/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CindexBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadConsistentIndex

@[expose] public section

noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage backend

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

private theorem snapshot_meta_range
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (sp tx : Loc) (γ : GName) (γd : DBNames) (D : Data) (q : Qp)
    (keyName : GoString) (sel : MetaCI → w64)
    (hsel : ∀ m, metaIs D m → dget D schema.metaName keyName = encMeta (sel m)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ snapAt sp γ tx γd ⊢
    metaRangeSpec ⟨go.GoType.PointerType snapshot.ty, #sp⟩ keyName sel ⊤
      (fun m => iprop(⌜metaIs D m⌝ ∗ txLive tx γd q (bbolt.TxView.ro D)))
      (fun _ => txLive tx γd q (bbolt.TxView.ro D)) := by
  iintro ⟨#Hbe, #Hsch, #Hsp⟩
  unfold metaRangeSpec
  iintro %bk %key %Φ #HM #Hkey HAU
  unfold readAU
  imod HAU with ⟨%m, ⟨%hm, Hl⟩, Hclose⟩
  ihave #Hb := mvcc.meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (hUR sp tx γ γd D q bk mvcc.metaBI key slice.nil keyName [] DFrac.discard DFrac.discard (W64 0))
    $$ [$Hsp $Hl $Hb $Hkey $Hnil] as %ks %vs ⟨Hl, -, -, Hout⟩
  have hr : ((D.lookup schema.metaName).map
        (fun b => cursorRange (bktEnts b) keyName [] (W64 0))).getD [] =
      (match (bktOf D schema.metaName).lookup keyName with
       | some v => [(keyName, v)] | none => []) := by
    change ((D.lookup schema.metaName).map _).getD [] = _
    unfold bktOf
    cases he : D.lookup schema.metaName with
    | none => simp
    | some b =>
      simp only [Option.map_some, Option.getD_some]
      rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts]
      cases b.lookup keyName <;> rfl
  irevert Hout
  rw [hr]
  iintro Hout
  have hvals := mvcc.kvsOutRd_keyVals (GF := GF) γd tx ks vs (bktOf D schema.metaName) keyName
  ihave Hobs : (|==> mvcc.keyVals (rdB γd tx) ks vs (bktOf D schema.metaName) keyName : IProp GF) $$ [Hout]
  · irevert Hout
    cases hk : (bktOf D schema.metaName).lookup keyName <;>
      simp only [hk] at hvals ⊢ <;> (iintro H; iapply hvals $$ H)
  imod Hobs with #Hkv
  have hv : (bktOf D schema.metaName).lookup keyName = encMeta (sel m) := by
    rw [← dget_eq_bktOf]; exact hsel m hm
  ihave #Hkv' := keyVals_enc hv $$ Hkv
  imod Hclose $$ [Hl] with Hret
  · dsimp only; iframe Hl; ipureintro; exact hm
  imodintro
  iapply Hret
  unfold metaValsA metaRdVals
  by_cases hz : sel m = W64 0
  · simp only [hz, ↓reduceIte]
    iexact Hkv'
  · simp only [hz, ↓reduceIte]
    icases Hkv' with ⟨%v, #Hvs, #Hv⟩
    iexists v
    iframe Hvs
    iintro !> Ha
    iapply rdB_acc γd tx v (u64Be (sel m)) q (bbolt.TxView.ro D) $$ [$Hv $Ha]

/-- Both reads return metadata from the frozen transaction, including the
zero term returned for a pre-3.5 backend with no term key. -/
theorem snapshot_read_cindex
    (hRead : schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG))
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (sp tx : Loc) (γ : GName) (γd : DBNames) (D : Data) (q : Qp) (m : MetaCI)
    (hm : metaIs D m) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        snapAt sp γ tx γd ∗ txLive tx γd q (bbolt.TxView.ro D)) -∗
      (txLive tx γd q (bbolt.TxView.ro D) -∗ Φ (PairV #m.1 #(if m.1 = W64 0 then W64 0 else m.2))) -∗
      WP (App (Val (@! schema.UnsafeReadConsistentIndex))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp))) {{ Φ }} := by
  iintro %Φ ⟨#Hbe, #Hsch, #Hsp, Hl⟩ HΦ
  let live := txLive (GF := GF) tx γd q (bbolt.TxView.ro D)
  let view := fun n : MetaCI => iprop(⌜metaIs D n⌝ ∗ live)
  iapply hRead ⟨go.GoType.PointerType snapshot.ty, #sp⟩ ⊤ view (fun _ => live) $$ %Φ []
  · iframe Hsch
    unfold metaReader
    isplitr <;> iintro !>
    · iapply snapshot_meta_range hUR hID hName hSafe sp tx γ γd D q _ _ (fun _ h => h.1) $$ [$Hbe $Hsch $Hsp]
    · iapply snapshot_meta_range hUR hID hName hSafe sp tx γ γd D q _ _ (fun _ h => h.2) $$ [$Hbe $Hsch $Hsp]
  unfold readCIAUA readAU view live
  imodintro
  iexists m
  isplitl [Hl]
  · iframe Hl; ipureintro; exact hm
  iintro ⟨-, Hl⟩
  imodintro
  by_cases hi : m.1 = W64 0
  · simp only [hi, ↓reduceIte]
    iapply HΦ $$ Hl
  · simp only [hi, ↓reduceIte]
    iframe Hl
    iintro Hl
    imodintro
    iexists m
    isplitl [Hl]
    · iframe Hl; ipureintro; exact hm
    iintro ⟨-, Hl⟩
    imodintro
    by_cases ht : m.2 = W64 0
    · simp only [ht, ↓reduceIte]
      iapply HΦ $$ Hl
    · simp only [ht, ↓reduceIte]
      iframe Hl
      iintro Hl
      iapply HΦ $$ Hl

/-- Reading the frozen image leaves the snapshot share available to the streaming reader. -/
theorem snapshot_read_cindex_open
    (hRead : schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG))
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (sp : Loc) (γ : GName) (D : Data) (q : Qp) (m : MetaCI) (hm : metaIs D m) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ snapOpenQ sp D γ q) -∗
      (snapOpenQ sp D γ q -∗ Φ (PairV #m.1 #(if m.1 = W64 0 then W64 0 else m.2))) -∗
      WP (App (Val (@! schema.UnsafeReadConsistentIndex))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp))) {{ Φ }} := by
  iintro %Φ ⟨#Hbe, #Hschema, Hsnap⟩ HΦ
  iunfold snapOpenQ at Hsnap
  icases Hsnap with ⟨%tx, %γd, #Hfields, Hshare, Htx⟩
  iapply snapshot_read_cindex hRead hUR hID hName hSafe sp tx γ γd D q m hm $$ %Φ [$Hbe $Hschema $Hfields $Htx]
  iintro Htx
  iapply HΦ
  iunfold snapOpenQ
  iexists tx, γd
  iframe Hfields Hshare Htx

end EtcdGrove
end Perennial
