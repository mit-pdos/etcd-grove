/-
Proof of the spec of the same name (the mvcc store's index-driven compaction job,
etcd-io/etcd#21951). The hypotheses are the callees' specs, in the order of
`etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__scheduleCompactionIndexDriven
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Compact
public import Spec.time.Since
public import Spec.sort.Slice
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Revision__GreaterThan
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BucketKeyToBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.String
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.time.Time__Unix
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Errorf
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A `BucketKey` points-to as its fields. -/
theorem mvcc.bk_split (l : Loc) (b : BucketKey) (dq : DFrac) :
    (l ↦{dq} b : IProp GF) ⊢
      l.[BucketKey, go!"Revision"] ↦{dq} b.Revision' ∗ l.[BucketKey, go!"tombstone"] ↦{dq} b.tombstone' ∗
        ⌜l ≠ null⌝ := by
  iintro H
  ihave %Hn := typedPointsto_not_null _ _ _ $$ H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe Revision tombstone
  ipureintro; exact Hn

/-- The fields of a `BucketKey` as its points-to. -/
theorem mvcc.bk_combine (l : Loc) (b : BucketKey) (dq : DFrac) (h : l ≠ null) :
    l.[BucketKey, go!"Revision"] ↦{dq} b.Revision' ∗ l.[BucketKey, go!"tombstone"] ↦{dq} b.tombstone' ⊢
      (l ↦{dq} b : IProp GF) := by
  iintro ⟨Hr, Ht⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hr Ht

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mvcc.store.scheduleCompactionIndexDriven.wp_proof
    (h0 : mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG))
    (h1 : time.Since.spec (GF := GF) (hG := hG))
    (h2 : sort.Slice.spec (GF := GF) (hG := hG))
    (h3 : mvcc.Revision.GreaterThan.spec (GF := GF) (hG := hG))
    (h4 : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (h5 : mvcc.BucketKeyToBytes.spec (GF := GF) (hG := hG))
    (h6 : mvcc.UnsafeSetFinishedCompact.spec (GF := GF) (hG := hG))
    (h7 : zap.Int64.spec (GF := GF) (hG := hG))
    (h8 : zap.Duration.spec (GF := GF) (hG := hG))
    (h9 : zap.Int'.spec (GF := GF) (hG := hG))
    (h10 : zap.String.spec (GF := GF) (hG := hG))
    (h11 : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (h12 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h13 : time.Time.Unix.spec (GF := GF) (hG := hG)) :
    mvcc.store.scheduleCompactionIndexDriven.spec (GF := GF) (hG := hG) := by
  intro s γ rev prev
  wp_start as ⟨#Hjob, Htok⟩
  iunfold mvcc.compactJobPre at Hjob
  icases Hjob with ⟨#Hs, #Hstop, %Hcmp, #Hlb, %log, #Hcert, %Hrev'⟩
  have Hrev : 0 ≤ sint.Z rev ∧ sint.Z rev < log.length := ⟨Hrev'.1, Hrev'.2.1⟩
  have Hnd : mvcc.NoDelPutAt log (sint.Z rev) := Hrev'.2.2
  ihave #Hs0 := Hs
  iunfold mvcc.isStore at Hs0
  iNamed Hs0
  ihave #Hbk' := mvcc.isKeyBackendG_cmp _ s γ _ _ _ Hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, #HBT, #HForce, #HSize, #HSizeU, -⟩
  subst Hbi
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%hIdx, #HIdxG, #HIdx⟩, ⟨%hPause, #HPauseG, #HPause⟩, ⟨%hTot, #HTotG, #HTot⟩,
    ⟨%cKeys, #HKeysG, #HKeys⟩, ⟨%gLast, #HLastG, #HLast⟩⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold mvcc.compactTok at Htok
  icases Htok with ⟨%c', %hc', Htok⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply time.wp_Now as %t0 -
  (try wp_auto)
  wp_apply h0 ti γ.idx rev log c' $$ [$Htok] as %keep %del ⟨Htok, -, %D, Hdel, %HD⟩
  · iframe #; ipureintro; exact ⟨hc', Hrev.1, Hrev.2⟩
  (try wp_auto)
  iunfold histSpec at HIdx HPause HTot
  iunfold counterSpec at HKeys
  icases HKeys with ⟨-, #HKeysAdd⟩
  iunfold gaugeSetSpec at HLast
  wp_apply h1 as %d1 -
  (try wp_auto)
  wp_apply HIdx
  (try wp_auto)
  wp_apply time.wp_Now as %t1 -
  (try wp_auto)
  wp_apply (wp_map_len_lt (K := BucketKey) (V := Unit) del D (DFrac.own 1)) $$ [$Hdel] as ⟨Hdel, %Hsz⟩
  wp_apply (wp_slice_make3 (V := BucketKey) (W64 0) (W64 (GMap.size D : Int)) (by word))
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  (try wp_auto)
  rw [List.replicate_zero]
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List BucketKey) (i : Int) => iprop(∃ (sl : GoSlice) (b : BucketKey),
      "dels" ∷ dels_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* keys.take i.toNat ∗
      "Hcap" ∷ ownSliceCap BucketKey sl (DFrac.own 1) ∗ "bk" ∷ bk_ptr ↦ b ∗ "%Hi" ∷ ⌜0 ≤ i⌝)) $$ Hdel
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [dels Hsl0 Hcap0 bk]
  · iexists sl0, _
    simp only [named]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := BucketKey) [key]
    isplitr
    · ipureintro; rfl
    iintro %ksl ⟨Hksl, -⟩
    wp_apply (wp_slice_append (V := BucketKey) sl (keys.take i.toNat) _ [key] (DFrac.own 1))
      $$ [$Hsl $Hcap $Hksl] as %sl' ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl', key
    simp only [named]
    iframe
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
    simp only [Option.toList_some]
    iframe
    ipureintro; omega
  iintro HP Hdel
  iNamed HP
  rw [show ((GMap.size D : Nat) : Int).toNat = keys.length by omega, List.take_length]
  wp_auto
  ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  wp_apply (h2 BucketKey BucketKey.ty sl keys _ iprop(dels_ptr ↦ sl)) $$ [$Hsl $dels]
    as ⟨dels, %ys, Hsl, %Hperm⟩
  · iframe #
    imodintro
    iintro %ys %i %j %Hij %Φ' !> ⟨dels, Hsl⟩ HΦ'
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    have Hyl : ys.length = keys.length := Hij.1.length_eq
    wp_auto
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
      refine ⟨Hij.2.1, ?_⟩; have := Hij.2.2.1; word
    simp only [Hbi, _root_.and_self, ↓reduceIte]
    obtain ⟨a, Ha⟩ : ∃ a, ys[(sint.Z i).toNat]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by have := Hij.2.2.1; omega)⟩
    icases ownSlice_elem_acc (sint.Z i) a sl _ ys Hij.2.1 Ha $$ Hsl with ⟨Ha, Hback⟩
    icases mvcc.bk_split _ _ _ $$ Ha with ⟨HaR, HaT, %Hann⟩
    wp_auto
    ihave Ha := mvcc.bk_combine _ a _ Hann $$ [HaR HaT]
    · iframe
    ispecialize Hback $$ %a Ha
    rw [mvcc.set_same Ha]
    have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
      refine ⟨Hij.2.2.2.1, ?_⟩; have := Hij.2.2.2.2; word
    simp only [Hbj, _root_.and_self, ↓reduceIte]
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType Revision.ty) (m := go!"GreaterThan")]
    wp_call
    obtain ⟨b, Hb⟩ : ∃ b, ys[(sint.Z j).toNat]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by have := Hij.2.2.2.2; omega)⟩
    icases ownSlice_elem_acc (sint.Z j) b sl _ ys Hij.2.2.2.1 Hb $$ Hback with ⟨Hb, Hback⟩
    icases mvcc.bk_split _ _ _ $$ Hb with ⟨HbR, HbT, %Hbnn⟩
    wp_auto
    ihave Hb := mvcc.bk_combine _ b _ Hbnn $$ [HbR HbT]
    · iframe
    ispecialize Hback $$ %b Hb
    rw [mvcc.set_same Hb]
    wp_apply h3
    iapply HΦ'
    iframe
  (try wp_auto)
  ihave #HcfgS := Hcfg
  iStructNamedSuffix HcfgS "C"
  (try wp_auto)
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩⟩
  wp_apply HBT as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #HbtS, -⟩
  ihave #HbtS0 := HbtS
  iunfold mvcc.batchTxSpecG at HbtS0
  icases HbtS0 with ⟨-, -, #HUnl0, -, -, #HLockOut, #HDel, -, -⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HLockOut $$ []
  · iframe #
  inext
  iintro ⟨Hlocked, HW, HP, -⟩
  (try wp_auto)
  wp_apply time.wp_Now as %ts -
  (try wp_auto)
  ihave %Hysl := ownSlice_len _ _ _ $$ Hsl
  have Hyd : ∀ y ∈ ys, mvcc.DelOk log (sint.Z rev) (mvcc.revOf y.Revision') y.tombstone' :=
    fun y hy => HD y ((Hkset y).1 (Hperm.mem_iff.1 hy))
  ihave IH : iprop(∃ (n kc : w64) (b : BucketKey) (bt : GoInterfaceOk) (Lk : mvcc.Puts → IProp GF)
      (st : time.Time),
      "i" ∷ i_ptr ↦ n ∗ "bk" ∷ bk_ptr ↦ b ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "tx" ∷ tx_ptr ↦ GoInterface.ok bt ∗ "start" ∷ start_ptr ↦ st ∗
      "#HbtS" ∷ mvcc.batchTxSpecG bt (mvcc.bucketView γ) iprop(True) iprop(True) mvcc.noPutCond
        (mvcc.delKey γ) (mvcc.writerRes s γ) Dep True Lk Ph fh ∗
      "Hlocked" ∷ Lk [] ∗ "HW" ∷ mvcc.writerRes s γ ∗ "HP" ∷ Ph ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ys.length⌝) $$ [i bk keyCompactions tx start Hlocked HW HP]
  · iexists W64 0, _, _, bt, Locked, _
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ys.length := by rw [Hysl.1]; word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨y, Hy⟩ : ∃ y, ys[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z n) ys (DFrac.own 1) y Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hy
    (try wp_auto)
    wp_apply h4 as %rb ⟨Hrb, Hrbc, %Hrbcap⟩
    wp_apply (h5 y rb _ (Or.inl (by simp))) $$ [$Hrb $Hrbc] as %kb ⟨Hkb, Hkbc⟩
    (try wp_auto)
    have HyD := Hyd y (List.mem_of_getElem? Hy)
    have Hkey : mvcc.bucketKeyBytes (mvcc.revOf y.Revision') y.tombstone'
        ((List.replicate 17 (W8 0)).drop 17) = mvcc.revBytes (mvcc.revOf y.Revision') y.tombstone' := by
      cases y.tombstone'
      · rw [mvcc.bucketKeyBytes_false]; simp
      · rw [mvcc.bucketKeyBytes_true]
    rw [Hkey]
    ihave #Hdk : mvcc.delKey γ (mvcc.revBytes (mvcc.revOf y.Revision') y.tombstone') $$ []
    · iunfold mvcc.delKey
      iexists (sint.Z rev), log
      iframe Hlb Hcert
      ipureintro
      exact ⟨by omega, HyD.keyDel Hrev.2, Hnd⟩
    ihave #HbtS2 := HbtS
    iunfold mvcc.batchTxSpecG at HbtS2
    icases HbtS2 with ⟨-, -, #HUnl2, -, -, -, #HDel2, -, -⟩
    ihave #HDel3 := HDel2 $$ []
    · ipureintro; trivial
    wp_bind (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #kb))
    iapply HDel3 $$ [Hlocked Hkb]
    · iframe Hlocked Hkb; iframe #
    inext
    iintro ⟨Hlocked, Hkb⟩
    (try wp_auto)
    rw [ite_eq_right (show ¬ sint.Z scfg.CompactionBatchLimit' = 0 by omega)]
    wp_auto
    wp_if_destruct
    rotate_left
    · -- not a full batch: on
      wp_for_post
      iframe
      iexists n + W64 1, _, y, bt, Lk, st
      simp only [named]
      iframe
      iframe #
      ipureintro
      constructor <;> word
    -- a full batch: committed, then the next one after the sleep, unless the store stops
    wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
    iapply HUnl2 $$ [Hlocked HW HP]
    · iframe Hlocked HW HP
    inext
    iintro -
    (try wp_auto)
    wp_apply HForce $$ []
    · isplitl [] <;> itrivial
    (try wp_auto)
    wp_apply h1 as %d5 -
    (try wp_auto)
    wp_apply HPause
    (try wp_auto)
    wp_apply +noauto time.wp_After as %tch %γt #Hbag
    wp_auto_lc 2
    ihave #Hstop0 := Hstop
    iunfold mvcc.storeStop at Hstop0
    icases Hstop0 with ⟨%stc, #Hstc, #Hstcc⟩
    iunfold mvcc.isStopChan at Hstcc
    icases Hstcc with ⟨%γs, #Hstcc⟩
    icombine Hstopc Hstc gives %Hsteq
    subst Hsteq
    ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
      inext
      iintro %tm' -
      wp_auto
      wp_apply HBT as %bt' #Hbt'
      (try wp_auto)
      iunfold mvcc.isBatchTxG at Hbt'
      icases Hbt' with ⟨%Lk', %LkO', #HbtS', -⟩
      ihave #HbtS3 := HbtS'
      iunfold mvcc.batchTxSpecG at HbtS3
      icases HbtS3 with ⟨-, -, -, -, -, #HLockOut', -, -, -⟩
      wp_bind (App (Val #(methods bt'.ty _ bt'.v)) (Val #()))
      iapply HLockOut' $$ []
      · iframe #
      inext
      iintro ⟨Hlocked, HW, HP, -⟩
      (try wp_auto)
      wp_apply time.wp_Now as %ts' -
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _, y, bt', Lk', ts'
      simp only [named]
      iframe
      iframe #
      ipureintro
      constructor <;> word
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sstop, γs
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hstcc
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hstcc
      iintro ⟨-, #Hdone⟩
      wp_auto
      wp_apply mvcc.wp_Errorf_errorfIs $$ [] as %err #Herr
      · iframe #; iapply ownSlice_nil
      (try wp_auto)
      wp_for_post
      wp_apply time.wp_Now as %tn -
      (try wp_auto)
      wp_apply h13 as %un -
      (try wp_auto)
      wp_apply HLast
      (try wp_auto)
      wp_apply HKeysAdd
      (try wp_auto)
      wp_apply h1 as %d4 -
      (try wp_auto)
      wp_apply HTot
      (try wp_auto)
      iapply HΦ
      iframe Htok
      iright
      iframe Herr
      iunfold mvcc.storeStopped
      iexists sstop, γs
      iframe Hstc Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- the loop's end: `finishedCompactRev = rev` in the last batch, the compaction finished
  ihave #HbtS1 := HbtS
  iunfold mvcc.batchTxSpecG at HbtS1
  icases HbtS1 with ⟨-, -, #HUnl1, -, -, -, -, -, -⟩
  (try wp_auto)
  wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
    (Val #(GoInterface.ok bt))) (Val #rev))
  iapply (h6 bt (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes s γ) Dep Lk Ph fh [] rev
    Hrev.1) $$ [Hlocked]
  · iframe Hlocked; iframe #
    iunfold mvcc.batchTxSpec; iexact HbtS
  inext
  iintro Hlocked
  (try wp_auto)
  iunfold mvcc.writerRes at HW
  icases HW with ⟨%ilog, %ntok, HW⟩
  iNamedSuffix HW "W"
  iunfold mvcc.compactRes at HcresW
  icases HcresW with ⟨%sched, %fin, %nf, Hmeta, Hfin, %Hnf⟩
  iunfold mvcc.metaCompact at Hmeta
  imod ghostVar_update (sched, some rev) γ.cmeta _ $$ Hmeta with Hmeta
  imod mono_nat_own_update (max nf (mvcc.crevN (sint.Z rev))) (Nat.le_max_left _ _) $$ Hfin
    with ⟨Hfin, #Hflb⟩
  ihave #Hdone : mvcc.compactedAt γ (sint.Z rev) $$ []
  · iunfold mvcc.compactedAt
    iapply monoNatLbOwn_le _ (Nat.le_max_right _ _) $$ Hflb
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnl1 $$ [Hlocked HtoksW HwW HclogW HcurW HbvW Hmeta Hfin HP HlrdW]
  · iframe Hlocked HP
    iunfold mvcc.writerRes
    iexists ilog, ntok
    simp only [named]
    iframe
    iframe #
    isplitr
    · ipureintro; exact HbudgetW
    isplitr
    · ipureintro; exact HneW
    iunfold mvcc.compactRes
    iexists sched, some rev, _
    iunfold mvcc.metaCompact
    iframe
    ipureintro
    exact Nat.le_max_right _ _
  inext
  iintro -
  (try wp_auto)
  wp_apply h1 as %d2 -
  (try wp_auto)
  wp_apply HPause
  (try wp_auto)
  wp_apply HSize as %sz -
  wp_apply HSizeU as %szu -
  (try wp_auto)
  wp_apply h7 as %f0 -
  (try wp_auto)
  wp_apply h1 as %d3 -
  (try wp_auto)
  wp_apply h8 as %f1 -
  (try wp_auto)
  wp_apply h9 as %f2 -
  (try wp_auto)
  wp_apply h7 as %f3 -
  (try wp_auto)
  wp_apply h11 as %str4 -
  (try wp_auto)
  wp_apply h10 as %f4 -
  (try wp_auto)
  wp_apply h7 as %f5 -
  (try wp_auto)
  wp_apply h11 as %str6 -
  (try wp_auto)
  wp_apply h10 as %f6 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3, f4, f5, f6]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply h12 lg _ _ $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply time.wp_Now as %tn -
  (try wp_auto)
  wp_apply h13 as %un -
  (try wp_auto)
  wp_apply HLast
  (try wp_auto)
  wp_apply HKeysAdd
  (try wp_auto)
  wp_apply h1 as %d4 -
  (try wp_auto)
  wp_apply HTot
  (try wp_auto)
  iapply HΦ
  iframe Htok
  ileft
  iframe Hdone
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
