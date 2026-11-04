/-
`DB.allocate` (U4c, `notes/bbolt-proof-plan.md`): `db.allocate(txid, count)` by the live writer:
a zeroed buffer (the page pool's for one page, else `make`), its header's overflow set; the
freelist's run (`Allocate`, a `store_alloc` step), or the high-water mark (`db.rwtx.meta.pgid`,
raised by `count`), after a remap (`DB.mmap`) when the new mark's page is past the mapping; with
`MaxSize` set, `ErrMaxSizeReached` past it.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Remap
public import Proof.go_etcd_io.bbolt.Mmap.MmapSize
public import Proof.go_etcd_io.bbolt.Mmap.GrowSize
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Mmap.FileSize
public import Proof.go_etcd_io.bbolt.Mmap.AllocPage
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Allocate
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetId
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetOverflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetPgid
public import Perennial.Spec.sync.Pool__Get
public import Spec.fmt.Errorf
public import Proof.go_etcd_io.bbolt.Read.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- **`db.allocate(txid, count)`'s success** from the records `X` and writer side `w`: the
records `Xr` (`X`, or after a remap `X` dereferenced and re-based) with the high-water mark `hwm`,
the writer side `w'`, the page `id`; from the freelist (no remap, the mark kept), or at the mark
(raised by `count`; no remap and nothing else changed, or a remap, `wdbRemap`). The mark's pages
stay inside the mapping. -/
def dbAllocRes [GooseExts] (X Xr : WX) (w w' : WDb) (txid : w64) (count : Nat) (id hwm : w64) :
    Prop :=
  w'.C = w.C ∧ hwm.toNat * 4096 ≤ mapLen w'.ms ∧
  ((Xr = X ∧ w.fl.canAlloc id count ∧ w' = w.withFl (w.fl.alloc txid id count) ∧
      hwm = X.t.mv.pgid') ∨
   (id = X.t.mv.pgid' ∧ id.toNat + count < 2 ^ 62 ∧ hwm = id + W64 (count : Int) ∧
     ((Xr = X ∧ w' = w) ∨ (∃ Xd b, derefRel X Xd ∧ Xr = Xd.rebase b ∧ wdbRemap w w'))))

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.allocate(txid, count)` by the live writer `tx`** (`txid` its id, `w.wtxid`; the
high-water mark's pages inside the mapping): a buffer `p` holding the fresh page `id`
(`allocBuf`), the records with the new mark (`dbAllocRes`); on an error (`fmtErrorOk`), nothing
changed (the freelist had no run; `MaxSize`; a remap that failed before unmapping), or the mapping
lost (the records dereferenced and re-based, `wtxLost`, `wdbLost`). -/
abbrev DB.allocate.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (txid count : w64),
  txid = w.wtxid → 0 < sint.Z count → sint.nat count * 4096 < 2 ^ 62 →
  X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"allocate")) (Val #txid))
      (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = interface.nil⌝ ∗ ∃ (Xr : WX) (w' : WDb) (id hwm : w64),
        wtxW K tx r m (Xr.withHwm hwm) ∗ wdbW K tx Xr.v w' ∗
        bytesPointsto p (DFrac.own 1) (allocBuf id (sint.nat count)) ∗
        ⌜p ≠ null ∧ dbAllocRes X Xr w w' txid (sint.nat count) id hwm⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW K tx X.v w) ∨
         (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost K tx X'.v w' ∗
           ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝))) }}

instance dbFixed_persistent' (db sp : Loc) : Persistent (dbFixed (GF := GF) db sp) := by
  unfold dbFixed dbLogger; infer_instance

/-- The writer's database core, kept. -/
theorem wtxW_core (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ wtxW K tx r m X := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hp, #H, Hr⟩, Hc⟩
  isplitr
  · iexact H
  iframe; iframe #

/-- `allocate`'s fixed fields of the database (`dbFixed`). -/
theorem BC.core_allocFields (K : BC) :
    K.core (GF := GF) ⊢ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      K.db.[DB, go!"AllocSize"] ↦□ W64 0x1000000 ∗ (∃ x : w64, K.db.[DB, go!"MaxSize"] ↦□ x) ∗
      (∃ lg, K.db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg) ∗ dbFixed K.db K.sp ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ⌜K.db ≠ null⌝ ∗
      inv (pagesN K.N) (pagesInv (GF := GF) K.B K.p) := by
  unfold BC.core isBoltCoreP
  iintro ⟨-, -, %Ht, #Hpkg, -, #Hfix, -, -, -, #Hpi, -⟩
  iframe #
  isplitr
  · iclear Hpkg Hpi
    unfold dbFixed
    icases Hfix with ⟨#H, -⟩
    iexact H
  isplitr
  · iclear Hpkg Hpi
    unfold dbFixed
    icases Hfix with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  isplitr
  · iclear Hpkg Hpi
    unfold dbFixed
    icases Hfix with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  isplitr
  · iclear Hpkg Hpi
    unfold dbFixed dbLogger
    icases Hfix with ⟨-, -, #H, -⟩
    iexact H
  ipureintro; exact Ht.2.1

/-- The mapping's length is at most `maxMapSize` (`mapFields`' pure part). -/
theorem mapFields_len (db : Loc) (dq : DFrac) (ms : MapSt) :
    mapFields (GF := GF) db dq ms ⊢ ⌜mapLen ms ≤ 0xFFFFFFFFFFFF⌝ := by
  rcases ms with _ | ⟨b, l⟩
  · iintro -; ipureintro; simp [mapLen]
  · simp only [mapFields, mapLen]
    iintro ⟨-, -, -, -, %H⟩
    ipureintro; exact H.1

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem hwm_fit (a n L : Nat) (h : ¬ L ≤ (a + n + 1) * 4096) : (a + n) * 4096 ≤ L := by omega

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem hwm_fit' (a n L : Nat) (h : (a + n + 1) * 4096 ≤ L) : (a + n) * 4096 ≤ L :=
  Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) h

/-- `wdbW` unfolded (as the proof's goals have it). -/
theorem wdbW_unf (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ iprop(wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C) w ∗
      ⌜wdbOK w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝) := by
  unfold wdbW; exact .rfl

/-- The view of `Xd.rebase b` as `wp_auto` leaves it. -/
theorem wdbLost_rebase (K : BC) (tx : Loc) (Xd : WX) (b : Loc) (w : WDb) :
    wdbLost (GF := GF) K tx { base := b, txid := Xd.v.txid, pages := Xd.v.pages, root := Xd.v.root } w ⊢
      wdbLost K tx (Xd.rebase b).v w := .rfl

/-- `DB.mmap`'s error state as `DB.allocate`'s. -/
theorem mmapErr_state (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) :
    ((wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w) ∨
      (∃ (Xd : WX) (b : Loc) (w' : WDb), wtxLost K tx r m (Xd.rebase b) ∗
        wdbLost K tx (Xd.rebase b).v w' ∗ ⌜derefRel X Xd ∧ w'.C = w.C ∧ w'.fl = w.fl⌝)) ⊢
    ((wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w) ∨
      (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost K tx X'.v w' ∗
        ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝)) := by
  iintro (H | ⟨%Xd, %b, %w', H1, H2, %h⟩)
  · ileft; iexact H
  · iright
    iexists Xd.rebase b, w'
    iframe
    ipureintro
    exact ⟨⟨Xd, b, h.1, rfl⟩, h.2⟩

theorem DB.allocate.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hMmapSize : DB.mmapSize.spec (GF := GF) (hG := hG))
    (hGrowSize : DB.growSize.spec (GF := GF) (hG := hG))
    (hMmap : DB.mmap.spec (GF := GF) (hG := hG))
    (hAlloc : internal.freelist.Interface.Allocate.spec (GF := GF) (hG := hG))
    (hSetId : internal.common.Page.SetId.spec (GF := GF) (hG := hG))
    (hSetOv : internal.common.Page.SetOverflow.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hSetPgid : internal.common.Meta.SetPgid.spec (GF := GF) (hG := hG))
    (hGet : sync.Pool.Get.spec (GF := GF) (hG := hG))
    (hErrMax : errMaxSizeOk (GF := GF) (hG := hG))
    (hPool : pagePoolNew (GF := GF) (hG := hG)) :
    DB.allocate.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w txid count htxid hc0 hc hhwm hdp hlf hlr
  subst htxid
  unfold errMaxSizeOk at hErrMax
  wp_start as ⟨Hw, Hdb⟩
  icases wtxW_core K tx r m X $$ Hw with ⟨#Hcore, Hw⟩
  icases BC.core_allocFields K $$ Hcore with ⟨#Hps, #Has, ⟨%mx, #Hmx⟩, ⟨%lg, #Hlg, #Hlgok⟩,
    #Hfix, #Hpkg, %Hdb, #Hpinv⟩
  icases hPool K.db K.sp $$ Hfix with ⟨%f, #Hpool, %Hf⟩
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ s : GoSlice, buf_ptr ↦ s ∗
    s ↦* List.replicate (sint.nat count * 4096) (W8 0) ∗ db_ptr ↦ K.db ∗ count_ptr ↦ count))) $$ [buf db count]
  · by_cases hc1 : count = W64 1
    · rw [decide_eq_true hc1]
      wp_auto
      wp_apply hGet $$ [Hpool]
      · iframe #
      iintro %x Hx
      icases Hx with (Hx | %hx)
      rotate_left
      · exact absurd hx.1 Hf
      unfold pageBuf
      icases Hx with ⟨%s, %hx, Hs⟩
      subst hx
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists s
      have h1 : sint.nat count = 1 := by rw [hc1]; word
      rw [h1, Nat.one_mul]
      iframe Hs
      isplitl [buf]
      · iexact buf
      isplitl [db]
      · iexact db
      · iexact count
    · rw [decide_eq_false hc1]
      wp_auto
      have hmul : sint.Z (count * W64 4096) = ((sint.nat count * 4096 : Nat) : Int) := by
        simp only [sint.nat] at hc ⊢; word
      wp_apply wp_slice_make2 (V := w8) $$ [] as %val ⟨Hv, -⟩
      · ipureintro; rw [hmul]; omega
      isplitr
      · ipureintro; rfl
      iexists val
      rw [show sint.nat (count * W64 4096) = sint.nat count * 4096 by simp only [sint.nat, hmul]; omega]
      rw [show (zero_val w8 : w8) = W8 0 from rfl]
      iframe
  iintro %v ⟨%hv, %s, buf, Hs, db, count⟩
  subst hv
  wp_auto
  have hcz : sint.nat count = (sint.Z count).toNat := rfl
  have hcn : 1 ≤ sint.nat count := by omega
  have hn16 : 16 ≤ sint.nat count * 4096 := by omega
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  icases zeroBuf_page s _ _ hn16 $$ Hs with ⟨%Hsp, Hh, Hz⟩
  have hslen : 0 < sint.Z s.len := by
    have h1 := Hsl.1; simp only [List.length_replicate] at h1
    have h2 : sint.nat s.len = (sint.Z s.len).toNat := rfl
    omega
  simp only [show sint.Z (W64 0) = 0 from rfl, hslen, Int.le_refl, and_self, ↓reduceIte]
  rw [sliceIndexRef_byte _ _ Hsp (Int.le_refl _), loc_add_0]
  wp_auto
  wp_apply hSetOv $$ [Hh] as Hh
  · iframe
  unfold wdbW wdbLive wdbCoreG
  icases Hdb with ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath, Hdsz,
    Hmf, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok⟩
  wp_auto
  wp_apply hAlloc w.fli w.fl w.wtxid count hc0 $$ [Hflo] as %rid Hflo
  · iframe
  try wp_auto
  wp_apply hSetId $$ [Hh] as Hh
  · iframe
  try wp_auto
  wp_apply hId $$ [Hh] as Hh
  · iframe
  try wp_auto
  simp only
  by_cases hr0 : rid = W64 0
  · subst hr0
    icases Hflo with (⟨-, Hflo⟩ | ⟨%h0, -⟩)
    rotate_left
    · exact absurd rfl h0.1
    rw [decide_eq_true rfl]
    ihave %Hml := mapFields_len _ _ _ $$ Hmf
    icases wtxW_txFields_acc K tx r m X $$ Hw with ⟨Hf, Hwback⟩
    unfold txFields
    icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
    wp_auto
    wp_apply hPgid $$ [Hmv] as Hmv
    · iframe
    try wp_auto
    wp_apply hSetId $$ [Hh] as Hh
    · iframe
    try wp_auto
    wp_apply hId $$ [Hh] as Hh
    · iframe
    try wp_auto
    simp only
    -- the numbers: the mark's page and `minsz`
    generalize hpg : X.t.mv.pgid' = pg at *
    have hpgb : pg.toNat < 2 ^ 36 := by omega
    have hM : sint.Z ((pg + count + W64 1) * W64 4096) =
        ((pg.toNat + sint.nat count + 1) * 4096 : Nat) := by
      have : (sint.Z count).toNat = sint.nat count := rfl
      word
    -- `MaxSize`: an error, or on
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun v => iprop(db_ptr ↦ K.db ∗
      minsz_ptr ↦ ((pg + count + W64 1) * W64 4096) ∗ «$res0_ptr» ↦ (null : Loc) ∗
      ((⌜v = executeVal⌝ ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
       (⌜v = returnVal #()⌝ ∗ ∃ e : GoInterface, «$res1_ptr» ↦ e ∗ ⌜e ≠ interface.nil⌝ ∗
         fmtErrorOk e))))) $$ [db minsz «$res0» «$res1»]
    · by_cases hmx : sint.Z (W64 0) < sint.Z mx
      · rw [decide_eq_true hmx]
        wp_auto
        wp_apply hMmapSize K.db _ (by rw [hM]; omega) as %nms %err Hms
        · iframe #
        try wp_auto
        irevert Hms
        rcases hmo : mmapSizeOf (sint.nat ((pg + count + W64 1) * W64 4096)) with _ | sz
        · iintro ⟨%hne, #HeS⟩
          cases err with
          | nil => exact absurd rfl hne
          | ok ii =>
          simp only
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
          · iframe
            simp only [fmt.argsOk]
            isplitl
            · iapply fmtErrorOk_argOk $$ HeS
            · itrivial
          try wp_auto
          iframe
          iright
          isplitr
          · ipureintro; rfl
          iexists GoInterface.ok ei
          iframe
          isplitr
          · ipureintro; exact fun h => nomatch h
          iapply fmtErrorOk_of_errorf ei Hty $$ HiS
        · iintro %hok
          obtain ⟨rfl, hsz⟩ := hok
          ihave %hgoos : ⌜goosLinux⌝ $$ []
          · iapply goosLinux_of_pkgInit $$ Hpkg
          ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
          · iapply goarchAmd64_of_pkgInit $$ Hpkg
          unfold goosLinux at hgoos
          unfold goarchAmd64 at hgoarch
          rw [hgoos]
          wp_auto
          wp_apply hGrowSize $$ []
          · iframe #
          try wp_auto
          by_cases hgt : sint.Z mx < sint.Z (growSizeOf nms ((pg + count + W64 1) * W64 4096))
          · rw [decide_eq_true hgt, hgoarch]
            wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl ⟨Hsl, -⟩
            try wp_auto
            wp_apply hLogger K.db lg Hdb $$ []
            · iframe; iframe #
            try wp_auto
            cases lg with
            | nil => unfold boltLogger; iexfalso; iexact Hlgok
            | ok li =>
            simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
              show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
              show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl,
              show sint.nat (W64 (0 + 1 + 1 + 1 + 1)) = 4 from rfl,
              List.set_cons_succ, List.set_cons_zero]
            wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 100, W8 100, W8 100] _
              [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
                interface.mkOk go.int #((pg + count + W64 1) * W64 4096),
                interface.mkOk go.int #(growSizeOf nms ((pg + count + W64 1) * W64 4096)),
                interface.mkOk go.int #mx] _ iprop(True) _
              (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
            · iframe
            · log_args_ok
            try wp_auto
            icases hErrMax $$ Hpkg with ⟨%e, #He, %hep, #HeOk⟩
            wp_auto
            iframe
            iright
            isplitr
            · ipureintro; rfl
            iexists GoInterface.ok e
            iframe
            isplitr
            · ipureintro; exact fun h => nomatch h
            iexact HeOk
          · rw [decide_eq_false hgt]
            wp_auto
            iframe
            ileft
            ipureintro; rfl
      · rw [decide_eq_false hmx]
        wp_auto
        iframe
        ileft
        ipureintro; rfl
    iintro %v ⟨db, minsz, «$res0», Hv⟩
    icases Hv with (⟨%hv, «$res1»⟩ | ⟨%hv, %e, «$res1», %hne, #HeOk⟩)
    rotate_left
    · -- `MaxSize`'s error: nothing changed
      subst hv
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact hne
      iframe HeOk
      ileft
      isplitl [Hwback Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
      · iapply Hwback $$ %X.t [] [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        · iframe
      isplitl
      · isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest]
        · iframe
        · iframe
      · ipureintro; exact Hwok
    subst hv
    wp_auto
    have hml : sint.Z (W64 ((mapLen w.ms : Nat) : Int)) = (mapLen w.ms : Int) := by word
    have hcW : W64 ((sint.nat count : Nat) : Int) = count := by
      have : (sint.Z count).toNat = sint.nat count := rfl
      word
    rw [hml, hM]
    by_cases hrm : ((mapLen w.ms : Nat) : Int) ≤ (((pg.toNat + sint.nat count + 1) * 4096 : Nat) : Int)
    · rw [decide_eq_true hrm]
      wp_auto
      -- the remap: the writer's state put back together for `mmap`
      ihave Hw : wtxW K tx r m X $$ [Hwback Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
      · iapply Hwback $$ %X.t [] [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        · iframe
      ihave Hdb : wdbW K tx X.v w $$ [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz
          Hmf Hrest Hflo Hrd Hrcpt]
      · unfold wdbW wdbLive wdbCoreG
        isplitl
        · isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest]
          · iframe
          · iframe
        · ipureintro; exact Hwok
      have hmL : mapLen w.ms ≤ sint.nat ((pg + count + W64 1) * W64 4096) := by
        have e : sint.nat ((pg + count + W64 1) * W64 4096) =
            (sint.Z ((pg + count + W64 1) * W64 4096)).toNat := rfl
        rw [e, hM]; omega
      wp_apply hMmap K tx r m X w _ (by rw [hM]; omega) hmL hdp hlf hlr $$ [Hw Hdb] as %err Hres
      · iframe
      try wp_auto
      icases Hres with (⟨%he, %Xd, %b, %w', Hw, Hdb, %hrel⟩ | ⟨%hnp, #HeOk, Hcase⟩)
      · subst he
        wp_auto
        obtain ⟨hdr, hrmp, hlen⟩ := hrel
        have hmv : (Xd.rebase b).t.mv = X.t.mv := hdr.2.2.2.2.2.2.1
        icases wtxW_txFields_acc K tx r m (Xd.rebase b) $$ Hw with ⟨Hf, Hwback⟩
        unfold txFields
        icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
        unfold wdbW wdbLive wdbCoreG
        icases Hdb with ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath,
          Hdsz, Hmf, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok'⟩
        wp_auto
        wp_apply hPgid Xd.t.t.meta' X.t.mv (DFrac.own 1) $$ [Hmv] as Hmv
        · rw [← hmv, show Xd.t.t.meta' = (Xd.rebase b).t.t.meta' from rfl]; iexact Hmv
        try wp_auto
        rw [hpg]
        wp_apply hSetPgid $$ [Hmv] as Hmv
        · iframe
        try wp_auto
        have hov : W32 (sint.Z (count - W64 1)) = W32 ((sint.nat count - 1 : Nat) : Int) := by
          have : sint.Z (count - W64 1) = sint.Z count - 1 := by word
          rw [this]; congr 1; omega
        rw [hov]
        ihave Hp := allocBuf_of_page s.ptr pg (sint.nat count) Hsp $$ [Hh Hz]
        · iframe
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists Xd.rebase b, w', pg, pg + W64 ((sint.nat count : Nat) : Int)
        isplitl [Hwback Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
        · rw [show (Xd.rebase b).withHwm (pg + W64 ((sint.nat count : Nat) : Int)) =
              { Xd.rebase b with t := ((Xd.rebase b).withHwm (pg + W64 ((sint.nat count : Nat) : Int))).t }
              from rfl]
          iapply Hwback $$ %((Xd.rebase b).withHwm (pg + W64 ((sint.nat count : Nat) : Int))).t []
            [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
          · ipureintro; exact ⟨rfl, rfl, rfl⟩
          · simp only [WX.withHwm]
            rw [hcW, hmv]
            iframe
        isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest Hflo Hrd Hrcpt]
        · isplitl
          · isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest]
            · iframe
            · iframe
          · ipureintro; exact Hwok'
        iframe Hp
        ipureintro
        refine ⟨?_, hrmp.1, ?_, .inr ⟨hpg.symm, by omega, rfl, .inr ⟨Xd, b, hdr, rfl, hrmp⟩⟩⟩
        · intro h; rw [h] at Hsp; exact absurd Hsp (by decide)
        · rw [hcW]
          have : (pg + count).toNat = pg.toNat + sint.nat count := by
            have : (sint.Z count).toNat = sint.nat count := rfl
            word
          rw [this]
          have h3 : sint.nat ((pg + count + W64 1) * W64 4096) =
              (pg.toNat + sint.nat count + 1) * 4096 := by
            rw [show sint.nat ((pg + count + W64 1) * W64 4096) =
              (sint.Z ((pg + count + W64 1) * W64 4096)).toNat from rfl, hM, Int.toNat_natCast]
          rw [h3] at hlen
          exact hwm_fit' _ _ _ hlen
      · -- `mmap`'s error: returned, or wrapped
        obtain ⟨hne, hpt⟩ := hnp
        cases err with
        | nil => exact absurd rfl hne
        | ok ii =>
        simp only
        wp_auto
        icases hErrMax $$ Hpkg with ⟨%e, #He, %hep, #HeOk2⟩
        wp_auto
        by_cases hty : ii.ty = e.ty
        · obtain ⟨T, l, hT, hl⟩ := hep
          obtain ⟨l', hl'⟩ := hpt ii rfl T (hty.trans hT)
          simp only [hty, ↓reduceIte]
          rw [hT, hl, hl']
          wp_auto
          by_cases hll : l' = l
          · rw [decide_eq_true hll]
            wp_auto
            iapply HΦ
            iright
            isplitr
            · ipureintro; exact hne
            iframe HeOk
            icases Hcase with (⟨H1, H2⟩ | ⟨%Xd, %b, %w', H1, H2, %h⟩)
            · ileft
              iframe H1
              iapply (show wdbW (GF := GF) K tx X.v w ⊢ _ by
                unfold wdbW wdbLive wdbCoreG; exact .rfl) $$ H2
            · iright
              iexists Xd.rebase b, w'
              iframe H1
              isplitl [H2]
              · iapply wdbLost_rebase $$ H2
              ipureintro
              exact ⟨⟨Xd, b, h.1, rfl⟩, h.2⟩
          · rw [decide_eq_false hll]
            wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl2 ⟨Hsl2, -⟩
            wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
            · iframe
              simp only [fmt.argsOk]
              isplitl
              · iapply fmtErrorOk_argOk $$ HeOk
              · itrivial
            try wp_auto
            iapply HΦ
            iright
            isplitr
            · ipureintro; exact fun h => nomatch h
            isplitr
            · iapply fmtErrorOk_of_errorf ei Hty $$ HiS
            icases Hcase with (⟨H1, H2⟩ | ⟨%Xd, %b, %w', H1, H2, %h⟩)
            · ileft
              iframe H1
              iapply (show wdbW (GF := GF) K tx X.v w ⊢ _ by
                unfold wdbW wdbLive wdbCoreG; exact .rfl) $$ H2
            · iright
              iexists Xd.rebase b, w'
              iframe H1
              isplitl [H2]
              · iapply wdbLost_rebase $$ H2
              ipureintro
              exact ⟨⟨Xd, b, h.1, rfl⟩, h.2⟩
        · simp only [hty, ↓reduceIte]
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
          · iframe
            simp only [fmt.argsOk]
            isplitl
            · iapply fmtErrorOk_argOk $$ HeOk
            · itrivial
          try wp_auto
          iapply HΦ
          iright
          isplitr
          · ipureintro; exact fun h => nomatch h
          isplitr
          · iapply fmtErrorOk_of_errorf ei Hty $$ HiS
          icases Hcase with (⟨H1, H2⟩ | ⟨%Xd, %b, %w', H1, H2, %h⟩)
          · ileft
            iframe H1
            iapply (show wdbW (GF := GF) K tx X.v w ⊢ _ by
              unfold wdbW wdbLive wdbCoreG; exact .rfl) $$ H2
          · iright
            iexists Xd.rebase b, w'
            iframe H1
            isplitl [H2]
            · iapply wdbLost_rebase $$ H2
            ipureintro
            exact ⟨⟨Xd, b, h.1, rfl⟩, h.2⟩
    rw [decide_eq_false hrm]
    wp_auto
    wp_apply hPgid $$ [Hmv] as Hmv
    · iframe
    try wp_auto
    rw [hpg]
    wp_apply hSetPgid $$ [Hmv] as Hmv
    · iframe
    try wp_auto
    have hov : W32 (sint.Z (count - W64 1)) = W32 ((sint.nat count - 1 : Nat) : Int) := by
      have : sint.Z (count - W64 1) = sint.Z count - 1 := by word
      rw [this]; congr 1; omega
    rw [hov]
    ihave Hp := allocBuf_of_page s.ptr pg (sint.nat count) Hsp $$ [Hh Hz]
    · iframe
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists X, w, pg, pg + W64 ((sint.nat count : Nat) : Int)
    isplitl [Hwback Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
    · rw [show X.withHwm (pg + W64 ((sint.nat count : Nat) : Int)) =
          { X with t := (X.withHwm (pg + W64 ((sint.nat count : Nat) : Int))).t } from rfl]
      iapply Hwback $$ %(X.withHwm (pg + W64 ((sint.nat count : Nat) : Int))).t []
        [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      · simp only [WX.withHwm]
        rw [hcW]
        iframe
    isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest Hflo Hrd Hrcpt]
    · isplitl
      · isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest]
        · iframe
        · iframe
      · ipureintro; exact Hwok
    iframe Hp
    ipureintro
    refine ⟨?_, rfl, ?_, .inr ⟨hpg.symm, by omega, rfl, .inl ⟨rfl, rfl⟩⟩⟩
    · intro h; rw [h] at Hsp; exact absurd Hsp (by decide)
    · rw [hcW]
      have : (pg + count).toNat = pg.toNat + sint.nat count := by
        have : (sint.Z count).toNat = sint.nat count := rfl
        word
      rw [this]
      have h2 : ¬ (mapLen w.ms ≤ (pg.toNat + sint.nat count + 1) * 4096) := by exact_mod_cast hrm
      exact hwm_fit _ _ _ h2
  icases Hflo with (⟨%h0, -⟩ | ⟨%hcan, Hflo⟩)
  · exact absurd h0 hr0
  -- the freelist's run: the store's step, the page's bytes
  imod (store_alloc K.B K.N K.p ⊤ CoPset.subseteq_top w.fl (wLive X.v w.C) (w.C.txid + 1) rid
    (sint.nat count) rfl hcan.2 hcn) $$ [Hgfl Hgwv] with ⟨Hgfl, Hgwv⟩
  · iframe; iframe #
  rw [decide_eq_false hr0]
  wp_auto
  have hov : W32 (sint.Z (count - W64 1)) = W32 ((sint.nat count - 1 : Nat) : Int) := by
    have : sint.Z (count - W64 1) = sint.Z count - 1 := by word
    rw [this]; congr 1; omega
  rw [hov]
  ihave Hp := allocBuf_of_page s.ptr rid (sint.nat count) Hsp $$ [Hh Hz]
  · iframe
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists X, w.withFl (w.fl.alloc w.wtxid rid (sint.nat count)), rid, X.t.mv.pgid'
  rw [show X.withHwm X.t.mv.pgid' = X from rfl]
  iframe Hw
  simp only [WDb.withFl]
  unfold WDb.wtxid
  isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest Hflo Hrd Hrcpt]
  · isplitl
    · isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hrest]
      · iframe
      · iframe
    · ipureintro
      exact ⟨wdbOK_alloc w _ rid _ Hwok.1, Hwok.2⟩
  iframe Hp
  ipureintro
  refine ⟨?_, rfl, hhwm, .inl ⟨rfl, hcan.2, rfl, rfl⟩⟩
  intro h; rw [h] at Hsp; exact absurd Hsp (by decide)

end alloc

end bbolt
end EtcdGrove
end Perennial
