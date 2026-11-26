/-
The proof of `Spec/go_etcd_io/bbolt/DB__grow.lean` (U4e, `notes/bbolt-proof-plan.md`): the file's
size by `fileSize`; past it, `growSize`'s size (the mapping's length up to `AllocSize`, else
`sz + AllocSize`, whole pages), `File.Truncate` to it (the mapping's cells past the file's end lent
to it, `Mmap/GrowRes`; on failure the file grew or did not, `os.ftDone`/`os.ftUndone`) and
`File.Sync` unless `NoGrowSync` (its byte-less `specB`: the writer holds none of the bytes); the writer side closed by
`Mmap/GrowEnd`. Three facts `wdbOK'` does not give are `Mmap/GrowPure`'s gaps (`sorry`s).
-/
module

public import Spec.go_etcd_io.bbolt.DB__grow
public import Proof.go_etcd_io.bbolt.Mmap.GrowEnd
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.FileSize
public import Proof.go_etcd_io.bbolt.Mmap.GrowSize
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.os.File__Truncate
public import Spec.os.File__Sync
public import Proof.go_etcd_io.bbolt.Inv.BFileTrunc
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- A resize to a page-aligned size at least the file's announces up to that size (`rsHi`: the end of
the page holding the larger of the two). -/
private theorem grow_rsHi (s tg : Nat) (h : s ≤ tg) (hal : tg % 4096 = 0) : rsHi true s tg = tg := by
  simp only [rsHi, if_true, pageEnd]; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.grow.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hFileSize : DB.fileSize.spec (GF := GF) (hG := hG))
    (hGrowSize : DB.growSize.spec (GF := GF) (hG := hG))
    (hTruncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (hTruncateC : os.File.Truncate.specCrashIL (GF := GF) (hG := hG))
    (hTruncateB : os.File.Truncate.specCrashILBig (GF := GF) (hG := hG))
    (hSync : os.File.Sync.specB (GF := GF) (hG := hG))
    (hSyncC : os.File.Sync.specCrashIL (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DB.grow.spec (GF := GF) (hG := hG) := by
  intro fr K tx v w sz hsz0 hszmax hszal
  wp_start as ⟨#Hcore, Hdb⟩
  icases BC.core_bfile K $$ Hcore with ⟨#Hci, %hns⟩
  icases BC.core_growFields K $$ Hcore with ⟨#Hpkg, #Hos, %Hdbnn, #Hps, #Has, ⟨%lg, #Hlg, #Hlgok⟩,
    #Hro, #Hml, ⟨%ngs, #Hngs⟩⟩
  ihave %hgoos : ⌜goosLinux⌝ $$ []
  · iapply goosLinux_of_pkgInit $$ Hpkg
  ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
  · iapply goarchAmd64_of_pkgInit $$ Hpkg
  unfold goosLinux at hgoos
  unfold goarchAmd64 at hgoarch
  icases wdbW'_grow_acc fr K tx v w $$ Hdb with ⟨%Hwok, %hL, Hres, Hclose⟩
  obtain ⟨hok, hms, hv⟩ := Hwok
  ihave Hclose : growCloser (GF := GF) fr K tx v w $$ [Hclose]
  · unfold growCloser; iexact Hclose
  unfold growRes
  icases Hres with ⟨Hfile, Hfo, Hfd, Hosm, Hdsz, Hwc, Hwb⟩
  wp_auto
  wp_apply hLogger K.db lg Hdbnn $$ []
  · iframe #
  try wp_auto
  icases bMeta_osMeta K.p w.C [] w.m $$ Hosm with ⟨%qm, Hosm, Hosmb⟩
  wp_apply hFileSize K.db w.f w.fd K.p (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) (DFrac.own qm)
    (dbFd K.p.ino) w.m rfl (by have := (hok.2.2.2.2.2.2.2.2.2.2.2.2.1).lt; omega) $$ [Hfile Hfo Hfd Hosm]
    as %fsz %err ⟨Hfile, Hfo, Hfd, Hosm, Hfs⟩
  · iframe; iframe #
  ihave Hosm := Hosmb $$ Hosm
  have hrefl : wdbGrown w { w with m := w.m, W := w.W, wb := w.wb } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun s hs => ⟨hs, fun _ => rfl⟩⟩
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlgok
  | ok li =>
  icases Hfs with (%Hfs | ⟨%hne, #HeS⟩)
  rotate_left
  · -- `fileSize` failed: logged, returned
    cases err with
    | nil => exact absurd rfl hne.1
    | ok ii =>
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    iapply HΦ
    iexists { w with m := w.m, W := w.W, wb := w.wb }
    isplitl
    · unfold growCloser; iapply Hclose $$ %w.m %w.W %w.wb [] [Hfile Hfo Hfd Hosm Hdsz Hwc Hwb]
      · ipureintro; exact ⟨hok, fun _ _ => rfl⟩
      · unfold growRes; iframe
    isplitr
    · ipureintro; exact hrefl
    iright
    iframe HeS
    ipureintro; exact hne.1
  obtain ⟨rfl, rfl, hfs8⟩ := Hfs
  have hszlt := (hok.2.2.2.2.2.2.2.2.2.2.2.2.1).lt
  have hszw := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfz : sint.Z (W64 (w.m.size : Int)) = w.m.size := by word
  wp_auto
  rw [hfz]
  by_cases hle : sint.Z sz ≤ (w.m.size : Int)
  · -- big enough: nothing to do
    rw [decide_eq_true hle]
    wp_auto
    iapply HΦ
    iexists { w with m := w.m, W := w.W, wb := w.wb }
    isplitl
    · unfold growCloser; iapply Hclose $$ %w.m %w.W %w.wb [] [Hfile Hfo Hfd Hosm Hdsz Hwc Hwb]
      · ipureintro; exact ⟨hok, fun _ _ => rfl⟩
      · unfold growRes; iframe
    isplitr
    · ipureintro; exact hrefl
    ileft; isplitr
    · ipureintro; rfl
    iintro #-; ipureintro; show min _ _ ≤ w.m.size; omega
  rw [decide_eq_false hle]
  wp_auto
  wp_apply hGrowSize K.db (W64 (mapLen w.ms : Int)) sz $$ []
  · iframe #
  try wp_auto
  cases ngs
  rotate_left
  · -- `NoGrowSync`: nothing to do
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iexists { w with m := w.m, W := w.W, wb := w.wb }
    isplitl
    · unfold growCloser; iapply Hclose $$ %w.m %w.W %w.wb [] [Hfile Hfo Hfd Hosm Hdsz Hwc Hwb]
      · ipureintro; exact ⟨hok, fun _ _ => rfl⟩
      · unfold growRes; iframe
    isplitr
    · ipureintro; exact hrefl
    ileft; isplitr
    · ipureintro; rfl
    iintro #Hf
    ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ Hngs Hf
    exact absurd h (by decide)
  simp only [Bool.not_false]
  wp_auto
  try rw [hgoos]
  try wp_auto
  -- the new size `S`: the mapping's length up to `AllocSize`, else `sz + AllocSize`
  have hk10 := hok.2.2.2.2.2.2.2.2.2.1 v.base (mapLen w.ms) hms
  have hfacts : 0 ≤ (growSizeOf (W64 (mapLen w.ms : Int)) sz).toInt ∧
      w.m.size ≤ (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat ∧
      (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat % 4096 = 0 ∧
      (mapLen w.ms ≤ 0x1000000 → (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat ≤ mapLen w.ms) ∧
      (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat ≤ 0xFFFFFFFFFFFF ∧
      (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat ≤ (sint.Z sz).toNat + 0x1000000 := by
    have hLz : sint.Z (W64 (mapLen w.ms : Int)) = (mapLen w.ms : Int) := by word
    unfold growSizeOf
    rw [hLz]
    by_cases hA : mapLen w.ms ≤ 0x1000000
    · have hA' : ((mapLen w.ms : Nat) : Int) ≤ sint.Z (W64 0x1000000) := by
        have : sint.Z (W64 0x1000000) = 0x1000000 := by word
        omega
      simp only [hA', ↓reduceIte]
      have hal : mapLen w.ms % 4096 = 0 := hL.2
      have := hk10 hA
      refine ⟨by word, ?_, ?_, fun _ => ?_, ?_, ?_⟩ <;>
        (have e : (W64 (mapLen w.ms : Int)).toNat = mapLen w.ms := by word) <;> omega
    · clear hL
      have hA' : ¬ ((mapLen w.ms : Nat) : Int) ≤ sint.Z (W64 0x1000000) := by
        have : sint.Z (W64 0x1000000) = 0x1000000 := by word
        omega
      simp only [hA', ↓reduceIte]
      have e : (sz + W64 0x1000000).toNat = (sint.Z sz).toNat + 0x1000000 := by word
      have e2 : (sz + W64 0x1000000).toInt = sint.Z sz + 0x1000000 := by word
      refine ⟨by omega, by omega, by omega, fun h => absurd h hA, by omega, by omega⟩
  obtain ⟨hS0, hSge, hSal, hS10, hS63, hSsz⟩ := hfacts
  -- W1 (step 4): the new size covers `sz` or the mapping
  have hSmin : min (sint.Z sz).toNat (mapLen w.ms) ≤
      (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat := by
    have hLz : sint.Z (W64 (mapLen w.ms : Int)) = (mapLen w.ms : Int) := by word
    unfold growSizeOf
    rw [hLz]
    by_cases hA : mapLen w.ms ≤ 0x1000000
    · have hA' : ((mapLen w.ms : Nat) : Int) ≤ sint.Z (W64 0x1000000) := by
        have : sint.Z (W64 0x1000000) = 0x1000000 := by word
        omega
      simp only [hA', ↓reduceIte]
      have e : (W64 (mapLen w.ms : Int)).toNat = mapLen w.ms := by word
      omega
    · have hA' : ¬ ((mapLen w.ms : Nat) : Int) ≤ sint.Z (W64 0x1000000) := by
        have : sint.Z (W64 0x1000000) = 0x1000000 := by word
        omega
      simp only [hA', ↓reduceIte]
      have e : (sz + W64 0x1000000).toNat = (sint.Z sz).toNat + 0x1000000 := by word
      omega
  -- the mapping's cells past the file's end, lent to `Truncate`
  have hmaps : w.m.maps = GMap.singleton v.base (mapLen w.ms) := hok.1 _ _ hms
  ihave Hwc : wCells (GF := GF) (some (v.base, mapLen w.ms)) w.W $$ [Hwc]
  · rw [← hms]; iexact Hwc
  icases wCells_gather' fr w hok v.base (mapLen w.ms) hms $$ Hwc with ⟨Hws, Hp⟩
  icases grow_cells_out w.C w.fl v.base (mapLen w.ms) (min w.m.size (mapLen w.ms))
    (Nat.min_le_right _ _) (grow_slots_ok fr w hok v.base _ hms hfs8) $$ [Hws Hp]
    with ⟨Hlow, Hpart, Htail⟩
  · iframe
  icases mcellsAny_single_split v.base (mapLen w.ms) w.m.size
    (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat hSge $$ Htail with ⟨Htail, Hrest⟩
  ihave Htail : mcellsAny (GF := GF) w.m.maps w.m.size
      (rsHi true w.m.size (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat) $$ [Htail]
  · rw [hmaps, grow_rsHi _ _ hSge hSal]; iexact Htail
  wp_apply wp_bTruncate hTruncate hTruncateC hTruncateB w.f w.fd K.p.path (DFrac.own (1 : Qp).half)
    (growSizeOf (W64 (mapLen w.ms : Int)) sz) (DFrac.own (1 : Qp).half) (dbFd K.p.ino) K.p w.C []
    w.m rfl (wdbOK'_fd fr w hok) rfl hS0 hSge hns
    (fun _ => hSal)
    $$ [Hfo Hfd Hosm Htail] as %e ⟨Hfo, Hfd, Htr, #HeOk⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  ihave Hfo : fileOwn w.f w.fd K.p.path (DFrac.own (1 : Qp).half) $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  generalize hSdef : growSizeOf (W64 (mapLen w.ms : Int)) sz = S at *
  -- the grown cells back, the mapping's tail joined
  have hcells : mcells (GF := GF) w.m.maps w.m.size (rsHi true w.m.size S.toNat) (rsCell S.toNat) ∗
      mcellsAny (GF := GF) (GMap.singleton v.base (mapLen w.ms)) S.toNat (mapLen w.ms) ⊢
      ∃ vf, cellsR (GF := GF) v.base (min w.m.size (mapLen w.ms))
        (mapLen w.ms - min w.m.size (mapLen w.ms)) vf := by
    rw [hmaps, grow_rsHi _ _ hSge hSal]
    iintro ⟨Hc, Hr⟩
    iapply grown_cells_back v.base (mapLen w.ms) w.m.size S.toNat _ hSge
    iframe
  have hfin := fun (m' : OsMeta) (h1 : m'.size = S.toNat) (h2 : m'.maps = w.m.maps) =>
    grow_finish (GF := GF) fr K tx v w hok v.base (mapLen w.ms) hms hL.2 hfs8 m' (by omega) h2
      (by omega) (fun h => by have := hS10 h; omega) (by omega) S.toNat h1
  cases e with
  | nil =>
    icases Htr with (⟨-, %m', %hm', Hmt, Hz, Hcm⟩ | ⟨%hne, -⟩)
    rotate_left
    · exact absurd rfl hne
    icases hcells $$ [Hcm Hrest] with Htail
    · iframe
    wp_auto
    -- the sync of the grown range
    unfold zBytes
    icases Hz with ⟨%zs, Hzs, %hzs⟩
    have hzl : zs.length = S.toNat - w.m.size := by
      have := congrArg List.length hzs; simpa using this
    ihave HR : bRanges (GF := GF) K.p [(w.m.size, zs)] $$ [Hzs]
    · unfold bRanges; iapply BigSepL.bigSepL_singleton.2; iexact Hzs
    wp_apply wp_bSync hSync hSyncC w.f w.fd K.p.path (DFrac.own (1 : Qp).half)
      (DFrac.own (1 : Qp).half) (dbFd K.p.ino) K.p w.C [(w.m.size, S.toNat - w.m.size)] m'
      [(w.m.size, zs)] rfl hns
      (fun k ⟨r, hr, h1, h2⟩ _ => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨(w.m.size, zs), List.mem_singleton_self _, h1, by simp only at h2 ⊢; omega⟩)
      (List.pairwise_singleton _ _)
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp only; omega)
      $$ [Hfo Hfd Hmt HR] as %e2 ⟨Hfo, Hfd, Hsy, #He2⟩
    · rw [← fileOwn_eq]; iframe; iframe #
    ihave Hfo : fileOwn w.f w.fd K.p.path (DFrac.own (1 : Qp).half) $$ [Hfo]
    · rw [fileOwn_eq]; iexact Hfo
    -- the grown bytes back from the synced range
    have hback : ∀ R' : List (Nat × List ByteG), RSame [(w.m.size, zs)] R' →
        bRanges (GF := GF) K.p R' ⊢ zBytes K.p w.m.size (S.toNat - w.m.size) := by
      intro R' hR
      unfold RSame at hR
      rcases hR with _ | ⟨⟨h1, h2⟩, hnil⟩
      cases hnil
      unfold bRanges zBytes
      iintro H
      icases BigSepL.bigSepL_singleton.1 $$ H with H
      iexists _
      rw [h1]
      iframe H
      ipureintro; rw [h2]; exact hzs
    icases Hsy with (⟨%he2, %m'', %R', Hm'', HR', %hh⟩ | ⟨%he2, Hmt, HR⟩)
    · subst he2
      wp_auto
      iapply HΦ
      ihave Hz := hback R' hh.2.2 $$ HR'
      ihave Hfin := hfin m'' (by rw [hh.1, hm'.1]) (by rw [hh.2.1, hm'.2])
        $$ Hclose Hfile Hfo Hfd Hm'' Hdsz Hlow Hpart Htail Hwb Hz
      icases Hfin with ⟨%w', Hw', %hg⟩
      iexists w'
      iframe Hw'
      isplitr
      · ipureintro; exact hg.1
      ileft; isplitr
      · ipureintro; rfl
      iintro #-; ipureintro; rw [hg.2, hh.1, hm'.1]; exact hSmin
    cases e2 with
    | nil => exact absurd rfl he2.1
    | ok ii =>
    ihave #HeS : fmtErrorOk (GF := GF) (GoInterface.ok ii) $$ []
    · iapply fmtErrorOkOrNil_ne (GoInterface.ok ii) (by intro h; cases h) $$ He2
    ihave Hm' := bMetaT_err K.p w.C _ [] m' he2.2 $$ Hmt
    ihave Hz := hback [(w.m.size, zs)] (RSame.refl _) $$ HR
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    try rw [hgoarch]
    simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
      show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl, List.set_cons_succ, List.set_cons_zero]
    wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 100, W8 118] _
      [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
        interface.mkOk go.int #(W64 (mapLen w.ms : Int)), GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
    · iframe
      fmt_args_intro
      isplitl
      · iapply fmt.argOkAt_of_fmtErrorOkOrNil
        isplitr
        · ipureintro; decide
        · iapply fmtErrorOkOrNil_of $$ HeS
      · itrivial
    try wp_auto
    iapply HΦ
    ihave Hfin := hfin m' hm'.1 hm'.2 $$ Hclose Hfile Hfo Hfd Hm' Hdsz Hlow Hpart Htail Hwb Hz
    icases Hfin with ⟨%w', Hw', %hg⟩
    iexists w'
    iframe Hw'
    isplitr
    · ipureintro; exact hg.1
    iright
    isplitr
    · ipureintro; intro h; cases h
    iapply fmtErrorOk_of_errorf ei Hty $$ HiS
  | ok ii =>
    ihave #HeS : fmtErrorOk (GF := GF) (GoInterface.ok ii) $$ []
    · iapply fmtErrorOkOrNil_ne (GoInterface.ok ii) (by intro h; cases h) $$ HeOk
    icases Htr with (⟨%he, -⟩ | ⟨-, Htr⟩)
    · exact absurd he (by intro h; cases h)
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    try rw [hgoarch]
    simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
      show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl,
      show sint.nat (W64 (0 + 1 + 1 + 1 + 1)) = 4 from rfl, List.set_cons_succ, List.set_cons_zero]
    wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 100, W8 100, W8 118] _
      [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
        interface.mkOk go.int #S, interface.mkOk go.int #(W64 (mapLen w.ms : Int)),
        GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
    · iframe
      fmt_args_intro
      isplitl
      · iapply fmt.argOkAt_of_fmtErrorOkOrNil
        isplitr
        · ipureintro; decide
        · iapply fmtErrorOkOrNil_of $$ HeS
      · itrivial
    try wp_auto
    iapply HΦ
    ihave Hfin : (∃ w' : WDb, wdbW' (GF := GF) fr K tx v w' ∗ ⌜wdbGrown w w'⌝) $$
      [Htr Hrest Hclose Hfile Hfo Hfd Hdsz Hlow Hpart Hwb]
    · icases Htr with (⟨%m', %hm', Hm', Hz, Hcm⟩ | ⟨%m', %hm', Hm', Htail⟩)
      · icases hcells $$ [Hcm Hrest] with Htail
        · iframe
        icases hfin m' hm'.1 hm'.2 $$ Hclose Hfile Hfo Hfd Hm' Hdsz Hlow Hpart Htail Hwb Hz
          with ⟨%w', Hw', %hg⟩
        iexists w'; iframe; ipureintro; exact hg.1
      · ihave Htail : mcellsAny (GF := GF) (GMap.singleton v.base (mapLen w.ms)) w.m.size S.toNat
          $$ [Htail]
        · rw [hmaps, grow_rsHi _ _ hSge hSal]; iexact Htail
        ihave Htail := mcellsAny_single_join v.base (mapLen w.ms) w.m.size S.toNat hSge $$ [Htail Hrest]
        · iframe
        iapply grow_finish_same fr K tx v w hok v.base (mapLen w.ms) hms hL.2 hfs8 m' hm'.1 hm'.2
          $$ Hclose Hfile Hfo Hfd Hm' Hdsz Hlow Hpart Htail Hwb
    icases Hfin with ⟨%w', Hw', %hg⟩
    iexists w'
    iframe Hw'
    isplitr
    · ipureintro; exact hg
    iright
    isplitr
    · ipureintro; intro h; cases h
    iapply fmtErrorOk_of_errorf ei Hty $$ HiS

end proof

end bbolt
end EtcdGrove
end Perennial
