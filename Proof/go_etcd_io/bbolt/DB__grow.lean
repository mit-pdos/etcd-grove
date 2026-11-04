/-
The proof of `Spec/go_etcd_io/bbolt/DB__grow.lean` (U4e, `notes/bbolt-proof-plan.md`): the file's
size by `fileSize`; past it, `growSize`'s size (the mapping's length up to `AllocSize`, else
`sz + AllocSize`, whole pages), `File.Truncate` to it (the mapping's cells past the file's end lent
to it, `Mmap/GrowRes`) and `File.Sync` unless `NoGrowSync`; the writer side closed by
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
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.grow.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hFileSize : DB.fileSize.spec (GF := GF) (hG := hG))
    (hGrowSize : DB.growSize.spec (GF := GF) (hG := hG))
    (hTruncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (hSync : os.File.Sync.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DB.grow.spec (GF := GF) (hG := hG) := by
  intro fr K tx v w sz hsz0 hszmax hszal
  wp_start as ⟨#Hcore, Hdb⟩
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
  wp_apply hFileSize K.db w.f w.fd K.p (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    ⟨K.p, true, true⟩ w.m rfl (hok.2.2.2.2.2.2.2.2.2.2.2.2.1) $$ [Hfile Hfo Hfd Hosm]
    as %fsz %err ⟨Hfile, Hfo, Hfd, Hosm, Hfs⟩
  · iframe; iframe #
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
  have hszlt := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
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
    ileft; ipureintro; rfl
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
    ileft; ipureintro; rfl
  simp only [Bool.not_false]
  wp_auto
  rw [hgoos]
  wp_auto
  -- the new size `S`: the mapping's length up to `AllocSize`, else `sz + AllocSize`
  have hk10 := hok.2.2.2.2.2.2.2.2.2.1 v.base (mapLen w.ms) hms
  have hfacts : 0 ≤ (growSizeOf (W64 (mapLen w.ms : Int)) sz).toInt ∧
      w.m.size ≤ (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat ∧
      (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat % 4096 = 0 ∧
      (mapLen w.ms ≤ 0x1000000 → (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat ≤ mapLen w.ms) ∧
      (growSizeOf (W64 (mapLen w.ms : Int)) sz).toNat < 2 ^ 63 := by
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
      refine ⟨by word, ?_, ?_, fun _ => ?_, ?_⟩ <;>
        (have e : (W64 (mapLen w.ms : Int)).toNat = mapLen w.ms := by word) <;> omega
    · clear hL
      have hA' : ¬ ((mapLen w.ms : Nat) : Int) ≤ sint.Z (W64 0x1000000) := by
        have : sint.Z (W64 0x1000000) = 0x1000000 := by word
        omega
      simp only [hA', ↓reduceIte]
      have e : (sz + W64 0x1000000).toNat = (sint.Z sz).toNat + 0x1000000 := by word
      have e2 : (sz + W64 0x1000000).toInt = sint.Z sz + 0x1000000 := by word
      refine ⟨by omega, by omega, by omega, fun h => absurd h hA, by omega⟩
  obtain ⟨hS0, hSge, hSal, hS10, hS63⟩ := hfacts
  -- the mapping's cells past the file's end, lent to `Truncate`
  have hmaps : w.m.maps = GMap.singleton v.base (mapLen w.ms) := hok.1 _ _ hms
  ihave Hwc : wCells (GF := GF) (some (v.base, mapLen w.ms)) w.W $$ [Hwc]
  · rw [← hms]; iexact Hwc
  icases wCells_gather' fr w hok v.base (mapLen w.ms) hms $$ Hwc with ⟨Hws, Hp⟩
  icases grow_cells_out w.C w.fl v.base (mapLen w.ms) (min w.m.size (mapLen w.ms))
    (Nat.min_le_right _ _) (grow_slots_ok fr w hok v.base _ hms hfs8) $$ [Hws Hp]
    with ⟨Hlow, Hpart, Htail⟩
  · iframe
  ihave Htail : mcellsAny (GF := GF) w.m.maps w.m.size (mapLen w.ms) $$ [Htail]
  · rw [hmaps]; iapply (mcellsAny_single_eq v.base (mapLen w.ms) w.m.size).2; iexact Htail
  have hbelow : MapsBelow w.m.maps (mapLen w.ms) := by
    intro b' l' h
    rw [hmaps] at h
    simp only [GMap.singleton, GMap.lookup_insert_eq_iff] at h
    by_cases hb : v.base = b'
    · simp only [hb, ↓reduceIte, Option.some.injEq] at h; omega
    · simp only [hb, ↓reduceIte] at h; exact absurd h (by simp [GMap.empty])
  wp_apply hTruncate w.f w.fd K.p (DFrac.own 1) (growSizeOf (W64 (mapLen w.ms : Int)) sz)
    (DFrac.own 1) ⟨K.p, true, true⟩ w.m (mapLen w.ms) (wdbOK'_fd fr w hok) rfl hS0 hSge hbelow
    $$ [Hfo Hfd Hosm Htail] as %e ⟨Hfo, Hfd, Htr, #HeOk⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  ihave Hfo : fileOwn w.f w.fd K.p (DFrac.own 1) $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  generalize hSdef : growSizeOf (W64 (mapLen w.ms : Int)) sz = S at *
  have hGrown : osGrown (GF := GF) K.p w.m S.toNat (mapLen w.ms) ⊢
      osMeta K.p (DFrac.own 1) (some (w.m.grown S.toNat)) ∗
      osBytes K.p w.m.size (DFrac.own 1) (List.replicate (S.toNat - w.m.size) ((0 : w8), false)) ∗
      ∃ vf, cellsR (GF := GF) v.base (min w.m.size (mapLen w.ms))
        (mapLen w.ms - min w.m.size (mapLen w.ms)) vf := by
    unfold osGrown
    iintro ⟨Hm, Hz, H1, H2⟩
    iframe Hm Hz
    rw [hmaps]
    iapply grown_cells_back v.base (mapLen w.ms) w.m.size S.toNat _ hSge
    iframe
  cases e with
  | nil =>
    icases Htr with (⟨-, Htr⟩ | ⟨%hne, -⟩)
    rotate_left
    · exact absurd rfl hne
    icases hGrown $$ Htr with ⟨Hosm, Hz, Htail⟩
    wp_auto
    ihave Hnil : osBytes (GF := GF) K.p 0 (DFrac.own 1) [] $$ []
    · iapply growBytes_nil
    wp_apply hSync w.f w.fd K.p (DFrac.own 1) (DFrac.own 1) ⟨K.p, true, true⟩ (w.m.grown S.toNat) 0 []
      $$ [Hfo Hfd Hosm Hnil] as %e2 ⟨Hfo, Hfd, Hsy, #He2⟩
    · rw [← fileOwn_eq]; iframe; iframe #
    ihave Hfo : fileOwn w.f w.fd K.p (DFrac.own 1) $$ [Hfo]
    · rw [fileOwn_eq]; iexact Hfo
    have hfin : ∀ m' : OsMeta, m'.size = S.toNat → m'.maps = w.m.maps →
        growCloser (GF := GF) fr K tx v w -∗
        K.db.[DB, go!"file"] ↦ w.f -∗ fileOwn w.f w.fd K.p (DFrac.own 1) -∗
        osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ -∗ osMeta K.p (DFrac.own 1) (some m') -∗
        K.db.[DB, go!"datasz"] ↦ W64 (mapLen w.ms : Int) -∗
        ([∗list] s ∈ wSlots (min w.m.size (mapLen w.ms) / 4096) w.C w.fl,
          ∃ vf, cellsR (GF := GF) v.base (4096 * s) 4096 vf) -∗
        (∃ vf, cellsR (GF := GF) v.base (4096 * (min w.m.size (mapLen w.ms) / 4096))
          (min w.m.size (mapLen w.ms) - 4096 * (min w.m.size (mapLen w.ms) / 4096)) vf) -∗
        (∃ vf, cellsR (GF := GF) v.base (min w.m.size (mapLen w.ms))
          (mapLen w.ms - min w.m.size (mapLen w.ms)) vf) -∗
        wBytes K.p w.W w.wb w.m.size -∗
        osBytes K.p w.m.size (DFrac.own 1) (List.replicate (S.toNat - w.m.size) ((0 : w8), false)) -∗
        ∃ w' : WDb, wdbW' fr K tx v w' ∗ ⌜wdbGrown w w'⌝ := by
      intro m' h1 h2
      exact grow_finish fr K tx v w hok v.base (mapLen w.ms) hms hL.2 hfs8 m' (by omega) h2
        (by omega) (fun h => by have := hS10 h; omega) (by omega) S.toNat h1
    icases Hsy with (⟨%he2, Hosm, -⟩ | ⟨%he2, Hosm, -⟩)
    · subst he2
      wp_auto
      iapply HΦ
      ihave Hfin := hfin ((w.m.grown S.toNat).synced 0 []) rfl rfl $$ Hclose Hfile Hfo Hfd Hosm Hdsz Hlow Hpart Htail Hwb Hz
      icases Hfin with ⟨%w', Hw', %hg⟩
      iexists w'
      iframe Hw'
      isplitr
      · ipureintro; exact hg
      ileft; ipureintro; rfl
    cases e2 with
    | nil => exact absurd rfl he2
    | ok ii =>
    ihave #HeS : fmtErrorOk (GF := GF) (GoInterface.ok ii) $$ []
    · iapply fmtErrorOkOrNil_ne (GoInterface.ok ii) (by intro h; cases h) $$ He2
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    rw [hgoarch]
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
      simp only [fmt.argsOk]
      isplitl
      · iapply fmtErrorOk_argOk $$ HeS
      · itrivial
    try wp_auto
    iapply HΦ
    have hfin' := hfin ⟨S.toNat, w.m.lo, max w.m.hi S.toNat, w.m.named, false, w.m.maps, w.m.dur,
      w.m.durHi⟩ rfl rfl
    ihave Hfin := hfin' $$ Hclose Hfile Hfo Hfd Hosm Hdsz Hlow Hpart Htail Hwb Hz
    icases Hfin with ⟨%w', Hw', %hg⟩
    iexists w'
    iframe Hw'
    isplitr
    · ipureintro; exact hg
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
    rw [hgoarch]
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
      simp only [fmt.argsOk]
      isplitl
      · iapply fmtErrorOk_argOk $$ HeS
      · itrivial
    try wp_auto
    iapply HΦ
    ihave Hfin : (∃ w' : WDb, wdbW' (GF := GF) fr K tx v w' ∗ ⌜wdbGrown w w'⌝) $$
      [Htr Hclose Hfile Hfo Hfd Hdsz Hlow Hpart Hwb]
    · icases Htr with (Htr | ⟨Hosm, Htail⟩)
      · icases hGrown $$ Htr with ⟨Hosm, Hz, Htail⟩
        have hfin := grow_finish (GF := GF) fr K tx v w hok v.base (mapLen w.ms) hms hL.2 hfs8
          (w.m.grown S.toNat) hSge rfl hSal hS10 hS63 S.toNat rfl
        iapply hfin $$ Hclose Hfile Hfo Hfd Hosm Hdsz Hlow Hpart Htail Hwb Hz
      · ihave Htail : (∃ vf, cellsR (GF := GF) v.base (min w.m.size (mapLen w.ms))
            (mapLen w.ms - min w.m.size (mapLen w.ms)) vf) $$ [Htail]
        · rw [hmaps]; iapply (mcellsAny_single_eq v.base (mapLen w.ms) w.m.size).1; iexact Htail
        iapply grow_finish_same fr K tx v w hok v.base (mapLen w.ms) hms hL.2 hfs8 (ftMeta w.m S.toNat)
          rfl rfl $$ Hclose Hfile Hfo Hfd Hosm Hdsz Hlow Hpart Htail Hwb
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
