/-
`db.mmapUnlocked(minsz)` by the live writer, `mmaplock` held (U4d, `notes/bbolt-proof-plan.md`;
`Mmap/Remap`'s plan, steps 1-9): the remap's body. `DB.mmap` (`Proof/go_etcd_io/bbolt/DB__mmap`)
takes the lock around it.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Alloc
public import Proof.go_etcd_io.bbolt.Mmap.Munmap
public import Proof.go_etcd_io.bbolt.Mmap.Map
public import Proof.go_etcd_io.bbolt.Mmap.Rebase
public import Proof.go_etcd_io.bbolt.Mmap.RemapBase
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Mmap.RemapGather
public import Proof.go_etcd_io.bbolt.Mmap.RemapEnd
public import Proof.go_etcd_io.bbolt.Mmap.RemapGaps
public import Spec.go_etcd_io.bbolt.Bucket__dereference
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section body
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.mmapUnlocked(minsz)` by the live writer `tx`, `mmaplock` held** (`Pm 1`): `DB.mmap.spec`'s
post, `Pm 1` back (batch 44.1: over the flagged writer side). -/
abbrev DB.mmapUnlocked.spec : Prop :=
  ∀ (fr : Bool) (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (minsz : w64),
  0 < sint.Z minsz → mapLen w.ms ≤ sint.nat minsz → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW' fr K tx X.v w ∗ Pm K.B K.db 1 }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"mmapUnlocked")) (Val #minsz))
  {{ (err : GoInterface), RET #err; Pm K.B K.db 1 ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (Xd : WX) (b : Loc) (w' : WDb),
        wtxW K tx r m (Xd.rebase b) ∗ wdbW' fr K tx (Xd.rebase b).v w' ∗
        ⌜derefRel X Xd ∧ wdbRemap w w' ∧ sint.nat minsz ≤ mapLen w'.ms⌝) ∨
      (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW' fr K tx X.v w) ∨
         (∃ (Xd : WX) (b : Loc) (w' : WDb), wtxLost K tx r m (Xd.rebase b) ∗
           wdbLost' fr K tx (Xd.rebase b).v w' ∗
           ⌜derefRel X Xd ∧ w'.C = w.C ∧ w'.fl = w.fl⌝)))) }}

/-- The remap's fixed fields of the database (`dbFixed`, `isBoltCoreP`). -/
theorem BC.core_mmapFields (K : BC) :
    K.core (GF := GF) ⊢ osInv (GF := GF) ∗ K.db.[DB, go!"Mlock"] ↦□ false ∗
      (∃ x : w64, K.db.[DB, go!"MmapFlags"] ↦□ x ∗ ⌜x = W64 0 ∨ x = W64 0x8000⌝) := by
  unfold BC.core isBoltCoreP
  iintro ⟨-, -, -, -, #Hos, #Hfix, -⟩
  iframe Hos
  unfold dbFixed
  icases Hfix with ⟨-, -, -, -, -, #Hml, -, -, -, -, -, #Hmf, -⟩
  iframe Hml
  iexact Hmf

/-- The writer side's file, for `fileSize`, and back. -/
theorem wdbW'_file_acc (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) fr K tx v w ⊢ (K.db.[DB, go!"file"] ↦ w.f ∗ fileOwn w.f w.fd K.p (DFrac.own 1) ∗
        osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗ osMeta K.p (DFrac.own 1) (some w.m)) ∗
      ((K.db.[DB, go!"file"] ↦ w.f ∗ fileOwn w.f w.fd K.p (DFrac.own 1) ∗
        osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗ osMeta K.p (DFrac.own 1) (some w.m)) -∗
        wdbW' fr K tx v w) ∗
      ⌜wdbOK' fr w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝ := by
  unfold wdbW' wdbLive wdbCoreG
  iintro ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf,
    Hosm, Hfo, Hfd, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok, Htok⟩
  iframe Hfile Hfo Hfd Hosm
  isplitl
  · iintro ⟨Hfile, Hfo, Hfd, Hosm⟩
    isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hrest
      Hflo Hrd Hrcpt]
    · iframe
    isplitr
    · ipureintro; exact Hwok
    · iexact Htok
  · ipureintro; exact Hwok

/-- A mapping's length facts, the fields kept. -/
theorem mapFields_pure (db : Loc) (dq : DFrac) (b : Loc) (l : Nat) :
    mapFields (GF := GF) db dq (some (b, l)) ⊢
      ⌜l % 4096 = 0 ∨ l = 0xFFFFFFFFFFFF⌝ ∗ mapFields (GF := GF) db dq (some (b, l)) := by
  simp only [mapFields]
  iintro ⟨H1, H2, H3, H4, %h⟩
  isplitr
  · ipureintro; exact h.2.2
  iframe
  ipureintro; exact h

/-- Bytes' bounds, the bytes kept. -/
theorem bytes_bounds_keep (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢
      ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ ∧ bytesPointsto (GF := GF) l dq bs := by
  iintro H
  isplit
  · iapply internal.common.bytesPointsto_in_bounds l dq bs h $$ H
  · iexact H

/-- A `bool` field's points-to as the heap's. -/
theorem bool_heap (l : Loc) (dq : DFrac) (b : Bool) :
    l ↦{dq} b ⊢ heapPointsto (GF := GF) l dq #b := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨H, -⟩
  simp only [typedPointsto_bool, typedPointstoDef_heap]
  iexact H

attribute [local instance] go.tagged_internal_inst in
/-- **A `bool` load split at its atomic first step** (`StartRead`, the step that `store_cells_agree`
opens the page store around). -/
theorem wp_load_bool_split (l : Loc) (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    WP (StartRead (Val #l)) @ s; E
      {{ v, WP (Let "v" (Val v) (Seq (FinishRead (Val #l)) (Var "v"))) @ s; E {{ Φ }} }} ⊢
      WP (App (Val (GoInstruction (GoLoad go.bool))) (Val #l)) @ s; E {{ Φ }} := by
  iintro H
  wp_pures
  wp_call
  wp_bind (StartRead _)
  iexact H

/-- `mmapSizeOf`'s result: at least the size, at least 32 KiB, a mapping's length. -/
theorem mmapSizeOf_props (size s : Nat) (h : mmapSizeOf size = some s) :
    size ≤ s ∧ 32768 ≤ s ∧ s ≤ 0xFFFFFFFFFFFF ∧ (s % 4096 = 0 ∨ s = 0xFFFFFFFFFFFF) := by
  unfold mmapSizeOf at h
  rcases hf : (List.range 16).find? (fun i => decide (size ≤ 2 ^ (15 + i))) with _ | i
  · rw [hf] at h
    simp only at h
    have hbig : 2 ^ 30 < size := by
      have := List.find?_eq_none.1 hf 15 (by simp)
      simpa using this
    split at h
    · cases h
    · rename_i hle
      obtain rfl := Option.some.inj h.symm
      split <;> omega
  · rw [hf] at h
    obtain rfl := Option.some.inj h.symm
    obtain ⟨h1, h2⟩ := List.find?_some hf, List.mem_of_find?_eq_some hf
    simp only [decide_eq_true_eq] at h1
    simp only [List.mem_range] at h2
    have hp : 2 ^ 15 ≤ 2 ^ (15 + i) := Nat.pow_le_pow_right (by decide) (by omega)
    have hq : 2 ^ (15 + i) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
    have hm : 2 ^ (15 + i) % 4096 = 0 := by
      rw [show 15 + i = 12 + (3 + i) by omega, Nat.pow_add]; simp
    omega

/-- The writer's location and database (`wtxCore`'s facts). -/
theorem wtxW_tx_ne (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜tx ≠ null ∧ r.db = K.db⌝ := by
  unfold wtxW wtxCore
  iintro ⟨⟨-, -, %H, -⟩, -⟩
  ipureintro; exact ⟨H.2.2.1, H.1⟩

theorem wtxW_unf (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊣⊢ iprop(wtxCore K tx r m X ∗ viewCells wq X.v ∗
      ∃ l : Nat, mapFields r.db (DFrac.own (1 : Qp).half.half) (some (X.v.base, l) : MapSt) ∗
        ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝) := .rfl

theorem Pm_unf (B : BNs) (db : Loc) (q : Qp) :
    Pm (GF := GF) B db q ⊣⊢ iprop(∃ ms : MapSt, ghostVar B.map q.half.half ms ∗
      mapFields db (DFrac.own q.half) ms ∗ ghostVar B.mtok q ()) := .rfl

private instance viewOf_persistent_rb (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

/-- The writer's core, its view registered at a base, and its database. -/
theorem wtxCore_viewOf (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxCore (GF := GF) K tx r m X ⊢ wtxCore K tx r m X ∗ viewOf r X.v ∗ ⌜r.db = K.db⌝ := by
  unfold wtxCore
  iintro ⟨Hpkg, #Hc, %Hp, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, #Hv, Hst⟩
  iframe; iframe #
  ipureintro; exact ⟨Hp, Hp.1⟩

/-- The writer's records after a failed remap, at the old base. -/
theorem remap_lostX (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (Xd : WX) (hcov : derefOK Xd) :
    wtxCore (GF := GF) K tx r m Xd ∗ mapFields K.db (DFrac.own (1 : Qp).half.half) (none : MapSt) ⊢
      wtxLost K tx r m (Xd.rebase Xd.v.base) := by
  iintro ⟨Hc, Hm⟩
  unfold wtxLost
  icases wtxCore_viewOf K tx r m Xd $$ Hc with ⟨Hc, #Hv, %Hp⟩
  rw [Hp]
  iframe Hm
  iapply wtxCore_rebase K tx r m Xd Xd.v.base hcov
  iframe Hc
  rw [View.with_base_self Xd.v]; iexact Hv

theorem DB.mmapUnlocked.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hFileSize : DB.fileSize.spec (GF := GF) (hG := hG))
    (hMmapSize : DB.mmapSize.spec (GF := GF) (hG := hG))
    (hDeref : Bucket.dereference.spec (GF := GF) (hG := hG))
    (hMunmap : DB.munmap.spec (GF := GF) (hG := hG))
    (hMmapF : mmapF.spec (GF := GF) (hG := hG))
    (hPage : DB.page.spec (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG)) :
    DB.mmapUnlocked.spec (GF := GF) (hG := hG) := by
  intro fr K tx r m X w minsz hmin hmL hdp hlf hlr
  wp_start as ⟨Hw, Hdb, Hpm⟩
  icases wtxW_core K tx r m X $$ Hw with ⟨#Hcore, Hw⟩
  icases BC.core_allocFields K $$ Hcore with ⟨#Hps, #Has, ⟨%mx, #Hmx⟩, ⟨%lg, #Hlg, #Hlgok⟩,
    #Hfix, #Hpkg, %Hdb, #Hpinv⟩
  icases BC.core_mmapFields K $$ Hcore with ⟨#Hos, #Hmlk, ⟨%mf, #Hmf, %Hmf⟩⟩
  ihave %hgoos : ⌜goosLinux⌝ $$ []
  · iapply goosLinux_of_pkgInit $$ Hpkg
  ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
  · iapply goarchAmd64_of_pkgInit $$ Hpkg
  unfold goosLinux at hgoos
  unfold goarchAmd64 at hgoarch
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply hLogger K.db lg Hdb $$ []
  · iframe #
  try wp_auto
  icases wdbW'_file_acc fr K tx X.v w $$ Hdb with ⟨⟨Hfile, Hfo, Hfd, Hosm⟩, Hdbback, %Hwok⟩
  obtain ⟨hok, hms, hv⟩ := Hwok
  wp_apply hFileSize K.db w.f w.fd K.p (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    ⟨K.p, true, true⟩ w.m rfl (wdbOK'_size_lt fr w hok) $$ [Hfile Hfo Hfd Hosm]
    as %fsz %err ⟨Hfile, Hfo, Hfd, Hosm, Hfs⟩
  · iframe; iframe #
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
    have Hpt := hne.2
    ihave Hdb := Hdbback $$ [Hfile Hfo Hfd Hosm]
    · iframe
    iapply HΦ
    iframe Hpm
    iright
    iframe HeS
    isplitr
    · ipureintro; exact ⟨(fun h => nomatch h), Hpt⟩
    ileft; iframe
  obtain ⟨rfl, rfl, hfs8⟩ := Hfs
  have hszlt := wdbOK'_size_lt fr w hok
  have hfz : sint.Z (W64 (w.m.size : Int)) = w.m.size := by word
  wp_auto
  wp_join iprop(∃ s : w64, size_ptr ↦ s ∗ minsz_ptr ↦ minsz ∗
      ⌜sint.Z s = max (w.m.size : Int) (sint.Z minsz)⌝) with [size minsz] as ⟨%sz0, size, minsz, %Hsz0⟩
  · iexists minsz; iframe; ipureintro; omega
  · iexists _; iframe; ipureintro; omega
  wp_apply hMmapSize K.db sz0 (by omega) as %nsz %err2 Hms
  · iframe #
  try wp_auto
  irevert Hms
  rcases hmo : mmapSizeOf (sint.nat sz0) with _ | L'
  · -- `mmapSize` failed: logged, returned
    iintro ⟨%hne, #HeS⟩
    cases err2 with
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
    have Hpt := hne.2
    ihave Hdb := Hdbback $$ [Hfile Hfo Hfd Hosm]
    · iframe
    iapply HΦ
    iframe Hpm
    iright
    iframe HeS
    isplitr
    · ipureintro; exact ⟨(fun h => nomatch h), Hpt⟩
    ileft; iframe
  iintro %Hms
  obtain ⟨rfl, hnsz⟩ := Hms
  try wp_auto
  rw [hgoos]
  wp_join with [size fileSize db]
  · try wp_auto
    wp_if_destruct
    all_goals try wp_auto
    all_goals try wp_if_destruct
    all_goals try wp_auto
    all_goals try wp_join_done
  -- `dereference` (steps 4-5): the writer's records off the mapping
  ihave Hdb := Hdbback $$ [Hfile Hfo Hfd Hosm]
  · iframe
  unfold wdbW' wdbLive wdbCoreG
  icases Hdb with ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath, Hdsz,
    Hmfw, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩, Hflo, Hrd, Hrcpt⟩, -, %F, Htok⟩
  ihave %Htx := wtxW_tx_ne K tx r m X $$ Hw
  try wp_auto
  rw [decide_eq_false Htx.1]
  try wp_auto
  wp_apply hDeref K tx r m X hdp hlf hlr $$ [Hw] as ⟨%Xd, Hw, %hrel⟩
  · iframe
  try wp_auto
  -- the gather (step 5): every cell of the old mapping back, the store's slots out
  have hXd : Xd.v = X.v := hrel.2.1
  obtain ⟨b0, L, hmsL⟩ : ∃ b0 L, w.ms = some (b0, L) := ⟨_, _, hms⟩
  have hb0 : X.v.base = b0 := by
    rw [hmsL] at hms; exact (Prod.mk.inj (Option.some.inj hms)).1.symm
  have hok' := hok
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9, hk10, hk11, hk12⟩ := hok'
  have hL8 : 8192 ≤ L := by
    by_cases h : L ≤ 0x1000000
    · have := hk10 b0 L hmsL h; omega
    · omega
  icases (wtxW_unf K tx r m Xd).1 $$ Hw with ⟨Hwc0, Hvc, %l, Hmft, %hpb⟩
  icases (Pm_unf K.B K.db 1).1 $$ Hpm with ⟨%ms, Hpmap, Hpmf, Hptok⟩
  icombine Hgmap Hpmap gives % ⟨_, hmsE⟩
  subst hmsE
  rw [Htx.2, hmsL]
  icases mapFields_agree K.db _ _ _ _ _ _ $$ [Hmft Hmfw] with ⟨%hag, Hmft, Hmfw⟩
  · iframe
  obtain ⟨hb0', rfl⟩ := hag
  icases mapFields_pure K.db _ _ _ $$ Hmfw with ⟨%hal, Hmfw⟩
  rw [hXd] at hpb
  ihave Hmft : mapFields K.db (DFrac.own (1 : Qp).half.half) (some (b0, l) : MapSt) $$ [Hmft]
  · rw [← hb0', hXd]; iexact Hmft
  ihave Hvc : viewCells wq X.v $$ [Hvc]
  · rw [← hXd]; iexact Hvc
  imod remap_gather K.B K.N K.p X.v w b0 l hok hmsL hL8 $$ Hpinv Hvc Hcur Hgfl Hgmap Hpmap Hptok
    Hgwv Hgout Hmc Hwc with ⟨⟨%vf, Hcells⟩, %bs, %W, Hcur, Hgfl, Hgmap, Hpmap, Hptok, Hgwv, Hgout,
      Hbyt, %hgat⟩
  icases (mapFields_join K.db (some (b0, l))).1 $$ [Hmft Hmfw Hpmf] with Hmf1
  · isplitl [Hmft]
    · iexact Hmft
    isplitl [Hmfw]
    · iexact Hmfw
    · iexact Hpmf
  have hmap0 : w.m.maps !! b0 = some l := by rw [hk1 b0 l hmsL]; exact GMap.lookup_singleton _ _
  simp only [mapLen]
  wp_apply hMunmap K.db b0 l (GoInterface.ok li) K.p w.m vf Hdb (by omega) hmap0
    $$ [Hmf1 Hdsz Hosm Hcells] as %e ⟨Hmf0, Hdsz, Hun⟩
  · iframe; iframe #
  have hv' : (Xd.rebase Xd.v.base).v = X.v := by
    show { Xd.v with base := Xd.v.base } = X.v
    rw [View.with_base_self Xd.v, hXd]
  icases Hun with (⟨%he, Hosm⟩ | ⟨%he, #HeS, Hun⟩)
  rotate_left
  · -- `munmap` failed: the mapping lost (or leaked)
    cases e with
    | nil => exact absurd rfl he.1
    | ok ii =>
    try wp_auto
    icases (mapFields_join K.db none).2 $$ Hmf0 with ⟨Hm1, Hm2, Hm3⟩
    have Hpt := he.2
    ihave Hwl := remap_lostX K tx r m Xd hrel.1 $$ [Hwc0 Hm1]
    · iframe
    ihave Hgwv : ghostVar K.B.wv (1 : Qp).half
        ((some (Xd.rebase Xd.v.base).v, some (w.C.txid + 1), false, false) : WSt) $$ [Hgwv]
    · rw [hv']; iexact Hgwv
    icases Hun with (Hosm | ⟨Hosm, Hcells⟩)
    · ihave Hwd := wdbLost'_intro fr K tx (Xd.rebase Xd.v.base).v w hok X.v F
        { w.m with maps := GMap.delete b0 w.m.maps } none rfl
        (Or.inl (by rw [hk1 b0 l hmsL]; exact GMap.delete_singleton _ _))
        $$ Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmob Hwb
          [] Hflo Hrd Hrcpt Htok
      · simp only [junkRes]; iempintro
      iapply HΦ
      isplitl [Hpmap Hm3 Hptok]
      · iapply (Pm_unf K.B K.db 1).2; iexists none; iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => nomatch h), Hpt⟩
      iframe HeS
      iright
      iexists Xd, Xd.v.base, _
      iframe Hwl Hwd
      ipureintro; exact ⟨hrel, rfl, rfl⟩
    · ihave Hwd := wdbLost'_intro fr K tx (Xd.rebase Xd.v.base).v w hok X.v F w.m (some (b0, l)) rfl
        (Or.inr ⟨b0, l, rfl, hk1 b0 l hmsL⟩)
        $$ Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmob Hwb
          [Hcells] Hflo Hrd Hrcpt Htok
      · simp only [junkRes]; iexists vf; iexact Hcells
      iapply HΦ
      isplitl [Hpmap Hm3 Hptok]
      · iapply (Pm_unf K.B K.db 1).2; iexists none; iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => nomatch h), Hpt⟩
      iframe HeS
      iright
      iexists Xd, Xd.v.base, _
      iframe Hwl Hwd
      ipureintro; exact ⟨hrel, rfl, rfl⟩
  subst he
  try wp_auto
  have hL'p := mmapSizeOf_props _ _ hmo
  have hnszZ : sint.Z nsz = (L' : Int) := by
    have : sint.nat nsz = (sint.Z nsz).toNat := rfl
    have h0 : 0 ≤ sint.Z nsz := by omega
    omega
  simp only [mapFields]
  icases Hmf0 with ⟨Hdr, Hdd, Hm0f, Hm1f⟩
  wp_apply hMmapF K.db w.f w.fd K.p (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) mf
    { w.m with maps := GMap.delete b0 w.m.maps } nsz slice.nil null (W64 0) Hmf
    (by simp only [sint.Z] at hnszZ; omega) $$ [Hfile Hfo Hfd Hosm Hdr Hdd Hdsz]
    as %e ⟨Hfile, Hfo, Hfd, Hres⟩
  · iframe; iframe #
  have hmaps1 : (GMap.delete b0 w.m.maps) = ∅ := by
    rw [hk1 b0 l hmsL]; exact GMap.delete_singleton _ _
  icases Hres with (⟨%base, %hbase, Hdr, Hdd, Hdsz, Hosm, Hmc⟩ | ⟨Hdr, Hdd, Hdsz, %he, #HeS, Hres⟩)
  rotate_left
  · -- `mmap` failed: the mapping lost (or leaked by `Madvise`)
    cases e with
    | nil => exact absurd rfl he.1
    | ok ii =>
    rw [hgoarch]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
      show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl, List.set_cons_succ, List.set_cons_zero]
    wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 100, W8 118] _
      [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
        interface.mkOk go.int #nsz, GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    have Hpt := he.2
    ihave Hmf0 : mapFields K.db (DFrac.own 1) (none : MapSt) $$ [Hdr Hdd Hm0f Hm1f]
    · simp only [mapFields]; iframe
    icases (mapFields_join K.db none).2 $$ Hmf0 with ⟨Hm1, Hm2, Hm3⟩
    ihave Hwl := remap_lostX K tx r m Xd hrel.1 $$ [Hwc0 Hm1]
    · iframe
    ihave Hgwv : ghostVar K.B.wv (1 : Qp).half
        ((some (Xd.rebase Xd.v.base).v, some (w.C.txid + 1), false, false) : WSt) $$ [Hgwv]
    · rw [hv']; iexact Hgwv
    icases Hres with (Hosm | ⟨%base, %hbase, Hosm, Hmc⟩)
    · ihave Hwd := wdbLost'_intro fr K tx (Xd.rebase Xd.v.base).v w hok X.v F
        { w.m with maps := GMap.delete b0 w.m.maps } none rfl (Or.inl hmaps1)
        $$ Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmob Hwb
          [] Hflo Hrd Hrcpt Htok
      · simp only [junkRes]; iempintro
      iapply HΦ
      isplitl [Hpmap Hm3 Hptok]
      · iapply (Pm_unf K.B K.db 1).2; iexists none; iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => nomatch h), Hpt⟩
      iframe HeS
      iright
      iexists Xd, Xd.v.base, _
      iframe Hwl Hwd
      ipureintro; exact ⟨hrel, rfl, rfl⟩
    · ihave Hwd := wdbLost'_intro fr K tx (Xd.rebase Xd.v.base).v w hok X.v F
        { { w.m with maps := GMap.delete b0 w.m.maps } with
          maps := <[base := nsz.toNat]> (GMap.delete b0 w.m.maps) } (some (base, nsz.toNat)) rfl
        (Or.inr ⟨base, nsz.toNat, rfl, by rw [hmaps1]; exact GMap.insert_empty _ _⟩)
        $$ Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmob Hwb
          [Hmc] Hflo Hrd Hrcpt Htok
      · simp only [junkRes]; unfold mapCells; icases Hmc with ⟨%bs', -, Hc⟩; iexists _; iexact Hc
      iapply HΦ
      isplitl [Hpmap Hm3 Hptok]
      · iapply (Pm_unf K.B K.db 1).2; iexists none; iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => nomatch h), Hpt⟩
      iframe HeS
      iright
      iexists Xd, Xd.v.base, _
      iframe Hwl Hwd
      ipureintro; exact ⟨hrel, rfl, rfl⟩

  obtain ⟨rfl, hbpos⟩ := hbase
  iclear Hmlk
  wp_auto
  -- the carve (step 7), around the first step of the `Mlock` load
  icases BC.core_mmapFields K $$ Hcore with ⟨-, #Hmlk, -⟩
  ihave %hdisj := core_osN_disj K $$ Hcore
  have hE' : (↑osN : CoPset) ⊆ ⊤ \ ↑(pagesN K.N) := fun x hx =>
    CoPset.in_diff.2 ⟨CoPset.subseteq_top x hx, fun hp => hdisj x ⟨hx, hp⟩⟩
  have hLn : nsz.toNat = L' := by
    have h1 := hnszZ
    simp only [sint.Z] at h1
    rw [BitVec.toInt_eq_toNat_cond] at h1
    split at h1 <;> omega
  have hll : l ≤ L' := by
    have h1 : (L' : Int) ≥ sint.Z sz0 := by
      have := hL'p.1; have e : sint.nat sz0 = (sint.Z sz0).toNat := rfl; omega
    have e2 : sint.nat minsz = (sint.Z minsz).toNat := rfl
    have h3 : mapLen w.ms = l := by rw [hmsL]; rfl
    have h4 : sint.Z minsz ≤ sint.Z sz0 := by rw [Hsz0]; exact Int.le_max_right _ _
    omega
  have hsl' : ∀ s ∈ slotsOf w.C w.fl, 2 ≤ s ∧ s < L' / 4096 := fun s hs =>
    ⟨(hgat.2.2 s hs).1, Nat.lt_of_lt_of_le (hgat.2.2 s hs).2 (Nat.div_le_div_right hll)⟩
  have hP' := slots_partition (L' / 4096) (slotsOf w.C w.fl) (wSlots (L' / 4096) w.C w.fl)
    (by have := hL'p.2.1; omega) (slotsOf_nodup _ _) (wSlots_nodup _ _ _) hsl'
    (fun s => by rw [mem_wSlots])
  have hb2 : ({ { w.m with maps := GMap.delete b0 w.m.maps } with
      maps := <[base := L']> (GMap.delete b0 w.m.maps) } : OsMeta).maps !! base = some L' :=
    GMap.lookup_insert _ _ _
  unfold mapCells
  icases Hmc with ⟨%bs', -, Hc⟩
  rw [hLn]
  icases mapCells_scatter base L' _ _ _ hP' $$ Hc with ⟨Hc01, HS, Hws, Hpart⟩
  wp_bind (App (Val (GoInstruction (GoLoad go.bool))) (Val #(K.db.[DB, go!"Mlock"])))
  iapply wp_load_bool_split
  iapply (store_cells_agree K.B K.N K.p ⊤ CoPset.subseteq_top _
    (StartRead (Val #(K.db.[DB, go!"Mlock"]))) rfl inferInstance hE' w.C w.fl
    _ base L' _ (DFrac.own 1) W hb2 (fun s hs => (hsl' s hs).2) _)
    $$ Hpinv Hos Hcur Hgfl Hgmap Hgwv Hbyt Hosm HS
  iintro %bs2 %hW2 Hcur Hgfl Hgmap Hgwv Hbyt Hosm HS
  unfold metaOsBytes
  icases Hmob with ⟨%xs, Hxs, %hxs⟩
  have hxl : xs.length = 8192 := by
    have := congrArg List.length hxs
    simp only [List.length_map, List.length_append] at this
    rw [this, hgat.2.1.1, hgat.2.1.2.1]
  rw [← hxl]
  iapply cellsR_agree_bytes _ rfl K.p (DFrac.own 1) _ base L' hb2 _
    hE' _ xs 0 _ (by omega) $$ Hos Hosm Hxs Hc01
  iintro Hosm Hxs Hcm
  -- the metas' bytes at the new mapping, at a half
  have hm0 := hgat.2.1.1
  have hm1 := hgat.2.1.2.1
  ihave Hmb : bytesPointsto base (DFrac.own (1 : Qp).half) (w.C.m0 ++ w.C.m1) $$ [Hcm]
  · rw [← hxs]
    have e := cellsR_bytes (GF := GF) base (xs.map Prod.fst) 0
    rw [List.length_map, Int.natCast_zero, loc_add_0] at e
    iapply e $$ Hcm
  icases (bytesPointsto_app base _ w.C.m0 w.C.m1).1 $$ Hmb with ⟨H0, H1⟩
  rw [hm0]
  icases (bytes_quarters base w.C.m0).2 $$ H0 with ⟨H0a, H0b⟩
  icases (bytes_quarters _ w.C.m1).2 $$ H1 with ⟨H1a, H1b⟩
  -- the step
  ihave Hml := bool_heap _ _ _ $$ Hmlk
  iapply (wp_start_read _ _ _) $$ [Hml]
  · iexact Hml
  inext
  iintro ⟨Hst, Hrest⟩
  -- the store's cells back (`store_carve`), the view re-borrowed (`store_wborrow`)
  imod store_carve K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl base L' _ bs2 W
    (fun s hs => (hsl' s hs).2) hW2 $$ [Hpinv Hcur Hgfl Hgmap Hpmap Hptok Hgwv Hbyt HS H0a H1a]
    with ⟨Hcur, Hgfl, Hgmap, Hpmap, Hptok, Hgwv⟩
  · isplitr
    · iexact Hpinv
    isplitl [Hcur]
    · iexact Hcur
    isplitl [Hgfl]
    · iexact Hgfl
    isplitl [Hgmap]
    · iexact Hgmap
    isplitl [Hpmap]
    · iexact Hpmap
    isplitl [Hptok]
    · iexact Hptok
    isplitl [Hgwv]
    · iexact Hgwv
    isplitl [Hbyt]
    · iexact Hbyt
    isplitl [HS]
    · iexact HS
    · simp only [metaCellsQ]
      iframe H0a
      iexact H1a
  imod store_wborrow K.B K.N K.p ⊤ CoPset.subseteq_top X.v (some (w.C.txid + 1)) false base L'
    $$ [Hpinv Hgwv Hgmap] with ⟨Hgwv, Hgmap, Hvc⟩
  · isplitr
    · iexact Hpinv
    isplitl [Hgwv]
    · iexact Hgwv
    · iexact Hgmap
  wp_pures
  wp_bind (FinishRead _)
  iapply (wp_finish_read _ _ _) $$ [Hst Hrest]
  · iframe
  inext
  iintro -
  wp_pures
  wp_auto
  -- the metas (step 8): `db.meta0/1 = db.page(0/1).Meta()`, both `Validate`d
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  have hm0ne : w.C.m0 ≠ [] := fun h => by rw [h] at hm0; simp at hm0
  have hm1ne : w.C.m1 ≠ [] := fun h => by rw [h] at hm1; simp at hm1
  icases bytes_bounds_keep base _ w.C.m0 hm0ne $$ H0b with ⟨%Hb0, H0b⟩
  icases bytes_bounds_keep _ _ w.C.m1 hm1ne $$ H1b with ⟨%Hb1, H1b⟩
  rw [hm0] at Hb0
  rw [hm1] at Hb1
  replace Hb1 : 0 < (base +ₗ (4096 : Int)).addr ∧ (base +ₗ (4096 : Int)).addr + 4096 ≤ maxAddr := Hb1
  wp_apply hPage K.db base (W64 0) (DFrac.own 1) hbpos (by decide) $$ [Hdd] as Hdd
  · iframe; iframe #
  rw [show (((0 * 4096 : Nat)) : Int) = 0 from rfl, loc_add_0]
  wp_apply hMeta base hbpos (by omega)
  try wp_auto
  wp_apply hPage K.db base (W64 1) (DFrac.own 1) hbpos (by decide) $$ [Hdd] as Hdd
  · iframe; iframe #
  rw [show (((1 * 4096 : Nat)) : Int) = 4096 from rfl]
  wp_apply hMeta (base +ₗ (4096 : Int)) Hb1.1 (by omega)
  try wp_auto
  have e0 : base +ₗ (16 : Int) = base +ₗ ((16 : Nat) : Int) := by simp
  have hl0' : 16 + 64 ≤ w.C.m0.length := by omega
  have hl1' : 16 + 64 ≤ w.C.m1.length := by omega
  icases bytesPointsto_view_read (V := Meta) base _ w.C.m0 16 _ e0 hl0' hbpos $$ H0b with ⟨M0, C0⟩
  have e1 : base +ₗ (4096 : Int) +ₗ (16 : Int) = base +ₗ (4096 : Int) +ₗ ((16 : Nat) : Int) := by simp
  icases bytesPointsto_view_read (V := Meta) (base +ₗ (4096 : Int)) _ w.C.m1 16 _ e1 hl1' Hb1.1
    $$ H1b with ⟨M1, C1⟩
  rw [show (decode ((w.C.m0.drop 16).take 64) : Meta) = metaOf w.C.m0 from rfl,
    show (decode ((w.C.m1.drop 16).take 64) : Meta) = metaOf w.C.m1 from rfl]
  have hpA : 0 < (base +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
  have hpB : 0 < (base +ₗ (4096 : Int) +ₗ (16 : Int)).addr := by
    simp only [Loc.add] at Hb1 ⊢; omega
  wp_apply hValidate _ (metaOf w.C.m0) (DFrac.own (1 : Qp).half.half) hpA $$ [M0]
    as %ev0 ⟨M0, %He0⟩
  · iframe
  try wp_auto
  wp_apply hValidate _ (metaOf w.C.m1) (DFrac.own (1 : Qp).half.half) hpB $$ [M1]
    as %ev1 ⟨M1, %He1⟩
  · iframe
  try wp_auto
  -- the current meta is valid (`metaOk`): not both invalid
  have hval : metaValid (metaOf w.C.m0) ∨ metaValid (metaOf w.C.m1) := by
    have h := hgat.2.1.2.2.2.2.2.1
    unfold CommitSt.slot at h
    split at h
    · exact .inl h
    · exact .inr h
  have hnszE : nsz = W64 (L' : Int) := by
    apply BitVec.toInt_inj.mp
    have : sint.Z (W64 (L' : Int)) = (L' : Int) := by
      have := hL'p.2.2.1; word
    simp only [sint.Z] at this hnszZ
    rw [hnszZ, this]
  have hfile : w.m.size ≤ L' := by
    have := hL'p.1; have e : sint.nat sz0 = (sint.Z sz0).toNat := rfl
    have h4 : (w.m.size : Int) ≤ sint.Z sz0 := by rw [Hsz0]; exact Int.le_max_left _ _
    omega
  have hminL : sint.nat minsz ≤ L' := by
    have := hL'p.1; have e : sint.nat sz0 = (sint.Z sz0).toNat := rfl
    have e2 : sint.nat minsz = (sint.Z minsz).toNat := rfl
    have h4 : sint.Z minsz ≤ sint.Z sz0 := by rw [Hsz0]; exact Int.le_max_right _ _
    omega
  cases ev0 with
  | nil =>
    ihave H0b := C0 $$ M0
    ihave H1b := C1 $$ M1
    ihave Hmf : mapFields K.db (DFrac.own 1) (some (base, L') : MapSt) $$ [Hdr Hdd Hm0f Hm1f]
    · simp only [mapFields]
      try rw [← hnszE]
      rw [show base +ₗ (4112 : Int) = base +ₗ (4096 : Int) +ₗ (16 : Int) by rw [loc_add_assoc]; rfl]
      iframe
      ipureintro; exact ⟨hL'p.2.2.1, hbpos, hL'p.2.2.2⟩
    ihave Hmob : metaOsBytes K.p (DFrac.own (1 : Qp).half) w.C $$ [Hxs]
    · unfold metaOsBytes; iexists xs; iframe; ipureintro; exact hxs
    ihave Hwcn := wCells_carve w.C w.fl base L' (max L' w.m.size / 4096)
      (Nat.div_le_div_right (Nat.le_max_left _ _)) $$ [Hws Hpart]
    · iframe
    try rw [hnszE]
    imod remap_post' fr K tx r m X Xd w hok F b0 base l L'
      { { w.m with maps := GMap.delete b0 w.m.maps } with
        maps := <[base := L']> (GMap.delete b0 w.m.maps) } hrel.1 hXd hv Htx.2 hmsL hll hal hL'p.2.2.1
      rfl (by rw [hmaps1]; exact GMap.insert_empty _ _) hfile hpb
      $$ Hwc0 Hvc Hmf Hpmap Hptok Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hosm
        Hfo Hfd [H0b H1b] Hmob Hwcn Hwb [Hjunk] Hflo Hrd Hrcpt Htok with ⟨Hpm, Hw, Hdb⟩
    · simp only [metaCellsQ]; iframe H0b; iexact H1b
    · unfold junkRes; iexact Hjunk
    try wp_auto
    iapply HΦ
    iframe Hpm
    ileft
    isplitr
    · ipureintro; rfl
    iexists Xd, base, w.remap base L' { { w.m with maps := GMap.delete b0 w.m.maps } with
        maps := <[base := L']> (GMap.delete b0 w.m.maps) }
    iframe Hw
    unfold wdbW' wdbLive wdbCoreG
    icases Hdb with ⟨⟨⟨Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7, Hd8, Hd9, Hd10, Hd11, Hd12, Hd13, Hd14,
      Hd15, Hd16, Hd17, Hd18, Hd19, Hd20, Hd21⟩, Hd22, Hd23, Hd24⟩, %Hdp, Hd25⟩
    isplitl
    · simp only [WDb.remap, mapFields, metaOsBytes]
      iframe
      ipureintro
      simp only [WDb.remap, mapLen] at Hdp ⊢
      exact Hdp
    ipureintro
    refine ⟨hrel, wdbRemap_remap' fr w hok base L' _ rfl (by rw [hmsL]; exact hll), ?_⟩
    simp only [WDb.remap, mapLen]
    exact hminL
  | ok i0 =>
    have hv1 : metaValid (metaOf w.C.m1) := by
      rcases hval with h | h
      · exact absurd (He0.2 h) (fun e => nomatch e)
      · exact h
    have he1 : ev1 = GoInterface.nil := He1.2 hv1
    subst he1
    ihave H0b := C0 $$ M0
    ihave H1b := C1 $$ M1
    ihave Hmf : mapFields K.db (DFrac.own 1) (some (base, L') : MapSt) $$ [Hdr Hdd Hm0f Hm1f]
    · simp only [mapFields]
      try rw [← hnszE]
      rw [show base +ₗ (4112 : Int) = base +ₗ (4096 : Int) +ₗ (16 : Int) by rw [loc_add_assoc]; rfl]
      iframe
      ipureintro; exact ⟨hL'p.2.2.1, hbpos, hL'p.2.2.2⟩
    ihave Hmob : metaOsBytes K.p (DFrac.own (1 : Qp).half) w.C $$ [Hxs]
    · unfold metaOsBytes; iexists xs; iframe; ipureintro; exact hxs
    ihave Hwcn := wCells_carve w.C w.fl base L' (max L' w.m.size / 4096)
      (Nat.div_le_div_right (Nat.le_max_left _ _)) $$ [Hws Hpart]
    · iframe
    try rw [hnszE]
    imod remap_post' fr K tx r m X Xd w hok F b0 base l L'
      { { w.m with maps := GMap.delete b0 w.m.maps } with
        maps := <[base := L']> (GMap.delete b0 w.m.maps) } hrel.1 hXd hv Htx.2 hmsL hll hal hL'p.2.2.1
      rfl (by rw [hmaps1]; exact GMap.insert_empty _ _) hfile hpb
      $$ Hwc0 Hvc Hmf Hpmap Hptok Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hosm
        Hfo Hfd [H0b H1b] Hmob Hwcn Hwb [Hjunk] Hflo Hrd Hrcpt Htok with ⟨Hpm, Hw, Hdb⟩
    · simp only [metaCellsQ]; iframe H0b; iexact H1b
    · unfold junkRes; iexact Hjunk
    try wp_auto
    iapply HΦ
    iframe Hpm
    ileft
    isplitr
    · ipureintro; rfl
    iexists Xd, base, w.remap base L' { { w.m with maps := GMap.delete b0 w.m.maps } with
        maps := <[base := L']> (GMap.delete b0 w.m.maps) }
    iframe Hw
    unfold wdbW' wdbLive wdbCoreG
    icases Hdb with ⟨⟨⟨Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7, Hd8, Hd9, Hd10, Hd11, Hd12, Hd13, Hd14,
      Hd15, Hd16, Hd17, Hd18, Hd19, Hd20, Hd21⟩, Hd22, Hd23, Hd24⟩, %Hdp, Hd25⟩
    isplitl
    · simp only [WDb.remap, mapFields, metaOsBytes]
      iframe
      ipureintro
      simp only [WDb.remap, mapLen] at Hdp ⊢
      exact Hdp
    ipureintro
    refine ⟨hrel, wdbRemap_remap' fr w hok base L' _ rfl (by rw [hmsL]; exact hll), ?_⟩
    simp only [WDb.remap, mapLen]
    exact hminL


end body

end bbolt
end EtcdGrove
end Perennial
