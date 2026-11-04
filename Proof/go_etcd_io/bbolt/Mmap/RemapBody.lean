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
public import Proof.go_etcd_io.bbolt.Mmap.RemapLost
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
post, `Pm 1` back. -/
abbrev DB.mmapUnlocked.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (minsz : w64),
  0 < sint.Z minsz → mapLen w.ms ≤ sint.nat minsz → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w ∗ Pm K.B K.db 1 }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"mmapUnlocked")) (Val #minsz))
  {{ (err : GoInterface), RET #err; Pm K.B K.db 1 ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (Xd : WX) (b : Loc) (w' : WDb),
        wtxW K tx r m (Xd.rebase b) ∗ wdbW K tx (Xd.rebase b).v w' ∗
        ⌜derefRel X Xd ∧ wdbRemap w w' ∧ sint.nat minsz ≤ mapLen w'.ms⌝) ∨
      (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW K tx X.v w) ∨
         (∃ (Xd : WX) (b : Loc) (w' : WDb), wtxLost K tx r m (Xd.rebase b) ∗
           wdbLost K tx (Xd.rebase b).v w' ∗
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
theorem wdbW_file_acc (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ (K.db.[DB, go!"file"] ↦ w.f ∗ fileOwn w.f w.fd K.p (DFrac.own 1) ∗
        osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗ osMeta K.p (DFrac.own 1) (some w.m)) ∗
      ((K.db.[DB, go!"file"] ↦ w.f ∗ fileOwn w.f w.fd K.p (DFrac.own 1) ∗
        osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗ osMeta K.p (DFrac.own 1) (some w.m)) -∗
        wdbW K tx v w) ∗ ⌜wdbOK w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝ := by
  unfold wdbW wdbLive wdbCoreG
  iintro ⟨⟨⟨%wa, Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf,
    Hosm, Hfo, Hfd, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok⟩
  iframe Hfile Hfo Hfd Hosm
  isplitl
  · iintro ⟨Hfile, Hfo, Hfd, Hosm⟩
    isplitl
    · iframe
    · ipureintro; exact Hwok
  · ipureintro; exact Hwok

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
  intro K tx r m X w minsz hmin hmL hdp hlf hlr
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
  icases wdbW_file_acc K tx X.v w $$ Hdb with ⟨⟨Hfile, Hfo, Hfd, Hosm⟩, Hdbback, %Hwok⟩
  obtain ⟨hok, hms, hv⟩ := Hwok
  wp_apply hFileSize K.db w.f w.fd K.p (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    ⟨K.p, true, true⟩ w.m rfl (wdbOK_size_lt w hok) $$ [Hfile Hfo Hfd Hosm]
    as %fsz %err ⟨Hfile, Hfo, Hfd, Hosm, Hfs⟩
  · iframe; iframe #
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlgok
  | ok li =>
  icases Hfs with (%Hfs | ⟨%hne, #HeS⟩)
  rotate_left
  · -- `fileSize` failed: logged, returned
    cases err with
    | nil => exact absurd rfl hne
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
    ihave %Hpt := fmtErrorOk_errPtrTyped _ $$ HeS
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
  have hszlt := wdbOK_size_lt w hok
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
    | nil => exact absurd rfl hne
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
    ihave %Hpt := fmtErrorOk_errPtrTyped _ $$ HeS
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
  unfold wdbW wdbLive wdbCoreG
  icases Hdb with ⟨⟨⟨%wa, Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hopen, Hwa, Hrw, Hfile, Hpath, Hdsz,
    Hmfw, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩, Hflo, Hrd, Hrcpt⟩, -⟩
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
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9, hk10, hk11⟩ := hok'
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
  icases (mapFields_join K.db none).2 $$ Hmf0 with ⟨Hm1, Hm2, Hm3⟩
  icases Hun with (⟨%he, Hosm⟩ | ⟨%he, #HeS, Hun⟩)
  rotate_left
  · -- `munmap` failed: the mapping lost (or leaked)
    cases e with
    | nil => exact absurd rfl he
    | ok ii =>
    try wp_auto
    ihave %Hpt := fmtErrorOk_errPtrTyped _ $$ HeS
    ihave Hwl := remap_lostX K tx r m Xd hrel.1 $$ [Hwc0 Hm1]
    · iframe
    ihave Hgwv : ghostVar K.B.wv (1 : Qp).half
        ((some (Xd.rebase Xd.v.base).v, some (w.C.txid + 1), false, false) : WSt) $$ [Hgwv]
    · rw [hv']; iexact Hgwv
    icases Hun with (Hosm | ⟨Hosm, Hcells⟩)
    · ihave Hwd := wdbLost_intro K tx (Xd.rebase Xd.v.base).v w hok
        { w.m with maps := GMap.delete b0 w.m.maps } none rfl
        (Or.inl (by rw [hk1 b0 l hmsL]; exact GMap.delete_singleton _ _)) wa
        $$ Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmob Hwb
          [] Hflo Hrd Hrcpt
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
    · ihave Hwd := wdbLost_intro K tx (Xd.rebase Xd.v.base).v w hok w.m (some (b0, l)) rfl
        (Or.inr ⟨b0, l, rfl, hk1 b0 l hmsL⟩) wa
        $$ Hcur Hgfl Hgmap Hgout Hgwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmob Hwb
          [Hcells] Hflo Hrd Hrcpt
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
  sorry

end body

end bbolt
end EtcdGrove
end Perennial
