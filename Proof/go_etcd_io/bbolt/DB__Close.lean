/-
The proof of `Spec/go_etcd_io/bbolt/DB__Close.lean` (session bbolt-inv's `Close_own`, canonical since S3f): `DB.Close`'s proof
(`DB__Close.lean`) with the file kept. Closed already: given up (`closedR`'s `nf`), or given back by
an earlier `Close_own` (`closedR` holds `bq`, which the caller's `boltState` excludes). Open: when
the file system can fail (`¬ FsNoErr`) `close` runs as in `DB.Close`; otherwise with no error
(`DB.close.spec_ownedNoErrM`), the `OsMeta` back without the mapping, the store slots' bytes taken
(`store_close`), and with the metas and the writer side's `W` slots the file's bytes
(`close_file_bytes`), an image of the committed state (`closeBytes_fileOK`), whole pages and at
most `maxMapSize` (`wdbSz`, session S3g: `fileHoldsM`); a leaked mapping (the junk clause) recorded
`¬ FsNoErr`, refuted here.
-/
module

public import Spec.go_etcd_io.bbolt.DB__Close
public import Proof.go_etcd_io.bbolt.Open.CloseTok
public import Proof.go_etcd_io.bbolt.Open.CloseFile
public import Proof.go_etcd_io.bbolt.Open.Congr
public import Proof.go_etcd_io.bbolt.Open.CloseFlx
public import Proof.go_etcd_io.bbolt.Inv.PmFile
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]

/-- `close_res` with the file's `OsMeta` named (`closeMapResM`; nothing mapped: kept). -/
private theorem close_resM (B : BNs) (N : Namespace) (p : BFile) (w : WDb) (hok : wdbOK w)
    (hL : ∀ b l, w.ms = some (b, l) → 8192 ≤ l) (hns : bNsOk p) :
    ⊢ inv (pagesN N) (pagesInv (GF := GF) B p) -∗ bCsInv p -∗
      ghostVar B.cur (1 : Qp).half.half w.C -∗ ghostVar B.fl (1 : Qp).half w.fl -∗
      ghostVar B.map (1 : Qp).half w.ms -∗ ghostVar B.map (1 : Qp).half.half w.ms -∗
      ghostVar B.mtok 1 () -∗
      ghostVar B.wv (1 : Qp).half wIdle -∗ ghostVar B.out (1 : Qp).half false -∗
      metaCellsQ (GF := GF) (1 : Qp).half.half w.ms w.C -∗
      wCells (GF := GF) w.ms w.W -∗ bMeta p w.C [] w.m -∗
    |={⊤}=> closeMapResM (GF := GF) p w.C [] w.m w.ms ∗ closeKeep (GF := GF) p w.C [] w.m w.ms ∗
      ghostVar B.cur (1 : Qp).half.half w.C ∗ ghostVar B.fl (1 : Qp).half w.fl ∗
      ghostVar B.map (1 : Qp).half (none : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostVar B.out (1 : Qp).half false := by
  iintro #Hinv #Hci Hcur Hfl Hmap Hmapq Htok Hwv Hout Hmc Hwc Hosm
  rcases hms : w.ms with _ | ⟨b, l⟩
  · simp only [closeMapResM, closeKeep]
    imodintro
    isplitr
    · iempintro
    isplitl [Hosm]
    · iexact Hosm
    iframe Hcur Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hmapq]
    · iexact Hmapq
    iframe
  · imod close_gather B N p w b l hok hms (hL b l hms) $$ Hinv Hcur Hfl Hmap Hmapq Htok Hwv Hout
      Hmc Hwc with ⟨⟨%vf, Hc⟩, Hcur, Hfl, Hmap, Hmapq, Htok, Hwv, Hout⟩
    imodintro
    simp only [closeMapResM, closeKeep]
    isplitl [Hosm Hc]
    · isplitr
      · ipureintro
        refine ⟨by have := hL b l hms; omega, ?_, hns⟩
        rw [hok.1 b l hms]; exact GMap.lookup_singleton _ _
      iframe Hci
      isplitl [Hosm]
      · iexact Hosm
      · iexists vf; iexact Hc
    isplitr
    · iempintro
    iframe Hcur Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hmapq]
    · iexact Hmapq
    iframe

/-- The file's `OsMeta` after `close`: no mapping (the idle writer side's, `wdbOK`, with no leaked
mapping), the size kept. -/
private theorem close_meta (p : BFile) (w : WDb) (hok : wdbOK w) (hj : w.junk = none) :
    closeMapBack (GF := GF) p w.C [] w.m w.ms ∗ closeKeep (GF := GF) p w.C [] w.m w.ms ⊢
    ∃ m : OsMeta, bMeta p w.C [] m ∗ ⌜m.maps = ∅ ∧ m.size = w.m.size⌝ := by
  rcases hms : w.ms with _ | ⟨b, l⟩
  · simp only [closeMapBack, closeKeep]
    iintro ⟨-, Hm⟩
    iexists w.m
    iframe Hm
    ipureintro
    refine ⟨?_, rfl⟩
    rcases hok.2.1 hms with h | ⟨jb, jl, hj', -⟩
    · exact h
    · rw [hj] at hj'; cases hj'
  · simp only [closeMapBack, closeKeep]
    iintro ⟨Hm, -⟩
    iexists _
    iframe Hm
    ipureintro
    refine ⟨?_, rfl⟩
    show GMap.delete b w.m.maps = ∅
    rw [hok.1 b l hms]; exact GMap.delete_singleton _ _

omit [ExtSemantics fsExt] [FsSemOk] hos in
theorem DB.Close.wp_proof
    (hOwned : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_owned (GF := GF) (hG := hG))
    (hOwnedM : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_ownedNoErrM (GF := GF) (hG := hG)) :
    DB.Close.spec (GF := GF) (hG := hG) := by
  intro _ _ _ db γ i D
  wp_start as ⟨#Hdb, #Hino, Hst, Hclo⟩
  iunfold boltCloser at Hclo
  unfold isBolt isBoltDef isBoltP
  icases Hdb with ⟨%p, %sp, %t0, #Hcore, #Hrw, -⟩
  -- the inode
  ihave %hi : ⌜p.ino = i⌝ $$ []
  · unfold boltIno
    icases Hino with ⟨%t0', #Ht⟩
    iapply isBoltCoreP_ino _ _ _ _ _ _ _ _ $$ [Hcore Ht]
    iframe #
  subst hi
  ihave %Hrb := isBoltCoreP_receipts _ _ _ _ _ _ $$ Hcore
  ihave #Hcore2 := Hcore
  unfold isBoltCoreP
  icases Hcore with ⟨-, #Ht0a, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, -, #Hpi, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨-, -, ⟨%lg, #Hlg, #Hlgok⟩, #Hro, -⟩
  unfold dbLogger
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hrw] as ⟨Hrwl, HW⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hml] as ⟨Hlk, HR⟩
  try wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hsync $Hmm] as ⟨Hmml, >HP⟩
  try wp_auto
  iunfold metaR at HR
  icases HR with ⟨%C, %F, %cl, %fli, %wa, Hcur', Hst', Hcls', Hop', Hfl', Hwa', Hmlk, Hfa,
    Hrof, #Hrcm, %Hok, %HF⟩
  iunfold rwR at HW
  icases HW with (⟨%w, Hwo, %Hwok, Hcls⟩ | Hclo')
  rotate_left
  · -- closed already: excluded by the caller's closer token (`closedR` holds the deposited one)
    iunfold closedR at Hclo'
    icases Hclo' with ⟨-, Hclo2, -⟩
    icombine Hclo Hclo2 gives %h
    exfalso
    have h1 := h.1
    rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
    grind
  -- open: the writer side idle
  icombine Hcls Hcls' gives % ⟨_, hcl⟩
  subst hcl
  obtain ⟨hmo, htree, htx1, -⟩ := Hok rfl
  iunfold wdbOwn at Hwo
  icases Hwo with ⟨Hcg, Hstw, -, -, -⟩
  iunfold wdbCore at Hcg
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hop, Hwa, -, Hfile, Hpath,
    Hdsz, Hmf, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjk⟩
  icombine Hfli Hfl' gives %hfli
  subst hfli
  icombine Hwa Hwa' gives %hwa
  subst hwa
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  subst hC
  -- the committed data is the caller's
  unfold boltState boltStateDef boltStateVDef
  icases Hst with ⟨%ν, Hs1, Hbq⟩
  icombine Hs1 Hst' gives % ⟨_, hD⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hD
  iunfold Pm at HP
  icases HP with ⟨%ms, Hpmap, Hpmf, Hptok, Hpf⟩
  icombine Hgmap Hpmap gives % ⟨_, hmsE⟩
  subst hmsE
  ihave Hmf := (mapFields_join2 db w.ms).1 $$ [Hmf Hpmf]
  · iframe
  icases pmFile_join (bnsOf γ.gs) db w.f w.fd p.path p.ino t0 w.ms $$ [Hfile Hfo Hfd Hpf] with
    ⟨Hfile, Hfo, Hfd⟩
  · iframe; iunfold t0At at Ht0a; iexact Ht0a
  simp only [Bool.not_false]
  ihave Hop := pt_join _ _ $$ [Hop Hop']
  · iframe
  ihave Hfli := pt_join _ _ $$ [Hfli Hfl']
  · iframe
  ihave Hwa := pt_join _ _ $$ [Hwa Hwa']
  · iframe
  have hL : ∀ b l, w.ms = some (b, l) → 8192 ≤ l := by
    intro b l h
    have h1 := Hwok.2.2.2.2.2.2.2.2.1 b l h
    have h2 := treeOK_root' w.C htree
    have : 3 * 4096 ≤ w.C.hwm * 4096 := Nat.mul_le_mul_right _ (by omega : 3 ≤ w.C.hwm)
    omega
  ihave #Hci : bCsInv (GF := GF) p $$ []
  · iapply bCsInv_none Ht0.2.2.2
  imod close_resM _ γ.ns p w Hwok hL (bNsOk_none Ht0.2.2.2) $$ Hpi Hci Hcur Hgfl Hgmap Hpmap Hptok
    Hgwv Hgout Hmc Hwc Hosm
    with ⟨Hres, Hosm0, Hcur, Hgfl, Hgmap, Hpmap, Hptok, Hgwv, Hgout⟩
  -- the store slots' bytes, `cls` set
  imod store_close _ γ.ns p ⊤ CoPset.subseteq_top w.C w.fl $$ [Hpi Hcur Hgfl Hgwv Hcls Hcls' Hgmap]
    with ⟨%bs, Hcur, Hgfl, Hgwv, Hcls, Hcls', Hgmap, HS, HX, %hS⟩
  · iframe; iframe #
  iunfold dbPathLk at Hpath
  icases Hpath with ⟨Hpath, Htok⟩
  iunfold fileOwn at Hfo
  icases Hfo with ⟨%inner, #Hfi, Hfdf, #Hfnm, #Hsysf⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hfi with ⟨-, %hfnn⟩
  ihave Hfo : fileOwn (GF := GF) w.f w.fd p.path (DFrac.own 1) $$ [Hfdf]
  · iunfold fileOwn; iexists inner; iframe; iframe #
  by_cases hne : FsNoErr
  rotate_left
  · -- the file system can fail: `close` as in `DB.Close`; the file given up
    iclear HS
    iclear HX
    iclear Hwb
    iclear Hmob
    iclear Hosm0
    ihave Hjk : junkRes (GF := GF) (bnsOf γ.gs) w.junk $$ [Hjk]
    · unfold junkRes; iexact Hjk
    imod junkRes_shut ⊤ (bnsOf γ.gs) w.junk $$ Hjk with #Hnf
    wp_apply hOwned db lg DFrac.discard w.fli _ p.path w.ms p w.f Ht0.2.1 $$ [Hop Hfli Hwa Hpath Hmf
      Hdsz Hres Hfile Hfo Hfd Htok]
      as %err ⟨-, Hop, Hfli, Hwa, Hpath, Hmf, Hdsz, Hfile⟩
    · iframe; iframe #
      isplitl [Hres]
      · iapply closeMapResM_res $$ Hres
      iright; iexists w.fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
    try wp_auto
    icases (mapFields_join2 db (none : MapSt)).2 $$ Hmf with ⟨Hmf1, Hmf2⟩
    icases pt_split _ _ $$ Hfile with ⟨Hfile, -⟩
    ihave Hpf := pmFile_null (bnsOf γ.gs) db (DFrac.own (1 : Qp).half) (t0, p.ino) none rfl
      $$ [Hfile]
    · iframe; iunfold t0At at Ht0a; iexact Ht0a
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hmml Hpmap Hmf1 Hptok Hpf]
    · iunfold Pm; iexists none; iframe
    try wp_auto
    icases pt_split _ _ $$ Hop with ⟨Hop, Hop'⟩
    icases pt_split _ _ $$ Hfli with ⟨Hfli, Hfl'⟩
    icases pt_split _ _ $$ Hwa with ⟨Hwa, Hwa'⟩
    wp_apply sync.Mutex.wp_Unlock _ (metaR (bnsOf γ.gs) db p) $$ [$Hsync $Hml $Hlk Hcur' Hst' Hcls'
        Hop' Hfl' Hwa' Hmlk Hfa]
    · iunfold metaR; iexists w.C, F, true, interface.nil, func.nil
      iframe Hrcm
      simp only [Bool.not_true, ↓reduceIte, flRoOpt]
      iframe
      ipureintro
      exact ⟨by simp, by simp, HF⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (rwR (bnsOf γ.gs) db p sp t0) $$ [$Hsync $Hrw $Hrwl Hcls Hcur
      Hstw Hgfl Hgmap Hmf2 Hgout Hgwv Hop Hfli Hwa Hclo]
    · iunfold rwR; iright; iunfold closedR
      iframe Hcls Hclo
      iexists w.C, w.fl, none
      iframe
    try wp_auto
    iapply HΦ
    iright; ipureintro; exact hne
  -- no error: `close` gives the `OsMeta` back
  wp_apply hOwnedM hne db lg DFrac.discard w.fli _ p.path w.ms p w.C [] w.m w.f w.fd p.path _ Ht0.2.1
    hfnn $$ [Hop Hfli Hwa Hpath Hmf Hdsz Hres Hfile Hfo Hfd Htok]
    as ⟨-, Hop, Hfli, Hwa, Hpath, Hmf, Hdsz, Hfile, Hback⟩
  · iframe; iframe #
    iapply dbFd_lockToks $$ Htok
  try wp_auto
  icases (mapFields_join2 db (none : MapSt)).2 $$ Hmf with ⟨Hmf1, Hmf2⟩
  icases pt_split _ _ $$ Hfile with ⟨Hfile, -⟩
  ihave Hpf := pmFile_null (bnsOf γ.gs) db (DFrac.own (1 : Qp).half) (t0, p.ino) none rfl
    $$ [Hfile]
  · iframe; iunfold t0At at Ht0a; iexact Ht0a
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hmml Hpmap Hmf1 Hptok Hpf]
  · iunfold Pm; iexists none; iframe
  try wp_auto
  icases pt_split _ _ $$ Hop with ⟨Hop, Hop'⟩
  icases pt_split _ _ $$ Hfli with ⟨Hfli, Hfl'⟩
  icases pt_split _ _ $$ Hwa with ⟨Hwa, Hwa'⟩
  wp_apply sync.Mutex.wp_Unlock _ (metaR (bnsOf γ.gs) db p) $$ [$Hsync $Hml $Hlk Hcur' Hst' Hcls'
      Hop' Hfl' Hwa' Hmlk Hfa]
  · iunfold metaR; iexists w.C, F, true, interface.nil, func.nil
    iframe Hrcm
    simp only [Bool.not_true, ↓reduceIte, flRoOpt]
    iframe
    ipureintro
    exact ⟨by simp, by simp, HF⟩
  try wp_auto
  ihave Hjk : junkRes (GF := GF) (bnsOf γ.gs) w.junk $$ [Hjk]
  · unfold junkRes; iexact Hjk
  rcases hj : w.junk with _ | ⟨jb, jl⟩
  rotate_left
  · -- a mapping leaked: excluded, the leak recorded a failure the premises refute (session S3f)
    ihave %hfs := junkRes_some_fs (bnsOf γ.gs) (some (jb, jl)) jb jl rfl $$ Hjk
    exact absurd hne hfs
  -- whole pages and mappable (`wdbSz`, session S3g: under the premises a failed write ends at
  -- `maxBytes`, page-aligned; the mapping lies below `maxAddr`)
  have hszw : wdbSz w.m w.ms := Hwok.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hal : w.m.size % 4096 = 0 := hszw.2.2 hne
  -- the file given back; the caller's validity token kept by the closed database
  wp_apply sync.Mutex.wp_Unlock _ (rwR (bnsOf γ.gs) db p sp t0) $$ [$Hsync $Hrw $Hrwl Hcls Hcur
    Hstw Hgfl Hgmap Hmf2 Hgout Hgwv Hop Hfli Hwa Hclo]
  · iunfold rwR; iright; iunfold closedR
    iframe Hcls Hclo
    iexists w.C, w.fl, none
    iframe
  try wp_auto
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  -- the file: its `OsMeta`, its bytes, an image of the committed state
  icases close_meta p w Hwok hj $$ [Hback Hosm0] with ⟨%m, Hm, %hm⟩
  · iframe
  icases metaOsBytes_slots p w.C hmo.1 hmo.2.1 $$ Hmob with ⟨H0, H1⟩
  have hsz : w.m.size < 2 ^ 62 ∧ w.m.size % 4096 = 0 := ⟨hszw.lt, hal⟩
  have hroot := treeOK_root' w.C htree
  have h2 : 2 ≤ w.m.size / 4096 := by
    have h3 := Hwok.2.2.1
    have : 3 * 4096 ≤ w.C.hwm * 4096 := Nat.mul_le_mul_right _ (by omega : 3 ≤ w.C.hwm)
    omega
  -- the synced freelist page's halves joined (session S4)
  have hwx := wdbOK_flxS w Hwok
  iunfold wBytesX at Hwb
  icases Hwb with ⟨Hwb0, Hwbx⟩
  icases flxS_agree_same p w.C w.fl bs w.wb (fun f hf _ => (hS.2.2.2 f hf).2)
    (fun f hf hp s hs => by
      have : s ∈ flxS w.C w.fl w.wb := by unfold flxS; rw [hf]; simp only [hp, ↓reduceIte]; exact hs
      exact (hwx s this).2.2) $$ [HX Hwbx] with ⟨HX, Hwbx, %hag⟩
  · iframe
  have hXe : flxS w.C w.fl bs = flxS w.C w.fl w.wb := by
    unfold flxS
    rcases hf : w.C.flpg with _ | f
    · rfl
    · by_cases hp : f ∈ pendSlots w.fl
      · simp only [hp, ↓reduceIte]
      · simp only [hp, ↓reduceIte]; exact ((hag f hf hp).1).symm
  rw [hXe] at *
  ihave Hwb := (show wBytes (GF := GF) p (w.W.filter (fun s => decide (s ∉ flxS w.C w.fl w.wb)))
      w.wb w.m.size ∗ ([∗list] s ∈ flxS w.C w.fl w.wb, osSlotH p s (w.wb s)) ⊢
      wBytesX p w.W (flxS w.C w.fl w.wb) w.wb w.m.size from by unfold wBytesX; exact .rfl) $$ [Hwb0 Hwbx]
  · iframe
  icases wBytes_joinX p w.W (flxS w.C w.fl w.wb) w.wb bs w.m.size
    (fun s hs => (hwx s hs).2.1)
    (fun s hs => by
      rw [(hwx s hs).2.2]
      rcases hf : w.C.flpg with _ | f
      · unfold flxS at hs; rw [hf] at hs; cases hs
      · exact ((hS.2.2.2 f hf).2 s (by
          unfold flxS at hs; rw [hf] at hs
          by_cases hp : f ∈ pendSlots w.fl
          · simp only [hp, ↓reduceIte] at hs; cases hs
          · simp only [hp, ↓reduceIte] at hs; rw [← (hag f hf hp).1]; exact hs)).symm)
    $$ [Hwb HX] with ⟨Hwb, -⟩
  · iframe
  icases close_file_bytes p w Hwok bs hmo.1 hmo.2.1 hS.2.1 h2 hal _
    (fun s hs => mem_filter_append _ _ s hs) $$ [H0 H1 HS Hwb] with
    ⟨%xs, Hxs, %hxs⟩
  · iframe
  ihave %htxb := preceipt_lt _ $$ Hrcm
  have hn : w.C.hwm ≤ w.m.size / 4096 := by
    have h3 := Hwok.2.2.1
    exact (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
  have hwbl : ∀ s, 2 ≤ s → s < w.m.size / 4096 → s ∉ slotsOf w.C w.fl → (w.wb s).length = 4096 := by
    intro s h1 h2' h3
    refine Hwok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s ((wdbOK_mem_W w Hwok s).2 ⟨h1, ?_, h3⟩) (by omega)
    have := Nat.le_max_right (mapLen w.ms) w.m.size
    have : w.m.size / 4096 ≤ max (mapLen w.ms) w.m.size / 4096 := Nat.div_le_div_right this
    omega
  obtain ⟨hfok, hlen, himg⟩ := closeBytes_fileOK w.C w.fl bs w.wb (w.m.size / 4096) hmo htree htx1
    (by omega) hn hS.1 hS.2.1 hwbl hS.2.2.1
    (fun s hs => Hwok.2.2.2.2.2.2.2.2.2.2.1 s (Or.inr hs)) Hwok.2.2.2.2.2.1
  have hsz4 : 4096 * (w.m.size / 4096) = w.m.size := by omega
  rw [hsz4] at hfok
  ihave Hxs := (bBytes_none (GF := GF) Ht0.2.2.2 _ _ _).1 $$ Hxs
  rw [bMeta_none (GF := GF) Ht0.2.2.2]
  unfold fileHoldsM fileHoldsMDef
  iexists m, xs
  iframe Hm Hxs
  isplitr
  · ipureintro
    refine ⟨hm.1, by rw [hm.2]; exact hxs.2, by rw [hm.2]; exact hsz, ?_⟩
    rw [hm.2, hxs.1]; exact hfok
  isplitr
  · ipureintro; rw [hm.2]; exact hszw.1
  rw [hxs.1]
  iapply fileRcpt_intro _ w.C himg hmo $$ Hrcm

end proof

end bbolt
end EtcdGrove
end Perennial
