/-
`db.loadFreelist()` at `Open` (U11e; design §3.11 "Open", steps 2-3): its own spec, which takes
`Open/Core.open_core`'s inputs before the carving (`Open/Carve.open_carve`) and performs the core
phase itself, where the code needs it: in the synced case after `Interface.Read` (which reads the
freelist page's bytes, writer-side `W` slots whose cells the core keeps only as `∃ vf`), in the
unsynced case before `freepages` (a read transaction on the core and the spare reader pair). The
loaded freelist is published under `metalock`, its free count under `statlock`; the post is
`Open/Core.open_writer`'s inputs but `rwlock`, with `wdbOK` of the writer side.

An internal spec of this unit (not in `Spec/`: `loadFreelist` is called only by `Open` here).
-/
module

public import Proof.go_etcd_io.bbolt.Open.LoadFL
public import Proof.go_etcd_io.bbolt.Open.Carve
public import Proof.go_etcd_io.bbolt.Open.OnceOwn
public import Proof.go_etcd_io.bbolt.Open.MutexOwn
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.SliceLen
public import Spec.go_etcd_io.bbolt.newFreelist
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.DB__freepages
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Read
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__FreeCount
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The slots' bytes of the opened file `xs`. -/
def openWb (xs : List (w8 × Bool)) : Nat → List w8 :=
  fun s => bytesAt (xs.map Prod.fst) (4096 * s) 4096

/-- The pure facts `loadFreelist` needs of the opened file `xs` (`fileHolds_decode`'s, the
mapping `(b, L)`'s, `Open`'s namespace and database). -/
def lfOK (N : Namespace) (db : Loc) (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta)
    (xs : List (w8 × Bool)) : Prop :=
  fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧ flFileOK (xs.map Prod.fst) C ∧
    C.hwm * 4096 ≤ xs.length ∧ 8192 ≤ xs.length ∧ xs.length = m.size ∧ m.size ≤ L ∧
    m.size < 2 ^ 63 ∧ m.maps = GMap.singleton b L ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧
    (↑N : CoPset) ## ↑osN ∧ db ≠ null

/-- **What `loadFreelist` takes at `Open`**: `open_core`'s inputs, the mapping's client halves
not yet carved (the file's bytes at a half, the rest any cells). -/
def lfPre (db sp f : Loc) (fd : w64) (p : GoString) (b : Loc) (L : Nat) (m : OsMeta)
    (xs : List (w8 × Bool)) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed db sp ∗
      db.[DB, go!"metalock"] ↦ (zero_val sync.Mutex) ∗
      db.[DB, go!"mmaplock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"statlock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"rwtx"] ↦ null ∗ db.[DB, go!"file"] ↦ f ∗ db.[DB, go!"path"] ↦ p ∗
      db.[DB, go!"datasz"] ↦ W64 (L : Int) ∗
      mapFields db (DFrac.own 1) (some (b, L)) ∗
      osMeta p (DFrac.own 1) (some m) ∗ fileOwn f fd p (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p, true, true⟩ ∗ Ps sp 1 ∗
      osBytes p 0 (DFrac.own 1) xs ∗
      bytesPointsto b (DFrac.own (1 : Qp).half) (xs.map Prod.fst) ∗
      ∃ vf, cellsR b xs.length (L - xs.length) vf)

/-- The writer side after `loadFreelist`. -/
def lfW (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List (w8 × Bool)) (f : Loc)
    (fd : w64) (fl : FLPg) (fli : GoInterface) : WDb :=
  { openW C b L m (openWb xs) f fd with fl := fl, fli := fli }

/-- **What `loadFreelist` gives at `Open`**: `open_writer`'s inputs but `rwlock`. -/
def lfPost (N : Namespace) (db sp f : Loc) (fd : w64) (p : GoString) (C : CommitSt) (b : Loc)
    (L : Nat) (m : OsMeta) (xs : List (w8 × Bool)) : IProp GF :=
  iprop(∃ (B : BNs) (fl : FLPg) (fli : GoInterface),
    isBoltCoreP B N db p sp C.txid ∗
    threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗
    wdbCore B db p (lfW C b L m xs f fd fl fli) ∗ ghostVar B.st (1 : Qp).half.half (treeData C) ∗
    flPgOwn fli fl ∗ rdPair B db sp ∗ ghostVar B.cls (1 : Qp).half false ∗
    boltStateDef B 1 (treeData C) ∗ ⌜wdbOK (lfW C b L m xs f fd fl fli)⌝)

/-- **`db.loadFreelist()` at `Open`**. -/
abbrev DB.loadFreelist.spec_open : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] (N : Namespace) (db sp f : Loc) (fd : w64) (p : GoString)
    (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List (w8 × Bool)),
  lfOK N db C b L m xs →
  {{ lfPre (GF := GF) db sp f fd p b L m xs ∗
      db.[DB, go!"freelistLoad"] ↦ (zero_val sync.Once) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"loadFreelist")) (Val #()))
  {{ RET #(); lfPost N db sp f fd p C b L m xs }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

instance dbFixed_persistent_lf (db sp : Loc) : Persistent (dbFixed (GF := GF) db sp) := by
  unfold dbFixed dbLogger; infer_instance

/-- The current meta's `Freelist()` when it names the page `g`. -/
theorem wp_curMeta_Freelist (hFreelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (b : Loc) (l : Nat) (C : CommitSt) (q : Qp) (hok : C.metaOk) (g : Nat)
    (hg : C.flpg = some g) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
        metaCellsQ q (some (b, l) : MapSt) C }}
      (App (Val ((b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) @!!
        go.GoType.PointerType Meta.ty @!! go!"Freelist")) (Val #()))
    {{ RET #(W64 (g : Int)); metaCellsQ q (some (b, l) : MapSt) C }} := by
  wp_start_folded as Hmc
  obtain ⟨hl0, hl1, -, -, -, -, ⟨-, -, -, hfl⟩, -⟩ := hok
  have hval : ∀ v : Meta, metaFlpg v = C.flpg → v.freelist' = W64 (g : Int) := by
    intro v hv
    rw [hg] at hv
    unfold metaFlpg at hv
    split at hv
    · cases hv
    · cases hv
      apply BitVec.eq_of_toNat_eq
      have := BitVec.isLt v.freelist'
      simp
  simp only [metaCellsQ]
  icases Hmc with ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · unfold CommitSt.slot at hfl
    simp only [hT, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    generalize metaOf C.m0 = v0 at hfl ⊢
    wp_apply hFreelist _ v0 (DFrac.own q) $$ [M0] as M0
    · iframe
    rw [hval _ hfl]
    ihave H0 := C0 $$ M0
    iapply HΦ; iframe
  · unfold CommitSt.slot at hfl
    simp only [show C.txid % 2 ≠ 0 by omega, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    generalize metaOf C.m1 = v1 at hfl ⊢
    wp_apply hFreelist _ v1 (DFrac.own q) $$ [M1] as M1
    · iframe
    rw [hval _ hfl]
    ihave H1 := C1 $$ M1
    iapply HΦ; iframe

theorem DB.loadFreelist.wp_proof_open
    (hNF : newFreelist.spec (GF := GF) (hG := hG))
    (hSync : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hMeta : DB.meta.spec (GF := GF) (hG := hG))
    (hFreelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (hPage : DB.page.spec (GF := GF) (hG := hG))
    (hRead : internal.freelist.Interface.Read.spec (GF := GF) (hG := hG))
    (hInit : internal.freelist.Interface.Init.spec (GF := GF) (hG := hG))
    (hFC : internal.freelist.Interface.FreeCount.spec (GF := GF) (hG := hG))
    (hFP : DB.freepages.spec (GF := GF) (hG := hG)) :
    DB.loadFreelist.spec_open (GF := GF) (hG := hG) := by
  intro _ N db sp f fd p C b L m xs hok
  wp_start as ⟨Hpre, Honce⟩
  iunfold lfPre at Hpre
  icases Hpre with ⟨#Hpkg, Hpre⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_func_lits
  wp_apply Once.wp_Do_own _ iprop(db_ptr ↦ db ∗ lfPre db sp f fd p b L m xs)
    (lfPost N db sp f fd p C b L m xs) _ $$ [Honce Hpre db] as HQ
  · iframe Honce
    isplitl [Hpre db]
    · iframe db; iunfold lfPre; iframe Hpkg Hpre
    iintro !> %Φ' ⟨db, Hpre⟩ HΦ'
    obtain ⟨himg, hmeta, htree, hflf, hhwm, h8, hxm, hL, hsz, hmaps, htx1, htx2, hN, hdb⟩ := hok
    iunfold lfPre at Hpre
    icases Hpre with ⟨-, #Hos, #Hfix, Hml, Hmm, Hsl, Hop, Hfli, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf,
      Hosm, Hfo, Hfd, Hps, Hxs, Hb, %vf, Hc⟩
    ihave #Hfix' := Hfix
    iunfold dbFixed at Hfix'
    icases Hfix' with ⟨#HpgSz, #Hstats, -, -, -, -, -, -, -, -, ⟨%ft, #Hft⟩, -⟩
    wp_auto
    wp_apply hNF ft as %fli ⟨%hfli, Hflo, Hro⟩
    try wp_auto
    icases (bytes_half_quarters b _).1 $$ Hb with ⟨Hb, Hbq⟩
    icases file_metaCells b L _ C _ himg (by simpa using h8) $$ Hbq with ⟨Hmc, Hmcw⟩
    wp_apply hSync db b L C (DFrac.own 1) _ hmeta $$ [Hmf Hmc] as ⟨Hmf, Hmc⟩
    · iframe
    have hxL : xs.length ≤ L := by omega
    rcases hfp : C.flpg with _ | g
    · sorry
    -- the synced freelist page: read it before the core phase
    simp only [reduceCtorEq, decide_false, Bool.not_false, Bool.not_true]
    wp_auto
    wp_apply hMeta db b L C (DFrac.own 1) _ hmeta $$ [Hmf Hmc] as ⟨Hmf, Hmc⟩
    · iframe
    ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
    · iPkgInit
    wp_apply wp_curMeta_Freelist hFreelist b L C _ hmeta g hfp $$ [Hmc] as Hmc
    · iframe
    -- the page's address
    obtain ⟨hg2, hext, hflag, hbnd, hnd, hids, hown, hcov⟩ := hflf g hfp
    have hysl : (xs.map Prod.fst).length = xs.length := List.length_map ..
    obtain ⟨pg, hpg⟩ : ∃ pg, pg = filePage (xs.map Prod.fst) g := ⟨_, rfl⟩
    rw [← hpg] at hext hflag hbnd hnd hids hown hcov
    have hpgl : pg.length = (1 + pageOverflow pg) * 4096 := by
      rw [hpg]; exact filePage_length (xs.map Prod.fst) g (by
        rw [← hpg]
        have : (g + (1 + pageOverflow pg)) * 4096 ≤ C.hwm * 4096 := Nat.mul_le_mul_right _ hext
        rw [Nat.add_mul] at this; omega)
    have hgw : (W64 (g : Int)).toNat = g := by simp; omega
    simp only [mapFields]
    icases Hmf with ⟨Hdr, Hdata, Hm0, Hm1, %hmfp⟩
    wp_apply hPage db b (W64 (g : Int)) (DFrac.own 1) hmfp.2.1 (by rw [hgw]; omega) $$ [Hdata] as Hdata
    · iframe; iexact HpgSz
    rw [hgw, show g * 4096 = 4096 * g by omega]
    -- the page's bytes, from the file's quarter
    ihave Hb' := Hmcw $$ Hmc
    have hpgo : pageOverflow pg = pageOverflow (bytesAt (xs.map Prod.fst) (4096 * g) 4096) := by
      rw [hpg, filePage_overflow]
    icases bytes_cut b _ (xs.map Prod.fst) (4096 * g)
      ((1 + pageOverflow (bytesAt (xs.map Prod.fst) (4096 * g) 4096)) * 4096)
      (by rw [← hpgo, hysl]; have := Nat.mul_le_mul_right 4096 hext; rw [Nat.add_mul] at this; omega)
      $$ Hb' with ⟨Hpg, Hpgw⟩
    have hpge : bytesAt (xs.map Prod.fst) (4096 * g)
        ((1 + pageOverflow (bytesAt (xs.map Prod.fst) (4096 * g) 4096)) * 4096) = pg := by
      rw [hpg]; rfl
    rw [hpge]
    ihave %hbd := bytesPointsto_in_bounds' _ _ pg (by
      intro h; have h2 := hpgl; rw [h] at h2; simp at h2 <;> omega) $$ Hpg
    ihave #Hflpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
    · iPkgInit
    wp_apply hRead fli _ pg _ hflag hbnd (by omega) hnd (fun x hx => (hids x hx).1) hbd.1
      (by rw [hpgl] at hbd; have := hbd.2; rw [hpgl]; exact this) $$ [Hflo Hpg] as ⟨Hflo, Hpg⟩
    · iframe
    ihave Hb' := Hpgw $$ Hpg
    ihave Hb := (bytes_half_quarters b _).2 $$ [Hb Hb']
    · iframe
    -- publish under the (still owned) `metalock`
    wp_apply Mutex.wp_Lock_own _ $$ Hml as Hml
    try wp_auto
    wp_apply Mutex.wp_Unlock_own _ $$ Hml as Hml
    -- the core phase, with the loaded freelist
    ihave Hmf : mapFields db (DFrac.own 1) (some (b, L)) $$ [Hdr Hdata Hm0 Hm1]
    · simp only [mapFields]; iframe; ipureintro; exact hmfp
    icases open_carve p b L C xs vf himg htree hhwm h8 hxL $$ [Hxs Hb Hc] with
      ⟨Hmo1, Hmo2, HSo, HWo, Hq1, Hq2, HSc, HWc⟩
    · iframe
    rw [hxm]
    have hok' := storeOK_open_fl (xs.map Prod.fst) C b L (flIds pg) himg hmeta htree
      (by rw [hysl]; exact hhwm) (by rw [hysl]; omega) (by rw [hysl]; omega) htx2 hnd
      (fun x hx => (hids x hx).1) (fun x hx => (hids x hx).2) (fun x hx => (hown x hx).2)
    ihave Hrop : flRoOpt fli ∅ $$ [Hro]
    · unfold flRoOpt; simp only [hfli, ↓reduceIte]; iexists []; iframe; ipureintro; simp
    imod open_core_fl ⊤ N db sp f fd p C b L m (fun s => bytesAt (xs.map Prod.fst) (4096 * s) 4096)
      (FLPg.ofInit (flIds pg)) fli rfl hok' ⟨htx1, htx2⟩ hN hdb $$
      [Hfix Hml Hmm Hsl Hop Hfli Hrop Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hps Hmo1 Hmo2 HSo
        HWo Hq1 Hq2 HSc HWc] with ⟨%B, #Hcore, Hw, Hst, Hcls, Hsp, #Hpool, Hstate⟩
    · iframe Hpkg Hos Hfix Hml Hmm Hsl Hop Hfli Hrop Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hps
      iframe
    have hwok : wdbOK (lfW C b L m xs f fd (FLPg.ofInit (flIds pg)) fli) := by
      unfold lfW openWb
      refine wdbOK_open (xs.map Prod.fst) C b L m f fd _ fli htree (by rw [hysl]; exact hhwm)
        (by rw [hysl]; exact hxm) hL hsz htx2 hmaps (ofInit_pending _) ?_ ?_
      · intro x hx; rw [hpg] at hx; exact flIds_facts _ C g hfp hflf x hx
      · intro g' hg'; rw [hfp] at hg'; cases hg'
        rw [extentBytes_filePage, ← hpg]
        rw [hpg]; exact flCurOK_ofInit _ C g hfp hflf (by rw [hysl]; exact hhwm) (by rw [hysl]; omega)
    generalize FLPg.ofInit (flIds pg) = fl0 at hwok ⊢
    -- the free count under `statlock`
    ihave Hcore' := Hcore
    iunfold isBoltCoreP at Hcore'
    icases Hcore' with ⟨-, -, -, -, -, -, -, -, #Hslg, -⟩
    by_cases hsp : sp = null
    · try wp_auto
      rw [decide_eq_true hsp]
      wp_auto
      iapply HΦ'
      iunfold lfPost
      iexists B, fl0, fli
      unfold lfW openWb
      iframe Hcore Hpool
      iframe
      ipureintro; exact hwok
    · try wp_auto
      rw [decide_eq_false hsp]
      try wp_auto
      wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hsync $Hslg] as ⟨Hsw, HPs⟩
      iunfold Ps at HPs
      simp only [hsp, ↓reduceIte]
      icases HPs with ⟨%st, Hs⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %Hspn⟩
      iStructNamed Hs
      try wp_auto
      wp_apply hFC fli fl0 $$ [Hflo] as Hflo
      · iframe
      try wp_auto
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hsw TxStats FreePageN PendingPageN FreeAlloc
        FreelistInuse TxN OpenTxN]
      · iunfold Ps; simp only [hsp, ↓reduceIte]
        iexists { st with FreePageN' := W64 (fl0.free.length : Int) }
        iapply typedPointsto_combine _ _ _ Hspn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iapply HΦ'
      iunfold lfPost
      iexists B, fl0, fli
      unfold lfW openWb
      iframe Hcore Hpool
      iframe
      ipureintro; exact hwok
  iapply HΦ; iexact HQ

end proof

end bbolt
end EtcdGrove
end Perennial
