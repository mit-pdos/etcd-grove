/-
`Open`'s core phase (U11c; design §3.11 "Open", step 2): from the resources `Open` owns once the
file is mapped (its fields, the file, the mapping's client cells and the page cache's bytes, carved
by slot), allocate the database's ghost names, the page store's and the transactions' invariants,
`metalock`'s, `mmaplock`'s and `statlock`'s resources and the reader pool (allocated here, not in
the writer phase: `txsInv`'s readers name the pool's ghost name, so it must exist before the
names are fixed), leaving the writer side before `loadFreelist` (`wdbOpen`), its half of the
closed flag, the spare reader-token pair and the client's `boltState`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt
public import Proof.go_etcd_io.bbolt.Mmap.RemapBase
public import Perennial.Proof.ThreadPool
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section core
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The page store's state once `Open` has mapped the file: the committed state `C`, no freelist
yet, no reader, no writer, the store slots' bytes `wb`. -/
def openSigma (b : Loc) (L : Nat) (C : CommitSt) (wb : Nat → List w8) : StoreSt :=
  ⟨some (b, L), C, FLPg.empty, ∅, none, none, false, false, wb⟩

/-- The writer side's record once `Open` has mapped the file (`b`, `L`) with the `OsMeta` `m`:
the `W` slots are every slot of the mapping but the metas and the tree's. -/
def openW (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (wb : Nat → List w8) (f : Loc)
    (fd : w64) : WDb :=
  { C := C, fl := FLPg.empty, ms := some (b, L), m := m, W := wSlots (L / 4096) C FLPg.empty,
    wb := wb, fli := interface.nil, junk := none, f := f, fd := fd }

theorem openSigma_slots (b : Loc) (L : Nat) (C : CommitSt) (wb : Nat → List w8) :
    storeSlots (openSigma b L C wb) = slotsOf C FLPg.empty := rfl

theorem openSigma_lent (b : Loc) (L : Nat) (C : CommitSt) (wb : Nat → List w8) (s : Nat) :
    lent (openSigma b L C wb) s = none := by
  unfold lent openSigma
  simp only [GMap.mapFold_empty]

/-- A ghost witness of the slots' bytes. -/
theorem exists_bytesWit (S : List Nat) (f : Nat → List w8) :
    ∃ W : GMap Nat (List w8), ∀ s ∈ S, W !! s = some (f s) := by
  induction S with
  | nil => exact ⟨∅, fun s hs => by simp at hs⟩
  | cons a S ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨W.insert a (f a), fun s hs => ?_⟩
    by_cases h : s = a
    · subst h; exact GMap.lookup_insert _ _ _
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]
      simp only [List.mem_cons] at hs
      exact hW s (hs.resolve_left h)

omit hos package_sem in
/-- Two lists of `k` copies, as `k` copies of both. -/
theorem replicate_sep (A B : IProp GF) :
    ∀ k : Nat, ([∗list] _x ∈ List.replicate k (), A) ∗ ([∗list] _x ∈ List.replicate k (), B) ⊢
      [∗list] _x ∈ List.replicate k (), iprop(A ∗ B)
  | 0 => by
    iintro -; simp only [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1 => by
    simp only [List.replicate_succ]
    iintro ⟨Ha, Hb⟩
    icases BigSepL.bigSepL_cons.1 $$ Ha with ⟨Ha, Has⟩
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨Hb, Hbs⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha Hb]
    · iframe
    · iapply replicate_sep A B k $$ [Has Hbs]
      iframe

omit hos package_sem in
/-- A whole points-to as two halves. -/
theorem pt_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  refine Entails.trans ?_ ((typedPointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).1
  rw [DFrac.op_own, Qp.half_add_half]

/-- **The core phase's ghost step.** Pure premises: the store's invariant of the opened state
(`storeOK`, from `fileHolds`' facts), the current meta's txid, `Open`'s namespace premise.
(`wdbOK` of `openW` is needed only when `rwlock`'s resource is formed, after `loadFreelist`.)
Every ghost share is as `Inv/Names` lists it; the store's cells and witness are allocated mapped
(no reader, so nothing lent), so `store_carve` is not needed. -/
theorem open_core_fl [ThreadBoundLe GF (2 ^ 29)] (E : CoPset) (N : Namespace) (db sp f : Loc)
    (fd : w64) (p : GoString) (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta)
    (wb : Nat → List w8) (fl : FLPg) (fli : GoInterface) (hpend : fl.pending = ∅)
    (hok : storeOK { openSigma b L C wb with fl := fl })
    (htx : 1 ≤ C.txid ∧ C.txid < 2 ^ 62) (hN : (↑N : CoPset) ## ↑osN) (hdb : db ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed db sp ∗
      db.[DB, go!"metalock"] ↦ (zero_val sync.Mutex) ∗
      db.[DB, go!"mmaplock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"statlock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ fli ∗ flRoOpt fli ∅ ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"rwtx"] ↦ null ∗ db.[DB, go!"file"] ↦ f ∗ db.[DB, go!"path"] ↦ p ∗
      db.[DB, go!"datasz"] ↦ W64 (L : Int) ∗
      mapFields db (DFrac.own 1) (some (b, L)) ∗
      osMeta p (DFrac.own 1) (some m) ∗ fileOwn f fd p (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p, true, true⟩ ∗ Ps sp 1 ∗
      metaOsBytes p (DFrac.own (1 : Qp).half) C ∗ metaOsBytes p (DFrac.own (1 : Qp).half) C ∗
      ([∗list] s ∈ slotsOf C FLPg.empty, osSlot p s (wb s)) ∗
      wBytes p (wSlots (L / 4096) C FLPg.empty) wb m.size ∗
      metaCellsQ (1 : Qp).half.half (some (b, L)) C ∗
      metaCellsQ (1 : Qp).half.half (some (b, L)) C ∗
      ([∗list] s ∈ slotsOf C FLPg.empty,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (wb s)) ∗
      wCells (some (b, L)) (wSlots (L / 4096) C FLPg.empty) ⊢
    |={E}=> ∃ B : BNs, isBoltCoreP B N db p sp C.txid ∗
      wdbCore B db p { openW C b L m wb f fd with fl := fl, fli := fli } ∗
      ghostVar B.st (1 : Qp).half.half (treeData C) ∗ ghostVar B.cls (1 : Qp).half false ∗
      sparePair B db sp ∗ threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗
      boltStateDef B 1 (treeData C) ∗ dghostVar B.opn (DFrac.own 1) false := by
  iintro ⟨#Hpkg, #Hos, Hfix, Hml, Hmm, Hsl, Hop, Hfli, Hro, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf, Hosm,
    Hfo, Hfd, Hps, Hmo1, Hmo2, Hslots, Hwb, Hmc1, Hmc2, Hcells, Hwc⟩
  -- the ghost names
  imod ghostVar_alloc (GF := GF) (treeData C) with ⟨%γst, Hst⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γbq, Hbq⟩
  imod ghostVar_alloc (GF := GF) C with ⟨%γcur, Hcur⟩
  imod ghostVar_alloc (GF := GF) fl with ⟨%γfl, Hfl⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat RdInfo) with ⟨%γrds, Hrds, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat w64) with ⟨%γfltx, Hfltx, -⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γmtok, Hmtok⟩
  imod ghostVar_alloc (GF := GF) (some (b, L) : MapSt) with ⟨%γmap, Hmap⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γout, Hout⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γmlk, Hmlk⟩
  imod ghostVar_alloc (GF := GF) wIdle with ⟨%γwv, Hwv⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Loc TxReg) with ⟨%γtxs, Htxs, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Unit Loc) with ⟨%γdbl, Hdbl, -⟩
  imod ghost_map_insert_persist () db (by rfl) $$ Hdbl with ⟨-, #Hdbl⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γcls, Hcls⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Unit Nat) with ⟨%γt0, Ht0, -⟩
  imod ghost_map_insert_persist () C.txid (by rfl) $$ Ht0 with ⟨-, #Ht0⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γmln, Hmln⟩
  obtain ⟨W, hW⟩ := exists_bytesWit (slotsOf C FLPg.empty) wb
  imod ghostVar_alloc (GF := GF) W with ⟨%γbyt, Hbyt⟩
  imod ghostVar_alloc (GF := GF) (∅ : GMap Nat (List w8)) with ⟨%γfpb, Hfpb⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%γopn, Hopn⟩
  imod ghostVar_alloc (GF := GF) (none : Option Nat) with ⟨%γspr, Hspr⟩
  -- the names but the pool's
  let B0 : BNs := ⟨γst, γbq, γcur, γfl, γrds, γfltx, γmtok, γmap, γout, γmlk, γwv, γtxs, γdbl,
    γcls, γt0, default, γmln, γbyt, γfpb, γopn, γspr⟩
  -- `mmaplock` and `statlock`, with their reader slots
  icases (ghostVar_split_half γmap 1 _).1 $$ Hmap with ⟨Hmap1, Hmap2⟩
  icases (ghostVar_split_half γmap _ _).1 $$ Hmap2 with ⟨Hmap2, Hmap3⟩
  have hmf : DFractional (fun dq => mapFields (GF := GF) db dq (some (b, L))) := by
    simp only [mapFields]; infer_instance
  icases (hmf.dfractional (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).1 $$
    [Hmf] with ⟨Hmf1, Hmf2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hmf
  haveI := Pm_fractional (GF := GF) B0 db
  haveI := Ps_fractional (GF := GF) sp
  imod sync.init_RWMutex (Pm B0 db) (E := E) db.[DB, go!"mmaplock"] $$ [Hmap3 Hmf1 Hmtok] Hmm
    with Hmms
  · inext; unfold Pm; iexists (some (b, L)); iframe
  imod sync.init_RWMutex (Ps sp) (E := E) db.[DB, go!"statlock"] $$ Hps Hsl with Hsls
  icases sync.ownRWMutex_slots_guard _ _ $$ Hmms with ⟨Hmms, #Hmg⟩
  icases sync.ownRWMutex_slots_guard _ _ $$ Hsls with ⟨Hsls, #Hsg⟩
  ihave Hpairs := replicate_sep (sync.ownRWMutex (GF := GF) db.[DB, go!"mmaplock"] (Pm B0 db))
    (sync.ownRWMutex (GF := GF) db.[DB, go!"statlock"] (Ps sp)) _ $$ [Hmms Hsls]
  · iframe
  obtain ⟨n, hk, hTB⟩ : ∃ n, Int.toNat sync.rwmutex.actualMaxReaders = n + 1 ∧
      threadBound GF ≤ n + 1 := by
    refine ⟨2 ^ 30 - 2, ?_, ?_⟩
    · rw [sync.rwmutex.actualMaxReaders_unseal]; rfl
    · have := ThreadBoundLe.threadBound_le (GF := GF) (k := 2 ^ 29); omega
  rw [hk, List.replicate_succ']
  icases BigSepL.bigSepL_snoc.1 $$ Hpairs with ⟨Hpairs, Hspare⟩
  -- the reader pool
  imod threadPool.init (poolN N) (rdPair B0 db sp) E n hTB $$ [Hpairs] with
    ⟨%γpool, #Hpool⟩
  · unfold rdPair; iexact Hpairs
  let B : BNs := ⟨γst, γbq, γcur, γfl, γrds, γfltx, γmtok, γmap, γout, γmlk, γwv, γtxs, γdbl,
    γcls, γt0, γpool, γmln, γbyt, γfpb, γopn, γspr⟩
  have hPm : Pm (GF := GF) B0 db = Pm B db := rfl
  have hrd : rdPair (GF := GF) B0 db sp = rdPair B db sp := rfl
  rw [hPm] at *
  rw [hrd] at *
  -- halves of the ghost state and of the shared fields
  icases (ghostVar_split_half γst 1 _).1 $$ Hst with ⟨Hst1, Hst2⟩
  icases (ghostVar_split_half γst _ _).1 $$ Hst2 with ⟨Hst2, Hst3⟩
  icases (ghostVar_split_half γcur 1 _).1 $$ Hcur with ⟨Hcur1, Hcur2⟩
  icases (ghostVar_split_half γcur _ _).1 $$ Hcur2 with ⟨Hcur2, Hcur3⟩
  icases (ghostVar_split_half γfl 1 _).1 $$ Hfl with ⟨Hfl1, Hfl2⟩
  icases (ghostVar_split_half γout 1 _).1 $$ Hout with ⟨Hout1, Hout2⟩
  icases (ghostVar_split_half γwv 1 _).1 $$ Hwv with ⟨Hwv1, Hwv2⟩
  icases (ghostVar_split_half γcls 1 _).1 $$ Hcls with ⟨Hcls1, Hcls2⟩
  icases (ghostVar_split_half γbyt 1 _).1 $$ Hbyt with ⟨Hbyt1, Hbyt2⟩
  icases (ghostVar_split_half γfpb 1 _).1 $$ Hfpb with ⟨Hfpb1, Hfpb2⟩
  icases (ghostVar_split_half γspr 1 _).1 $$ Hspr with ⟨Hspr1, Hspr2⟩
  icases (ghostVar_split_half γspr _ _).1 $$ Hspr2 with ⟨Hspr2, Hspr3⟩
  icases pt_halves _ _ $$ Hop with ⟨Hop1, Hop2⟩
  icases pt_halves _ _ $$ Hfli with ⟨Hfli1, Hfli2⟩
  icases pt_halves _ _ $$ Hwa with ⟨Hwa1, Hwa2⟩
  -- the page store
  imod inv_alloc (pagesN N) E (pagesInv (GF := GF) B p) $$
    [Hcur2 Hfl1 Hmap2 Hwv1 Hrds Hcells Hslots Hbyt1 Hbyt2 Hmc1 Hout1 Hmln Hfpb1 Hfpb2 Hspr2]
    with #Hpages
  · inext
    unfold pagesInv
    iexists { openSigma b L C wb with fl := fl }, W
    have hws : ({ openSigma b L C wb with fl := fl } : StoreSt).wst = wIdle := rfl
    rw [hws]
    unfold storeCells bytesWit metaLend rdsAuth fbInv
    have hsl : storeSlots ({ openSigma b L C wb with fl := fl } : StoreSt) = slotsOf C FLPg.empty := by
      show slotsOf C fl = slotsOf C FLPg.empty
      unfold slotsOf pendSlots FLPg.pendingIds
      rw [hpend]; rfl
    simp only [hsl]
    simp only [openSigma]
    iframe Hcur2 Hfl1 Hmap2 Hwv1 Hrds Hslots Hbyt1 Hbyt2
    isplitl [Hspr2]
    · iexists none; iframe Hspr2; iright; ipureintro; intro k v h; simp at h
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitl [Hcells]
    · iapply BigSepL.bigSepL_mono ?_ $$ Hcells
      intro _ s _
      iintro H
      iexists (1 : Qp).half
      iframe H
      ipureintro
      have : lent ({ openSigma b L C wb with fl := fl } : StoreSt) s = none := by
        unfold lent openSigma
        simp only [GMap.mapFold_empty]
      simp only [openSigma] at this
      rw [this]; rfl
    isplitl [Hfpb1 Hfpb2]
    · isplitr
      · ipureintro; exact hW
      iexists ∅; iframe Hfpb1
      isplitl [Hfpb2]
      · ileft; iexact Hfpb2
      ipureintro; intro _ s v h; simp at h
    isplitl [Hmc1 Hout1 Hmln]
    · ileft; iframe
    · ipureintro; exact hok
  -- the transactions
  imod inv_alloc (txsN N) E (txsInv (GF := GF) B p sp C.txid) $$ [Htxs] with #Htxsi
  · inext
    unfold txsInv
    iexists ∅
    iframe Htxs
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- `metalock`
  ihave Hfa : fltxAuth (GF := GF) B ∅ $$ [Hfltx Hspr3]
  · unfold fltxAuth; iframe Hfltx; iexists none; iframe Hspr3; iright; ipureintro
    intro k v h; simp at h
  imod sync.init_Mutex (metaR (GF := GF) B db p) E _ $$ Hml
    [Hcur1 Hst2 Hcls1 Hop1 Hfli1 Hwa1 Hmo1 Hmlk Hfa Hro] with #Hmeta
  · inext
    unfold metaR
    iexists C, ∅, false, fli,
      methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    iframe
    ipureintro
    and_intros <;> first | exact hok.1 | exact hok.2.1 | exact htx.1 | trivial |
      (intro k t h; simp at h) | (intro _; exact ⟨hok.1, hok.2.1, htx.1⟩)
  ihave Hspare : sparePair (GF := GF) B db sp $$ [Hspare Hspr1]
  · unfold sparePair rdPair spareTok; iframe Hspr1; iexact Hspare
  imodintro
  iexists B
  unfold isBoltCoreP wdbCore wdbCoreG boltStateDef dblAt t0At
  simp only [openW, mapLen]
  iframe Hdbl Ht0 Hpkg Hos Hfix Hmeta Hmg Hsg Hpages Htxsi Hpool Hspare Hcls2 Hst1 Hbq
  iframe Hcur3 Hfl2 Hmap1 Hout2 Hwv2 Hfli2 Hop2 Hwa2 Hrw Hfile Hpath Hdsz Hmf2 Hosm Hfo Hfd Hmc2
  iframe Hmo2 Hwc Hwb Hst3 Hopn
  ipureintro
  exact ⟨htx.2, hdb, hN⟩

/-- **The core phase's ghost step** with no freelist yet (`db.freelist` nil). -/
theorem open_core [ThreadBoundLe GF (2 ^ 29)] (E : CoPset) (N : Namespace) (db sp f : Loc)
    (fd : w64) (p : GoString) (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta)
    (wb : Nat → List w8)
    (hok : storeOK (openSigma b L C wb))
    (htx : 1 ≤ C.txid ∧ C.txid < 2 ^ 62) (hN : (↑N : CoPset) ## ↑osN) (hdb : db ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed db sp ∗
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
      metaOsBytes p (DFrac.own (1 : Qp).half) C ∗ metaOsBytes p (DFrac.own (1 : Qp).half) C ∗
      ([∗list] s ∈ slotsOf C FLPg.empty, osSlot p s (wb s)) ∗
      wBytes p (wSlots (L / 4096) C FLPg.empty) wb m.size ∗
      metaCellsQ (1 : Qp).half.half (some (b, L)) C ∗
      metaCellsQ (1 : Qp).half.half (some (b, L)) C ∗
      ([∗list] s ∈ slotsOf C FLPg.empty,
        bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (wb s)) ∗
      wCells (some (b, L)) (wSlots (L / 4096) C FLPg.empty) ⊢
    |={E}=> ∃ B : BNs, isBoltCoreP B N db p sp C.txid ∗
      wdbOpen B db p (openW C b L m wb f fd) ∗ ghostVar B.cls (1 : Qp).half false ∗
      sparePair B db sp ∗ threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗
      boltStateDef B 1 (treeData C) ∗ dghostVar B.opn (DFrac.own 1) false := by
  iintro ⟨#Hpkg, #Hos, Hfix, Hml, Hmm, Hsl, Hop, Hfli, Hrest⟩
  imod open_core_fl E N db sp f fd p C b L m wb FLPg.empty interface.nil rfl hok htx hN hdb $$
    [Hfix Hml Hmm Hsl Hop Hfli Hrest] with ⟨%B, Hc, Hw, Hst, Hrest⟩
  · iframe Hpkg Hos Hfix Hml Hmm Hsl Hop Hfli Hrest
    unfold flRoOpt; simp only [↓reduceIte]; iempintro
  imodintro
  iexists B
  iframe Hc Hrest
  unfold wdbOpen
  have hw : ({ openW C b L m wb f fd with fl := FLPg.empty, fli := interface.nil } : WDb) =
      openW C b L m wb f fd := rfl
  rw [hw]
  iframe Hw
  isplitl [Hst]
  · simp only [openW]; iexact Hst
  ipureintro; exact ⟨rfl, rfl⟩

/-- **The writer phase** (design §3.11 "Open", step 4): `rwlock`'s resource, the writer side
idle with its freelist (after `loadFreelist`), the spare pair, no receipt yet (`t0` the current
txid), the opening over (`opnShot`, batch 41), and the full database. -/
theorem open_writer (E : CoPset) (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (w : WDb) (hw : wdbOK w) :
    isBoltCoreP (GF := GF) B N db p sp w.C.txid ∗
      threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗
      db.[DB, go!"rwlock"] ↦ (zero_val sync.Mutex) ∗
      wdbCore B db p w ∗ ghostVar B.st (1 : Qp).half.half (treeData w.C) ∗
      flPgOwn w.fli w.fl ∗ sparePair B db sp ∗ ghostVar B.cls (1 : Qp).half false ∗
      dghostVar B.opn (DFrac.own 1) false ⊢
    |={E}=> isBoltDef B N db := by
  iintro ⟨#Hc, #Hpool, Hrwl, Hcore, Hst, Hfl, Hsp, Hcls, Hopn⟩
  imod dghostVar_update true B.opn false $$ Hopn with Hopn
  imod dghostVar_persist B.opn 1 true $$ Hopn with #Hopn
  ihave #Hshot : opnShot (GF := GF) B $$ [Hopn]
  · unfold opnShot; iexact Hopn
  imod receipt_zero (GF := GF) with Hr
  imod sync.init_Mutex (rwR (GF := GF) B db p sp w.C.txid) E _ $$ Hrwl
    [Hcore Hst Hfl Hsp Hcls Hr] with #Hrw
  · inext
    unfold rwR
    ileft
    iexists w
    unfold wdbOwn
    rw [Nat.sub_self]
    iframe
    ipureintro; exact hw
  imodintro
  unfold isBoltDef isBoltP
  iexists p, sp, w.C.txid
  iframe #

end core

end bbolt
end EtcdGrove
end Perennial
