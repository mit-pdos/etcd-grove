/-
`DB.Close` by the closer token's holder, an internal spec (`DB.Close.specTok`, session S3f) and the pieces the
canonical `DB.Close.spec`'s proof (`DB__Close.lean`) shares (U11d, `notes/bbolt-proof-plan.md`): `rwlock`,
`metalock` and `mmaplock` (through its guard, `Pm 1`), deferred unlocks, then `db.close()`. Closed
already (`rwR`'s `closedR`): `close` sees `opened` false (`DB.close.spec_closed`). Open: the writer
side idle (`wdbOwn`), `metaR`'s and `Pm 1`'s halves join the fields, the mapping's cells are
gathered from the store (`store_gather`), the metas' quarters, the `W` slots and the partial last
slot (as `Mmap/RemapGather.remap_gather`, with the writer idle), and `close` runs over owned fields
(`DB.close.spec_owned`, `ms` the mapping); then `metaR` and `rwR` are closed (`cls` set), `Pm 1`
holds the cleared fields.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.PmFile
public import Spec.go_etcd_io.bbolt.Api
public import Proof.go_etcd_io.bbolt.Open.Close
public import Proof.go_etcd_io.bbolt.Mmap.RemapGather
public import Proof.go_etcd_io.bbolt.Mmap.RemapLost
public import Perennial.Proof.sync.Results
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

/-- The root page of a well-formed committed state lies in `[2, hwm)` (as `Txn/WInit.treeOK_root`). -/
theorem treeOK_root' [GooseExts] (C : CommitSt) (htree : treeOK C) : 2 ≤ C.root ∧ C.root < C.hwm := by
  obtain ⟨⟨hwf, -⟩, -⟩ := htree
  cases hwf with
  | page _ _ h2 hlt _ _ _ _ => exact ⟨h2, hlt⟩

/-- Two halves of a points-to, as the whole. -/
theorem pt_join {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
      typedPointsto l v (DFrac.own (1 : Qp).half) ⊢ typedPointsto l v (DFrac.own 1) := by
  refine ((typedPointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).2.trans ?_
  rw [DFrac.op_own, Qp.half_add_half]

/-- A whole points-to as two halves. -/
theorem pt_split {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  refine Entails.trans ?_ ((typedPointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).1
  rw [DFrac.op_own, Qp.half_add_half]

variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]

/-- Two halves of the mapping fields, as the whole. -/
theorem mapFields_join2 (db : Loc) (ms : MapSt) :
    mapFields (GF := GF) db (DFrac.own (1 : Qp).half) ms ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) ms ⊣⊢ mapFields (GF := GF) db (DFrac.own 1) ms := by
  have h := (mapFields_dfractional (GF := GF) db ms).dfractional (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h.symm

/-- **The idle writer's gather** (`Close`, with `Pm 1`'s `map` quarter and `mtok`, the writer
side's `map` half and meta quarter): the mapping's cells, the store's slots out. -/
theorem close_gather (B : BNs) (N : Namespace) (p : BFile) (w : WDb) (b : Loc) (L : Nat)
    (hok : wdbOK w) (hms : w.ms = some (b, L)) (hL : 8192 ≤ L) :
    ⊢ inv (pagesN N) (pagesInv (GF := GF) B p) -∗
      ghostVar B.cur (1 : Qp).half.half w.C -∗ ghostVar B.fl (1 : Qp).half w.fl -∗
      ghostVar B.map (1 : Qp).half (some (b, L) : MapSt) -∗
      ghostVar B.map (1 : Qp).half.half (some (b, L) : MapSt) -∗ ghostVar B.mtok 1 () -∗
      ghostVar B.wv (1 : Qp).half wIdle -∗ ghostVar B.out (1 : Qp).half false -∗
      metaCellsQ (GF := GF) (1 : Qp).half.half (some (b, L)) w.C -∗
      wCells (GF := GF) (some (b, L)) w.W -∗
    |={⊤}=> (∃ vf, cellsR (GF := GF) b 0 L vf) ∗
      ghostVar B.cur (1 : Qp).half.half w.C ∗ ghostVar B.fl (1 : Qp).half w.fl ∗
      ghostVar B.map (1 : Qp).half (none : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostVar B.out (1 : Qp).half false := by
  iintro #Hinv Hcur Hfl Hmap Hmapq Htok Hwv Hout Hmc Hwc
  imod store_gather B N p ⊤ CoPset.subseteq_top w.C w.fl b L wIdle rfl
    $$ [Hinv Hcur Hfl Hmap Hmapq Htok Hwv Hout]
    with ⟨%bs, %W, Hcur, Hfl, Hmap, Hmapq, Htok, Hwv, Hout, -, %hW, %hfacts, HS, Hml⟩
  · isplitr
    · iexact Hinv
    isplitl [Hcur]
    · iexact Hcur
    isplitl [Hfl]
    · iexact Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hmapq]
    · iexact Hmapq
    isplitl [Htok]
    · iexact Htok
    isplitl [Hwv]
    · iexact Hwv
    · iexact Hout
  obtain ⟨hmo, hsl⟩ := hfacts
  ihave Hc : ∃ vf, cellsR (GF := GF) b 0 L vf $$ [Hmc Hml HS Hwc]
  · unfold metaCellsQ
    icases Hmc with ⟨H0, H1⟩
    icases Hml with ⟨H0', H1'⟩
    ihave H0 := (bytes_quarters b w.C.m0).1 $$ [H0 H0']
    · iframe
    ihave H1 := (bytes_quarters _ w.C.m1).1 $$ [H1 H1']
    · iframe
    icases wCells_gather w hok b L hms $$ Hwc with ⟨Hws, Hp⟩
    have hP := slots_partition (L / 4096) (slotsOf w.C w.fl) (wSlots (L / 4096) w.C w.fl)
      (by omega) (slotsOf_nodup _ _) (wSlots_nodup _ _ _)
      (fun s hs => ⟨(hsl s hs).1, (hsl s hs).2.1⟩)
      (fun s => by rw [mem_wSlots])
    iapply mapCells_gather b L w.C.m0 w.C.m1 _ _ bs hmo.1 hmo.2.1 (fun s hs => (hsl s hs).2.2) hP
    iframe
  imodintro
  iframe Hc Hcur Hfl
  isplitl [Hmap]
  · iexact Hmap
  isplitl [Hmapq]
  · iexact Hmapq
  iframe

/-- **What `Close` unmaps, gathered** (the idle writer side's resources and `Pm 1`'s): the
mapping's `closeMapRes`, the mapping's ghost state cleared. -/
theorem close_res (B : BNs) (N : Namespace) (p : BFile) (w : WDb) (hok : wdbOK w)
    (hL : ∀ b l, w.ms = some (b, l) → 8192 ≤ l) (hns : bNsOk p) :
    ⊢ inv (pagesN N) (pagesInv (GF := GF) B p) -∗ bCsInv p -∗
      ghostVar B.cur (1 : Qp).half.half w.C -∗ ghostVar B.fl (1 : Qp).half w.fl -∗
      ghostVar B.map (1 : Qp).half w.ms -∗ ghostVar B.map (1 : Qp).half.half w.ms -∗
      ghostVar B.mtok 1 () -∗
      ghostVar B.wv (1 : Qp).half wIdle -∗ ghostVar B.out (1 : Qp).half false -∗
      metaCellsQ (GF := GF) (1 : Qp).half.half w.ms w.C -∗
      wCells (GF := GF) w.ms w.W -∗ bMeta p w.C [] w.m -∗
    |={⊤}=> closeMapRes (GF := GF) p w.ms ∗
      ghostVar B.cur (1 : Qp).half.half w.C ∗ ghostVar B.fl (1 : Qp).half w.fl ∗
      ghostVar B.map (1 : Qp).half (none : MapSt) ∗
      ghostVar B.map (1 : Qp).half.half (none : MapSt) ∗ ghostVar B.mtok 1 () ∗
      ghostVar B.wv (1 : Qp).half wIdle ∗ ghostVar B.out (1 : Qp).half false := by
  iintro #Hinv #Hci Hcur Hfl Hmap Hmapq Htok Hwv Hout Hmc Hwc Hosm
  rcases hms : w.ms with _ | ⟨b, l⟩
  · unfold closeMapRes
    imodintro
    iframe Hcur Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hmapq]
    · iexact Hmapq
    iframe
  · imod close_gather B N p w b l hok hms (hL b l hms) $$ Hinv Hcur Hfl Hmap Hmapq Htok Hwv Hout
      Hmc Hwc with ⟨⟨%vf, Hc⟩, Hcur, Hfl, Hmap, Hmapq, Htok, Hwv, Hout⟩
    imodintro
    unfold closeMapRes
    isplitl [Hosm Hc]
    · iexists w.C, [], w.m, vf
      iframe
      isplitr
      · ipureintro
        refine ⟨by have := hL b l hms; omega, ?_, hns⟩
        rw [hok.1 b l hms]; exact GMap.lookup_singleton _ _
      iexact Hci
    iframe Hcur Hfl
    isplitl [Hmap]
    · iexact Hmap
    isplitl [Hmapq]
    · iexact Hmapq
    iframe

instance Pm_timeless' (B : BNs) (db : Loc) (q : Qp) : Timeless (Pm (GF := GF) B db q) := by
  have : ∀ ms : MapSt, Timeless (mapFields (GF := GF) db (DFrac.own q.half) ms) := by
    intro ms; rcases ms with _ | ⟨b, l⟩ <;> simp only [mapFields] <;> infer_instance
  unfold Pm; infer_instance

/-- **`db.close()` over owned fields, its error satisfying `Q`** (`DB.close.spec_owned` at
`Q := fun _ => True`, `DB.close.spec_ownedNoErr` at `Q := (· = nil)` under the premises): what
`DB.Close`'s proof (`DB.Close.wp_proofQ`) is generic in. -/
private abbrev DB.close.spec_ownedQ (Q : GoInterface → Prop) : Prop :=
  ∀ (db : Loc) (lg : GoInterface) (dqr : DFrac) (fli : GoInterface) (wa : GoFunc) (s : GoString)
    (ms : MapSt) (p : BFile) (f : Loc),
  db ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗ db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ fli ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ wa ∗ db.[DB, go!"path"] ↦ s ∗
      mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
      closeMapRes p ms ∗
      db.[DB, go!"file"] ↦ f ∗
      (⌜f = null⌝ ∨ ∃ (fd : w64) (name : GoString) (d : OsFd), fileOwn f fd name (DFrac.own 1) ∗
        osFd fd (DFrac.own 1) d ∗ lockToks fd d) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜Q err⌝ ∗ db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ false ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ func.nil ∗ db.[DB, go!"path"] ↦ (go!"" : GoString) ∗
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      db.[DB, go!"file"] ↦ null }}

private theorem DB.close.spec_ownedQ_of (h : DB.close.spec_owned (GF := GF) (hG := hG)) :
    DB.close.spec_ownedQ (GF := GF) (hG := hG) (fun _ => True) := by
  intro db lg dqr fli wa s ms p f hdb
  iintro %Φ Hpre HΦ
  iapply h db lg dqr fli wa s ms p f hdb $$ Hpre
  inext
  iintro %err Hpost
  iapply HΦ
  isplitr
  · ipureintro; trivial
  iexact Hpost

/-- **`DB.Close`, generic in its `close`'s error** (`Q`, which `nil` satisfies: `close` of a closed
database returns `nil`). -/
private theorem DB.Close.wp_proofQ (Q : GoInterface → Prop) (hQ : Q interface.nil)
    (hOwned : DB.close.spec_ownedQ (GF := GF) (hG := hG) Q) (db : Loc) (γ : BoltName) :
    {{ isBolt (GF := GF) db γ ∗ boltCloser γ }}
      (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; ⌜Q err⌝ }} := by
  wp_start as ⟨#Hdb, Hclo⟩
  iunfold boltCloser at Hclo
  unfold isBolt isBoltDef isBoltP
  icases Hdb with ⟨%p, %sp, %t0, #Hcore, #Hrw, -⟩
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
  icases Hwo with ⟨Hcg, Hst, -, -, -⟩
  iunfold wdbCore at Hcg
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hop, Hwa, -, Hfile, Hpath,
    Hdsz, Hmf, Hosm, Hfo, Hfd, Hmc, -, Hwc, -, Hjk⟩
  -- the file given up: `DB.Close` does not give it back
  iclear Hjk
  icombine Hfli Hfl' gives %hfli
  subst hfli
  icombine Hwa Hwa' gives %hwa
  subst hwa
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  subst hC
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
  imod close_res _ γ.ns p w Hwok hL (bNsOk_none Ht0.2.2.2) $$ Hpi Hci Hcur Hgfl Hgmap Hpmap Hptok
    Hgwv Hgout Hmc Hwc Hosm
    with ⟨Hres, Hcur, Hgfl, Hgmap, Hpmap, Hptok, Hgwv, Hgout⟩
  -- the `flock` token (`dbPathLk`), for `close`'s `funlock` and `File.Close`
  iunfold dbPathLk at Hpath
  icases Hpath with ⟨Hpath, Htok, -⟩
  wp_apply hOwned db lg DFrac.discard w.fli _ p.path w.ms p w.f Ht0.2.1 $$ [Hop Hfli Hwa Hpath Hmf Hdsz
    Hres Hfile Hfo Hfd Htok]
    as %err ⟨%hq, -, Hop, Hfli, Hwa, Hpath, Hmf, Hdsz, Hfile⟩
  · iframe; iframe #
    iright; iexists w.fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
  try wp_auto
  -- the deferred unlocks
  icases (mapFields_join2 db (none : MapSt)).2 $$ Hmf with ⟨Hmf1, Hmf2⟩
  icases pt_split _ _ $$ Hfile with ⟨Hfile, -⟩
  ihave Hpf := pmFile_null (bnsOf γ.gs) db (DFrac.own (1 : Qp).half) (t0, p.ino) none rfl
    $$ [Hfile]
  · iframe; iunfold t0At at Ht0a; iexact Ht0a
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hmml Hpmap Hmf1 Hptok Hpf]
  · iunfold Pm; iexists none; iframe
  try wp_auto
  imod store_close _ γ.ns p ⊤ CoPset.subseteq_top w.C w.fl $$ [Hpi Hcur Hgfl Hgwv Hcls Hcls' Hgmap]
    with ⟨%bs, Hcur, Hgfl, Hgwv, Hcls, Hcls', Hgmap, -, -, -⟩
  · iframe; iframe #
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
  wp_apply sync.Mutex.wp_Unlock _ (rwR (bnsOf γ.gs) db p sp t0) $$ [$Hsync $Hrw $Hrwl Hcls Hcur Hst
    Hgfl Hgmap Hmf2 Hgout Hgwv Hop Hfli Hwa Hclo]
  · iunfold rwR; iright; iunfold closedR
    iframe Hcls Hclo
    iexists w.C, w.fl, none
    iframe
  try wp_auto
  iapply HΦ
  ipureintro; exact hq

/-- **`db.Close()` by the closer token's holder, nothing about the file** (an internal spec, session
S3f: `Open`'s error exits after the database is built close it while keeping the client's
`boltState`, which `DB.Close.spec`, the canonical spec, consumes). -/
abbrev DB.Close.specTok : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (db : Loc) (γ : BoltName),
  {{ isBolt (GF := GF) db γ ∗ boltCloser γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

omit [ExtSemantics fsExt] [FsSemOk] hos in
theorem DB.Close.wp_proofTok
    (hOwned : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.close.spec_owned (GF := GF) (hG := hG)) :
    DB.Close.specTok (GF := GF) (hG := hG) := by
  intro _ _ _ db γ
  iintro %Φ Hpre HΦ
  iapply DB.Close.wp_proofQ (fun _ => True) trivial (DB.close.spec_ownedQ_of hOwned) db γ $$ Hpre
  inext
  iintro %err -
  iapply HΦ
  itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
