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

W5: `Close` syncs the file first (the fork's `1710e5c`: `fdatasync.specR`, in crash mode the size's
crash bounds collapsed), and both `DB.Close.spec` and the crash-mode `DB.Close.specC` are proved from
one core (`DB.Close.wp_core`), generic in what its commit point (`closeCommit`, where the file leaves
its mode: `bfile_out_dur`) is given: the other half of the committed data, and either nothing
(`DB.Close.spec`: the file given back as `fileHoldsM`) or, from the crash record that `specC`'s atomic
update opens, the crash names' registration, which puts the file in crash mode, so that it comes out
every byte durable (`fileHoldsMDur`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Close
public import Spec.go_etcd_io.bbolt.fdatasync
public import Proof.go_etcd_io.bbolt.Open.CloseTok
public import Proof.go_etcd_io.bbolt.Open.CloseFile
public import Proof.go_etcd_io.bbolt.Open.Congr
public import Proof.go_etcd_io.bbolt.Open.CloseFlx
public import Proof.go_etcd_io.bbolt.Inv.PmFile
public import Proof.go_etcd_io.bbolt.Inv.AuMask
import all Spec.go_etcd_io.bbolt.Api
import all Spec.go_etcd_io.bbolt.ApiCrash

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

/-- `close_res` with the file's `OsMeta` `m0` named (`closeMapResM`; nothing mapped: kept); `m0` has
the writer side's mappings (after `Close`'s sync). -/
private theorem close_resM (B : BNs) (N : Namespace) (p : BFile) (w : WDb) (hok : wdbOK w)
    (hL : ∀ b l, w.ms = some (b, l) → 8192 ≤ l) (hns : bNsOk p) (m0 : OsMeta)
    (hmm : m0.maps = w.m.maps) :
    ⊢ inv (pagesN N) (pagesInv (GF := GF) B p) -∗ bCsInv p -∗
      ghostVar B.cur (1 : Qp).half.half w.C -∗ ghostVar B.fl (1 : Qp).half w.fl -∗
      ghostVar B.map (1 : Qp).half w.ms -∗ ghostVar B.map (1 : Qp).half.half w.ms -∗
      ghostVar B.mtok 1 () -∗
      ghostVar B.wv (1 : Qp).half wIdle -∗ ghostVar B.out (1 : Qp).half false -∗
      metaCellsQ (GF := GF) (1 : Qp).half.half w.ms w.C -∗
      wCells (GF := GF) w.ms w.W -∗ bMeta p w.C [] m0 -∗
    |={⊤}=> closeMapResM (GF := GF) p w.C [] m0 w.ms ∗ closeKeep (GF := GF) p w.C [] m0 w.ms ∗
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
        rw [hmm, hok.1 b l hms]; exact GMap.lookup_singleton _ _
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
mapping), the size and the size's crash bounds `m0`'s (the `OsMeta` `close` was given, with the writer
side's mappings). -/
private theorem close_meta (p : BFile) (w : WDb) (m0 : OsMeta) (hmm : m0.maps = w.m.maps)
    (hok : wdbOK w) (hj : w.junk = none) :
    closeMapBack (GF := GF) p w.C [] m0 w.ms ∗ closeKeep (GF := GF) p w.C [] m0 w.ms ⊢
    ∃ m : OsMeta, bMeta p w.C [] m ∗ ⌜m.maps = ∅ ∧ m.size = m0.size⌝ ∗
      ⌜m.lo = m0.lo ∧ m.hi = m0.hi⌝ := by
  rcases hms : w.ms with _ | ⟨b, l⟩
  · simp only [closeMapBack, closeKeep]
    iintro ⟨-, Hm⟩
    iexists m0
    iframe Hm
    isplitr
    · ipureintro
      refine ⟨?_, rfl⟩
      rw [hmm]
      rcases hok.2.1 hms with h | ⟨jb, jl, hj', -⟩
      · exact h
      · rw [hj] at hj'; cases hj'
    · ipureintro; exact ⟨rfl, rfl⟩
  · simp only [closeMapBack, closeKeep]
    iintro ⟨Hm, -⟩
    iexists _
    iframe Hm
    isplitr
    · ipureintro
      refine ⟨?_, rfl⟩
      show GMap.delete b m0.maps = ∅
      rw [hmm, hok.1 b l hms]; exact GMap.delete_singleton _ _
    · ipureintro; exact ⟨rfl, rfl⟩

/-! ### The commit point (W5) -/

/-- What the commit point is given beside the committed data's other half: with `true`, the crash
names' registration (the crash record's), so that the file is in crash mode. -/
def closeEv (B : BNs) : Bool → IProp GF
  | true => iprop(∃ g : CsG, cnReg B (some g))
  | false => iprop(True)

/-- The file the commit point gives back: every byte durable (`fileHoldsMDur`) with the registration,
else `fileHoldsM`. -/
def closeOut (i : Ino) (D : Data) : Bool → IProp GF
  | true => fileHoldsMDurC i D
  | false => fileHoldsM i D

/-- **`Close`'s commit point** (W5): at `⊤`, opening into the database's namespace, the committed
data's other half (at `Dn`), the registration if `dur`, and, given `Dn = D` and the file
(`closeOut`), back to `⊤` with `Q`. -/
def closeCommit (γ : BoltName) (i : Ino) (D : Data) (Q : IProp GF) : IProp GF :=
  iprop(|={⊤, closeMask γ.ns}=> ∃ (dur : Bool) (Dn : Data), boltState γ (1 : Qp).half Dn ∗
    closeEv (bnsOf γ.gs) dur ∗ (⌜Dn = D⌝ ∗ closeOut i D dur ={closeMask γ.ns, ⊤}=∗ Q))

/-- `DB.Close.spec`'s commit point: the closer's other half, the file as `fileHoldsM`. -/
theorem closeCommit_plain (γ : BoltName) (i : Ino) (D : Data) :
    boltState (GF := GF) γ (1 : Qp).half D ⊢ closeCommit γ i D (fileHoldsM i D) := by
  unfold closeCommit
  iintro Hs
  imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := closeMask γ.ns)
    CoPset.subseteq_top) with Hcl
  imodintro
  iexists false, D
  simp only [closeEv, closeOut]
  isplitl [Hs]
  · iexact Hs
  isplitr
  · itrivial
  iintro ⟨-, Hf⟩
  imod Hcl
  imodintro
  iexact Hf

/-- The crash record's half of the committed data, and the crash names' registration it holds. -/
private theorem boltCrashRec_half (γ : BoltName) (i0 : Ino) (Dl Dn : Data) :
    boltCrashRec (GF := GF) γ i0 Dl Dn ⊢
      boltState γ (1 : Qp).half Dn ∗ ∃ g : CsG, cnReg (bnsOf γ.gs) (some g) := by
  unfold boltCrashRec cRecDef
  iintro ⟨%ν, %c, Hs, %hc, -, #Hreg, -⟩
  isplitl [Hs]
  · iapply (boltState_eq_V γ (1 : Qp).half Dn).2
    iexists ν; iexact Hs
  · iexists c.cg; iexact Hreg

/-- `DB.Close.specC`'s commit point: the atomic update opened (from `⊤`, the mask inside the
database's namespace), its record's half and registration; committed with the durable file. -/
theorem closeCommit_au (γ : BoltName) (i : Ino) (D : Data) (Q : IProp GF) :
    AU <{ ∃∃ (Dl Dn : Data), boltCrashRec (GF := GF) γ i Dl Dn }> @ ⊤ \ ↑γ.ns, ∅
      <{ ⌜Dn = D⌝ ∗ fileHoldsMDurC i D, COMM Q }> ⊢ closeCommit γ i D Q := by
  iintro Hau
  unfold closeCommit
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  iapply fupd_open_closeMask
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%Dl, %Dn, Hrec, Hucl⟩
  icases boltCrashRec_half γ i Dl Dn $$ Hrec with ⟨Hs, Hev⟩
  imodintro
  iexists true, Dn
  simp only [closeEv, closeOut]
  isplitl [Hs]
  · iexact Hs
  isplitl [Hev]
  · iexact Hev
  iintro ⟨%hD, Hf⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iapply fupd_close_closeMask
  iapply Hcommit
  isplitr
  · ipureintro; exact hD
  · iexact Hf

/-- **`DB.Close`, generic in its commit point** (W5): by the owner of half of the committed data `D`
and of the closer token, with the commit point `closeCommit` (the other half, and what the file
becomes): `nil` and the commit point's `Q`, or `¬ FsNoErr`. -/
private theorem DB.Close.wp_core
    (hOwned : DB.close.spec_owned (GF := GF) (hG := hG))
    (hOwnedM : DB.close.spec_ownedNoErrM (GF := GF) (hG := hG))
    (hSyncR : fdatasync.specR (GF := GF) (hG := hG))
    (db : Loc) (γ : BoltName) (i : Ino) (D : Data) (Q : IProp GF) :
    {{ isBolt (GF := GF) db γ ∗ boltIno γ i ∗ boltState γ (1 : Qp).half D ∗ boltCloser γ ∗
        closeCommit γ i D Q }}
      (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
    {{ (err : GoInterface), RET #err; (⌜err = GoInterface.nil⌝ ∗ Q) ∨ ⌜¬ FsNoErr⌝ }} := by
  wp_start as ⟨#Hdb, #Hino, Hst, Hclo, Hcc⟩
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
  icases isBoltCoreP_bfile _ _ _ _ _ _ $$ Hcore with ⟨#Hci, %hnsp⟩
  ihave #Hmode := isBoltCoreP_mode _ _ _ _ _ _ $$ Hcore
  ihave #Hsy := bMode_bSyncs _ _ _ _ _ $$ Hmode
  unfold isBoltCoreP
  icases Hcore with ⟨-, #Ht0a, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, -, #Hpi, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨-, -, ⟨%lg, #Hlg, #Hlgok⟩, #Hro, -, -, ⟨%nos, #Hns⟩, -⟩
  -- in crash mode `NoSync` is off (`bSyncs`), so `Close` syncs
  ihave %hnsc := bSyncs_ns db p nos $$ Hsy Hns
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
  icases Hst with ⟨%ν, Hs1, Hbq, -⟩
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
  -- `Close`'s sync (the fork's `1710e5c`): unless `NoSync`, `fdatasync(db)`: the file's `OsMeta` back
  -- with the same size and mappings, in crash mode the size's crash bounds the size (`fdatasync.specR`),
  -- or an error only a failing file system gives
  wp_join iprop(∃ (e : GoInterface) (m' : OsMeta), err_ptr ↦ e ∗ db_ptr ↦ db ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"file"] ↦ w.f ∗
      fileOwn w.f w.fd p.path (DFrac.own 1) ∗ osFd w.fd (DFrac.own 1) (dbFd p.ino) ∗
      bMeta p w.C [] m' ∗
      ⌜m'.size = w.m.size ∧ m'.maps = w.m.maps ∧ (e ≠ interface.nil → ¬ FsNoErr) ∧
        (FsNoErr → p.cs ≠ none → m'.lo = m'.size ∧ m'.hi = m'.size)⌝)
    at next with [err db Hop Hfile Hfo Hfd Hosm]
    as ⟨%e, %m', err, db, Hop, Hfile, Hfo, Hfd, Hosm, %hsyn⟩
  · try wp_auto
    cases nos
    · -- `NoSync` false: the sync
      try wp_auto
      wp_apply hSyncR db w.f w.fd p w.C [] w.m [] (fun _ => []) (DFrac.own 1) (DFrac.own 1) hnsp
          (fun _ => ⟨List.nodup_nil, (fun s hs => by cases hs), (fun r hr => by cases hr)⟩)
        $$ [Hfile Hfo Hfd Hosm] as %serr ⟨Hfile, Hfo, Hfd, -, Hsr⟩
      · iframe; iframe #
        try (iapply BigSepL.bigSepL_nil.2; iempintro)
      try wp_auto
      icases Hsr with (⟨%he, %m2, Hosm, %hm2⟩ | ⟨%he, -, Hosm⟩)
      · subst he
        wp_join_done
        iexists _, m2
        iframe
        ipureintro
        exact ⟨hm2.1, hm2.2.1, fun h => absurd rfl h, fun _ => hm2.2.2⟩
      · wp_join_done
        iexists _, w.m
        iframe
        ipureintro
        exact ⟨rfl, rfl, fun _ => he.2, fun h => absurd h he.2⟩
    · -- `NoSync` true: no sync (so not crash mode)
      try wp_auto
      wp_join_done
      iexists _, w.m
      iframe
      ipureintro
      exact ⟨rfl, rfl, fun h => absurd rfl h, fun _ hc => absurd (hnsc hc) (by decide)⟩
  obtain ⟨hms', hmm', hse, hlh⟩ := hsyn
  have hL : ∀ b l, w.ms = some (b, l) → 8192 ≤ l := by
    intro b l h
    have h1 := Hwok.2.2.2.2.2.2.2.2.1 b l h
    have h2 := treeOK_root' w.C htree
    have : 3 * 4096 ≤ w.C.hwm * 4096 := Nat.mul_le_mul_right _ (by omega : 3 ≤ w.C.hwm)
    omega
  imod close_resM _ γ.ns p w Hwok hL hnsp m' hmm' $$ Hpi Hci Hcur Hgfl Hgmap Hpmap Hptok
    Hgwv Hgout Hmc Hwc Hosm
    with ⟨Hres, Hosm0, Hcur, Hgfl, Hgmap, Hpmap, Hptok, Hgwv, Hgout⟩
  -- the store slots' bytes, `cls` set
  imod store_close _ γ.ns p ⊤ CoPset.subseteq_top w.C w.fl $$ [Hpi Hcur Hgfl Hgwv Hcls Hcls' Hgmap]
    with ⟨%bs, Hcur, Hgfl, Hgwv, Hcls, Hcls', Hgmap, HS, HX, %hS⟩
  · iframe; iframe #
  iunfold dbPathLk at Hpath
  icases Hpath with ⟨Hpath, Htok, -⟩
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
      as %cerr ⟨-, Hop, Hfli, Hwa, Hpath, Hmf, Hdsz, Hfile⟩
    · iframe; iframe #
      isplitl [Hres]
      · iapply closeMapResM_res $$ Hres
      iright; iexists w.fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
    try wp_auto
    -- `if err == nil { err = cerr }`
    wp_join iprop(∃ v : GoInterface, err_ptr ↦ v) at next with [err cerr] as ⟨%v, err⟩
    · cases e with
      | nil =>
        try wp_auto
        wp_join_done
        try (iexists _; iframe)
      | ok ei =>
        try wp_auto
        wp_join_done
        try (iexists _; iframe)
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
  -- no error: the sync's error is `nil`, `close` gives the `OsMeta` back
  have he : e = interface.nil := Classical.byContradiction fun h => hse h hne
  subst he
  wp_apply hOwnedM hne db lg DFrac.discard w.fli _ p.path w.ms p w.C [] m' w.f w.fd p.path _ Ht0.2.1
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
  -- the file: its `OsMeta`, its bytes, an image of the committed state
  icases close_meta p w m' hmm' Hwok hj $$ [Hback Hosm0] with ⟨%m, Hm, %hm0, %hmlh⟩
  · iframe
  have hm : m.maps = ∅ ∧ m.size = w.m.size := ⟨hm0.1, hm0.2.trans hms'⟩
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
  -- the commit point (W5): the file out of its mode (in crash mode the crash invariant closed with the
  -- two halves of `bq`), the closer's commit point given the file
  have hxl : xs.length = m.size := by rw [hm.2]; exact hxs.2
  ihave HQ : (|={⊤}=> Q) $$ [Hcc Hm Hxs Hbq Hs1]
  · unfold closeCommit
    imod Hcc with ⟨%dur, %Dn, HsT, Hev, Hfin⟩
    unfold boltState boltStateDef boltStateVDef
    icases HsT with ⟨%νT, HsT1, HbqT, -⟩
    icombine Hs1 HsT1 gives % ⟨_, hDn⟩
    ihave Hbq := (ghostVar_split_half (bnsOf γ.gs).bq 1 ()).2 $$ [Hbq HbqT]
    · iframe
    imod bfile_out_dur _ _ _ _ p w.C [] m xs hxl (closeMask γ.ns) (crash_sub_closeMask γ.ns)
      $$ Hmode Hm Hxs Hbq with ⟨Hm, Hxs, %hdur⟩
    ihave Hout : closeOut (GF := GF) p.ino (treeData w.C) dur $$ [Hm Hxs Hev]
    · cases dur
      · -- the plain file
        simp only [closeOut]
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
      · -- crash mode (the registration): every byte durable, the size's crash bounds the size
        simp only [closeOut, closeEv]
        icases Hev with ⟨%g, #Hreg⟩
        ihave #Hreg' := bMode_cnReg _ _ _ _ $$ Hmode
        ihave %hreg := cnReg_agree (bnsOf γ.gs) (some g) (p.cs.map CsN.cg) $$ [Hreg Hreg']
        · iframe #
        have hcs : p.cs ≠ none := by
          intro h; simp [h] at hreg
        obtain ⟨hd, hcut, l, hxl', hxls⟩ := hdur hcs
        have hxd : (xs.map Prod.fst).map durB = xs := by
          rw [List.map_map]
          conv => rhs; rw [← List.map_id xs]
          apply List.map_congr_left
          intro x hx
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
          exact (hd k xs[k] (List.getElem?_eq_getElem hk) (fun r hr => by cases hr)).symm
        obtain ⟨hlo, hhi⟩ := hlh hne hcs
        have hlen : (xs.map Prod.fst).length = w.m.size := by rw [List.length_map]; exact hxs.2
        unfold fileHoldsMDurC
        iexists m, xs.map Prod.fst
        rw [hxd]
        iframe Hm Hxs
        isplitr
        · ipureintro
          refine ⟨hm.1, by rw [hm.2, hlen], by rw [hmlh.1, hlo, hms', hlen],
            by rw [hmlh.2, hhi, hms', hlen],
            by rw [hlen]; have := hroot.1; have := hroot.2; omega, hcut, ⟨l, hxl', fun x hx => by
              rw [hxls x hx, hm.2, hlen]⟩, ?_, ?_⟩
          · unfold boltImage
            rw [hlen, hxs.1]
            exact ⟨hsz, hfok⟩
          · unfold boltMaxMapSize; rw [hlen]; exact hszw.1
        unfold boltImageRcpt
        rw [hxs.1]
        iapply fileRcpt_intro _ w.C himg hmo $$ Hrcm
    iapply Hfin
    isplitr
    · ipureintro; exact (Prod.mk.inj hDn).1.symm
    · iexact Hout
  imod HQ
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
  iexact HQ

omit [ExtSemantics fsExt] [FsSemOk] hos in
theorem DB.Close.wp_proof
    (hOwned : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_owned (GF := GF) (hG := hG))
    (hOwnedM : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_ownedNoErrM (GF := GF) (hG := hG))
    (hSyncR : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      fdatasync.specR (GF := GF) (hG := hG)) :
    DB.Close.spec (GF := GF) (hG := hG) := by
  intro _ _ _ db γ i D
  iintro %Φ ⟨#Hdb, #Hino, Hst, Hclo⟩ HΦ
  have hsplit : boltState (GF := GF) γ 1 D ⊣⊢
      boltState γ (1 : Qp).half D ∗ boltState γ (1 : Qp).half D := by
    have h := (boltState_fractional (GF := GF) γ D).fractional (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at h
    exact h
  icases hsplit.1 $$ Hst with ⟨Hst, Hst2⟩
  ihave Hcc := closeCommit_plain γ i D $$ Hst2
  iapply DB.Close.wp_core hOwned hOwnedM hSyncR db γ i D (fileHoldsM i D) $$ [Hdb Hino Hst Hclo Hcc]
  · iframe; iframe #
  inext
  iintro %err Hpost
  iapply HΦ
  iexact Hpost

omit [ExtSemantics fsExt] [FsSemOk] hos in
theorem DB.Close.wp_proofC
    (hOwned : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_owned (GF := GF) (hG := hG))
    (hOwnedM : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      DB.close.spec_ownedNoErrM (GF := GF) (hG := hG))
    (hSyncR : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      fdatasync.specR (GF := GF) (hG := hG)) :
    DB.Close.specC (GF := GF) (hG := hG) := by
  intro _ _ _ db γ i D Q
  iintro %Φ ⟨#Hdb, #Hino, Hst, Hclo, Hau⟩ HΦ
  ihave Hcc := closeCommit_au γ i D Q $$ Hau
  iapply DB.Close.wp_core hOwned hOwnedM hSyncR db γ i D Q $$ [Hdb Hino Hst Hclo Hcc]
  · iframe; iframe #
  inext
  iintro %err Hpost
  iapply HΦ
  iexact Hpost

end proof

end bbolt
end EtcdGrove
end Perennial
