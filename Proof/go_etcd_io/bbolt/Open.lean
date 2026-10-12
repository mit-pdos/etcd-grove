module
public import Spec.go_etcd_io.bbolt.Open
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.DB__close
public import Spec.go_etcd_io.bbolt.DB__getPageSize
public import Spec.go_etcd_io.bbolt.flock
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.os.OpenFile
public import Spec.os.File__Name
public import Spec.os.File__Stat
public import Spec.io.fs.FileInfo__Size
public import Proof.go_etcd_io.bbolt.DBAcc
public import Proof.os.FileLemmas
public import Proof.go_etcd_io.bbolt.MmapSize
public import Proof.sync.PoolModel
public import Spec.go_etcd_io.bbolt.DB__loadFreelist
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__init
public import Proof.go_etcd_io.bbolt.DBOpenInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.freelist

section openrec
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The database's fields once `Open` has set them. -/
def openDBRec (ov : Options) (dl : Loc) (fname : GoString) (f : Loc) (b : GoSlice) (sz : w64)
    (ps : Nat) (st : Loc) (fli : GoInterface) (ofn wa : GoFunc) : DB :=
  DB.mk false ov.NoSync' false ov.FreelistType' ov.NoGrowSync' true ov.MmapFlags' (W64 1000)
    (W64 10000000) (W64 16777216) ov.MaxSize' false
    (GoInterface.ok { ty := DefaultLogger.ty.PointerType, v := #dl }) fname
    ofn f b b.ptr sz (b.ptr +ₗ 16)
    (b.ptr +ₗ ((ps + 16 : Nat) : Int)) (W64 (ps : Int)) true null st fli
    (zero_val sync.Once) (zero_val sync.Pool) false null false false (zero_val sync.RWMutex)
    (zero_val sync.RWMutex)
    { writeAt' := wa } false

end openrec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

-- An error once the file is open and locked (before the mapping): close the database (its
-- file given back), log, return the error.
set_option hygiene false in
macro "open_close_err" bsF:term:max pf:term:max : tactic => `(tactic| (
  try wp_auto
  try iStructNamed ops
  wp_apply hclose «$r0_ptr» f fd $bsF path _ false _ _ slice.nil _ _ _ _ 0
    $$ [opened freelist writeAt meta0 meta1 dataref data datasz file readOnly path Hfb Hfm Hfp]
    as %cerr Hcl
  · iframe; iright; iframe; iframe #
    isplitr
    · ipureintro; exact Hfnn
    ileft; iframe; try (ipureintro; rfl); try (iexists _; iframe)
  icases Hcl with ⟨-, -, -, -, -, -, -, -, -, readOnly, -, (%Hn | Hfs)⟩
  · exact absurd Hn Hfnn
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  wp_apply hErrorf dl _ _ $$ [Hdlok]
  · iframe; iexact Hdlok
  try wp_auto
  iapply HΦ
  iframe
  iright
  isplitr
  · ipureintro; intro h; cases h
  iexists $bsF
  iframe
  ipureintro; exact $pf))

set_option hygiene false in
macro "oc_err_exit" bsF:term:max pf:term:max : tactic => `(tactic| (
  try wp_auto
  try iStructNamed ops
  wp_apply hclose «$r0_ptr» f fd $bsF path _ false _ _ slice.nil _ _ _ _ 0
    $$ [opened freelist writeAt meta0 meta1 dataref data datasz file readOnly path Hfb Hfm Hfp]
    as %cerr Hcl
  · iframe; iright; iframe; iframe #
    isplitr
    · ipureintro; exact Hfnn
    ileft; iframe; try (ipureintro; rfl); try (iexists _; iframe)
  icases Hcl with ⟨-, -, -, -, -, -, -, -, -, readOnly, -, (%Hn | Hfs)⟩
  · exact absurd Hn Hfnn
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  wp_apply hErrorf dl _ _ $$ [Hdlok]
  · iframe; iexact Hdlok
  try wp_auto
  iright
  iexists _, GoInterface.ok ei, $bsF
  isplitr
  · ipureintro; exact ⟨rfl, (fun h => by cases h), $pf⟩
  iframe))

open Lean Elab Tactic Meta in
/-- `open_join [H…] [K…] (Rx) (Err)`: bind the next `if:` and prove it once per case up to
`fun v => (⌜v = executeVal⌝ ∗ F ∗ Rx) ∨ Err v`, `F` the spatial hypotheses but `H…` and `K…`
at their current types (`wp_join`'s frame mode, with an exit for a `return`); the cases get every
spatial hypothesis but `H…`. The continuation introduces `v` and either `%Hv`, `F` under its
names (an inaccessible one as `HjoinN`) and `HRx`, or `HErr`. -/
elab "open_join" " [" ex:ident* "]" " [" kx:ident* "]" " (" rx:term ")" " (" er:term ")" : tactic =>
  withMainContext do
  let some g := Iris.ProofMode.parseIrisGoal? (← instantiateMVars (← getMainTarget))
    | throwError "open_join: not in the Iris proof mode"
  let exn := ex.map (·.getId)
  let kxn := kx.map (·.getId)
  let mut tys : Array Term := #[]
  let mut pats : Array (TSyntax `icasesPat) := #[]
  let mut k := 0
  for iv in g.hyps.spatialIVarIds .topToBottom do
    let some (name, _, _, ty) := g.hyps.getDecl? iv | continue
    if exn.contains name || kxn.contains name then continue
    tys := tys.push (← Term.exprToSyntax ty)
    let nm : Ident := if name.hasMacroScopes || name.isInaccessibleUserName then
      mkIdent (Name.mkSimple s!"Hjoin{k}") else mkIdent name
    k := k + 1
    pats := pats.push (← `(icasesPat| $nm:ident))
  let mut r : Term := rx
  for t in tys.reverse do
    r ← `(iprop($t ∗ $r))
  let Q ← `(fun (v : val) => iprop((⌜v = executeVal⌝ ∗ $r) ∨ $er v))
  let ids : Array (TSyntax `frameIdent) ← ex.mapM fun i => `(frameIdent| $i:ident)
  evalTactic (← `(tactic| wp_bind (if: _ then _ else _)))
  evalTactic (← `(tactic| iapply (wp_join_gen $Q) $$ [- $ids*]))
  match ← getGoals with
  | gCase :: gCont :: rest =>
    setGoals [gCont]
    let hv := mkIdent `Hv
    let hrx := mkIdent `HRx
    let herr := mkIdent `HErr
    let vv := mkIdent `v
    let all := #[(← `(icasesPat| %$hv:ident))] ++ pats ++ #[(← `(icasesPat| $hrx:ident))]
    let alts : Array (TSyntax ``Iris.ProofMode.icasesPatAlts) ←
      all.mapM fun p => `(Iris.ProofMode.icasesPatAlts| $p:icasesPat)
    let main ← `(icasesPat| ⟨$alts,*⟩)
    evalTactic (← `(tactic| iintro %$vv:ident ($main:icasesPat | $herr:ident)))
    let conts ← getGoals
    setGoals (gCase :: conts ++ rest)
  | _ => throwError "open_join: unexpected goals"


theorem open_sz_eq (sz : w64) (ps : Nat) (h : sint.Z sz = (ps : Int)) (hps : ps < 2 ^ 32) :
    sz = W64 (ps : Int) := by
  word

theorem open_unat (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by word

theorem open_len_le (n : Nat) (sz : w64) (h : (n : Int) ≤ sint.Z sz) : n ≤ sint.nat sz := by word

theorem open_mul (f : w64) (ps : Nat) (h : uint.nat f * ps < 2 ^ 47) (hps : ps < 2 ^ 32) :
    uint.Z (f * W64 (ps : Int)) = ((uint.nat f * ps : Nat) : Int) := by
  have hc : (W64 (ps : Int)).toNat = ps := by simp; omega
  have hf : uint.nat f = f.toNat := by word
  rw [hf] at h ⊢
  show (((f * W64 (ps : Int)).toNat : Nat) : Int) = _
  rw [BitVec.toNat_mul, hc, Nat.mod_eq_of_lt (by omega)]

theorem open_sint_ps (ps : Nat) (h : ps < 2 ^ 32) : sint.Z (W64 (ps : Int)) = ps := by word

theorem open_snat_ps (ps : Nat) (h : ps < 2 ^ 32) : sint.nat (W64 (ps : Int)) = ps := by word

theorem open_sz_w64 (sz : w64) (h : 0 < sint.Z sz) : W64 ((sint.nat sz : Nat) : Int) = sz := by word

theorem open_snat_le (sz : w64) (h : sint.Z sz ≤ 281474976710655) (h0 : 0 < sint.Z sz) :
    sint.nat sz ≤ 281474976710655 := by word

theorem open_ps_ne (ps : Nat) (h1 : 80 ≤ ps) (h2 : ps < 2 ^ 32) : W64 (ps : Int) ≠ W64 0 := by
  intro e
  have h3 : uint.Z (W64 (ps : Int)) = ps := w64_nat_z ps (by omega)
  rw [e] at h3
  have h0 : uint.Z (W64 0) = 0 := by word
  omega

theorem open_len_ne (n : Nat) (h1 : 0 < n) (h2 : n < 2 ^ 47) : W64 (n : Int) ≠ W64 0 := by
  intro e
  have h3 : uint.Z (W64 (n : Int)) = n := w64_nat_z n (by omega)
  rw [e] at h3
  have h0 : uint.Z (W64 0) = 0 := by word
  omega

/-- `getPageSize`'s result for a file whose page size it finds: `ps`. -/
theorem open_gps (bs : List w8) (ps : Nat) (sz : w64) (hok : pageSizeOK bs ps) (hps : ps < 2 ^ 32)
    (h : (4096 ≤ bs.length ∧ metaValid (metaAt bs 16) ∧
            sint.Z sz = uint.Z (metaAt bs 16).pageSize') ∨
          (∃ i < 15, 1024 * 2 ^ i + 1024 < bs.length ∧
            metaValid (metaAt (probeAt bs (1024 * 2 ^ i)) 16) ∧
            sint.Z sz = uint.Z (metaAt (probeAt bs (1024 * 2 ^ i)) 16).pageSize') ∨
          sz = W64 (ps : Int)) :
    sz = W64 (ps : Int) := by
  rcases h with ⟨hl, hv, hs⟩ | ⟨i, hi, hl, hv, hs⟩ | h
  · have := hok.1 hl hv; rw [this] at hs; exact open_sz_eq sz ps hs hps
  · have := hok.2 i hi hl hv; rw [this] at hs; exact open_sz_eq sz ps hs hps
  · exact h

instance statsInv_fractional : Fractional (statsInv (GF := GF)) :=
  ⟨fun _ _ => by
    unfold statsInv
    constructor
    · iintro _; isplitl; itrivial; itrivial
    · iintro _; itrivial⟩

set_option maxRecDepth 20000 in
set_option pp.deepTerms true in
set_option pp.maxSteps 5000000 in
set_option maxHeartbeats 4000000 in
theorem Open.wp_proof (hDL : getDiscardLogger.spec (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hOpenFile : os.OpenFile.spec (GF := GF) (hG := hG))
    (hName : os.File.Name.spec (GF := GF) (hG := hG))
    (hflock : flock.spec (GF := GF) (hG := hG))
    (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : fs.FileInfo.Size.spec (GF := GF) (hG := hG))
    (hgps : DB.getPageSize.spec (GF := GF) (hG := hG))
    (hinit : DB.init.spec (GF := GF) (hG := hG))
    (hmmap : DB.mmap.spec (GF := GF) (hG := hG))
    (hload : DB.loadFreelist.spec (GF := GF) (hG := hG))
    (hhsf : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hclose : DB.close.spec (GF := GF) (hG := hG))
    (hErrorf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG)) :
    Open.spec (GF := GF) (hG := hG) := by
  intro path mode ol ov dq bs ps hC hro hlg hof hft hnfs hml hps hims0 hims1 hps80 hps32 hbs0
  wp_start as ⟨Hov, Hfs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hov with ⟨Hov, %Holnn⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  rw [decide_eq_false Holnn]
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hdbnn⟩
  iStructNamed «$r0»
  try wp_auto
  simp only [internal.common.DefaultMaxBatchSize, internal.common.DefaultMaxBatchDelay,
    internal.common.DefaultAllocSize]
  try wp_auto
  wp_join iprop(db_ptr ↦ «$r0_ptr» ∗ ∃ (st : Loc), structFieldRef DB go!"stats" «$r0_ptr» ↦ st ∗
      (⌜st = null⌝ ∨ ∃ (sv : Stats), st ↦ sv)) at next with [db stats] as ⟨db, %st, stats, Hst⟩
  · cases hns : ov.NoStatistics'
    · simp only [Bool.not_false]
      try wp_auto
      isplitl []
      · ipureintro; try rfl
      iframe
      try (iright; iexists _; iframe)
    · simp only [Bool.not_true]
      try wp_auto
      isplitl []
      · ipureintro; try rfl
      iframe
      ileft; ipureintro; rfl
  try wp_auto
  rw [hlg]
  try wp_auto
  icases bboltRoot_access $$ Hpkg with ⟨%dl, #Hdl, #Hdlok⟩
  wp_apply hDL dl $$ [Hdl]
  · iframe; iframe #
  try wp_auto
  wp_apply hLogger «$r0_ptr» (DFrac.own 1) _ dl Hdbnn $$ [logger Hdl] as logger
  · iframe; iframe #
  try wp_auto
  simp only [ite_self, discardIface, interface.mkOk, ↓reduceIte]
  try wp_auto
  simp only [_root_.Perennial.os.O_RDWR, _root_.Perennial.os.O_RDONLY, _root_.Perennial.os.O_CREATE]
  try wp_auto
  rw [hro]
  try wp_auto
  rw [hof, decide_eq_true (show (zero_val GoFunc : GoFunc) = func.nil from rfl)]
  try wp_auto
  wp_apply hOpenFile path _ _ (some bs) $$ [Hfs] as %f %err Hof
  · iframe
  try wp_auto
  icases Hof with (⟨%Herr, Hfs⟩ | ⟨%Hok, %fd, %bs', %Hbs, #Hosf, Hfb, Hfp, Hfm⟩)
  · -- the file did not open: close the database (no file), the error
    obtain ⟨Hne, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      try wp_auto
      iStructNamed ops
      wp_apply hclose «$r0_ptr» null (W64 0) [] path _ false _ _ slice.nil _ _ null null 0
        $$ [opened freelist writeAt meta0 meta1 dataref data datasz file readOnly path]
        as %cerr Hcl
      · iframe; ileft; ipureintro; exact ⟨rfl, rfl⟩
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      wp_apply hErrorf dl _ _ $$ [Hdlok]
      · iframe; iexact Hdlok
      try wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact Hne
      iexists bs
      iframe
      ipureintro; exact fun _ => rfl
  -- the file opened
  obtain ⟨rfl, Hfnn⟩ := Hok
  try wp_auto
  wp_apply hName f as %fname _
  try wp_auto
  wp_apply hflock «$r0_ptr» f fd (DFrac.own 1) true ov.Timeout' $$ [file Hosf] as %ferr file
  · iframe; iframe #
  have hbs : bs' = bs := by
    rcases Hbs with h | ⟨h, -⟩
    injection h with h; exact h.symm
  subst hbs
  try wp_auto
  cases ferr with
  | ok ei =>
    -- the file could not be locked: close it, the error
    open_close_err bs' (fun _ => rfl)
  | nil =>
  try wp_auto
  try wp_auto
  rw [hps, decide_eq_false (open_ps_ne ps hps80 hps32)]
  try wp_auto
  wp_apply hStat f fd bs' $$ [Hosf Hfb] as %fi %serr ⟨Hfb, Hfi⟩
  · iframe; iframe #
  icases Hfi with (%Hse | ⟨%Hse, #Hfi⟩)
  · obtain ⟨Hne', -⟩ := Hse
    cases serr with
    | nil => exact absurd rfl Hne'
    | ok ei => open_close_err bs' (fun _ => rfl)
  subst Hse
  try wp_auto
  wp_apply hSize fi bs'.length $$ [Hfi]
  · iexact Hfi
  try wp_auto
  ipersist logger
  -- a new file (`init` writes a fresh database) or an existing one (its page size): the file's
  -- bytes `bsF` and their facts
  open_join [HΦ Hov Hdefer] [Hfb]
    (iprop(∃ bsF : List w8, ⌜bsF = openBytes bs' ps ∧ fileWF bsF ps⌝ ∗ fileBytes fd bsF))
    (fun v => iprop(∃ (w : val) (e : GoInterface) (bs2 : List w8),
      ⌜v = returnVal w ∧ e ≠ interface.nil ∧ (bs' ≠ [] → bs2 = bs')⌝ ∗
      db_ptr ↦ (null : Loc) ∗ err_ptr ↦ e ∗ fsFile path (some bs2)))
  · by_cases hbe : bs' = []
    · -- a new file: `init`
      subst hbe
      rw [decide_eq_true (show W64 ((([] : List w8).length : Nat) : Int) = W64 0 from rfl)]
      try wp_auto
      icases typedPointsto_not_null_dup _ _ _ $$ ops with ⟨ops, %Hopsnn⟩
      iStructNamed ops
      wp_apply hinit «$r0_ptr» f fd ps (discardIface dl) dl
          (methods _root_.Perennial.os.File.ty.PointerType go!"WriteAt" #f) (DFrac.own 1) Hdbnn
          hps80 hps32 (Or.inr rfl) rfl
        $$ [pageSize file writeAt Hfb Hfm] as %ierr ⟨pageSize, file, writeAt, Hfm, Hir⟩
      · simp only [discardIface, interface.mkOk]
        iframe; iframe #
      icases Hir with (⟨%Hie, Hfb⟩ | ⟨%Hie, %bs2, Hfb⟩)
      · subst Hie
        try wp_auto
        ihave ops := typedPointsto_combine (structFieldRef DB go!"ops" «$r0_ptr»)
          ({ writeAt' := methods _root_.Perennial.os.File.ty.PointerType go!"WriteAt" #f } :
            anonStruct_f41ae3ebe286c14c) (DFrac.own 1) Hopsnn $$ [writeAt]
        · simp only [TypedPointsto.typedPointstoDef]
          iframe
        ileft
        isplitr
        · ipureintro; first | rfl | trivial
        iframe
        ipureintro
        exact ⟨by simp [openBytes], fileWF_initBytes ps hps80 hps32⟩
      · cases ierr with
        | nil => exact absurd rfl Hie
        | ok ei => oc_err_exit bs2 (fun h => absurd rfl h)
    · -- an existing file: its page size
      obtain ⟨hwf, hpsok⟩ := hbs0.resolve_left hbe
      have hlen47 := hwf.2.2.2.1
      have hlen0 : 0 < bs'.length := by
        cases bs' with
        | nil => exact absurd rfl hbe
        | cons _ _ => simp
      rw [decide_eq_false (open_len_ne bs'.length hlen0 hlen47)]
      try wp_auto
      wp_apply hgps «$r0_ptr» f fd bs' (W64 (ps : Int)) (DFrac.own 1) (by omega)
        $$ [file pageSize Hosf Hfb] as %gsz %gerr ⟨file, pageSize, Hfb, %Hg⟩
      · iframe; iframe #
      try wp_auto
      cases gerr with
      | ok ei =>
        -- no page size: close the file, the error
        oc_err_exit bs' (fun _ => rfl)
      | nil =>
      rcases Hg with ⟨-, Hg⟩ | ⟨h, -⟩
      rotate_left
      · exact absurd rfl h
      have hgsz := open_gps bs' ps gsz hpsok hps32 Hg
      subst hgsz
      try wp_auto
      ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
      ipureintro
      exact ⟨by simp [openBytes, hbe], hwf⟩
  · -- the file's bytes
    subst Hv
    icases HRx with ⟨%bsF, %HbsF, Hfb⟩
    obtain ⟨hBdef, hwf⟩ := HbsF
    have hBeq : bs' ≠ [] → bsF = bs' := fun h => by rw [hBdef]; simp [openBytes, h]
    have hlen47 := hwf.2.2.2.1
    have h2ps := hwf.2.2.1
    try wp_auto
    rw [recv_eq_func_mk BAnon BAnon]
    try wp_auto
    -- the mapping: its lock and ghost token, the fields `mmap` reads persistently
    rw [hml]
    ipersist pageSize
    ipersist Mlock
    imod (ghostVar_alloc (GF := GF) ()) with ⟨%γm, Htok⟩
    imod (sync.init_RWMutex (fun q => ghostVar (GF := GF) γm q ()) (structFieldRef DB go!"mmaplock" «$r0_ptr»))
      $$ [Htok] mmaplock with Hmmh
    · inext; iexact Htok
    ihave Hmmh := (show ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        sync.ownRWMutex (structFieldRef DB go!"mmaplock" «$r0_ptr») (fun q => ghostVar (GF := GF) γm q ()))
        ⊢ sync.ownRWMutex (structFieldRef DB go!"mmaplock" «$r0_ptr») (mmapTok (GF := GF) γm) ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
            sync.ownRWMutex (structFieldRef DB go!"mmaplock" «$r0_ptr») (mmapTok γm)) from by
      rw [show Int.toNat sync.rwmutex.actualMaxReaders =
        (Int.toNat sync.rwmutex.actualMaxReaders - 1) + 1 by rw [sync.rwmutex.actualMaxReaders_unseal]; decide,
        List.replicate_succ]
      exact BigSepL.bigSepL_cons.1) $$ Hmmh
    icases Hmmh with ⟨Hmm1, Hmmh⟩
    wp_apply hmmap «$r0_ptr» f fd bsF (discardIface dl) dl (W64 (ps : Int)) ov.MaxSize' ov.MmapFlags' null
        (DFrac.own 1) slice.nil null (W64 0) null null none 0 γm ∅ iprop(emp) iprop(emp) iprop(emp)
        ov.InitialMmapSize' Hdbnn (by omega) (by rw [w64_nat_z ps (by omega)]; omega)
        (by rw [w64_nat_z ps (by omega)]; omega) hims0 hims1 (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩)
        (fun _ => .rfl) (fun h => absurd rfl h)
      $$ [file MaxSize rwtx MmapFlags dataref datasz meta0 meta1 Hfm Hfb Hmm1 data]
      as %merr Hm
    · simp only [discardIface, interface.mkOk]
      iframe; iframe #
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; iempintro
      iintro %_ _
      iframe
      iapply (mapRange_empty none bsF 0 0 (Nat.le_refl _)).2; iempintro
    icases Hm with ⟨-, file, MaxSize, #Mlock2, rwtx, MmapFlags, Hfb, Hmm1, Hmr⟩
    icases Hmr with (⟨%Hme, -, Hwand, dataref, datasz, meta0, meta1, Hfm⟩ |
      ⟨%Hme, -, %dp', %ds', %m0', %m1', %mm', %n', dataref, data, datasz, meta0, meta1, Hfm, -⟩ |
      ⟨%Hme, -, %b, %sz, %v0, %v1, %Hmb, dataref, data, datasz, meta0, meta1, Hfm, Hrange⟩)
    · -- the mapping failed, nothing mapped: close the file, the error
      ihave Hwd : (structFieldRef DB go!"data" «$r0_ptr» ↦ (null : Loc) ∗ mapRange none bsF 0 0 ∗ emp : IProp GF)
        $$ [Hwand]
      · iapply Hwand
        · ipureintro; first | rfl | trivial
        · iempintro
      icases Hwd with ⟨data, -, -⟩
      obtain ⟨Hne', -⟩ := Hme
      cases merr with
      | nil => exact absurd rfl Hne'
      | ok ei => open_close_err bsF hBeq
    · -- the mapping failed, after unmapping: close the file, the error
      obtain ⟨Hne', -⟩ := Hme
      cases merr with
      | nil => exact absurd rfl Hne'
      | ok ei => open_close_err bsF hBeq
    subst Hme
    try wp_auto
    -- the mapping: the database's slots and tail; the freelist page and the metas lent out
    obtain ⟨hbl, hbc, hbp, hms, hmeta⟩ := Hmb
    have hpsn : uint.nat (W64 (ps : Int)) = ps := open_unat ps (by omega)
    rw [hpsn] at hmeta
    have hcur := hwf.2.2.2.2 v0 v1 hmeta.1 hmeta.2.1 hmeta.2.2
    have hcur' := hcur
    obtain ⟨cwf, cdisj, cin, cfree, cfl, cfid2, cfid, cfpg, cids, ctx⟩ := hcur'
    have hszge := mmapSizeOf_ge _ _ _ (by omega) (by rw [w64_nat_z ps (by omega)]; omega) hms
    have hszle := mmapSizeOf_le _ _ _ hms
    have hszn : bsF.length ≤ sint.nat sz := by
      have h1 := hszge.1
      have h2 : (bsF.length : Int) ≤ max (bsF.length : Int) (sint.Z ov.InitialMmapSize') :=
        Int.le_max_left _ _
      exact open_len_le _ _ (by omega)
    have hnn : min (sint.nat sz) bsF.length / ps = bsF.length / ps := by rw [Nat.min_eq_right hszn]
    have hfit : (bsF.length / ps) * ps ≤ bsF.length := Nat.div_mul_le_self _ _
    icases open_slots (GF := GF) b.ptr bsF (sint.nat sz) ps $$ Hrange with ⟨Hslots, Htail⟩
    rw [hnn]
    icases (open_flpage (GF := GF) b.ptr bsF ps (bsF.length / ps) _ (by omega) hfit cfid).1 $$ Hslots
      with ⟨Hslots, Hfpg⟩
    icases open_metas (GF := GF) b.ptr bsF ps (bsF.length / ps) _ v0 v1 hps80
      ((Nat.le_div_iff_mul_le (by omega)).2 (by omega)) hfit hbp hmeta.1 hmeta.2.1
      (by unfold flRem; rw [if_neg (by omega)]) (by unfold flRem; rw [if_neg (by omega)]) $$ Hslots
      with ⟨HM0, HM1, Hmback⟩
    -- `loadFreelist`: the freelist page's ids the free ids
    have hfidps : uint.nat (if metaPick v0 v1 then v1 else v0).freelist' * ps < 2 ^ 47 := by
      have h1 : uint.nat (if metaPick v0 v1 then v1 else v0).freelist' + 1 ≤ bsF.length / ps := by
        unfold pageSpan at cfid; omega
      have h2 := Nat.mul_le_mul_right ps h1
      rw [Nat.succ_mul] at h2; omega
    have haddr := open_mul _ ps hfidps (by omega)
    have hm1eq : b.ptr +ₗ (uint.Z (W64 (ps : Int)) + 16) = b.ptr +ₗ ((ps + 16 : Nat) : Int) := by
      rw [w64_nat_z ps (by omega)]; congr 1
    rw [hm1eq, ← haddr]
    wp_apply hload «$r0_ptr» b.ptr (b.ptr +ₗ 16) (b.ptr +ₗ ((ps + 16 : Nat) : Int)) st (W64 (ps : Int))
        ov.FreelistType' GoInterface.nil (DFrac.own 1) (DFrac.own 1) (DFrac.own halfQ) (DFrac.own halfQ)
        (DFrac.own 1) DFrac.discard (DFrac.own halfQ.half) v0 v1
        (pageAt bsF ps (uint.nat (if metaPick v0 v1 then v1 else v0).freelist')) hC hft
        (by simpa [Loc.add] using hbp) (by simpa [Loc.add] using hbp) hmeta.2.2 cfl hbp
        (by rw [haddr]; omega) cfpg
      $$ [freelistLoad freelist FreelistType meta0 meta1 HM0 HM1 data Hfpg stats Hst]
      as ⟨%a, %s, %free, %Hfree, freelist, Hfl, FreelistType, meta0, meta1, HM0, HM1, data, -,
        Hfpg, stats, Hst⟩
    · iframe; iframe #
    try wp_auto
    rw [hnfs]
    try wp_auto
    wp_apply hhsf «$r0_ptr» (b.ptr +ₗ 16) (b.ptr +ₗ ((ps + 16 : Nat) : Int)) (DFrac.own 1)
        (DFrac.own halfQ) (DFrac.own halfQ) v0 v1 (by simpa [Loc.add] using hbp)
        (by simpa [Loc.add] using hbp) hmeta.2.2 $$ [meta0 meta1 HM0 HM1]
      as ⟨meta0, meta1, HM0, HM1⟩
    · iframe
    rw [decide_eq_false cfl]
    -- the database: the mapping's slots back, the locks, the ghost state, the page pool
    ihave Hslots := Hmback $$ HM0 HM1
    rw [haddr]
    ihave Hslots := (open_flpage (GF := GF) b.ptr bsF ps (bsF.length / ps) _ (by omega) hfit cfid).2
      $$ [Hslots Hfpg]
    · iframe
    imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Reader)) with ⟨%γr, Hrauth⟩
    imod (sync.init_Mutex iprop(True) ⊤ (structFieldRef DB go!"metalock" «$r0_ptr»)) $$ metalock []
      with #Hmetalock
    · inext; itrivial
    imod (sync.init_Mutex iprop(True) ⊤ (structFieldRef DB go!"rwlock" «$r0_ptr»)) $$ rwlock []
      with #Hrwlock
    · inext; itrivial
    imod (sync.init_RWMutex (statsInv (GF := GF)) (structFieldRef DB go!"statlock" «$r0_ptr»))
      $$ [] statlock with Hsth
    · inext; simp only [statsInv]; itrivial
    ihave Hsth := (show ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        sync.ownRWMutex (structFieldRef DB go!"statlock" «$r0_ptr») (statsInv (GF := GF)))
        ⊢ sync.ownRWMutex (structFieldRef DB go!"statlock" «$r0_ptr») (statsInv (GF := GF)) from by
      rw [show Int.toNat sync.rwmutex.actualMaxReaders =
        (Int.toNat sync.rwmutex.actualMaxReaders - 1) + 1 by rw [sync.rwmutex.actualMaxReaders_unseal]; decide,
        List.replicate_succ]
      iintro ⟨H, -⟩; iexact H) $$ Hsth
    try wp_pures
    wp_load
    try wp_pures
    wp_store
    ipersist db
    imod (pool_init (GF := GF) (structFieldRef DB go!"pagePool" «$r0_ptr») _ (pageBuf (GF := GF) ps))
      $$ pagePool [] with #Hpool
    · imodintro
      iintro %Φ' HΦ'
      try wp_auto
      wp_apply (wp_slice_make2 (V := w8) (W64 (ps : Int))) as %sl ⟨Hsl, -⟩
      · ipureintro; rw [open_sint_ps ps (by omega)]; omega
      try wp_auto
      iapply HΦ'
      unfold pageBuf
      iexists sl
      rw [open_snat_ps ps (by omega)]
      iframe
      ipureintro; rfl
    try wp_auto
    -- the database
    have hsz64 := open_sz_w64 sz (by omega)
    have hdr : b = slice.mk b.ptr (W64 ((sint.nat sz : Nat) : Int)) (W64 ((sint.nat sz : Nat) : Int)) := by
      rw [hsz64]; cases b; simp only at hbl hbc ⊢; rw [hbl, hbc]
    have hns : (openState f fd bsF b.ptr (sint.nat sz) ps free path).nslots = bsF.length / ps := by
      unfold DBState.nslots openState; simp only; rw [Nat.min_eq_right hszn]
    iapply HΦ
    isplitl [Hov]
    · iexact Hov
    ileft
    isplitr
    · ipureintro; rfl
    iexists a, ⟨γm, γr⟩, openState f fd bsF b.ptr (sint.nat sz) ps free path
    isplitr
    · ipureintro; exact ⟨Hfnn, hBdef, rfl, rfl, rfl, rfl⟩
    ihave Hplain : dbPlain «$r0_ptr» (DFrac.own 1)
        (openDBRec ov dl fname f b sz ps st (arrayImpl (GF := GF) (hG := hG) a).iface (functions _root_.Perennial.os.OpenFile []) (methods _root_.Perennial.os.File.ty.PointerType go!"WriteAt" #f))
      $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags
        MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1
        opened rwtx stats batch ops readOnly]
    · simp only [dbPlain, openDBRec]; iframe
    ihave Hmmaph : ([∗list] _x ∈ List.replicate
        (Int.toNat sync.rwmutex.actualMaxReaders - (∅ : GMap Nat Reader).size) (),
        sync.ownRWMutex (structFieldRef DB go!"mmaplock" «$r0_ptr») (mmapTok (GF := GF) γm)) $$ [Hmm1 Hmmh]
    · rw [GMap.map_size_empty, Nat.sub_zero, show Int.toNat sync.rwmutex.actualMaxReaders =
        (Int.toNat sync.rwmutex.actualMaxReaders - 1) + 1 by rw [sync.rwmutex.actualMaxReaders_unseal]; decide,
        List.replicate_succ]
      iapply BigSepL.bigSepL_cons.2; iframe
    ihave Htoks : ([∗map] _k ↦ _r ∈ (∅ : GMap Nat Reader), mmapTok (GF := GF) γm sync.rfrac) $$ []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    unfold ownDB
    iexists openDBRec ov dl fname f b sz ps st (arrayImpl (GF := GF) (hG := hG) a).iface (functions _root_.Perennial.os.OpenFile []) (methods _root_.Perennial.os.File.ty.PointerType go!"WriteAt" #f), s, v0, v1, dl
    isplitr
    · ipureintro
      exact ⟨rfl, rfl, hsz64.symm, rfl, rfl, rfl, rfl, rfl, rfl, Hdbnn⟩
    isplitr
    · ipureintro
      exact dbOK_open f fd bsF b.ptr (sint.nat sz) ps free path v0 v1 hwf hmeta hszn
        (open_snat_le sz hszle hszge.2)
        hbp Hfree.2
    isplitr
    · ipureintro; exact hdr
    isplitr
    · ipureintro; first | rfl | simp only [openDBRec, openState]
    simp only [openState, openDBRec, flfQ, ↓reduceIte, _root_.decide_true]
    try rw [hns]
    try simp only [DBState.nslots]
    try rw [hnn]
    iframe
    iframe #
    ipureintro; right; trivial
    done
  · -- an error: the database closed, the file given back
    icases HErr with ⟨%w, %e, %bs2, %Hw, Hdb, Herr, Hfs⟩
    obtain ⟨rfl, he, hb2⟩ := Hw
    try wp_auto
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; exact he
    iexists bs2
    iframe
    ipureintro; exact hb2

end proof

end bbolt
end EtcdGrove
end Perennial
