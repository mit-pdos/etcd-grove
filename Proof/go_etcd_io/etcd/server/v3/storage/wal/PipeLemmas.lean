/- Lean-first (no Rocq counterpart).

# Lemmas of the file pipeline's proofs (`alloc`, `run`; W2 of `notes/wal-fsext-plan.md`)

* `pipeTmp_sprintf`: `fmt.Sprintf("%d.tmp", count % 2)` is `pipeTmp count` (`count < 2^63`: the
  signed remainder is the unsigned one).
* `cleanAbs_osPathS`: a directory with a path in the shared mode (`osPathS`) is a clean absolute
  path, so `filepath.Join(dir, b)` is `child dir b` (`join_child`).
* `osAUnc_triv`: the trivial update of a caller holding a whole claim.
* `wp_createTmp`: `createNewWALFile(dir/b, true)` of a pipeline name (`tmpClaim`): over
  `os.OpenFile.specCreateTruncSnc` when the name is absent, `os.OpenFile.wp_truncS` when it holds a
  (leftover) file; on success the locked file, empty (`trFile i True`), the claim holding it; on an
  error the claim (`tmpClaim`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Pipe
public import Proof.os.OpenFileTruncLemmas
public import Proof.path.filepath.Names
public import Spec.os.Remove
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

/-! ## Pure -/

theorem srem_two_of_lt (n : Nat) (hn : n < 2 ^ 63) :
    BitVec.srem (W64 n) (W64 2) = W64 (n % 2 : Nat) := by
  have hx : W64 n = BitVec.ofNat 64 n := by simp [W64]
  rw [hx]
  have hmsb : (BitVec.ofNat 64 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmsb2 : (W64 2).msb = false := by decide
  rw [BitVec.srem, hmsb, hmsb2]
  dsimp only
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.umod, BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  have h2 : (W64 2).toNat = 2 := by decide
  rw [h2]
  simp [W64]
  omega

/-- `fmt.Sprintf("%d.tmp", count % 2)` of the `int` `count < 2^63`. -/
theorem pipeTmp_sprintf (n : Nat) (hn : n < 2 ^ 63) :
    _root_.Perennial.fmt.decimal (sint.Z (BitVec.srem (W64 n) (W64 2))) ++ go!".tmp" =
      pipeTmp n := by
  rw [srem_two_of_lt n hn]
  unfold pipeTmp
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, if_pos rfl, show sint.Z (W64 ((0 : Nat) : Int)) = 0 by decide,
      _root_.Perennial.fmt.decimal, if_neg (by omega), show Int.natAbs 0 = 0 from rfl,
      _root_.Perennial.fmt.decimalNat_of_lt (by omega)]
    rfl
  · rw [h, if_neg (by omega), show sint.Z (W64 ((1 : Nat) : Int)) = 1 by decide,
      _root_.Perennial.fmt.decimal, if_neg (by omega), show Int.natAbs 1 = 1 from rfl,
      _root_.Perennial.fmt.decimalNat_of_lt (by omega)]
    rfl

theorem segsPath_flatMap (segs : List (List w8)) :
    path.segsPath segs = segs.flatMap (fun c => path.slash :: c) := by
  induction segs with
  | nil => rfl
  | cons s ss ih =>
    unfold path.segsPath
    rw [List.foldl_cons, path.segsPath_foldl, ih]
    simp

theorem cleanSeg_of_nameOk {b : GoString} (hb : NameOk b) : path.cleanSeg b := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hb
  refine ⟨h1, fun c hc hcs => h4 ?_, h2, h3⟩
  rw [show slashB = path.slash from rfl, ← hcs]; exact hc

/-- The path of a directory under a root is a clean absolute path. -/
theorem cleanAbs_joinPath {R : Roots} {r : GoString} {j0 : Ino} {cs : List GoString}
    (hR : RootsOk R) (hr : (r, j0) ∈ R) (hcs : ∀ c ∈ cs, NameOk c) :
    filepath.CleanAbs (joinPath r cs) := by
  obtain ⟨⟨cs0, hne, hcs0, rfl⟩, -⟩ := hR.2.2 (r, j0) hr
  refine ⟨cs0 ++ cs, by simp [hne], ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact cleanSeg_of_nameOk (hcs0 s hs)
    · exact cleanSeg_of_nameOk (hcs s hs)
  · rw [segsPath_flatMap]
    simp [joinPath, List.flatMap_append]
    rfl

/-- `filepath.Join(dir, b)` of a clean absolute `dir` and a name. -/
theorem join_child {d b : GoString} (hd : filepath.CleanAbs d) (hb : NameOk b) :
    path.joinModel [d, b] = child d b := by
  rw [filepath.joinModel_name d b hd (cleanSeg_of_nameOk hb)]
  simp [child]
  rfl

theorem pipeTmp_nameOk (n : Nat) : NameOk (pipeTmp n) := by
  unfold pipeTmp; split <;> decide

/-! ## Iris -/

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- A path in the shared mode is a clean absolute path. -/
theorem osPathS_cleanAbs (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) :
    osPathS (GF := GF) R d dq j ⊢ ⌜filepath.CleanAbs d⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %h, -⟩
  obtain ⟨hR, hr, hcs, rfl⟩ := h
  ipureintro; exact cleanAbs_joinPath hR hr hcs

/-- **The trivial update** of a caller holding all of `α`: it commits with whatever the step
gives. -/
theorem osAUnc_triv {A : Type} (α : IProp GF) (β : A → IProp GF) :
    α ⊢ osAUnc α β β := by
  iintro Hα
  iapply osAUnc_coiter α β β α $$ [] Hα
  iintro !> Hα
  unfold osAUncPre
  iintro Hnc
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ osAuMask from
    Std.LawfulSet.empty_subset)) with Hcl
  imodintro
  iframe Hα Hnc
  isplit
  · iintro Hα
    imod Hcl
    imodintro
    iexact Hα
  · iintro %o Hβ
    imod Hcl
    imodintro
    iexact Hβ

/-- The outcome of a create, split in two halves, joined. -/
theorem crOut_join (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) :
    crOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ∗ crOut j b h (DFrac.own (1 : Qp).half) o ⊢
      crOut j b h (DFrac.own 1) o := by
  cases o with
  | none =>
    simp only [crOut]
    iintro ⟨H1, H2⟩
    iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1 $$ [$H1 $H2]
  | some xsi =>
    obtain ⟨x, s, i⟩ := xsi
    simp only [crOut]
    iintro ⟨⟨%hh, Hl, H1⟩, ⟨-, -, H2⟩⟩
    isplitr
    · ipureintro; exact hh
    iframe Hl
    iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1 $$ [$H1 $H2]

/-- `walOpenFlag true` with `O_CLOEXEC` is a valid write-only create-truncate open. -/
theorem walOpenFlag_ok :
    OpenFlagsOk (wal.walOpenFlag true ||| W64 0x80000).toNat ∧
      (wal.walOpenFlag true ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (wal.walOpenFlag true ||| W64 0x80000).toNat / O_TRUNC % 2 = 1 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC wal.walOpenFlag
  decide

/-- A file's `OsMeta` and zero bytes (no mappings): the file whole, any size (`trFile i False`). -/
theorem zerosA_trFile (i : Ino) (m : OsMeta) (hm : m.maps = ∅) (hcut : m.cut = none)
    (hlo : m.lo ≤ m.size) (hzf : m.ZfGe) :
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osZerosA i 0 m.size (DFrac.own 1) ⊢ trFile i False := by
  iintro ⟨Hm, Hz⟩
  icases (osZerosA_unfold i 0 m.size (DFrac.own 1)).1 $$ Hz with ⟨%zs, %hzs, Hz⟩
  iunfold trFile
  iexists m, zs.map (fun c => ((0 : w8), c))
  iframe Hm Hz
  isplitl []
  · iapply mcellsAny_empty m.maps hm
  ipureintro
  exact ⟨by simp [hzs], fun h => h.elim, hm, hcut, hlo, hzf, fun h => h.elim⟩

/-! ## The pipeline names' steps under the WAL invariant (step 2 (B)) -/

/-- The program's three quarters of a pipeline name's claim: half for the call, a quarter for the
update. -/
theorem osNames_quarters (j : Ino) (N : NameSet) (h : NamesH) :
    osNames (GF := GF) j N (DFrac.own qTmp) h ⊢
      osNames j N (DFrac.own (1 : Qp).half) h ∗ osNames j N (DFrac.own (1 : Qp).half.half) h :=
  (osNames_frac (L := hG.goose_localGS) j N (1 : Qp).half (1 : Qp).half.half h).1

/-- A create's history after its outcome. -/
def crHist (j : Ino) (b : GoString) (h : NamesH) : Option (Nat × Nat × Ino) → NamesH
  | none => h
  | some (x, s, i) => h.log x (crEnt j b i s) (<[b := .file i]> h.cur)

theorem crOut_frac (j : Ino) (b : GoString) (h : NamesH) (q1 q2 : Qp) (o : Option (Nat × Nat × Ino)) :
    crOut (GF := GF) j b h (DFrac.own (q1 + q2)) o ⊣⊢
      crOut j b h (DFrac.own q1) o ∗ crOut j b h (DFrac.own q2) o := by
  cases o with
  | none => simp only [crOut]; exact osNames_frac j _ q1 q2 h
  | some xsi =>
    obtain ⟨x, s, i⟩ := xsi
    haveI : Persistent (osLogged (L := hG.goose_localGS) x (crEnt j b i s)) := by
      unfold osLogged; infer_instance
    simp only [crOut]
    constructor
    · iintro ⟨%hh, #Hl, Hn⟩
      icases (osNames_frac j _ q1 q2 _).1 $$ Hn with ⟨H1, H2⟩
      isplitl [H1]
      · iframe H1 Hl; ipureintro; exact hh
      · iframe H2 Hl; ipureintro; exact hh
    · iintro ⟨⟨%hh, #Hl, H1⟩, ⟨-, -, H2⟩⟩
      iframe Hl
      isplitr
      · ipureintro; exact hh
      iapply (osNames_frac j _ q1 q2 _).2 $$ [$H1 $H2]

theorem crOut_joinQ (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) :
    crOut (GF := GF) j b h (DFrac.own (1 : Qp).half.half) o ∗
      crOut j b h (DFrac.own (1 : Qp).half) o ⊢ crOut j b h (DFrac.own qTmp) o := by
  iintro ⟨H1, H2⟩
  iapply (crOut_frac (GF := GF) j b h (1 : Qp).half (1 : Qp).half.half o).2 $$ [$H1 $H2]

theorem crOut_tmpSplit (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) :
    crOut (GF := GF) j b h (DFrac.own (1 : Qp).half) o ⊢
      osNames j (.only [b]) (DFrac.own qTmpI) (crHist j b h o) ∗
        crOut j b h (DFrac.own (1 : Qp).half.half) o := by
  have e := (crOut_frac (GF := GF) j b h (1 : Qp).half.half (1 : Qp).half.half o).1
  rw [Qp.half_add_half] at e
  refine e.trans ?_
  cases o with
  | none => exact .rfl
  | some xsi =>
    obtain ⟨x, s, i⟩ := xsi
    simp only [crOut, crHist]
    iintro ⟨⟨-, -, H1⟩, H2⟩
    iframe H1 H2

theorem crHist_fo (j : Ino) (b : GoString) (h : NamesH) (o : Option (Nat × Nat × Ino)) (n0 : Nat)
    (hf : HistFoP (fun _ => True) n0 j (.only [b]) h) :
    HistFoP (fun _ => True) n0 j (.only [b]) (crHist j b h o) := by
  cases o with
  | none => exact hf
  | some xsi =>
    obtain ⟨x, s, i⟩ := xsi
    refine HistFoP.log hf x _ _ (fun b' hb' _ _ J => ?_)
    have e : b' = b := List.mem_singleton.1 hb'
    subst e
    rw [GMap.lookup_insert_eq]
    nofun

/-- An unlink's history after its outcome. -/
def rmHist (j : Ino) (b : GoString) (i : Ino) (h : NamesH) : Option (Nat × Nat) → NamesH
  | none => h
  | some (x, s) => h.log x (rmFileEnt j b i s) (restrictN (.only [b]) (GMap.delete b h.cur))

theorem rmFileOut_frac (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (q1 q2 : Qp)
    (o : Option (Nat × Nat)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (q1 + q2)) o ⊣⊢
      rmFileOut j b i h (DFrac.own q1) o ∗ rmFileOut j b i h (DFrac.own q2) o := by
  unfold rmFileOut
  cases o with
  | none =>
    simp only [claimOut]
    constructor
    · iintro ⟨#Hl, Hn⟩
      icases (osNames_frac j _ q1 q2 _).1 $$ Hn with ⟨H1, H2⟩
      iframe Hl H1 H2
    · iintro ⟨⟨#Hl, H1⟩, ⟨-, H2⟩⟩
      iframe Hl
      iapply (osNames_frac j _ q1 q2 _).2 $$ [$H1 $H2]
  | some xs =>
    obtain ⟨x, s⟩ := xs
    simp only [claimOut]
    constructor
    · iintro ⟨#Hl, Hn⟩
      icases (osNames_frac j _ q1 q2 _).1 $$ Hn with ⟨H1, H2⟩
      iframe Hl H1 H2
    · iintro ⟨⟨#Hl, H1⟩, ⟨-, H2⟩⟩
      iframe Hl
      iapply (osNames_frac j _ q1 q2 _).2 $$ [$H1 $H2]

theorem rmFileOut_joinQ (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (o : Option (Nat × Nat)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half.half) o ∗
      rmFileOut j b i h (DFrac.own (1 : Qp).half) o ⊢ rmFileOut j b i h (DFrac.own qTmp) o := by
  iintro ⟨H1, H2⟩
  iapply (rmFileOut_frac (GF := GF) j b i h (1 : Qp).half (1 : Qp).half.half o).2 $$ [$H1 $H2]

theorem rmFileOut_tmpSplit (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (o : Option (Nat × Nat)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half) o ⊢
      osNames j (.only [b]) (DFrac.own qTmpI) (rmHist j b i h o) ∗
        rmFileOut j b i h (DFrac.own (1 : Qp).half.half) o := by
  have e := (rmFileOut_frac (GF := GF) j b i h (1 : Qp).half.half (1 : Qp).half.half o).1
  rw [Qp.half_add_half] at e
  refine e.trans ?_
  unfold rmFileOut
  cases o with
  | none =>
    simp only [claimOut, rmHist]
    iintro ⟨⟨-, H1⟩, H2⟩
    iframe H1 H2
  | some xs =>
    obtain ⟨x, s⟩ := xs
    simp only [claimOut, rmHist]
    iintro ⟨⟨-, H1⟩, H2⟩
    iframe H1 H2

theorem rmHist_fo (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (o : Option (Nat × Nat)) (n0 : Nat)
    (hf : HistFoP (fun _ => True) n0 j (.only [b]) h) :
    HistFoP (fun _ => True) n0 j (.only [b]) (rmHist j b i h o) := by
  cases o with
  | none => exact hf
  | some xs =>
    obtain ⟨x, s⟩ := xs
    refine HistFoP.log hf x _ _ (fun b' hb' _ _ J => ?_)
    have e : b' = b := List.mem_singleton.1 hb'
    subst e
    rw [restrictN_lookup _ _ _ hb', GMap.lookup_delete]
    nofun

end iris

section irisW
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- **`createNewWALFile(dir/b, true)` of a pipeline name.** -/
theorem wp_createTmp [os.file.FieldAssumptions]
    (wp_create : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF)
      (hG := hG))
    (wp_open : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG))
    (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (r : GoString) (X : List GoString)
    (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (b : GoString) (hb : NameOk b)
    (hbt : b ∈ walTmps) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
        osSharedInv R ∗ walInv (W := W) C Mr R jr r ∗ walDirKey (W := W) dir j X ∗
        osPathS R dir dq j ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗ tmpClaim j b }}
      (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
          [go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty]))
          (Val #(child dir b))) (Val #true))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
        osPathS R dir dq j ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (f : Loc) (fd : w64) (i : Ino) (h : NamesH) (lo lk : Option Bool),
            fileutil.lockedFile lf f ∗ os.ownFile f fd (child dir b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) ⟨i, false, true, lo, lk⟩ ∗ fdLocks fd ⟨i, false, true, lo, lk⟩ ∗
            trFile i True ∗ osNames j (.only [b]) (DFrac.own qTmp) h ∗
            ⌜0 ≤ fd.toInt ∧ h.cur !! b = some (.file i)⌝) ∨
         (⌜err ≠ interface.nil⌝ ∗ tmpClaim j b ∗ ⌜¬ (FsNoErrOn (· = child dir b) ∧ PathFits (child dir b))⌝)) }} := by
  iintro %Φ ⟨#Hos, #Hpkg, #Hsi, #Hwi, #Hkey, Hp, Hperm, Hc⟩ HΦ
  unfold tmpClaim
  icases Hc with ⟨%h, Hn, Hent⟩
  obtain ⟨hfl, hcr, htr⟩ := walOpenFlag_ok
  cases hcur : h.cur !! b with
  | none =>
    -- the name absent: a create, under the WAL invariant (its half of the claim, `walTmp_osAUnc`)
    let A : Option (Nat × Nat × Ino) → Bool → IProp GF := fun o ok =>
      iprop(osPathS R dir dq j ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
        crOut j b h (DFrac.own qTmp) o ∗
        crTr (ok = true) o ∗ ⌜ok = false → ¬ (FsNoErrOn (· = child dir b) ∧ PathFits (child dir b))⌝)
    have hT : fileutil.OpenTriple
        iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
          osNames j (.only [b]) (DFrac.own qTmp) h ∗ walInv (W := W) C Mr R jr r ∗
          walDirKey (W := W) dir j X)
        (child dir b) (wal.walOpenFlag true) (W32 384) A (crIno b h) := by
      unfold fileutil.OpenTriple
      iintro %Ψ ⟨#Hosp, #Hos, #Hsi, Hp, Hperm, Hn, #Hwi, #Hkey⟩ HΨ
      icases osNames_quarters j (.only [b]) h $$ Hn with ⟨Hn, Hr⟩
      ihave Hau := walTmp_osAUnc (W := W) (A := Option (Nat × Nat × Ino)) C Mr R jr r dir j X b hbt h
        (crOut j b h) (crHist j b h) (crOut_tmpSplit j b h) (crHist_fo j b h) $$ Hwi [Hr]
      · iunfold walTmpP; iframe Hr; iexact Hkey
      iapply wp_open dir b (wal.walOpenFlag true) (W32 384) R j dq h (1 : Qp).half
        (1 : Qp).half (1 : Qp).half.half
        (crOut j b h (DFrac.own (1 : Qp).half.half)) hfl hcr htr hb hcur
        (Qp.half_add_half 1) $$ [$Hosp $Hos $Hsi $Hp $Hperm $Hn $Hau]
      inext
      iintro %f %err ⟨Hp, Hperm, %o, Ho1, Ho2, Htr, Hr⟩
      iapply HΨ
      unfold fileutil.openPost
      iexists o
      ihave Ho := crOut_joinQ j b h o $$ [$Ho1 $Ho2]
      icases Hr with (⟨%fd, %i, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok, %hWo⟩)
      · obtain ⟨rfl, hfd, hi⟩ := hres
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hp Hperm Ho Htr]
        · simp only [A]
          iframe
          ipureintro; nofun
        iexists fd, i
        iframe
        ipureintro; exact ⟨hfd, hi⟩
      · iright
        isplitr
        · ipureintro; exact herr
        iframe Hok
        simp only [A]
        iframe
        have : (false = true) = (err = interface.nil) := by
          simp only [Bool.false_eq_true, false_iff, eq_iff_iff]; exact herr.1
        rw [this]
        iframe Htr
        ipureintro; exact fun _ => hWo
    ihave #Hosp : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
    · iPkgInit
    wp_apply wp_create (child dir b) true _ _ A (crIno b h) hT $$ [$Hosp $Hos $Hpkg $Hsi $Hp $Hperm $Hn $Hwi $Hkey]
      as %lf %err Hpost
    unfold fileutil.lockPostW
    icases Hpost with ⟨%o, (⟨%he, HA, %f, %fd, %i, %k, %hc, Hlf, Hf, Hoff, Hfd, Hlk, #Hkind⟩ | ⟨%he, %ok, HA, %hWk⟩)⟩
    · simp only [A]
      icases HA with ⟨Hp, Hperm, Ho, Htr, -⟩
      iapply HΦ
      iframe Hp Hperm
      ileft
      isplitr
      · ipureintro; exact he
      cases o with
      | none =>
        simp only [crIno] at hc; rw [hcur] at hc; cases hc.2
      | some xsi =>
        obtain ⟨x, s, i'⟩ := xsi
        obtain ⟨hfd, hc⟩ := hc
        simp only [crIno] at hc; subst hc
        simp only [crOut, crTr]
        icases Ho with ⟨-, -, Hn⟩
        iexists f, fd, i, _
        ihave Hfd := lkFd_open k i _ fd false true rfl rfl $$ [$Hfd $Hlk $Hkind]
        icases Hfd with ⟨%lo, %lk, Hfd, Hlks⟩
        iexists lo, lk
        iframe
        ipureintro; exact ⟨hfd, by simp [NamesH.log]⟩
    · simp only [A]
      icases HA with ⟨Hp, Hperm, Ho, Htr, %hWo⟩
      iapply HΦ
      iframe Hp Hperm
      iright
      isplitr
      · ipureintro; exact he.1
      isplitl
      rotate_left
      · ipureintro
        cases ok
        · exact hWo rfl
        · exact fun hw => hWk rfl (hw.1.mono (fun _ h => h.elim))
      cases o with
      | none =>
        simp only [crOut]
        iexists h
        iframe Ho
        rw [hcur]
        simp only [tmpEnt]
        iempintro
      | some xsi =>
        obtain ⟨x, s, i⟩ := xsi
        simp only [crOut, crTr]
        icases Ho with ⟨-, -, Hn⟩
        iexists _
        iframe Hn
        simp only [NamesH.log, GMap.lookup_insert_eq, tmpEnt]
        iapply trFile_mono i (ok = true) _ (fun h => h.elim) $$ Htr
  | some nd =>
    cases nd with
    | dir J =>
      simp only [tmpEnt]
      icases Hent with %H
      exact H.elim
    | file i =>
      simp only [tmpEnt]
      -- a leftover file: truncated
      let A : Unit → Bool → IProp GF := fun _ ok =>
        iprop(osPathS R dir dq j ∗ osNames j (.only [b]) (DFrac.own qTmp) h ∗
          osCallPerm (callKey R dir) (1 : Qp).half.half ∗ trFile i (ok = true) ∗ ⌜ok = false → ¬ (FsNoErrOn (· = child dir b) ∧ PathFits (child dir b))⌝)
      have hT : fileutil.OpenTriple
          iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗
            osNames j (.only [b]) (DFrac.own qTmp) h ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗ trFile i False)
          (child dir b) (wal.walOpenFlag true) (W32 384) A (fun _ i' => i' = i) := by
        unfold fileutil.OpenTriple
        iintro %Ψ ⟨#Hosp, #Hos, #Hsi, Hp, Hn, Hperm, Htr⟩ HΨ
        iapply os.OpenFile.wp_truncS dir b (wal.walOpenFlag true) (W32 384) R j i (.only [b]) dq
          (DFrac.own qTmp) h (1 : Qp).half.half hfl htr hb (by simp [NameSet.Mem]) hcur
          $$ [$Hosp $Hos $Hsi $Hp $Hn $Hperm $Htr]
        inext
        iintro %f %err ⟨Hp, Hn, Hperm, Htr, Hr⟩
        iapply HΨ
        unfold fileutil.openPost
        iexists ()
        icases Hr with (⟨%fd, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok, %hWo⟩)
        · obtain ⟨rfl, hfd⟩ := hres
          ileft
          isplitr
          · ipureintro; rfl
          isplitl [Hp Hperm Hn Htr]
          · simp only [A]
            iframe
            ipureintro; nofun
          iexists fd, i
          iframe
          ipureintro; exact ⟨hfd, rfl⟩
        · iright
          isplitr
          · ipureintro; exact herr
          iframe Hok
          simp only [A]
          iframe
          isplitl [Htr]
          · iapply trFile_mono i _ _ (fun h => by cases h) $$ Htr
          ipureintro; exact fun _ => hWo
      ihave #Hosp : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
      · iPkgInit
      wp_apply wp_create (child dir b) true _ _ A (fun _ i' => i' = i) hT
        $$ [$Hosp $Hos $Hpkg $Hsi $Hp $Hn $Hperm $Hent] as %lf %err Hpost
      unfold fileutil.lockPostW
      icases Hpost with ⟨%o, (⟨%he, HA, %f, %fd, %i', %k, %hc, Hlf, Hf, Hoff, Hfd, Hlk, #Hkind⟩ | ⟨%he, %ok, HA, %hWk⟩)⟩
      · simp only [A]
        icases HA with ⟨Hp, Hn, Hperm, Htr, -⟩
        obtain ⟨hfd, rfl⟩ := hc
        iapply HΦ
        iframe Hp Hperm
        ileft
        isplitr
        · ipureintro; exact he
        iexists f, fd, i', h
        ihave Hfd := lkFd_open k i' _ fd false true rfl rfl $$ [$Hfd $Hlk $Hkind]
        icases Hfd with ⟨%lo, %lk, Hfd, Hlks⟩
        iexists lo, lk
        iframe
        ipureintro; exact ⟨hfd, hcur⟩
      · simp only [A]
        icases HA with ⟨Hp, Hn, Hperm, Htr, %hWo⟩
        iapply HΦ
        iframe Hp Hperm
        iright
        isplitr
        · ipureintro; exact he.1
        isplitl
        rotate_left
        · ipureintro
          cases ok
          · exact hWo rfl
          · exact fun hw => hWk rfl (hw.1.mono (fun _ h => h.elim))
        iexists h
        iframe Hn
        rw [hcur]
        simp only [tmpEnt]
        iapply trFile_mono i _ _ (fun h => h.elim) $$ Htr


/-- **After an unlink of the pipeline's file** (the program's three quarters of the outcome), with the file: the claim, the name absent (the file dropped), or still the file. -/
theorem rmFile_tmpClaim (j : Ino) (b : GoString) (i : Ino) (h : NamesH)
    (o : Option (Nat × Nat)) (hcur : h.cur !! b = some (.file i)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half.half) o ∗
      rmFileOut j b i h (DFrac.own (1 : Qp).half) o ∗ trFile i False ⊢ tmpClaim j b := by
  iintro ⟨H1, H2, Ht⟩
  ihave H := rmFileOut_joinQ j b i h o $$ [$H1 $H2]
  unfold rmFileOut tmpClaim
  cases o with
  | none =>
    simp only [claimOut]
    icases H with ⟨-, H⟩
    iexists h
    iframe H
    rw [hcur]
    simp only [tmpEnt]
    iexact Ht
  | some xs =>
    obtain ⟨x, s⟩ := xs
    simp only [claimOut]
    icases H with ⟨-, H⟩
    iexists _
    iframe H
    simp only [NamesH.log]
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), GMap.lookup_delete]
    simp only [tmpEnt]
    iempintro

/-- **The unlink of the pipeline's file** `b` (`run`'s on `donec`, `Close`'s leftover), by the holder
of the program's three quarters of its claim, under the WAL invariant (its half, `walTmp_osAUnc`). -/
theorem wp_removeTmp (wp_Remove : os.Remove.specFileSnc (GF := GF) (hG := hG))
    (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (r : GoString) (X : List GoString)
    (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (b : GoString) (i : Ino) (h : NamesH)
    (qc : Qp) (hb : NameOk b) (hbt : b ∈ walTmps) (hcur : h.cur !! b = some (.file i)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ walInv (W := W) C Mr R jr r ∗ walDirKey (W := W) dir j X ∗
        osPathS R dir dq j ∗ osCallPerm (callKey R dir) qc ∗
        osNames j (.only [b]) (DFrac.own qTmp) h ∗ trFile i False }}
      (App (Val (@! os.Remove)) (Val #(child dir b)))
    {{ (err : GoInterface), RET #err; osPathS R dir dq j ∗ osCallPerm (callKey R dir) qc ∗ tmpClaim j b }} := by
  iintro %Φ ⟨#Hpk, #Hos, #Hsi, #Hwi, #Hkey, Hp, Hperm, Hn, Ht⟩ HΦ
  icases osNames_quarters j (.only [b]) h $$ Hn with ⟨Hn, Hr⟩
  ihave Hau := walTmp_osAUnc (W := W) (A := Option (Nat × Nat)) C Mr R jr r dir j X b hbt h
    (rmFileOut j b i h) (rmHist j b i h) (rmFileOut_tmpSplit j b i h) (rmHist_fo j b i h) $$ Hwi [Hr]
  · iunfold walTmpP; iframe Hr; iexact Hkey
  iapply wp_Remove dir b j i R dq h (1 : Qp).half (1 : Qp).half qc
    (rmFileOut j b i h (DFrac.own (1 : Qp).half.half)) hb hcur (Qp.half_add_half 1)
    $$ [$Hpk $Hos $Hsi $Hp $Hperm $Hn $Hau]
  inext
  iintro %err ⟨-, Hp, Hperm, %o, -, Ho1, Ho2⟩
  iapply HΦ
  iframe Hp Hperm
  iapply rmFile_tmpClaim j b i h o hcur $$ [$Ho1 $Ho2 $Ht]

end irisW


end WalFs
end EtcdGrove
end Perennial
