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

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Pipe
public import LinuxFs.Proof.os.OpenFileTruncS
public import LinuxFs.Proof.path.filepath.Names
public import LinuxFs.Spec.os.Remove

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

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

/-- **`createNewWALFile(dir/b, true)` of a pipeline name.** -/
theorem wp_createTmp [os.file.FieldAssumptions]
    (wp_create : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF)
      (hG := hG))
    (wp_open : os.OpenFile.specCreateTruncSnc (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (b : GoString) (hb : NameOk b) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
        osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm (1 : Qp).half ∗ tmpClaim j b }}
      (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
          [go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty]))
          (Val #(child dir b))) (Val #true))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
        osPathS R dir dq j ∗ osCallPerm (1 : Qp).half ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (f : Loc) (fd : w64) (i : Ino) (h : NamesH),
            fileutil.lockedFile lf f ∗ os.ownFile f fd (child dir b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (wal.walOpenFlag true ||| W64 0x80000)) ∗
            trFile i True ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
            ⌜0 ≤ fd.toInt ∧ h.cur !! b = some (.file i)⌝) ∨
         (⌜err ≠ interface.nil⌝ ∗ tmpClaim j b)) }} := by
  iintro %Φ ⟨#Hos, #Hpkg, #Hsi, Hp, Hperm, Hc⟩ HΦ
  unfold tmpClaim
  icases Hc with ⟨%h, Hn, Hent⟩
  obtain ⟨hfl, hcr, htr⟩ := walOpenFlag_ok
  cases hcur : h.cur !! b with
  | none =>
    -- the name absent: a create, with the trivial update
    let A : Option (Nat × Nat × Ino) → Bool → IProp GF := fun o ok =>
      iprop(osPathS R dir dq j ∗ osCallPerm (1 : Qp).half ∗ crOut j b h (DFrac.own 1) o ∗
        crTr (ok = true) o)
    have hT : fileutil.OpenTriple
        iprop(osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm (1 : Qp).half ∗
          osNames j (.only [b]) (DFrac.own 1) h)
        (child dir b) (wal.walOpenFlag true) (W32 384) A (crIno b h) := by
      unfold fileutil.OpenTriple
      iintro %Ψ ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩ HΨ
      icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hr⟩
      ihave Hau := osAUnc_triv (A := Option (Nat × Nat × Ino))
        (osNames (GF := GF) j (.only [b]) (DFrac.own (1 : Qp).half) h)
        (crOut j b h (DFrac.own (1 : Qp).half)) $$ Hr
      iapply wp_open dir b (wal.walOpenFlag true) (W32 384) R j dq h (1 : Qp).half (1 : Qp).half
        (1 : Qp).half (crOut j b h (DFrac.own (1 : Qp).half)) hfl hcr htr hb hcur
        (Qp.half_add_half 1) $$ [$Hos $Hsi $Hp $Hperm $Hn $Hau]
      inext
      iintro %f %err ⟨Hp, Hperm, %o, Ho1, Ho2, Htr, Hr⟩
      iapply HΨ
      unfold fileutil.openPost
      iexists o
      ihave Ho := crOut_join j b h o $$ [$Ho1 $Ho2]
      icases Hr with (⟨%fd, %i, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok⟩)
      · obtain ⟨rfl, hfd, hi⟩ := hres
        ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hp Hperm Ho Htr]
        · simp only [A]
          iframe
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
        iexact Htr
    wp_apply wp_create (child dir b) true _ _ A (crIno b h) hT $$ [$Hos $Hpkg $Hsi $Hp $Hperm $Hn]
      as %lf %err Hpost
    unfold fileutil.lockPost
    icases Hpost with ⟨%o, (⟨%he, HA, %f, %fd, %i, %hc, Hlf, Hf, Hoff, Hfd⟩ | ⟨%he, %ok, HA⟩)⟩
    · simp only [A]
      icases HA with ⟨Hp, Hperm, Ho, Htr⟩
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
        iframe
        ipureintro; exact ⟨hfd, by simp [NamesH.log]⟩
    · simp only [A]
      icases HA with ⟨Hp, Hperm, Ho, Htr⟩
      iapply HΦ
      iframe Hp Hperm
      iright
      isplitr
      · ipureintro; exact he.1
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
        iprop(osPathS R dir dq j ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
          osCallPerm (1 : Qp).half ∗ trFile i (ok = true))
      have hT : fileutil.OpenTriple
          iprop(osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗
            osNames j (.only [b]) (DFrac.own 1) h ∗ osCallPerm (1 : Qp).half ∗ trFile i False)
          (child dir b) (wal.walOpenFlag true) (W32 384) A (fun _ i' => i' = i) := by
        unfold fileutil.OpenTriple
        iintro %Ψ ⟨#Hos, #Hsi, Hp, Hn, Hperm, Htr⟩ HΨ
        iapply os.OpenFile.wp_truncS dir b (wal.walOpenFlag true) (W32 384) R j i (.only [b]) dq
          (DFrac.own 1) h (1 : Qp).half hfl htr hb (by simp [NameSet.Mem]) hcur
          $$ [$Hos $Hsi $Hp $Hn $Hperm $Htr]
        inext
        iintro %f %err ⟨Hp, Hn, Hperm, Htr, Hr⟩
        iapply HΨ
        unfold fileutil.openPost
        iexists ()
        icases Hr with (⟨%fd, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok⟩)
        · obtain ⟨rfl, hfd⟩ := hres
          ileft
          isplitr
          · ipureintro; rfl
          isplitl [Hp Hperm Hn Htr]
          · simp only [A]
            iframe
          iexists fd, i
          iframe
          ipureintro; exact ⟨hfd, rfl⟩
        · iright
          isplitr
          · ipureintro; exact herr
          iframe Hok
          simp only [A]
          iframe
          iapply trFile_mono i _ _ (fun h => by cases h) $$ Htr
      wp_apply wp_create (child dir b) true _ _ A (fun _ i' => i' = i) hT
        $$ [$Hos $Hpkg $Hsi $Hp $Hn $Hperm $Hent] as %lf %err Hpost
      unfold fileutil.lockPost
      icases Hpost with ⟨%o, (⟨%he, HA, %f, %fd, %i', %hc, Hlf, Hf, Hoff, Hfd⟩ | ⟨%he, %ok, HA⟩)⟩
      · simp only [A]
        icases HA with ⟨Hp, Hn, Hperm, Htr⟩
        obtain ⟨hfd, rfl⟩ := hc
        iapply HΦ
        iframe Hp Hperm
        ileft
        isplitr
        · ipureintro; exact he
        iexists f, fd, i', h
        iframe
        ipureintro; exact ⟨hfd, hcur⟩
      · simp only [A]
        icases HA with ⟨Hp, Hn, Hperm, Htr⟩
        iapply HΦ
        iframe Hp Hperm
        iright
        isplitr
        · ipureintro; exact he.1
        iexists h
        iframe Hn
        rw [hcur]
        simp only [tmpEnt]
        iapply trFile_mono i _ _ (fun h => h.elim) $$ Htr


/-- A file's `OsMeta` and zero bytes (no mappings): the file whole, any size (`trFile i False`). -/
theorem zerosA_trFile (i : Ino) (m : OsMeta) (hm : m.maps = ∅) (hcut : m.cut = none)
    (hlo : m.lo ≤ m.size) :
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osZerosA i 0 m.size (DFrac.own 1) ⊢ trFile i False := by
  iintro ⟨Hm, Hz⟩
  icases (osZerosA_unfold i 0 m.size (DFrac.own 1)).1 $$ Hz with ⟨%zs, %hzs, Hz⟩
  iunfold trFile
  iexists m, zs.map (fun c => ((0 : w8), c))
  iframe Hm Hz
  isplitl []
  · iapply mcellsAny_empty m.maps hm
  ipureintro
  exact ⟨by simp [hzs], fun h => h.elim, hm, hcut, hlo⟩

/-- **After an unlink of the pipeline's file** (both halves of the outcome), with the file: the
claim, the name absent (the file dropped), or still the file. -/
theorem rmFile_tmpClaim (j : Ino) (b : GoString) (i : Ino) (h : NamesH)
    (o : Option (Nat × Nat)) (hcur : h.cur !! b = some (.file i)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half) o ∗
      rmFileOut j b i h (DFrac.own (1 : Qp).half) o ∗ trFile i False ⊢ tmpClaim j b := by
  unfold rmFileOut tmpClaim
  cases o with
  | none =>
    simp only [claimOut]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩, Ht⟩
    iexists h
    isplitl [H1 H2]
    · iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1 $$ [$H1 $H2]
    rw [hcur]
    simp only [tmpEnt]
    iexact Ht
  | some xs =>
    obtain ⟨x, s⟩ := xs
    simp only [claimOut]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩, -⟩
    iexists _
    isplitl [H1 H2]
    · iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1 $$ [$H1 $H2]
    simp only [NamesH.log]
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), GMap.lookup_delete]
    simp only [tmpEnt]
    iempintro

/-- **`walInv`-free unlink of the pipeline's file**, by a caller holding the whole claim. -/
theorem wp_removeTmp (wp_Remove : os.Remove.specFileSnc (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (b : GoString) (i : Ino) (h : NamesH)
    (qc : Qp) (hb : NameOk b) (hcur : h.cur !! b = some (.file i)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm qc ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ trFile i False }}
      (App (Val (@! os.Remove)) (Val #(child dir b)))
    {{ (err : GoInterface), RET #err; osPathS R dir dq j ∗ osCallPerm qc ∗ tmpClaim j b }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, Hn, Ht⟩ HΦ
  icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hr⟩
  ihave Hau := osAUnc_triv (A := Option (Nat × Nat))
    (osNames (GF := GF) j (.only [b]) (DFrac.own (1 : Qp).half) h)
    (rmFileOut j b i h (DFrac.own (1 : Qp).half)) $$ Hr
  iapply wp_Remove dir b j i R dq h (1 : Qp).half (1 : Qp).half qc
    (rmFileOut j b i h (DFrac.own (1 : Qp).half)) hb hcur (Qp.half_add_half 1)
    $$ [$Hos $Hsi $Hp $Hperm $Hn $Hau]
  inext
  iintro %err ⟨Hp, Hperm, %o, -, Ho1, Ho2⟩
  iapply HΦ
  iframe Hp Hperm
  iapply rmFile_tmpClaim j b i h o hcur $$ [$Ho1 $Ho2 $Ht]

end iris

end WalFs
end EtcdGrove
end Perennial
