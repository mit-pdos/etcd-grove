/- Lean-first (no Rocq counterpart).

# What `Create` gives `renameWAL` (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", eighteenth
session)

`renameWAL.spec` is generic in the update's result `U`, the spine law's resource `Sp` and its remainder
`SpR`; `RenameWALOk` asks two laws of them. `Create`'s choices:

* `createU`: `walCreateQ` with `walInv` and a commit bound past `J`'s entries (persistent), so that
  the aborted result `U none` rebuilds the update (`createU_none`, over `createFresh_osAUnc` and
  `osAUnc_mono`) inside a closed `⊢`.
* `createSp`/`createSpR`, `create_spine`: two fractions `d` of the area's spine; after the commit
  `walInv_splitNew` splits the program's half of the creating claim into its half of `.only [nm]` (two
  fractions `d` of it make the two spines to the new WAL's directory, `osPathS_child`; the rest `c` is
  `SpR`'s) and the whole claim on `nm.tmp` (absent now; `SpR`'s, for the deferred `RemoveAll`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuFresh
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSplit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import LinuxFs.Proof.os.SharedAu
public import LinuxFs.Spec.os.Rename

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode Fs WalEnc

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **An `osAUnc`'s result weakened** (coinduction). -/
theorem osAUnc_mono {A : Type} (α : IProp GF) (β Q Q' : A → IProp GF) :
    ⊢ □ (∀ o, Q o -∗ Q' o) -∗ osAUnc α β Q -∗
      osAUnc α β Q' := by
  iintro #HQ Hau
  iapply osAUnc_coiter α β Q' (osAUnc α β Q) $$ [] Hau
  iintro !> Hau
  ihave Hp := osAUnc_unfold α β Q $$ Hau
  unfold osAUncPre
  iintro Hnc
  imod Hp $$ Hnc with ⟨Hα, Hnc, Hcl⟩
  imodintro
  iframe Hα Hnc
  isplit
  · icases Hcl with ⟨Hcl, -⟩
    iexact Hcl
  · icases Hcl with ⟨-, Hcl⟩
    iintro %o Hb
    imod Hcl $$ %o Hb with HQo
    imodintro
    iapply HQ $$ HQo

/-- **`Create`'s result of the rename's update**: `walCreateQ`, with the WAL invariant. -/
def createU (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (hC : NamesH) (md : List w8)
    (Q : IProp GF) (J : Ino) (hJ : NamesH) (g : SegG) (o : Option (Nat × Nat)) : IProp GF :=
  iprop(walInv (W := W) walCodec Mr R jr r ∗
    (∃ m : Nat, ⌜∀ xe ∈ hJ.ents, xe.1 < m⌝ ∗ osCommitLb m) ∗
    walCreateQ (W := W) (child r nm) (.only [nm, tmpName nm]) hC md Q J walTmps hJ g o)

/-- **The aborted result rebuilds the update** (`RenameWALOk`'s last conjunct), over the fresh layout. -/
theorem createU_none (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString)
    (md : List w8) (Q : IProp GF) (hC : NamesH) (J : Ino) (hJ' : NamesH) (i : Ino)
    (m2 mS : OsMeta) (zs2 : List Cands) (ysS : List ByteG) (lb : Nat)
    (hin : InArea r (child r nm) nm) (hnm : walNameOk nm) (hMr : WalMarshalCreateOk Mr)
    (hmd : md.length < 2 ^ 41)
    (hctmp : hC.cur !! tmpName nm = some (.dir J)) (hJjr : J ≠ jr)
    (hlb : hC.next ≤ lb) (hJlb : (hJ'.restrict J ((NameSet.except []).diff walTmps)).next ≤ lb)
    (hJcoh : ClaimCoh (hJ'.restrict J ((NameSet.except []).diff walTmps)) J (.except walTmps))
    (hcur : ∀ b, hJ'.cur !! b = if b = walFileName 0 0 then some (.file i) else none)
    (hok : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS)
    (hm2s : m2.size = 64000000) (hm2c : m2.cut = none) :
    ⊢ createU (W := W) Mr R jr r nm hC md Q J (hJ'.restrict J ((NameSet.except []).diff walTmps))
        (createSeg i mS ysS) none -∗
      osAUnc (osNames jr (.only [nm, tmpName nm]) (DFrac.own (1 : Qp).half) hC)
        (renDirOut jr J (.only [nm, tmpName nm]) (tmpName nm) nm hC (DFrac.own (1 : Qp).half) lb)
        (createU (W := W) Mr R jr r nm hC md Q J (hJ'.restrict J ((NameSet.except []).diff walTmps))
          (createSeg i mS ysS)) := by
  rw [show createU (W := W) Mr R jr r nm hC md Q J (hJ'.restrict J ((NameSet.except []).diff walTmps))
      (createSeg i mS ysS) none = iprop(walInv (W := W) walCodec Mr R jr r ∗
        (∃ m : Nat, ⌜∀ xe ∈ (hJ'.restrict J ((NameSet.except []).diff walTmps)).ents, xe.1 < m⌝ ∗
          osCommitLb m) ∗
        walCreateP (W := W) (child r nm) (.only [nm, tmpName nm]) hC md Q J walTmps
          (hJ'.restrict J ((NameSet.except []).diff walTmps)) (createSeg i mS ysS)) from rfl]
  iintro ⟨#Hinv, ⟨%m, %hJm, #Hcm⟩, HP⟩
  ihave Hau := createFresh_osAUnc Mr R jr r nm md Q hC J hJ' i m2 mS zs2 ysS lb hin hnm hMr hmd
    hctmp hJjr hlb hJlb hJcoh m hJm hcur hok hm2s hm2c $$ Hinv Hcm HP
  iapply osAUnc_mono $$ [] Hau
  iintro !> %o HQ
  unfold createU
  iframe HQ Hinv
  iexists m
  iframe Hcm
  ipureintro; exact hJm

/-- **`Create`'s spine resource**: the WAL invariant, the shared invariant, two fractions `d` of the
area's spine. -/
def createSp (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (d : Qp) : IProp GF :=
  iprop(walInv (W := W) walCodec Mr R jr r ∗ osSharedInv R ∗
    osPathS R r (DFrac.own d) jr ∗
    osPathS R r (DFrac.own d) jr)

/-- **`Create`'s remainder after the spines**: the rest `c` of its half of the new name's claim, which
names the WAL's directory, and the whole claim on `nm.tmp`, which is absent now. -/
def createSpR (jr J : Ino) (nm : GoString) (c : Qp) (_ : Nat × Nat) : IProp GF :=
  iprop(∃ hn ht : NamesH, osNames jr (.only [nm]) (DFrac.own c) hn ∗
    osNames jr (.only [tmpName nm]) (DFrac.own 1) ht ∗
    ⌜hn.cur !! nm = some (.dir J) ∧ ht.cur !! tmpName nm = none⌝)

/-- **The spine law** (`RenameWALOk`'s third conjunct) of `Create`'s choices: `d + (d + c)` the
program's half of the new name's claim. -/
theorem create_spine (Mr : WalMarshal) (R : Roots) (jr J : Ino) (r nm : GoString) (hC : NamesH)
    (md : List w8) (Q : IProp GF) (hJ : NamesH) (g : SegG) (lb : Nat) (d c : Qp)
    (hd : d + (d + c) = (1 : Qp).half) (hnm : walNameOk nm) (hnmO : NameOk nm) :
    ⊢ ∀ x : Nat × Nat, createSp (W := W) Mr R jr r d -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      createU (W := W) Mr R jr r nm hC md Q J hJ g (some x) -∗
      renDirOut jr J (.only [nm, tmpName nm]) (tmpName nm) nm hC
        (DFrac.own (1 : Qp).half) lb (some x) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      createU (W := W) Mr R jr r nm hC md Q J hJ g (some x) ∗
      osPathS R (child r nm) (DFrac.own d) J ∗
      osPathS R (child r nm) (DFrac.own d) J ∗
      createSpR (hG := hG) jr J nm c x := by
  iintro %x Hsp Hnc HU Hout
  unfold createSp
  icases Hsp with ⟨#Hinv, #Hsi, Hp1, Hp2⟩
  obtain ⟨x, s⟩ := x
  unfold renDirOut claimOut
  icases Hout with ⟨-, Hn⟩
  have hT : ⊢ createU (W := W) Mr R jr r nm hC md Q J hJ g (some (x, s)) -∗
      walUnlockedTok (W := W) -∗ False := by
    unfold createU
    iintro ⟨-, -, HQ⟩ Hu
    unfold walCreateQ
    icases HQ with ⟨-, -, -, Hl, -⟩
    iapply walLockedTok_unlocked_excl $$ Hl Hu
  imod walInv_splitNew walCodec Mr R jr r nm (tmpName nm) _ _ hT hnm (tmpName_ne nm)
    (tmpName_walNameP nm) (tmpName_not_walName nm) (tmpName_areaSlot hnm)
    $$ Hinv Hsi Hnc HU Hn with ⟨Hnc, HU, Hnm, Htmp⟩
  have hcnm : (restrictN (NameSet.only [nm, tmpName nm]) (<[nm := Node.dir J]> (GMap.delete (tmpName nm) hC.cur))) !! nm = some (.dir J) := by
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem])]; simp
  have hctmp : (restrictN (NameSet.only [nm, tmpName nm]) (<[nm := Node.dir J]> (GMap.delete (tmpName nm) hC.cur))) !! tmpName nm = none := by
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]),
      GMap.lookup_insert_ne _ _ (tmpName_ne nm).symm]
    simp
  have hn1 : ((hC.log x (renDirEnt jr (tmpName nm) nm J s) (restrictN (NameSet.only [nm, tmpName nm]) (<[nm := Node.dir J]> (GMap.delete (tmpName nm) hC.cur)))).restrict jr
      ((NameSet.only [nm, tmpName nm]).diff [tmpName nm])).cur !! nm = some (.dir J) := by
    simp only [NamesH.restrict, NamesH.log]
    rw [restrictN_lookup _ _ _ ((NameSet.mem_diff _ _ _).2 ⟨by simp [NameSet.Mem],
      by simpa using (tmpName_ne nm).symm⟩), hcnm]
  have ht1 : ((hC.log x (renDirEnt jr (tmpName nm) nm J s) (restrictN (NameSet.only [nm, tmpName nm]) (<[nm := Node.dir J]> (GMap.delete (tmpName nm) hC.cur)))).restrict jr
      ((NameSet.only [nm, tmpName nm]).inter [tmpName nm])).cur !! tmpName nm = none := by
    simp only [NamesH.restrict, NamesH.log]
    rw [restrictN_lookup _ _ _ ((NameSet.mem_inter _ _ _).2 ⟨by simp [NameSet.Mem], by simp⟩), hctmp]
  rw [← hd]
  icases (osNames_frac _ _ d (d + c) _).1 $$ Hnm with ⟨Hn1, Hnm⟩
  icases (osNames_frac _ _ d c _).1 $$ Hnm with ⟨Hn2, Hnm⟩
  ihave Hs1 := osPathS_child R r nm (DFrac.own d) jr J _ hnmO hn1 $$ Hp1 Hn1
  ihave Hs2 := osPathS_child R r nm (DFrac.own d) jr J _ hnmO hn1 $$ Hp2 Hn2
  imodintro
  iframe Hnc HU Hs1 Hs2
  unfold createSpR
  iexists _, _
  iframe Hnm Htmp
  ipureintro; exact ⟨hn1, ht1⟩

end au

end WalFs
end EtcdGrove
end Perennial
