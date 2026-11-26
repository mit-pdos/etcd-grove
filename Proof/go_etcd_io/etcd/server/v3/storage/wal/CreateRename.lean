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

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuFresh
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSplit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import Proof.os.SharedAu
public import Spec.os.RenameS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamedPure

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
def createU (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (ic : Nat) (hC : NamesH) (md : List w8)
    (Q : IProp GF) (Pv : Option WalDur → Prop) (Wn : List GoString) (J : Ino) (hJ : NamesH) (g : SegG) (o : Option (Nat × Nat)) : IProp GF :=
  iprop(walInv (W := W) walCodec Mr R jr r ∗
    (∃ m : Nat, ⌜∀ xe ∈ hJ.ents, xe.1 < m⌝ ∗ osCommitLb m) ∗
    walCreateQ (W := W) (child r nm) ic (.only [nm, tmpName nm]) hC md Q Pv Wn J walTmps hJ g
      (createTailG Mr md jr nm J g) o)

/-- **`Create`'s result once the pipeline has its share** (`renameWAL`'s `UH`): `createU (some _)` but the
reserve of the incarnations, which the spine law gives the pipeline (`walPipeKey`), and the commit bound,
which no committed arm uses. -/
def createUK (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (ic : Nat) (md : List w8)
    (Q : IProp GF) (Wn : List GoString) (J : Ino) (g : SegG) (_x : Nat × Nat) : IProp GF :=
  iprop(walInv (W := W) walCodec Mr R jr r ∗
    walCreateQK (W := W) (child r nm) ic md Q Wn J walTmps g (createTailG Mr md jr nm J g))

/-- **The aborted result rebuilds the update** (`RenameWALOk`'s last conjunct), over the fresh layout. -/
theorem createU_none (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (ic : Nat)
    (md : List w8) (Q : IProp GF) (Pv : Option WalDur → Prop) (Wn : List GoString) (hnW : nm ∉ Wn)
    (hC : NamesH) (J : Ino) (hJ' : NamesH) (i : Ino)
    (m2 mS : OsMeta) (zs2 : List Cands) (ysS : List ByteG) (lb : Nat)
    (hin : InArea r (child r nm) nm) (hnm : walNameOk nm) (hMr : WalMarshalCreateOk Mr)
    (hmd : md.length < 2 ^ 41) (hmdne : md ≠ [])
    (hctmp : hC.cur !! tmpName nm = some (.dir J)) (hJjr : J ≠ jr)
    (hlb : hC.next ≤ lb) (hJlb : (hJ'.restrict J ((NameSet.except []).diff walTmps)).next ≤ lb)
    (hJcoh : ClaimCoh (hJ'.restrict J ((NameSet.except []).diff walTmps)) J (.except walTmps))
    (hcur : ∀ b, hJ'.cur !! b = if b = walFileName 0 0 then some (.file i) else none)
    (hok : os.StreamOk m2 0 (zs2.map (fun c => ((0 : w8), c))) (createStream Mr md) mS ysS)
    (hm2s : m2.size = 64000000) (hm2c : m2.cut = none) (hm2m : m2.maps = ∅) :
    ⊢ createU (W := W) Mr R jr r nm ic hC md Q Pv Wn J (hJ'.restrict J ((NameSet.except []).diff walTmps))
        (createSeg i mS ysS) none -∗
      osAUnc (osNames jr (.only [nm, tmpName nm]) (DFrac.own (1 : Qp).half) hC)
        (renDirOut jr J (.only [nm, tmpName nm]) (tmpName nm) nm hC (DFrac.own (1 : Qp).half) lb)
        (createU (W := W) Mr R jr r nm ic hC md Q Pv Wn J (hJ'.restrict J ((NameSet.except []).diff walTmps))
          (createSeg i mS ysS)) := by
  rw [show createU (W := W) Mr R jr r nm ic hC md Q Pv Wn J (hJ'.restrict J ((NameSet.except []).diff walTmps))
      (createSeg i mS ysS) none = iprop(walInv (W := W) walCodec Mr R jr r ∗
        (∃ m : Nat, ⌜∀ xe ∈ (hJ'.restrict J ((NameSet.except []).diff walTmps)).ents, xe.1 < m⌝ ∗
          osCommitLb m) ∗
        walCreateP (W := W) (child r nm) ic (.only [nm, tmpName nm]) hC md Q Pv Wn J walTmps
          (hJ'.restrict J ((NameSet.except []).diff walTmps)) (createSeg i mS ysS)) from rfl]
  iintro ⟨#Hinv, ⟨%m, %hJm, #Hcm⟩, HP⟩
  ihave Hau := createFresh_osAUnc Mr R jr r nm ic md Q Pv Wn hnW hC J hJ' i m2 mS zs2 ysS lb hin hnm hMr hmd hmdne
    hctmp hJjr hlb hJlb hJcoh m hJm hcur hok hm2s hm2c hm2m $$ Hinv Hcm HP
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
names the WAL's directory, and the whole claim on `nm.tmp`, which is absent now; the rename (logged at
`x.1`) the new name's last writer, and the log past it (the parent fsync's bound, `walInv_named`). -/
def createSpR (jr J : Ino) (nm : GoString) (c : Qp) (x : Nat × Nat) : IProp GF :=
  iprop(∃ hn ht : NamesH, osNames jr (.only [nm]) (DFrac.own c) hn ∗
    osNames jr (.only [tmpName nm]) (DFrac.own 1) ht ∗
    ⌜hn.cur !! nm = some (.dir J) ∧ ht.cur !! tmpName nm = none⌝ ∗
    ⌜∃ e E, LastWrite hn jr nm x.1 e E ∧ E !! nm = some (.dir J)⌝ ∗ osLogLb (x.1 + 1))

open Classical in
/-- **The last entry of a claim restricted to names it writes**, after it is logged. -/
theorem lastWrite_log_restrict (h : NamesH) (j : Ino) (M : NameSet) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hM : M.Mem b) (hw : e.op.Writes j b) :
    LastWrite ((h.log x e c).restrict j M) j b x e (restrictN M c) := by
  have h1 : decide (∃ b', M.Mem b' ∧ e.op.Writes j b') = true := decide_eq_true ⟨b, hM, hw⟩
  have h2 : decide (e.op.Writes j b) = true := decide_eq_true hw
  unfold LastWrite NamesH.restrict NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil, h1, h2, if_true, List.map_append,
    List.map_cons, List.map_nil]
  simp

/-- **`Create`'s residue once the WAL's handle holds its share** (`renameWALPost`'s `UH`, the two
success arms' convergence point): the client's `Q`, the past state with the fresh WAL, the rest of
its fraction `c` of the new name's claim with the rename its last writer and the log past it (the
parent fsync's naming, `walInv_named`), `c` being the program's half less the two paths to `dir` the
handle holds (`qh` each, pinned in `walOpenWFU`; design P, `notes/wal-units/create.md`: the name is not
registered until `Create` succeeds), the whole claim on the absent `nm.tmp` (the deferred `RemoveAll`,
the area's merge), and the area's split record (`nm` not in it). -/
def createUH (jr J : Ino) (r nm : GoString) (ic : Nat) (md : List w8) (Q : IProp GF) (Wn : List GoString)
    (qh : Qp) (x : Nat × Nat) : IProp GF :=
  iprop(Q ∗ (∃ (s' : AbsDiskState) (I : GMap GoString Nat), walPastI (W := W) (s', I) ∗
      ⌜incOf I (child r nm) = ic ∧ s'.wal !! child r nm = some (walDurFresh md)⌝) ∗
    (∃ (c : Qp) (hn : NamesH), osNames jr (.only [nm]) (DFrac.own c) hn ∗
      ⌜qh + (qh + c) = (1 : Qp).half ∧
        hn.cur !! nm = some (.dir J) ∧ ∃ e E, LastWrite hn jr nm x.1 e E ∧ E !! nm = some (.dir J)⌝) ∗
    osLogLb (x.1 + 1) ∗
    (∃ ht : NamesH, osNames jr (.only [tmpName nm]) (DFrac.own 1) ht ∗ ⌜ht.cur !! tmpName nm = none⌝) ∗
    walSplitFrag (W := W) Wn)

/-- **The spine law** (`RenameWALOk`'s third conjunct) of `Create`'s choices: `d + (d + c)` the
program's half of the new name's claim. -/
theorem create_spine (Mr : WalMarshal) (R : Roots) (jr J : Ino) (r nm : GoString) (ic : Nat) (hC : NamesH)
    (md : List w8) (Q : IProp GF) (Pv : Option WalDur → Prop) (Wn : List GoString) (hJ : NamesH) (g : SegG) (lb : Nat) (d c : Qp)
    (hd : d + (d + c) = (1 : Qp).half) (hnm : walNameOk nm) (hnmO : NameOk nm) :
    ⊢ ∀ x : Nat × Nat, createSp (W := W) Mr R jr r d -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      createU (W := W) Mr R jr r nm ic hC md Q Pv Wn J hJ g (some x) -∗
      renDirOut jr J (.only [nm, tmpName nm]) (tmpName nm) nm hC
        (DFrac.own (1 : Qp).half) lb (some x) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      createUK (W := W) Mr R jr r nm ic md Q Wn J g x ∗
      osPathS R (child r nm) (DFrac.own d) J ∗
      osPathS R (child r nm) (DFrac.own d) J ∗
      createSpR (hG := hG) jr J nm c x ∗
      (∃ (C : WalCodec) (Mr' : WalMarshal) (jr' : Ino) (r' : GoString),
        walInv (W := W) C Mr' R jr' r') ∗ walPipeKey (W := W) (child r nm) J := by
  iintro %x Hsp Hnc HU Hout
  iunfold createU at HU
  icases HU with ⟨#Hinv0, -, HQ⟩
  isimp only [walCreateQ, walCreateQK] at HQ
  icases HQ with ⟨⟨HQ, Hsf, Hm, Hb, Ho, Htr, Hnf, #Hkey, %s', %I, Hl, Hpast, %hIs⟩, Hres⟩
  icases walPipeKey_ofLocked (W := W) I (child r nm) ic J walTmps hIs.1 $$ Hl Hkey Hres with ⟨Hl, Hpk⟩
  ihave HU : createUK (W := W) Mr R jr r nm ic md Q Wn J g x $$ [HQ Hsf Hm Hb Ho Htr Hnf Hl Hpast]
  · unfold createUK walCreateQK
    iframe Hinv0 HQ Hsf Hm Hb Ho Htr Hnf Hkey
    iexists s', I
    iframe Hl Hpast
    ipureintro; exact hIs
  ihave #Hwk : (∃ (C : WalCodec) (Mr' : WalMarshal) (jr' : Ino) (r' : GoString),
      walInv (W := W) C Mr' R jr' r') $$ []
  · iexists walCodec, Mr, jr, r
    iexact Hinv0
  unfold createSp
  icases Hsp with ⟨#Hinv, #Hsi, Hp1, Hp2⟩
  obtain ⟨x, s⟩ := x
  unfold renDirOut claimOut logOut osLogged
  icases Hout with ⟨⟨-, -, -, #Hlg⟩, Hn⟩
  have hT : ⊢ createUK (W := W) Mr R jr r nm ic md Q Wn J g (x, s) -∗
      walUnlockedTokX (W := W) -∗ False := by
    unfold createUK
    iintro ⟨-, HQ⟩ Hu
    unfold walCreateQK
    icases HQ with ⟨-, -, -, -, -, -, -, -, %s', %I, Hl, -⟩
    ihave Hl : walLockedTok (W := W) $$ [Hl]
    · unfold walLockedTok; iexists I; iexact Hl
    iapply walLockedTok_exclX $$ Hl Hu
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
  iframe Hnc HU Hs1 Hs2 Hwk Hpk
  unfold createSpR
  iexists _, _
  iframe Hnm Htmp Hlg
  ipureintro
  refine ⟨⟨hn1, ht1⟩, _, _, lastWrite_log_restrict _ _ _ _ _ _ _
    ((NameSet.mem_diff _ _ _).2 ⟨by simp [NameSet.Mem], by simpa using (tmpName_ne nm).symm⟩)
    (by simp [renDirEnt, MetaOp.Writes, MetaOp.slots]), ?_⟩
  rw [restrictN_lookup _ _ _ ((NameSet.mem_diff _ _ _).2 ⟨by simp [NameSet.Mem],
      by simpa using (tmpName_ne nm).symm⟩), hcnm]

end au

end WalFs
end EtcdGrove
end Perennial
