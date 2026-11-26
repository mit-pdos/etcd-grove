/-
**bbolt's crash record** (W3 of `plans/bbolt-crash-plan.md` §3; Lean-first, no Rocq counterpart): what
C-I1's `dbCrashKeep`/`dbCrashHole` (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`)
are, sealed, and the laws of them that need no file reasoning.

`boltCrashRec γ i0 Dl Dn`: half of the committed data at its version `ν` (`boltStateV γ ½ Dn ν`) and the
crash record's evidence `cRec`: the file's crash invariant (`csInvIR` at `crashN γ.ns`, its client
resource `bR`), the crash names' registration (`cnReg`, so the committed data's crash part is the
invariant's), and either `syncedE ν` (the commit that made `ν` finished its second sync) or the
history's element of `ν - 1` (`histE`), whose data is `Dl` or `Dn`. The hole keeps the evidence and
the history's element of `ν` (`Dn`), which the next commit's record takes as its fallback.

* `boltCrashRec_take`, `boltCrashRec_putSame`, `boltCrashRec_putStep`, `boltCrashRec_close`: the
  repackaging laws (C-I1's `take`, `putSame`, `putStep`, `close`).
* `fileHoldsMDur i D` (moved here from `backend/FileDur.lean` by W5, text unchanged; the backend's
  `fileHoldsMDur` is this one): bbolt's `fileHoldsM i D` with every byte durable (`durB`) and the
  size's crash bounds collapsed (`lo = hi = size`), written over bbolt's public API (`boltImage`,
  `boltImageRcpt`), so no new bbolt law is needed for it (`fileHoldsMDur_holds`, by
  `fileHoldsM_of_image`). What the crash-mode `DB.Close` (`DB.Close.specC`) hands over in the record's
  place; `backend.fileHoldsMDur_crash`: a file the new tree names comes back whole at the new
  generation.
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import GooseLang.Ext.Fs.FsNoErr
public import Spec.go_etcd_io.bbolt.CrashPremise
import all Spec.go_etcd_io.bbolt.Api
import Proof.go_etcd_io.bbolt.CrashMode
import Proof.go_etcd_io.bbolt.Inv.BFileOps
import Proof.go_etcd_io.bbolt.Read.PubWBkt
import Proof.go_etcd_io.bbolt.Read.TxBytes
import Proof.go_etcd_io.bbolt.Crash.Ok
import Proof.os.CrashFileQ

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

section crec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The crash record's evidence** at version `ν` (see the file header). -/
private def cRecDef (B : BNs) (N : Namespace) (i0 : Ino) (c : CsN) (Dl Dn : Data) (ν : Nat) : IProp GF :=
  iprop(⌜c.gc = B.bq ∧ c.N = crashN N ∧ FsNoErr⌝ ∗ csInvIR c.N i0 c.g c.ga c.gc bCsOk (bR c.cg) ∗
    cnReg B (some c.cg) ∗
    (syncedE c.cg ν ∨ ∃ P : Data, histE c.cg (ν - 1) P ∗ ⌜1 ≤ ν ∧ (P = Dl ∨ P = Dn)⌝))

private instance cRecDef_persistent (B : BNs) (N : Namespace) (i0 : Ino) (c : CsN) (Dl Dn : Data)
    (ν : Nat) : Persistent (cRecDef (GF := GF) B N i0 c Dl Dn ν) := by
  unfold cRecDef; infer_instance

/-- **The crash record of the open database `γ`, whose file is the inode `i0`** (exclusive; C-I1's
`dbCrashKeep`): the committed data `Dn` (half of it, at its version), the data `Dl` its file falls
back to (see the file header). -/
@[no_expose] def boltCrashRec (γ : BoltName) (i0 : Ino) (Dl Dn : Data) : IProp GF :=
  iprop(∃ (ν : Nat) (c : CsN), boltStateV γ (1 : Qp).half Dn ν ∗
    cRecDef (bnsOf γ.gs) γ.ns i0 c Dl Dn ν)

/-- **The crash record with its half lent at version `ν`** (C-I1's `dbCrashHole`). -/
@[no_expose] def boltCrashHole (γ : BoltName) (i0 : Ino) (Dl Dn : Data) (ν : Nat) : IProp GF :=
  iprop(∃ c : CsN, cRecDef (bnsOf γ.gs) γ.ns i0 c Dl Dn ν ∗ histE c.cg ν Dn)

variable [sem : go.Semantics]

/-- The committed data's crash part, in crash mode, holds the history's element of its version. -/
private theorem crashPart_histE (B : BNs) (g : CsG) (q : Qp) (D : Data) (ν : Nat) :
    cnReg (GF := GF) B (some g) ∗ crashPart B q D ν ⊢ crashPart B q D ν ∗ histE g ν D := by
  unfold crashPart
  iintro ⟨#Hr, %o, #Hr', Hc⟩
  ihave %ho := cnReg_agree B (some g) o $$ [Hr Hr']
  · iframe #
  subst ho
  icases (cpart_some g q D ν).1 $$ Hc with ⟨Hv, #He⟩
  iframe He
  iexists (some g)
  iframe Hr
  iapply (cpart_some g q D ν).2
  iframe Hv; iframe #

/-- **C-I1's `take`**: the half at its version, and the hole. -/
theorem boltCrashRec_take (γ : BoltName) (i0 : Ino) (Dl Dn : Data) :
    boltCrashRec (GF := GF) γ i0 Dl Dn ⊢
      ∃ ν, boltStateV γ (1 : Qp).half Dn ν ∗ boltCrashHole γ i0 Dl Dn ν := by
  unfold boltCrashRec boltCrashHole boltStateV boltStateVDef
  iintro ⟨%ν, %c, ⟨Hs, Hbq, Hcp⟩, #Hrec⟩
  ihave #Hreg : cnReg (GF := GF) (bnsOf γ.gs) (some c.cg) $$ []
  · unfold cRecDef; icases Hrec with ⟨-, -, $, -⟩
  icases crashPart_histE (bnsOf γ.gs) c.cg _ Dn ν $$ [Hcp] with ⟨Hcp, #He⟩
  · iframe; iframe #
  iexists ν
  iframe Hs Hbq Hcp
  iexists c
  iframe #

/-- **C-I1's `putSame`**: the half back at the same version. -/
theorem boltCrashRec_putSame (γ : BoltName) (i0 : Ino) (Dl Dn : Data) (ν : Nat) :
    boltCrashHole (GF := GF) γ i0 Dl Dn ν ∗ boltStateV γ (1 : Qp).half Dn ν ⊢
      boltCrashRec γ i0 Dl Dn := by
  unfold boltCrashRec boltCrashHole
  iintro ⟨⟨%c, #Hrec, -⟩, Hs⟩
  iexists ν, c
  iframe Hs; iframe #

open Classical in
/-- **C-I1's `putStep`**: the half back one commit later; the fallback is the data of `ν`, `Dn`
(the hole's history element), or stays `Dl` when the commit kept the data. -/
theorem boltCrashRec_putStep (γ : BoltName) (i0 : Ino) (Dl Dn S : Data) (ν : Nat) :
    boltCrashHole (GF := GF) γ i0 Dl Dn ν ∗ boltStateV γ (1 : Qp).half S (ν + 1) ⊢
      boltCrashRec γ i0 (if S = Dn then Dl else Dn) S := by
  unfold boltCrashRec boltCrashHole
  iintro ⟨⟨%c, #Hrec, #He⟩, Hs⟩
  iexists (ν + 1), c
  iframe Hs
  unfold cRecDef
  icases Hrec with ⟨%hc, #Hinv, #Hreg, -⟩
  iframe Hinv Hreg
  isplitr
  · ipureintro; exact hc
  iright
  iexists Dn
  rw [show ν + 1 - 1 = ν by omega]
  iframe He
  ipureintro
  refine ⟨by omega, ?_⟩
  by_cases h : S = Dn
  · rw [if_pos h]; exact .inr h.symm
  · rw [if_neg h]; exact .inl rfl

/-- **C-I1's `close`**: the half back (a write transaction may be live: no commit is in flight). -/
theorem boltCrashRec_close (γ : BoltName) (i0 : Ino) (Dl Dn : Data) :
    boltCrashRec (GF := GF) γ i0 Dl Dn ⊢ boltState γ (1 : Qp).half Dn := by
  unfold boltCrashRec
  iintro ⟨%ν, %c, Hs, -⟩
  iapply (boltState_eq_V (GF := GF) γ (1 : Qp).half Dn).2
  iexists ν; iexact Hs

/-- **C-I1's `_new`**: a fresh write transaction (it holds `rwlock`: its registration carries the
synced mark of its view's version, `regX`), the database syncing (`boltSyncs`) in a run where the
file system does not fail, and the half of the committed data give the record at `(D, D)`, its
evidence the synced mark. Crash mode is on by `crashMode_on`. -/
theorem boltCrashRec_new (hfs : Fs.FsNoErr) (γ : BoltName) (i0 : Ino) (D : Data)
    (tx : Loc) :
    boltSyncs (GF := GF) γ ∗ boltIno γ i0 ∗ boltState γ (1 : Qp).half D ∗ boltTx tx γ 1 (TxView.wr D) ⊢
      boltCrashRec γ i0 D D ∗ boltTx tx γ 1 (TxView.wr D) := by
  unfold boltSyncs boltIno boltState boltStateDef boltTx
  iintro ⟨⟨%db', Hdl', #Hns, #Hngs⟩, ⟨%t0', Ht0'⟩, ⟨%ν, Hs⟩, Htx⟩
  ihave Ht := (boltTxDef_wtxWQ _ _ tx 1 (TxView.wr D) rfl).1 $$ Htx
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvf, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  icases wtxWQ_reg_rw K tx r true 1 X $$ Hw with ⟨Hw, #Hreg, %hrw⟩
  ihave #Hcore : isBoltCoreP (GF := GF) K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.full isBoltP; icases Hfull with ⟨$, -⟩
  rw [hKB, hKN]
  -- crash mode
  ihave %hcm := crashMode_on _ γ.ns K.db db' K.p K.sp K.t0
    $$ [Hdl' Hns Hngs Hcore]
  · iframe Hdl'; iframe #; ipureintro; exact hfs
  obtain ⟨cc, hcc, hcN, hcgc⟩ := hcm
  icases isBoltCoreP_bfile _ _ _ _ _ _ $$ Hcore with ⟨#Hci, -⟩
  ihave #Hinv := bCsInv_some K.p cc hcc $$ Hci
  ihave #Hmd := isBoltCoreP_mode _ _ _ _ _ _ $$ Hcore
  icases bMode_some _ _ _ K.p cc hcc $$ Hmd with ⟨-, #Hreg'⟩
  -- the file is `i0`
  ihave %h0 : ⌜(K.t0, K.p.ino) = (t0', i0)⌝ $$ [Ht0']
  · unfold isBoltCoreP t0At
    icases Hcore with ⟨-, #Ht0, -⟩
    icombine Ht0 Ht0' gives %h
    ipureintro; exact h.2
  have hino : K.p.ino = i0 := (Prod.mk.inj h0).2
  -- the version is the writer's
  unfold boltStateVDef
  icases Hs with ⟨Hs1, Hbq, Hcp⟩
  icombine Hst Hs1 gives %hv
  have hνX : X.v.txid = ν := (Prod.mk.inj hv.2).2
  -- the synced mark
  ihave #HX := reg_regX _ _ _ $$ Hreg
  icases regX_rw _ _ hrw $$ HX with ⟨%v, #Hvo, #Hsb⟩
  ihave %hvv := viewOf_agree r v X.v $$ [Hvo Hvf]
  · iframe #
  subst hvv
  unfold syncedB
  icases Hsb with ⟨%o, #Hro, #Hso⟩
  ihave %ho := cnReg_agree _ (some cc.cg) o $$ [Hreg' Hro]
  · iframe #
  subst ho
  unfold syncedM
  isplitl [Hs1 Hbq Hcp]
  · unfold boltCrashRec boltStateV boltStateVDef cRecDef
    iexists ν, cc
    iframe Hs1 Hbq Hcp
    rw [← hino]
    iframe Hinv Hreg'
    isplitr
    · ipureintro; exact ⟨hcgc, hcN, hfs⟩
    ileft
    rw [← hνX]; iexact Hso
  · iapply (boltTxDef_wtxWQ _ _ tx 1 (TxView.wr D) rfl).2
    iexists K, r, c, X
    iframe Hv Hw Hst Hfull Hvf
    ipureintro
    exact ⟨⟨hKB, hKN, hTc⟩, Hf⟩

end crec

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

private theorem fileOkS_mono {Q Q' : OsState → OsState → Prop} {Gd : Option OsFile → Prop} {i : Ino}
    {s : CSt} (hQ : ∀ st st', Q st st' → Q' st st') (h : FileOkS Q' Gd i s) : FileOkS Q Gd i s := by
  intro hcut f hfc hseen
  obtain ⟨st, st', Γb, Γm, Γf, Γt, h1, h2, h3, h4, h5⟩ := hseen
  exact h hcut f hfc ⟨st, st', Γb, Γm, Γf, Γt, h1, h2, h3, hQ _ _ h4, h5⟩

/-- **C-I1's `dbCrash`**: under the crash premise `BoltCrashWhole` for the inode `i0`, the old
generation's record and the crash rest of a crash whose tree names `i0` give the file `i0` holding
`Dl` or `Dn` (whole, with its txid's receipt) at the new generation, `i0` taken. The crash invariant
(`csInvIR_crash_keep`, open by the record's half of `bq`) reports a value whose client resource agrees
with the record: its current state is the record's `(Dn, ν)` (the version variable), its previous one's
data is `Dl` or `Dn` (the history's element of `ν - 1`, or the synced mark of `ν` making the previous
state the current one), not `init`; its crash images are good of these (`bDur_okST`) and name no txid
past `ν`, whose receipt the resource holds. -/
theorem boltCrashRec_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    [sem : @go.Semantics _ L.goose_go_local_context _] (γ : BoltName)
    (i0 : Ino) (Dl Dn : Data) (hQ : ∀ st st', Q st st' → BoltCrashWhole (· = i0) st st')
    (Dx : List Ino) (hi : i0 ∉ Dx) (V' : Hist) (hN : Named V'.now i0) (E : CoPset)
    (hE : (↑(crashN γ.ns) : CoPset) ⊆ E) :
    ⊢ boltCrashRec (hG := ⟨G, L⟩) γ i0 Dl Dn -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) Dx false V' ={E}=∗
      ∃ D' : Data, ⌜D' = Dl ∨ D' = Dn⌝ ∗ fileHoldsM (hG := ⟨G, L'⟩) i0 D' ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (i0 :: Dx) false V' := by
  unfold boltCrashRec cRecDef boltStateV boltStateVDef
  iintro ⟨%ν, %c, ⟨Hs, Hbq, Hcp⟩, %hc, #Hinv, #Hreg, Hev⟩ Hr
  obtain ⟨hcgc, hcN, hfs⟩ := hc
  unfold crashPart
  icases Hcp with ⟨%o, #Hro, Hcp⟩
  ihave %ho := cnReg_agree (hG := ⟨G, L⟩) _ (some c.cg) o $$ [Hreg Hro]
  · iframe #
  subst ho
  icases (cpart_some (hG := ⟨G, L⟩) c.cg _ Dn ν).1 $$ Hcp with ⟨Hcv, #Hhe⟩
  rw [← hcgc]
  imod csInvIR_crash_keep Q L L' Dx false V' c.N i0 c.g c.ga c.gc bCsOk (bR (hG := ⟨G, L⟩) c.cg)
    (fun a fo => FsNoErr → bOkT a fo) E (by rw [hcN]; exact hE) hi
    (fun a s h hcut f hfc hseen hfs' => fileOkS_mono hQ (bDur_okST i0 a s (h hfs')) hcut f hfc hseen)
    _ iprop(ghostVar c.cg.cv (1 : Qp).half.half (Dn, ν) ∗
      (syncedE (hG := ⟨G, L⟩) c.cg ν ∨ ∃ P : Data, histE (hG := ⟨G, L⟩) c.cg (ν - 1) P ∗
        ⌜1 ≤ ν ∧ (P = Dl ∨ P = Dn)⌝))
    (fun a => iprop(⌜treeData a.cur = Dn ∧ a.cur.txid = ν ∧
      (treeData a.prev = Dl ∨ treeData a.prev = Dn) ∧ a.phase ≠ .init⌝ ∗ ⧖ a.cur.txid))
    $$ Hinv Hbq [Hcv Hev] [] Hr with ⟨%a, %fo, %Hfo, ⟨%Ha, #Hrc⟩, Hf, Hr⟩
  · iframe Hcv Hev
  · iintro %a HR ⟨Hcv, Hev⟩
    unfold bR
    icases HR with ⟨Hcv', ⟨%H, %y, Hh, Hy, %Hfacts⟩, #Hrc⟩
    icombine Hcv' Hcv gives %hv
    obtain ⟨hHc, hHp, hHle, hy, hpc, hni⟩ := Hfacts
    have hcur : treeData a.cur = Dn ∧ a.cur.txid = ν := Prod.mk.inj hv.2
    ihave %hprev : ⌜treeData a.prev = Dl ∨ treeData a.prev = Dn⌝ $$ [Hev Hh Hy]
    · icases Hev with (#Hsy | ⟨%P, #HP, %hP⟩)
      · unfold syncedE
        ihave %hl := monoNatLbOwn_valid _ _ _ _ $$ Hy Hsy
        rcases hpc with h | h
        · exfalso; have := hl.2; omega
        · ipureintro; right; rw [h, hcur.1]
      · rcases hpc with h | h
        · unfold histE
          icombine HP Hh gives %hl
          have hk : a.prev.txid = ν - 1 := by omega
          have hHp' := hHp
          rw [hk] at hHp'
          have e : some (treeData a.prev) = some P := hHp'.symm.trans hl
          ipureintro
          rw [Option.some.inj e]; exact hP.2
        · ipureintro; right; rw [h, hcur.1]
    iframe Hrc
    isplitl
    · iframe Hcv'
      iexists H, y; iframe Hh Hy; ipureintro; exact ⟨hHc, hHp, hHle, hy, hpc, hni⟩
    · ipureintro; exact ⟨hcur.1, hcur.2, hprev, hni⟩
  obtain ⟨⟨s, hOk, -⟩, hnm, hgd⟩ := Hfo
  obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm hN)
  obtain ⟨hbc, htx⟩ := hgd f rfl hfs f rfl
  obtain ⟨hdc, hdt, hdp, hdi⟩ := Ha
  have hrcpt := htx hdi
  -- the data
  obtain ⟨D', hD', hg⟩ : ∃ D', (D' = Dl ∨ D' = Dn) ∧ bGood D' f := by
    unfold bCrash at hbc
    revert hbc hdi
    cases a.phase <;> intro hbc hdi <;> dsimp only at hbc
    · exact ⟨Dn, .inr rfl, hdc ▸ hbc⟩
    · rcases hbc with h | h
      · exact ⟨Dn, .inr rfl, hdc ▸ h⟩
      · exact ⟨treeData a.prev, hdp, h⟩
    · exact absurd rfl hdi
  imodintro
  iexists D'
  iframe Hr
  isplitr
  · ipureintro; exact hD'
  unfold osFileStartO osFileStart
  icases Hf with ⟨Hm', Hb'⟩
  have hfs' : f.size = f.contents.length := (contents_length' f).symm
  have hmap : (f.contents.map durB).map Prod.fst = f.contents := by
    simp only [List.map_map]; exact List.map_id' _ |>.trans rfl
  unfold fileHoldsM fileHoldsMDef
  iexists initMeta f, f.contents.map durB
  iframe Hm' Hb'
  isplitr
  · ipureintro
    rw [hmap]
    exact ⟨rfl, by simp only [List.length_map]; exact hfs'.symm, hg.2.1, hg.1⟩
  isplitr
  · ipureintro; exact hg.2.2
  rw [hmap]
  unfold fileRcpt
  iright
  iexists a.cur.txid
  iframe Hrc
  ipureintro
  exact hrcpt

end crash

/-! ### A database file every byte of which is durable (W5) -/

section dur
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The file of inode `i` holds `D`, mappable, every byte durable** (see the file header). -/
def fileHoldsMDur (i : Ino) (D : Data) : IProp GF :=
  iprop(∃ (m : OsMeta) (bs : List w8), osMeta i (DFrac.own 1) m ∗
    osBytes i 0 (DFrac.own 1) (bs.map durB) ∗
    ⌜m.maps = ∅ ∧ m.size = bs.length ∧ m.lo = bs.length ∧ m.hi = bs.length ∧ bbolt.boltImage bs D ∧
      bs.length ≤ bbolt.boltMaxMapSize⌝ ∗ bbolt.boltImageRcpt bs)

/-- A durable file holds its data, mappable (`fileHoldsM_of_image`). -/
theorem fileHoldsMDur_holds (i : Ino) (D : Data) :
    fileHoldsMDur (GF := GF) i D ⊢ bbolt.fileHoldsM i D := by
  unfold fileHoldsMDur
  iintro ⟨%m, %bs, Hm, Hb, %h, Hr⟩
  obtain ⟨hmaps, hsize, -, -, himg, hlen⟩ := h
  have hfst : (bs.map durB).map Prod.fst = bs := by simp [List.map_map, Function.comp_def]
  iapply bbolt.fileHoldsM_of_image i m (bs.map durB) D hmaps (by simpa using hsize)
    (by rw [hfst]; exact himg) (by simpa using hlen)
  iframe Hm Hb
  rw [hfst]; iexact Hr

end dur

end bbolt
end EtcdGrove
end Perennial
