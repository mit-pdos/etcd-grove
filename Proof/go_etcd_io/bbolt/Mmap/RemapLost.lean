/-
The remap's end states (U4d, `notes/bbolt-proof-plan.md`; `Mmap/Remap`'s plan, steps 5-9): the
writer's records re-based (`wtxCore_rebase`, over `Mmap/Rebase`'s `wtxHeap_rebase`), and the
writer side after a failed remap (`wdbLost'_intro`: no mapping, the `W` slots those of the file,
`wdbOK'_lost`; batch 44.1: flagged).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.RemapBase
public import Proof.go_etcd_io.bbolt.Mmap.Rebase
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

theorem View.with_base_self (v : View) : { v with base := v.base } = v := by cases v; rfl

/-- The writer side after a failed remap: no mapping, the file's `OsMeta` `m'` (its maps empty, or
the leaked mapping `j`), the `W` slots those inside the file. -/
def WDb.lost [GooseExts] (w : WDb) (m' : OsMeta) (j : Option (Loc × Nat)) : WDb :=
  { w with ms := none, m := m', W := wSlots (w.m.size / 4096) w.C w.fl, junk := j }

theorem wdbOK'_lost [GooseExts] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] (fr : Bool) (w : WDb) (hok : wdbOK' fr w) (m' : OsMeta)
    (j : Option (Loc × Nat)) (hsz : m'.size = w.m.size)
    (hmaps : m'.maps = ∅ ∨ ∃ jb jl, j = some (jb, jl) ∧ m'.maps = GMap.singleton jb jl) :
    wdbOK' fr (w.lost m' j) := by
  have hc := flClause_congr fr w (w.lost m' j) rfl rfl rfl (wdbOK'_flClause fr w hok)
  obtain ⟨_, _, hk3, hk4, hk5, hk6, hk7, hk8, _, _, hk11, hk12, hk13, -, hk15, hk16, hk17⟩ := hok
  refine ⟨?_, fun _ => hmaps, ?_, ?_, hk5, hc, hk7, hk8, ?_, ?_, hk11, hk12, ?_, ?_, ?_,
    fun s h1 h2 => by simp only [WDb.lost, hsz] at h1 h2 ⊢; exact hk16 s h1 h2, hk17⟩
  · intro b l h; simp [WDb.lost] at h
  · simp only [WDb.lost]; rw [hsz]; exact hk3
  · intro s
    simp only [WDb.lost, mapLen, hsz, Nat.zero_max]
    exact mem_W_of_wSlots _ _ _ s
  · intro b l h; simp [WDb.lost] at h
  · intro b l h; simp [WDb.lost] at h
  · obtain ⟨a1, -, a3⟩ := hk13
    refine ⟨?_, ?_, ?_⟩ <;> simp only [WDb.lost, mapLen, hsz] <;> first | exact a1 | exact a3 | omega
  · intro b l h; simp [WDb.lost] at h
  · intro s hs hle
    simp only [WDb.lost, hsz] at hs hle ⊢
    obtain ⟨a, b, c, d⟩ := (mem_W_of_wSlots _ _ _ s).1 hs
    refine hk15 s ((hk4 s).2 ⟨a, ?_, c, d⟩) hle
    have := Nat.le_max_right (mapLen w.ms) w.m.size
    have : s < w.m.size / 4096 := by omega
    omega

section lost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's core re-based** on the new mapping `b` (after `dereference`'s coverage contract),
with its view registered at `b`. -/
theorem wtxCore_rebase (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (b : Loc)
    (hcov : derefOK X) :
    wtxCore (GF := GF) K tx r m X ∗ viewBase r { X.v with base := b } ⊢
      wtxCore K tx r m (X.rebase b) := by
  unfold wtxCore
  iintro ⟨⟨Hpkg, Hc, %Hp, Hreg, Hh, Hf, Hbk, Hnl, Hdb, -, Hst⟩, Hv⟩
  ihave Hh := wtxHeap_rebase tx (DFrac.own 1) X b hcov $$ Hh
  iframe
  ipureintro; exact Hp

/-- The junk mapping's cells, and the file-given-up flag `nf` (session bbolt-inv): discarded at
`true` once a mapping leaked, `false` at 1 while none did (`wdbCoreG`'s last clause); a leak records
that the file system can fail (session S3f: a remap's `munmap`, or `madvise` after its `mmap`, failed,
which the premises `FsNoErr` names exclude). -/
def junkRes (B : BNs) (j : Option (Loc × Nat)) : IProp GF :=
  match j with
  | some (jb, jl) => iprop((∃ vf, cellsR jb 0 jl vf) ∗ dghostVar B.nf DFrac.discard true ∗
      ⌜¬ FsNoErr⌝)
  | none => iprop(dghostVar B.nf (DFrac.own 1) false)

/-- **A mapping leaks** (a failed remap's `munmap`, or `madvise` after its `mmap`): the old junk
clause's flag set to `true` (or kept, if a mapping leaked before), the leaked mapping's cells. -/
theorem junkRes_leak (E : CoPset) (B : BNs) (jo : Option (Loc × Nat)) (jb : Loc) (jl : Nat)
    (hfs : ¬ FsNoErr) :
    junkRes (GF := GF) B jo ∗ (∃ vf, cellsR jb 0 jl vf) ⊢ |={E}=> junkRes B (some (jb, jl)) := by
  iintro ⟨Hj, Hc⟩
  rcases jo with _ | ⟨jb', jl'⟩
  · simp only [junkRes]
    imod dghostVar_update (GF := GF) true B.nf false $$ Hj with Hj
    imod dghostVar_persist (GF := GF) B.nf 1 true $$ Hj with #Hj
    imodintro
    iframe Hc Hj
    ipureintro; exact hfs
  · simp only [junkRes]
    icases Hj with ⟨-, #Hj, -⟩
    imodintro
    iframe Hc Hj
    ipureintro; exact hfs

/-- **The file given up** (`DB.Close`, which does not give it back): the junk clause's flag set to
`true`, discarded (kept, if a mapping leaked before); the leaked mapping's cells dropped. -/
theorem junkRes_shut (E : CoPset) (B : BNs) (jo : Option (Loc × Nat)) :
    junkRes (GF := GF) B jo ⊢ |={E}=> dghostVar B.nf DFrac.discard true := by
  iintro Hj
  rcases jo with _ | ⟨jb', jl'⟩
  · simp only [junkRes]
    imod dghostVar_update (GF := GF) true B.nf false $$ Hj with Hj
    imod dghostVar_persist (GF := GF) B.nf 1 true $$ Hj with #Hj
    imodintro; iexact Hj
  · simp only [junkRes]
    icases Hj with ⟨-, #Hj, -⟩
    imodintro; iexact Hj

/-- **A failed remap's outcome with the junk clause**: no leak (`P`), the old clause kept; a
leaked mapping `x` (its cells), the clause at the leak (`junkRes_leak`). Taken while the remap's
WP is open, before its failure path's steps (the ghost update needs a modality). -/
theorem junkRes_leak_or (E : CoPset) (B : BNs) (jo : Option (Loc × Nat)) (P : IProp GF) {X : Type}
    (Q : X → IProp GF) (jb : X → Loc) (jl : X → Nat) (hfs : ¬ FsNoErr) :
    junkRes (GF := GF) B jo ∗ (P ∨ ∃ x, Q x ∗ ∃ vf, cellsR (jb x) 0 (jl x) vf) ⊢
      |={E}=> (P ∗ junkRes B jo) ∨ ∃ x, Q x ∗ junkRes B (some (jb x, jl x)) := by
  iintro ⟨Hj, (HP | ⟨%x, HQ, Hc⟩)⟩
  · imodintro; ileft; iframe
  · imod junkRes_leak E B jo (jb x) (jl x) hfs $$ [Hj Hc] with Hj
    · iframe
    imodintro; iright; iexists x; iframe

/-- A leaked mapping's junk clause holds the file-given-up flag at `true`. -/
theorem junkRes_some_nf (B : BNs) (j : Option (Loc × Nat)) (jb : Loc) (jl : Nat)
    (hj : j = some (jb, jl)) :
    junkRes (GF := GF) B j ⊢ dghostVar B.nf DFrac.discard true := by
  subst hj
  simp only [junkRes]
  iintro ⟨-, #H, -⟩
  iexact H

/-- A leaked mapping's junk clause records that the file system can fail (session S3f). -/
theorem junkRes_some_fs (B : BNs) (j : Option (Loc × Nat)) (jb : Loc) (jl : Nat)
    (hj : j = some (jb, jl)) :
    junkRes (GF := GF) B j ⊢ ⌜¬ FsNoErr⌝ := by
  subst hj
  simp only [junkRes]
  iintro ⟨-, -, %h⟩
  ipureintro; exact h

/-- **The writer side after a failed remap**, from its pieces (batch 44.1: flagged, with the
writer's `fbTok`). -/
theorem wdbLost'_intro (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) (hok : wdbOK' fr w)
    (v0 : View) (F : GMap Nat (List w8)) (hF : fbRel w F) (m' : OsMeta)
    (j : Option (Loc × Nat)) (hsz : m'.size = w.m.size)
    (hmaps : m'.maps = ∅ ∨ ∃ jb jl, j = some (jb, jl) ∧ m'.maps = GMap.singleton jb jl) :
    ⊢ ghostVar (GF := GF) K.B.cur (1 : Qp).half.half w.C -∗ ghostVar K.B.fl (1 : Qp).half w.fl -∗
      ghostVar K.B.map (1 : Qp).half (none : MapSt) -∗ ghostVar K.B.out (1 : Qp).half false -∗
      ghostVar K.B.wv (1 : Qp).half ((some v, some (w.C.txid + 1), false, false) : WSt) -∗
      K.db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli -∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true -∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f -∗
      K.db.[DB, go!"rwtx"] ↦ tx -∗ K.db.[DB, go!"file"] ↦{DFrac.own (1 : Qp).half} w.f -∗
      dbPathLk K.db K.p w.fd -∗
      K.db.[DB, go!"datasz"] ↦ W64 0 -∗
      mapFields K.db (DFrac.own (1 : Qp).half.half) (none : MapSt) -∗
      bMeta K.p w.C [] m' -∗ fileOwn w.f w.fd K.p.path (DFrac.own (1 : Qp).half) -∗
      osFd w.fd (DFrac.own (1 : Qp).half) (dbFd K.p.ino) -∗
      metaOsBytes K.p (DFrac.own (1 : Qp).half) w.C -∗
      wBytesX K.p w.W (flxS w.C w.fl w.wb) w.wb w.m.size -∗
      junkRes K.B j -∗ flPgOwn w.fli w.fl -∗ sparePair K.B K.db K.sp -∗ receipt (w.C.txid - K.t0) -∗
      fbTok K.B w.C w.fl (wLive v0 w.C) F -∗
      wdbLost' fr K tx v (w.lost m' j) := by
  iintro Hcur Hfl Hmap Hout Hwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hmob Hwb Hj
    Hflo Hrd Hrc Htok
  ihave Htok := fbTok_ws K.B w.C w.fl (wLive v0 w.C) (some v, some (w.C.txid + 1), false, false) F
    rfl rfl $$ Htok
  unfold wdbLost' wdbLive wdbCoreG
  have hW : ∀ s ∈ (w.lost m' j).W, 4096 * s < (w.lost m' j).m.size → s ∈ w.W := by
    intro s hs hlt
    simp only [WDb.lost] at hs hlt
    obtain ⟨h1, h2, h3⟩ := (mem_wSlots _ _ _ s).1 hs
    exact (wdbOK'_mem_W fr w hok s).2 ⟨h1, Nat.lt_of_lt_of_le h2
      (Nat.div_le_div_right (Nat.le_max_right _ _)), h3⟩
  ihave Hwb := wBytesX_restrict K.p w.W (w.lost m' j).W _ w.wb w.m.size (wSlots_nodup _ _ _)
    (by simpa [WDb.lost, hsz] using hW) $$ Hwb
  isplitl [Hcur Hfl Hmap Hout Hwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hmob Hwb Hj
    Hflo Hrd Hrc]
  · simp only [WDb.lost, mapLen, metaCellsQ, wCells, hsz]
    iframe
    rcases j with _ | ⟨jb, jl⟩ <;> simp only [junkRes] <;> iexact Hj
  isplitr
  · ipureintro
    exact ⟨wdbOK'_lost fr w hok m' j hsz hmaps, rfl⟩
  iexists F
  isplitl [Htok]
  · simp only [WDb.lost]
    iexact Htok
  · ipureintro; exact fbRel_congr w _ F rfl rfl rfl hF

end lost

end bbolt
end EtcdGrove
end Perennial
