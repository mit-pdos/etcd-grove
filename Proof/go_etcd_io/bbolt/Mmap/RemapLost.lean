/-
The remap's end states (U4d, `notes/bbolt-proof-plan.md`; `Mmap/Remap`'s plan, steps 5-9): the
writer's records re-based (`wtxCore_rebase`, over `Mmap/Rebase`'s `wtxHeap_rebase`), and the
writer side after a failed remap (`wdbLost_intro`: no mapping, the `W` slots those of the file,
`wdbOK_lost`).
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

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

theorem View.with_base_self (v : View) : { v with base := v.base } = v := by cases v; rfl

/-- The writer side after a failed remap: no mapping, the file's `OsMeta` `m'` (its maps empty, or
the leaked mapping `j`), the `W` slots those inside the file. -/
def WDb.lost [GooseExts] (w : WDb) (m' : OsMeta) (j : Option (Loc × Nat)) : WDb :=
  { w with ms := none, m := m', W := wSlots (w.m.size / 4096) w.C w.fl, junk := j }

theorem wdbOK_lost [GooseExts] (w : WDb) (hok : wdbOK w) (m' : OsMeta) (j : Option (Loc × Nat))
    (hsz : m'.size = w.m.size)
    (hmaps : m'.maps = ∅ ∨ ∃ jb jl, j = some (jb, jl) ∧ m'.maps = GMap.singleton jb jl) :
    wdbOK (w.lost m' j) := by
  obtain ⟨_, _, hk3, _, hk5, hk6, hk7, hk8, _, _, hk11⟩ := hok
  refine ⟨?_, fun _ => hmaps, ?_, ?_, hk5, hk6, hk7, hk8, ?_, ?_, hk11⟩
  · intro b l h; simp [WDb.lost] at h
  · simp only [WDb.lost]; rw [hsz]; exact hk3
  · intro s
    simp only [WDb.lost, mapLen, hsz, Nat.zero_max]
    exact mem_W_of_wSlots _ _ _ s
  · intro b l h; simp [WDb.lost] at h
  · intro b l h; simp [WDb.lost] at h

section lost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's core re-based** on the new mapping `b` (after `dereference`'s coverage contract),
with its view registered at `b`. -/
theorem wtxCore_rebase (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (b : Loc)
    (hcov : derefOK X) :
    wtxCore (GF := GF) K tx r m X ∗ viewOf r { X.v with base := b } ⊢
      wtxCore K tx r m (X.rebase b) := by
  unfold wtxCore
  iintro ⟨⟨Hpkg, Hc, %Hp, Hreg, Hh, Hf, Hbk, Hnl, Hdb, -, Hst⟩, Hv⟩
  ihave Hh := wtxHeap_rebase tx (DFrac.own 1) X b hcov $$ Hh
  iframe
  ipureintro; exact Hp

/-- The junk mapping's cells. -/
def junkRes (j : Option (Loc × Nat)) : IProp GF :=
  match j with
  | some (jb, jl) => iprop(∃ vf, cellsR jb 0 jl vf)
  | none => iprop(emp)

/-- **The writer side after a failed remap**, from its pieces. -/
theorem wdbLost_intro (K : BC) (tx : Loc) (v : View) (w : WDb) (hok : wdbOK w) (m' : OsMeta)
    (j : Option (Loc × Nat)) (hsz : m'.size = w.m.size)
    (hmaps : m'.maps = ∅ ∨ ∃ jb jl, j = some (jb, jl) ∧ m'.maps = GMap.singleton jb jl)
    (wa : GoFunc) :
    ⊢ ghostVar (GF := GF) K.B.cur (1 : Qp).half.half w.C -∗ ghostVar K.B.fl (1 : Qp).half w.fl -∗
      ghostVar K.B.map (1 : Qp).half (none : MapSt) -∗ ghostVar K.B.out (1 : Qp).half false -∗
      ghostVar K.B.wv (1 : Qp).half ((some v, some (w.C.txid + 1), false, false) : WSt) -∗
      K.db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli -∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true -∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half} wa -∗
      K.db.[DB, go!"rwtx"] ↦ tx -∗ K.db.[DB, go!"file"] ↦ w.f -∗ K.db.[DB, go!"path"] ↦ K.p -∗
      K.db.[DB, go!"datasz"] ↦ W64 0 -∗
      mapFields K.db (DFrac.own (1 : Qp).half.half) (none : MapSt) -∗
      osMeta K.p (DFrac.own 1) (some m') -∗ fileOwn w.f w.fd K.p (DFrac.own 1) -∗
      osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ -∗
      metaOsBytes K.p (DFrac.own (1 : Qp).half) w.C -∗ wBytes K.p w.W w.wb w.m.size -∗
      junkRes j -∗ flPgOwn w.fli w.fl -∗ rdPair K.B K.db K.sp -∗ receipt (w.C.txid - K.t0) -∗
      wdbLost K tx v (w.lost m' j) := by
  iintro Hcur Hfl Hmap Hout Hwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hmob Hwb Hj
    Hflo Hrd Hrc
  unfold wdbLost wdbLive wdbCoreG
  have hW : ∀ s ∈ (w.lost m' j).W, 4096 * s < (w.lost m' j).m.size → s ∈ w.W := by
    intro s hs hlt
    simp only [WDb.lost] at hs hlt
    obtain ⟨h1, h2, h3⟩ := (mem_wSlots _ _ _ s).1 hs
    exact (wdbOK_mem_W w hok s).2 ⟨h1, Nat.lt_of_lt_of_le h2
      (Nat.div_le_div_right (Nat.le_max_right _ _)), h3⟩
  ihave Hwb := wBytes_restrict K.p w.W (w.lost m' j).W w.wb w.m.size (wSlots_nodup _ _ _)
    (by simpa [WDb.lost, hsz] using hW) $$ Hwb
  isplitl
  · simp only [WDb.lost, mapLen, metaCellsQ, wCells, hsz]
    iframe
    rcases j with _ | ⟨jb, jl⟩ <;> simp only [junkRes] <;> iexact Hj
  · ipureintro
    exact ⟨wdbOK_lost w hok m' j hsz hmaps, rfl⟩

end lost

end bbolt
end EtcdGrove
end Perennial
