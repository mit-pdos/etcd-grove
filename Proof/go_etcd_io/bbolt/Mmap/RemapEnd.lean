/-
The remap's success state (U4d, `notes/bbolt-proof-plan.md`; `Mmap/Remap`'s plan, step 9): the
writer side on the new mapping `(b, L')` (`WDb.remap`: the `W` slots those below the new mapping or
the file, `wdbOK_remap`, `wdbRemap`), from its pieces (`wdbW_remap_intro`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.RemapLost
public import Proof.go_etcd_io.bbolt.Mmap.RemapGaps
public import Proof.go_etcd_io.bbolt.Mmap.RemapGather

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

/-- The writer side on the new mapping `(b, L')`, the file's `OsMeta` `m'`. -/
def WDb.remap [GooseExts] (w : WDb) (b : Loc) (L' : Nat) (m' : OsMeta) : WDb :=
  { w with ms := some (b, L'), m := m', W := wSlots (max L' w.m.size / 4096) w.C w.fl }

theorem wdbOK_remap [GooseExts] (w : WDb) (hok : wdbOK w) (b : Loc) (L' : Nat) (m' : OsMeta)
    (hsz : m'.size = w.m.size) (hmaps : m'.maps = GMap.singleton b L') (hfile : w.m.size ≤ L') :
    wdbOK (w.remap b L' m') := by
  obtain ⟨_, _, hk3, hk4, hk5, hk6, hk7, hk8, _, _, hk11, hk12, hk13, -, hk15⟩ := hok
  refine ⟨?_, ?_, ?_, ?_, hk5, hk6, hk7, hk8, ?_, ?_, hk11, hk12, ?_, ?_, ?_⟩
  · intro b' l' h
    simp only [WDb.remap, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hmaps
  · intro h; simp [WDb.remap] at h
  · simp only [WDb.remap]; rw [hsz]; exact hk3
  · intro s
    simp only [WDb.remap, mapLen, hsz]
    exact mem_W_of_wSlots _ _ _ s
  · intro b' l' h
    simp only [WDb.remap, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [WDb.remap]; omega
  · intro b' l' h _
    simp only [WDb.remap, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [WDb.remap]; omega
  · simp only [WDb.remap]; rw [hsz]; exact hk13
  · intro b' l' h
    simp only [WDb.remap, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    left; simp only [WDb.remap]; omega
  · intro s hs hle
    simp only [WDb.remap, hsz] at hs hle ⊢
    obtain ⟨a, b, c, d⟩ := (mem_W_of_wSlots _ _ _ s).1 hs
    refine hk15 s ((hk4 s).2 ⟨a, ?_, c, d⟩) hle
    have := Nat.le_max_right (mapLen w.ms) w.m.size
    have : s < w.m.size / 4096 := by omega
    omega

theorem wdbRemap_remap [GooseExts] (w : WDb) (hok : wdbOK w) (b : Loc) (L' : Nat) (m' : OsMeta)
    (hsz : m'.size = w.m.size) (hL : mapLen w.ms ≤ L') : wdbRemap w (w.remap b L' m') := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, hsz, fun s hs => ⟨?_, rfl⟩⟩
  obtain ⟨h1, h2, h3⟩ := (wdbOK_mem_W w hok s).1 hs
  refine (mem_wSlots _ _ _ s).2 ⟨h1, Nat.lt_of_lt_of_le h2 (Nat.div_le_div_right ?_), h3⟩
  omega

section remap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The new `W`'s slots inside the file are old `W` slots (gap 2 for a partial last page). -/
theorem remap_W_file (w : WDb) (hok : wdbOK w) (b0 : Loc) (L L' : Nat)
    (hms : w.ms = some (b0, L)) (hL : L ≤ L') (hal : L % 4096 = 0 ∨ L = 0xFFFFFFFFFFFF)
    (hL' : L' ≤ 0xFFFFFFFFFFFF) :
    ∀ s ∈ wSlots (max L' w.m.size / 4096) w.C w.fl, 4096 * s < w.m.size → s ∈ w.W := by
  intro s hs hlt
  obtain ⟨h1, h2, h3⟩ := (mem_wSlots _ _ _ s).1 hs
  refine (wdbOK_mem_W w hok s).2 ⟨h1, ?_, h3⟩
  rw [hms]; simp only [mapLen]
  by_cases hw : 4096 * (s + 1) ≤ w.m.size
  · exact Nat.lt_of_lt_of_le (by omega) (Nat.div_le_div_right (Nat.le_max_right _ _))
  · rcases wdbOK_size_page w hok b0 L hms with hle | hal'
    · have : 4096 * (s + 1) ≤ L := by
        rcases hal with hal | hal
        · omega
        · -- `L` is the cap: the new mapping is at most `L`, so `s`'s page is in it
          have : 4096 * (s + 1) ≤ max L' w.m.size := by omega
          omega
      exact Nat.lt_of_lt_of_le (by omega) (Nat.div_le_div_right (Nat.le_max_left _ _))
    · omega

/-- **The writer side on the new mapping**, from its pieces. -/
theorem wdbW_remap_intro (K : BC) (tx : Loc) (v : View) (w : WDb) (hok : wdbOK w) (b : Loc)
    (L' : Nat) (m' : OsMeta) (hsz : m'.size = w.m.size) (hmaps : m'.maps = GMap.singleton b L')
    (hfile : w.m.size ≤ L') (hsub : ∀ s ∈ (w.remap b L' m').W, 4096 * s < w.m.size → s ∈ w.W)
    (hv : v = View.ofC b w.C) :
    ⊢ ghostVar (GF := GF) K.B.cur (1 : Qp).half.half w.C -∗ ghostVar K.B.fl (1 : Qp).half w.fl -∗
      ghostVar K.B.map (1 : Qp).half (some (b, L') : MapSt) -∗ ghostVar K.B.out (1 : Qp).half false -∗
      ghostVar K.B.wv (1 : Qp).half (wLive v w.C) -∗
      K.db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli -∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true -∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f -∗
      K.db.[DB, go!"rwtx"] ↦ tx -∗ K.db.[DB, go!"file"] ↦ w.f -∗ K.db.[DB, go!"path"] ↦ K.p -∗
      K.db.[DB, go!"datasz"] ↦ W64 (L' : Int) -∗
      mapFields K.db (DFrac.own (1 : Qp).half.half) (some (b, L') : MapSt) -∗
      osMeta K.p (DFrac.own 1) (some m') -∗ fileOwn w.f w.fd K.p (DFrac.own 1) -∗
      osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ -∗
      metaCellsQ (1 : Qp).half.half (some (b, L')) w.C -∗
      metaOsBytes K.p (DFrac.own (1 : Qp).half) w.C -∗
      wCells (some (b, L')) (w.remap b L' m').W -∗ wBytes K.p w.W w.wb w.m.size -∗
      junkRes w.junk -∗ flPgOwn w.fli w.fl -∗ rdPair K.B K.db K.sp -∗ receipt (w.C.txid - K.t0) -∗
      wdbW K tx v (w.remap b L' m') := by
  iintro Hcur Hfl Hmap Hout Hwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hmc Hmob Hwc
    Hwb Hj Hflo Hrd Hrc
  unfold wdbW wdbLive wdbCoreG
  ihave Hwb := wBytes_restrict K.p w.W (w.remap b L' m').W w.wb w.m.size (wSlots_nodup _ _ _)
    hsub $$ Hwb
  isplitl
  · simp only [WDb.remap, mapLen, hsz]
    iframe
    rcases hj : w.junk with _ | ⟨jb, jl⟩ <;> simp only [junkRes, hj] <;> iexact Hj
  · ipureintro
    refine ⟨wdbOK_remap w hok b L' m' hsz hmaps hfile, ?_, ?_⟩
    · subst hv; rfl
    · subst hv; rfl

/-- **The remap's success state** (step 9), from its pieces: `Pm 1` back, the writer's records
re-based on the new mapping (`wtxCore_rebase`, its view registered there: gap 3), the writer side
remapped. -/
theorem remap_post (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X Xd : WX) (w : WDb)
    (hok : wdbOK w) (b0 base : Loc) (l L' : Nat) (m2 : OsMeta) (hcov : derefOK Xd)
    (hXd : Xd.v = X.v) (hv : X.v = View.ofC X.v.base w.C) (hrdb : r.db = K.db)
    (hms : w.ms = some (b0, l)) (hll : l ≤ L') (hal : l % 4096 = 0 ∨ l = 0xFFFFFFFFFFFF)
    (hL'max : L' ≤ 0xFFFFFFFFFFFF) (hsz : m2.size = w.m.size)
    (hmaps : m2.maps = GMap.singleton base L') (hfile : w.m.size ≤ L')
    (hpb : ∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l) :
    ⊢ wtxCore (GF := GF) K tx r m Xd -∗ viewCells wq { X.v with base := base } -∗
      mapFields K.db (DFrac.own 1) (some (base, L') : MapSt) -∗
      ghostVar K.B.map (1 : Qp).half.half (some (base, L') : MapSt) -∗ ghostVar K.B.mtok 1 () -∗
      ghostVar K.B.cur (1 : Qp).half.half w.C -∗ ghostVar K.B.fl (1 : Qp).half w.fl -∗
      ghostVar K.B.map (1 : Qp).half (some (base, L') : MapSt) -∗
      ghostVar K.B.out (1 : Qp).half false -∗
      ghostVar K.B.wv (1 : Qp).half
        ((some { X.v with base := base }, some (w.C.txid + 1), false, true) : WSt) -∗
      K.db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli -∗
      K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true -∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f -∗
      K.db.[DB, go!"rwtx"] ↦ tx -∗ K.db.[DB, go!"file"] ↦ w.f -∗ K.db.[DB, go!"path"] ↦ K.p -∗
      K.db.[DB, go!"datasz"] ↦ W64 (L' : Int) -∗
      osMeta K.p (DFrac.own 1) (some m2) -∗ fileOwn w.f w.fd K.p (DFrac.own 1) -∗
      osFd w.fd (DFrac.own 1) ⟨K.p, true, true⟩ -∗
      metaCellsQ (1 : Qp).half.half (some (base, L')) w.C -∗
      metaOsBytes K.p (DFrac.own (1 : Qp).half) w.C -∗
      wCells (some (base, L')) (wSlots (max L' w.m.size / 4096) w.C w.fl) -∗
      wBytes K.p w.W w.wb w.m.size -∗
      junkRes w.junk -∗ flPgOwn w.fli w.fl -∗ rdPair K.B K.db K.sp -∗ receipt (w.C.txid - K.t0) -∗
      |={⊤}=> Pm K.B K.db 1 ∗ wtxW K tx r m (Xd.rebase base) ∗
        wdbW K tx (Xd.rebase base).v (w.remap base L' m2) := by
  iintro Hwc Hvc Hmf Hpmap Hptok Hcur Hfl Hmap Hout Hwv Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hosm
    Hfo Hfd Hmc Hmob Hwc' Hwb Hj Hflo Hrd Hrc
  icases (mapFields_join K.db (some (base, L') : MapSt)).2 $$ Hmf with ⟨Hm1, Hm2, Hm3⟩
  ihave Hwc := wtxCore_viewOf_rebase K tx r m Xd base ⊤ $$ Hwc
  imod Hwc with ⟨Hwc, Hvo⟩
  ihave Hwc := wtxCore_rebase K tx r m Xd base hcov $$ [Hwc Hvo]
  · iframe
  have hv' : (Xd.rebase base).v = { X.v with base := base } := by
    show { Xd.v with base := base } = _; rw [hXd]
  have hvc : (Xd.rebase base).v = View.ofC base w.C := by
    rw [hv', hv]; rfl
  ihave Hwd := wdbW_remap_intro K tx (Xd.rebase base).v w hok base L' m2 hsz hmaps hfile
    (remap_W_file w hok b0 l L' hms hll hal hL'max) hvc
    $$ Hcur Hfl Hmap Hout [Hwv] Hfli Hopen Hwa Hrw Hfile Hpath Hdsz Hm2 Hosm Hfo Hfd Hmc Hmob [Hwc']
      Hwb Hj Hflo Hrd Hrc
  · simp only [wLive]; rw [hv']; iexact Hwv
  · simp only [WDb.remap]; iexact Hwc'
  imodintro
  isplitl [Hpmap Hm3 Hptok]
  · unfold Pm; iexists (some (base, L')); iframe
  iframe Hwd
  unfold wtxW
  iframe Hwc
  rw [hv']
  iframe Hvc
  iexists L'
  rw [hrdb]
  iframe Hm1
  ipureintro
  intro id pg h
  have := hpb id pg h
  omega

end remap

end bbolt
end EtcdGrove
end Perennial
