/-
`Commit`'s tail accessors (U10k of `notes/bbolt-proof-plan.md`): what `tx.write()` and
`tx.writeMeta()` take out of the writer's working state `wtxW` (`tx.pages` with its buffers, the
statistics token, `tx.db`) and of its database side `wdbLive` (the file, the `W` slots' cells and
bytes), and what they give back (`WX.clearPages`: `tx.pages` a fresh empty map; the writer side
with a new `OsMeta`, `W` list and slot bytes).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WSlots
public import Proof.go_etcd_io.bbolt.Commit.AssembleAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The records after `tx.write()`: `tx.pages` the fresh empty map `pml`, no buffers. -/
def WX.clearPages (X : WX) (pml : Loc) : WX :=
  { X with t := { X.t with t := { X.t.t with pages' := pml }, pm := ∅, bufs := ∅ } }

@[simp] theorem WX.clearPages_v (X : WX) (pml : Loc) : (X.clearPages pml).v = X.v := rfl
@[simp] theorem WX.clearPages_rl (X : WX) (pml : Loc) : (X.clearPages pml).rl = X.rl := rfl
@[simp] theorem WX.clearPages_bs (X : WX) (pml : Loc) : (X.clearPages pml).t.bs = X.t.bs := rfl
@[simp] theorem WX.clearPages_mv (X : WX) (pml : Loc) : (X.clearPages pml).t.mv = X.t.mv := rfl
@[simp] theorem WX.clearPages_meta (X : WX) (pml : Loc) :
    (X.clearPages pml).t.t.meta' = X.t.t.meta' := rfl
@[simp] theorem WX.clearPages_writable (X : WX) (pml : Loc) :
    (X.clearPages pml).t.t.writable' = X.t.t.writable' := rfl
@[simp] theorem WX.clearPages_ch (X : WX) (pml : Loc) :
    (X.clearPages pml).t.t.commitHandlers' = X.t.t.commitHandlers' := rfl
@[simp] theorem WX.clearPages_withMv (X : WX) (pml : Loc) (mv : Meta) :
    (X.clearPages pml).withMv mv = (X.withMv mv).clearPages pml := rfl

/-- The writer side with the file's `OsMeta` `m`, the `W` slots `W` and their bytes `wb`. -/
def WDb.reslot (w : WDb) (m : OsMeta) (W : List Nat) (wb : Nat → List w8) : WDb :=
  { w with m := m, W := W, wb := wb }

proj_simps WDb.reslot

/-- The writer side re-slotted with its own values is itself. -/
theorem WDb.reslot_self (w : WDb) : w.reslot w.m w.W w.wb = w := rfl

/-- **`wdbOK` with the `W` slots re-listed and re-written**: the same slots, the file's mappings
kept, its size grown at most to the mapping's end (a write past the end, `Tx.write_ext`), the
slots inside the file whole pages, the synced freelist page's bytes kept. -/
theorem wdbOK_reslot (w : WDb) (m : OsMeta) (W : List Nat) (wb : Nat → List w8) (hok : wdbOK w)
    (hW : ∀ s, s ∈ W ↔ s ∈ w.W) (hsz1 : w.m.size ≤ m.size)
    (hsz2 : m.size ≤ max w.m.size (mapLen w.ms)) (hsz63 : m.size < 2 ^ 63)
    (hmaps : m.maps = w.m.maps)
    (hwb : ∀ s ∈ w.W, 4096 * (s + 1) ≤ m.size → (wb s).length = 4096)
    (hfl : ∀ f, w.C.flpg = some f → extentBytes wb f = extentBytes w.wb f) :
    wdbOK (w.reslot m W wb) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hok
  have hmax : max (mapLen w.ms) m.size = max (mapLen w.ms) w.m.size := by omega
  simp only [wdbOK, WDb.reslot]
  refine ⟨fun b l e => by rw [hmaps]; exact h1 b l e, fun e => by rw [hmaps]; exact h2 e,
    by omega, fun s => by rw [hW, hmax]; exact h4 s, h5,
    fun f hf => by rw [hfl f hf]; exact h6 f hf, h7, h8, h9,
    fun b l e hl => ?_, h11, h12, hsz63, fun b l e => ?_, fun s hs hz => hwb s ((hW s).1 hs) hz⟩
  · have := h10 b l e hl
    rw [e] at hsz2; simp only [mapLen] at hsz2
    omega
  · rw [e] at hsz2; simp only [mapLen] at hsz2
    rcases Nat.lt_or_ge w.m.size m.size with h | h
    · left; omega
    · have : m.size = w.m.size := by omega
      rw [this]; exact h14 b l e

end pure

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`tx.write()`'s part of the working state**: the core, the registration, the statistics
token, `tx.db`, `tx.pages` with its map and buffers out of `wtxW`; back with `tx.pages` any
empty map (`WX.clearPages`). -/
theorem cm_write_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ reg tx K.B r ∗ statsTok r m 1 ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ tx.[Tx, go!"pages"] ↦ X.t.t.pages' ∗
      X.t.t.pages' ↦$ X.t.pm ∗
      ([∗map] id ↦ pl ∈ X.t.pm, ∃ bs, ⌜X.t.bufs !! id = some bs⌝ ∗
        bytesPointsto pl (DFrac.own 1) bs) ∗
      (∀ pml : Loc, statsTok r m 1 -∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗
        tx.[Tx, go!"pages"] ↦ pml -∗ pml ↦$ (∅ : GMap w64 Loc) -∗ wtxW K tx r m (X.clearPages pml)) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨#Hpkg, #Hcore, %Hc, #Hreg, ⟨%Hh, ⟨Hwr, Hmg, Hme, Hpg, Hch, Hwf, Hmv, Hpm, Hbufs⟩,
    Hrf, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hvc, Hmap⟩
  have hdb : r.db = K.db := Hc.1
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db $$ [Hdb]
  · rw [← hdb]; iexact Hdb
  iframe Hcore Hreg Hst Hdb Hpg Hpm Hbufs
  iintro %pml Hst Hdb Hpg Hpm
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db $$ [Hdb]
  · rw [hdb]; iexact Hdb
  simp only [WX.clearPages]
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hc
  isplitr
  · ipureintro; exact Hh
  iapply BigSepM.bigSepM_empty.2
  iempintro

/-- **The writer side's file and `W` slots** out of `wdbLive`: `db.file`, `db.ops.writeAt`'s half,
the file, its fd and its `OsMeta`, the `W` slots' cells and bytes; back with any `OsMeta`, `W`
list and bytes (`WDb.reslot`). -/
theorem cm_file_acc (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (ws : WSt)
    (w : WDb) :
    wdbLive (GF := GF) B db p sp t0 tx ws w ⊢
      db.[DB, go!"file"] ↦ w.f ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f ∗
      fileOwn w.f w.fd p (DFrac.own 1) ∗ osFd w.fd (DFrac.own 1) ⟨p, true, true⟩ ∗
      osMeta p (DFrac.own 1) (some w.m) ∗ wCells w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗
      (∀ (m : OsMeta) (W : List Nat) (wb : Nat → List w8),
        db.[DB, go!"file"] ↦ w.f -∗
        (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half}
          methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #w.f -∗
        fileOwn w.f w.fd p (DFrac.own 1) -∗ osFd w.fd (DFrac.own 1) ⟨p, true, true⟩ -∗
        osMeta p (DFrac.own 1) (some m) -∗ wCells w.ms W -∗ wBytes p W wb m.size -∗
        wdbLive B db p sp t0 tx ws (w.reslot m W wb)) := by
  unfold wdbLive wdbCoreG
  iintro ⟨⟨Hcur, Hfl, Hmap, Hout, Hwv, Hfli, Hopn, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf, Hom, Hfo, Hfd,
    Hmc, Hmb, Hwc, Hwb, Hjk⟩, Hflo, Hsp, Hrc⟩
  iframe Hfile Hwa Hfo Hfd Hom Hwc Hwb
  iintro %m %W %wb Hfile Hwa Hfo Hfd Hom Hwc Hwb
  simp only [WDb.reslot]
  iframe

/-- The writer side's mapping is at most `maxMapSize` long. -/
theorem cm_wdbLive_mapLen (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc)
    (ws : WSt) (w : WDb) :
    wdbLive (GF := GF) B db p sp t0 tx ws w ⊢ ⌜mapLen w.ms ≤ 0xFFFFFFFFFFFF⌝ := by
  unfold wdbLive wdbCoreG
  iintro ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, Hmf, -⟩, -⟩
  iapply cm_mapFields_len db _ w.ms $$ Hmf

end acc

end bbolt
end EtcdGrove
end Perennial
