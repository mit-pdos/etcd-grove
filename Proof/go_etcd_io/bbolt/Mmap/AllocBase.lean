/-
`DB.allocate`'s and `Tx.allocate`'s vocabulary and lemmas (U4c, `notes/bbolt-proof-plan.md`):
the buffer of a fresh page (`allocBuf`, `WX.addPage`'s), the writer's records with a new
high-water mark (`WX.withHwm`), the writer's transaction fields opened from `wtxW` and closed
over a new `WTx` with the same struct, buckets and dead objects (`wtxW_txFields_acc`), and the
writer side's facts kept by a freelist allocation (`wdbOK_alloc`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- The bytes of a fresh page `id` of `count` pages (`db.allocate`'s buffer, `WX.addPage`'s): its
header (`id`, flags and count 0, overflow `count - 1`) and zeros. -/
def allocBuf [GooseExts] (id : w64) (count : Nat) : List w8 :=
  encode (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) ++
    List.replicate (count * 4096 - 16) (W8 0)

section hwm
variable [GooseExts]

/-- The writer's records with the high-water mark `hwm` (`tx.meta.SetPgid(hwm)`). -/
def WX.withHwm (X : WX) (hwm : w64) : WX :=
  { X with t := { X.t with mv := { X.t.mv with pgid' := hwm } } }

theorem WX.withHwm_v (X : WX) (hwm : w64) : (X.withHwm hwm).v = X.v := rfl

/-- `WX.addPage` is a high-water mark, then the page cache's new entry. -/
theorem WX.addPage_eq (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64) :
    X.addPage id p count hwm = { X.withHwm hwm with t := { (X.withHwm hwm).t with
      pm := X.t.pm.insert id p, bufs := X.t.bufs.insert id (allocBuf id count) } } := rfl

end hwm

/-! ## The writer side's facts after an allocation -/

section pure
variable [GooseExts]

omit [GooseExts] in
/-- An allocation keeps the pending ids. -/
theorem pendSlots_alloc (fl : FLPg) (txid r : w64) (n : Nat) :
    pendSlots (fl.alloc txid r n) = pendSlots fl := rfl

/-- **`wdbOK` after a freelist allocation** (`FLPg.alloc`: free ids removed, `allocs` grown; the
pending ids and so the `W` slots unchanged). -/
theorem wdbOK_alloc (w : WDb) (txid r : w64) (n : Nat) (hok : wdbOK w) :
    wdbOK (w.withFl (w.fl.alloc txid r n)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, htx, hhwm, hmap, hsmall, hslots, hfree⟩ := hok
  refine ⟨h1, h2, h3, fun s => ?_, fun x hx => ?_, fun f hf => ?_, htx, hhwm, hmap, hsmall, hslots,
    fun x hx => hfree x (List.mem_filter.1 hx).1⟩
  · exact h4 s
  · exact h5 x ((List.mem_filter.1 hx).1)
  · have h := h6 f hf
    intro f' hf'
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h f' hf'
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, fun s a b => ?_, fun x hx => c10 x
      ((List.mem_filter.1 hx).1), fun x hx => c11 x hx, fun x hx => c12 x hx⟩
    obtain ⟨d1, d2⟩ := c9 s a b
    refine ⟨d1, fun hm => d2 ?_⟩
    simp only [FLPg.allIds, List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact .inl ((List.mem_filter.1 hm).1)
    · exact .inr hm

end pure

/-! ## The transaction's fields in `wtxW` -/

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's transaction fields** out of `wtxW`, back over a new `WTx` with the same struct,
buckets and dead objects (a new meta copy or page cache: `SetPgid`, `tx.pages[id] = p`). -/
theorem wtxW_txFields_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ txFields tx (DFrac.own 1) X ∗
      ∀ T : WTx, ⌜T.t = X.t.t ∧ T.bs = X.t.bs ∧ (T.dead, T.deadB) = (X.t.dead, X.t.deadB)⌝ -∗
        txFields tx (DFrac.own 1) { X with t := T } -∗ wtxW K tx r m { X with t := T } := by
  unfold wtxW wtxCore wtxHeap
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, ⟨%Hok, Hf, Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdbf,
    Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hf
  iintro %T %hT Hf
  obtain ⟨h1, h2, h3⟩ := hT
  have h3a : T.dead = X.t.dead := congrArg Prod.fst h3
  have h3b : T.deadB = X.t.deadB := congrArg Prod.snd h3
  have ho : T.objs = X.t.objs := by unfold WTx.objs; rw [h2, h3a]
  have hbo : T.bobjs = X.t.bobjs := by unfold WTx.bobjs; rw [h2, h3b]
  have hok' : heapOK (GF := GF) tx { X with t := T } := by
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := Hok
    refine ⟨k1, ?_, ?_, ?_, ?_, ?_⟩
    · unfold objsDisj at k2 ⊢; rw [h2]; exact k2
    · show ∀ bl B, T.bs !! bl = some B → _; rw [h2]; exact k3
    · show ∀ bl B n r, T.bs !! bl = some B → _; rw [h2]; exact k4
    · show ∀ n y, X.nloc !! n = some y → (T.objs !! n).isSome; rw [ho]; exact k5
    · show ∀ bl B, T.bs !! bl = some B → _; rw [h2]; exact k6
  simp only
  rw [ho, hbo, h1]
  iframe; iframe #
  ipureintro; exact ⟨Hr, hok'⟩

end acc

end bbolt
end EtcdGrove
end Perennial
