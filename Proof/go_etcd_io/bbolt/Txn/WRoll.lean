/-
A writer's `Rollback` on the writer side (U5 of `notes/bbolt-proof-plan.md`): what the store says of
the live writer's freelist (`store_wfacts`: `flBelow`'s writer clause, the pending slots inside the
mapping), and the writer side after `freelist.Rollback` (`wdb_rollback`: the slots leaving the
store join the `W` slots).
-/
module

public import Proof.go_etcd_io.bbolt.Txn.Txs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wroll
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit go_gctx sem in
private theorem pagesInv_timeless_w (B : BNs) (p : GoString) : Timeless (pagesInv (GF := GF) B p) := by
  have h1 : ∀ σ : StoreSt, Timeless (storeCells (GF := GF) σ) := by
    intro σ; unfold storeCells; split <;> infer_instance
  have h2 : ∀ σ : StoreSt, Timeless (metaLend (GF := GF) B σ) := by
    intro σ; unfold metaLend metaCellsQ; split <;> infer_instance
  have h4 : ∀ σ W, Timeless (bytesWit (GF := GF) B σ W) := by
    intro σ W; unfold bytesWit; split <;> infer_instance
  have h3 : ∀ s bs, Timeless (osSlot (GF := GF) p s bs) := by
    intro s bs
    have : ∀ off dq xs, Timeless (osBytes (GF := GF) p off dq xs) := fun _ _ _ => by
      unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
    unfold osSlot; infer_instance
  unfold pagesInv
  infer_instance

/-- **No writer's own allocation is in its pending entry** (`freelist.Rollback`'s premise), from
`flBelow`'s writer clause. -/
theorem flBelow_rollback_pre (fl : FLPg) (C : CommitSt) (hb : flBelow fl C (some (C.txid + 1)))
    (h64 : C.txid + 1 < 2 ^ 64) :
    ∀ pd, fl.pending !! W64 ((C.txid + 1 : Nat) : Int) = some pd →
      W64 ((C.txid + 1 : Nat) : Int) ∉ pd.alloctx := by
  intro pd hpd hin
  have ht : (W64 ((C.txid + 1 : Nat) : Int)).toNat = C.txid + 1 := by
    simp; omega
  rcases hb.2.2.1 _ pd hpd with h | ⟨-, h⟩
  · omega
  · have := h _ hin; omega

/-- `Rollback(txid)` leaves no pending entry for `txid`. -/
theorem FLPg.rollback_pending_none (fl : FLPg) (txid : w64) :
    (fl.rollback txid).pending !! txid = none := by
  unfold FLPg.rollback
  split
  · assumption
  · unfold FLPg.rollbackEntry; simp

section store
variable (B : BNs) (N : Namespace) (p : GoString) (E : CoPset) (hE : ↑(pagesN N) ⊆ E)
include hE

omit sem in
/-- **What the store says of the writer's freelist**: `flBelow` with the writer's txid, and the
pending slots inside the mapping. -/
theorem store_wfacts (C : CommitSt) (fl : FLPg) (ms : MapSt) (ws : WSt) :
    inv (pagesN N) (pagesInv (GF := GF) B p) ∗ ghostVar B.cur (1 : Qp).half.half C ∗
      ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ⊢
    |={E}=> ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.fl (1 : Qp).half fl ∗
      ghostVar B.map (1 : Qp).half ms ∗ ghostVar B.wv (1 : Qp).half ws ∗
      ⌜flBelow fl C ws.2.1 ∧ ∀ b l, ms = some (b, l) → ∀ s ∈ pendSlots fl, 2 ≤ s ∧ s < l / 4096⌝ := by
  iintro ⟨#Hinv, Hcur, Hfl, Hmap, Hwv⟩
  have := pagesInv_timeless_w (GF := GF) B p
  imod inv_acc hE $$ Hinv with ⟨>Hi, Hclose⟩
  unfold pagesInv
  icases Hi with ⟨%σ, %W, Hcur', Hfl', Hmap', Hwv', Hrds, Hdep, Hcells, Hos, Hbw, Hml, %Hok⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  icombine Hfl Hfl' gives % ⟨_, hfl⟩
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  icombine Hwv Hwv' gives % ⟨_, hws⟩
  imod Hclose $$ [Hcur' Hfl' Hmap' Hwv' Hrds Hdep Hcells Hos Hbw Hml] with -
  · inext; iexists σ, W; iframe; ipureintro; exact Hok
  imodintro
  iframe
  ipureintro
  subst hC hfl hms hws
  refine ⟨Hok.2.2.1, fun b l hbl s hs => ?_⟩
  have hs' : s ∈ storeSlots σ := by
    unfold storeSlots
    rw [Perennial.mem_list_dedup, List.mem_append]
    exact Or.inr hs
  exact ⟨(Hok.2.2.2.2.2.2.2.2.2.2.2.1 s hs').1, Hok.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hbl s hs'⟩

end store

/-- **The writer side after `freelist.Rollback`** (by the live writer, before its publish): the
freelist rolled back, the slots leaving the store (`store_rollback`'s `S`, B3: a freed old synced
freelist page) joining the `W` slots with their cells and page-cache bytes (`slotsOwn`), the rest
unchanged; `wdbOK` kept. (Not yet proved: the `W` clause's membership, `wBytes`' cases for the new
slots against the file's size, and `flCurOK` of the rolled-back freelist.) -/
theorem wdb_rollback (p : GoString) (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8)
    (hok : wdbOK w) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (hpend : ∀ b l, w.ms = some (b, l) → ∀ s ∈ pendSlots w.fl, 2 ≤ s ∧ s < l / 4096) :
    wCells (GF := GF) w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗ slotsOwn w.ms p S bs ⊢
      ∃ w' : WDb, ⌜w'.C = w.C ∧ w'.fl = fl' ∧ w'.ms = w.ms ∧ w'.m = w.m ∧ w'.fli = w.fli ∧
          w'.junk = w.junk ∧ w'.f = w.f ∧ w'.fd = w.fd ∧ wdbOK w'⌝ ∗
        wCells w'.ms w'.W ∗ wBytes p w'.W w'.wb w'.m.size := by
  sorry

end wroll

end bbolt
end EtcdGrove
end Perennial
