/-
An allocation from the freelist (`db.allocate` when `Allocate` finds a run): the run's ids
were free, so no view covers them (MVCC: a slot a view covers is not free), and allocating them
(`FLState.allocate`: off the free list, recorded as allocated by the writer) keeps the
database's facts (`dbOK_allocate`); they are below the high-water mark (`flBelow`).
-/
module

public import Proof.go_etcd_io.bbolt.DBRemap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- A page covers its own slot. -/
theorem covers_self (pages : GMap Nat (List w8)) (id : Nat) (pg : List w8)
    (h : pages !! id = some pg) : coversSlot pages id := by
  unfold coversSlot; exact ⟨id, pg, h, by omega, by omega⟩

/-- The run's first id is in it. -/
theorem inRun_self (r : w64) (n : Nat) (hn : 0 < n) : inRun r n r := by
  unfold inRun; omega

/-- Pages covering no free slot keep their allocations' bound when free ids are allocated. -/
theorem allocs_allocate (fl : FLState) (txid r : w64) (n : Nat) (hn : 0 < n)
    (hcan : fl.canAllocate r n) (pages : GMap Nat (List w8)) (T : w64)
    (hnf : ∀ s, coversSlot pages s → W64 s ∉ fl.free)
    (ha : ∀ id pg, pages !! id = some pg → ∀ a, fl.allocs !! W64 id = some a →
      uint.Z a ≤ uint.Z T) :
    ∀ id pg, pages !! id = some pg → ∀ a, (fl.allocate txid r n).allocs !! W64 id = some a →
      uint.Z a ≤ uint.Z T := by
  intro id pg hid a hal
  by_cases he : r = W64 id
  · exact absurd (he ▸ hcan.2 r (inRun_self r n hn)) (hnf id (covers_self pages id pg hid))
  · unfold FLState.allocate at hal
    simp only at hal
    rw [GMap.lookup_insert_ne _ _ he] at hal
    exact ha id pg hid a hal

/-- Allocated ids are off the free list. -/
theorem free_allocate (fl : FLState) (txid r : w64) (n : Nat) (x : w64)
    (h : x ∈ (fl.allocate txid r n).free) : x ∈ fl.free := by
  unfold FLState.allocate at h
  simp only [List.mem_filter] at h
  exact h.1

/-- An MVCC view keeps the rule when free ids are allocated. -/
theorem mvccView_allocate (σ : DBState) (txid r : w64) (n : Nat) (hn : 0 < n)
    (hcan : σ.fl.canAllocate r n) (T : w64) (pages : GMap Nat (List w8))
    (h : mvccView σ T pages) :
    mvccView { σ with fl := σ.fl.allocate txid r n } T pages := by
  obtain ⟨ha, hc⟩ := h
  refine ⟨allocs_allocate σ.fl txid r n hn hcan pages T (fun s hs => (hc s hs).2.1) ha,
    fun s hs => ?_⟩
  obtain ⟨h2, h3, h4⟩ := hc s hs
  exact ⟨h2, fun hf => h3 (free_allocate σ.fl txid r n _ hf), h4⟩

/-- Allocating a run of free ids keeps the database's facts. -/
theorem dbOK_allocate (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (txid r : w64) (n : Nat) (hn : 0 < n) (hcan : σ.fl.canAllocate r n) :
    dbOK { σ with fl := σ.fl.allocate txid r n } v0 v1 := by
  obtain ⟨hps, hps2, hns, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow⟩ := hcur
  obtain ⟨b1, b2, b3, b4⟩ := cbelow
  refine ⟨hps, hps2, hns, hsz, hdc, hm0, hm1, hv,
    ⟨cwf, cdisj, cin,
      allocs_allocate σ.fl txid r n hn hcan _ _ (fun s hs => (cfree s hs).2.1) calloc,
      fun s hs => ⟨(cfree s hs).1, fun hf => (cfree s hs).2.1 (free_allocate σ.fl txid r n _ hf),
        (cfree s hs).2.2⟩,
      ⟨fun x hx => b1 x (free_allocate σ.fl txid r n x hx), b2, b3, b4⟩⟩,
    hrd, fun k rd hk => mvccView_allocate σ txid r n hn hcan _ _ (hmv k rd hk), hsl, hfl, hro, hrs,
    ⟨hwr.1, fun w hw => ⟨(hwr.2 w hw).1,
      mvccView_allocate σ txid r n hn hcan _ _ (hwr.2 w hw).2⟩⟩⟩

/-- The writer's view covers none of a run of free ids. -/
theorem alloc_not_covered (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (r : w64) (n : Nat) (hcan : σ.fl.canAllocate r n) :
    ∀ k < n, ¬ coversSlot w.pages (uint.nat r + k) := by
  intro k hk hc
  have hmv := (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 w hw).2
  apply (hmv.2 _ hc).2.1
  apply hcan.2
  have hr := hcan.1
  unfold inRun
  constructor <;> word

/-- A run of free ids is below the current high-water mark, which is the writer's view's. -/
theorem alloc_below (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (r : w64) (n : Nat) (hn : 0 < n)
    (hcan : σ.fl.canAllocate r n) : uint.Z r + n ≤ w.hwm := by
  obtain ⟨b1, -, -, b4⟩ := h.2.2.2.2.2.2.2.2.1.2.2.2.2.2
  rw [b4 w hw]
  have := hcan.1
  have hz : uint.Z (r + W64 ((n - 1 : Nat) : Int)) = uint.Z r + (n - 1 : Nat) := by word
  have hlast := b1 _ (hcan.2 (r + W64 ((n - 1 : Nat) : Int)) (by unfold inRun; omega))
  have : (uint.nat (if metaPick v0 v1 = true then v1 else v0).pgid' : Int) =
      uint.Z (if metaPick v0 v1 = true then v1 else v0).pgid' := by word
  omega

/-- The writer's view covers no slot at its high-water mark or above. -/
theorem writer_not_covered_above (σ : DBState) (v0 v1 : internal.common.Meta)
    (h : dbOK σ v0 v1) (w : Reader) (hw : σ.wr = some w) (s : Nat) (hs : w.hwm ≤ s) :
    ¬ coversSlot w.pages s := by
  intro hc
  have hro := writer_readerOK σ v0 v1 h w hw
  have hps16 : 16 ≤ σ.ps := by have := h.1; omega
  obtain ⟨id, pg, hid, h1, h2⟩ := hc
  have hin := hro.2.2 id pg hid
  have hspan := span_of_pageAt σ.bs σ.ps id pg hps16 hin.1.symm
  omega

end alloc

end bbolt
end EtcdGrove
end Perennial
