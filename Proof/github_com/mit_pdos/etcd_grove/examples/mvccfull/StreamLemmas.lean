/-
Lemmas about the stream vocabulary (`Streams.lean`) the stream proofs share. Lean-first (no Rocq
counterpart).

- `maxK_attained'`: `Streams.lean`'s `maxK_attained` (the registry's largest `k`, attained),
  proved (through the registry's list of entries).
- `watcherOk_stamp`: marking a watcher stamped keeps `watcherOk` when its `k` is at most the
  responses received (`recvOne`'s default branch, after `stamp_ok`).
- `regs_sentLb`: the poll's bound out of the lock's watchers: some `n` at least every
  registration's `k`, with `wsSentLb ws n` (`wsSentLb_zero.law` for an empty registry).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- The largest `k` of a list of entries, attained (or `0`). -/
theorem maxK_list (L : List (w64 × Reg)) :
    ∃ n, (∀ p ∈ L, p.2.k ≤ n) ∧ (n = 0 ∨ ∃ p ∈ L, p.2.k = n) := by
  induction L with
  | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil, Or.inl rfl⟩
  | cons a L ih =>
    obtain ⟨n, h1, h2⟩ := ih
    by_cases h : a.2.k ≤ n
    · refine ⟨n, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact h
        · exact h1 p hp
      · rcases h2 with h2 | ⟨p, hp, hpk⟩
        · exact Or.inl h2
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hpk⟩
    · refine ⟨a.2.k, ?_, Or.inr ⟨a, List.mem_cons_self, rfl⟩⟩
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact Nat.le_refl _
      · have := h1 p hp; omega

/-- `maxK_attained` (`Streams.lean`, `sorry` there), proved. -/
theorem maxK_attained' (W : GMap w64 Reg) :
    ∃ n, (∀ id x, W !! id = some x → x.k ≤ n) ∧
      (n = 0 ∨ ∃ id x, W !! id = some x ∧ x.k = n) := by
  obtain ⟨n, h1, h2⟩ := maxK_list W.toList
  refine ⟨n, fun id x hx => h1 (id, x) ((GMap.mem_toList W id x).2 hx), ?_⟩
  rcases h2 with h2 | ⟨p, hp, hpk⟩
  · exact Or.inl h2
  · exact Or.inr ⟨p.1, p.2, (GMap.mem_toList W p.1 p.2).1 hp, hpk⟩

/-- **Stamping a watcher** keeps `watcherOk` once its registration's `k` is received. -/
theorem watcherOk_stamp (Hl : List HRev) (rs : List WResp) (id : w64) (x : Reg) (wv : watcher)
    (h : watcherOk Hl rs id x wv) (hk : x.k ≤ rs.length) :
    watcherOk Hl rs id x { wv with stamped' := true } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun _ => hk, h13, h14⟩

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The poll's bound** (`recvOne`): out of the lock's watchers, some `n` at least every
registration's `k`, with `wsSentLb ws n` (the largest registration's, or `wsSentLb_zero.law`'s). -/
theorem regs_sentLb (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hzero : mvcc.api.wsSentLb_zero.law (GF := GF) (hG := hG))
    (Hl : List HRev) (rs : List WResp) (ws : WsName) (W : GMap w64 Reg) :
    ([∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hl rs ws id x) ⊢
      ([∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hl rs ws id x) ∗
        ∃ n, wsSentLb ws n ∗ ⌜∀ id x, W !! id = some x → x.k ≤ n⌝ := by
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  obtain ⟨n, hn, hat⟩ := maxK_attained' W
  iintro H
  rcases hat with rfl | ⟨id, x, hx, rfl⟩
  · iframe H
    iexists 0
    isplitl []
    · iapply hzero
    · ipureintro; exact hn
  · icases (BigSepM.bigSepM_lookup_acc
      (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs ws id x) (m := W) hx)
      $$ H with ⟨Hi, Hrest⟩
    iunfold watcherOwn' at Hi
    icases Hi with ⟨%wv, Hp, #Hk, #He, #Hlb, %Hok⟩
    isplitl [Hp Hrest]
    · iapply Hrest
      iunfold watcherOwn'
      iexists wv
      iframe
      iframe #
      ipureintro; exact Hok
    · iexists x.k
      iframe #
      ipureintro; exact hn

end defs

end mvccfull
end EtcdGrove
end Perennial
