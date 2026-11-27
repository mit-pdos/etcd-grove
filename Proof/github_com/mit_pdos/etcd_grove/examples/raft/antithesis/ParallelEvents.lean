/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **the reports of a `-parallel`
leader's `Ready`** (`node.parallel`):
- `eventOwn_setW`: Go's `ev.Has |= check.FW; ev.W = x` on a report being built;
- `stateEv_mem`: Go's `mem` report (`withByRole(stateEv("mem", hs, ents), by, role)` with `W`), recorded
  at the node, is the Sim's `evMem`; `stateEv_write`: the `write` report is `evWrite`;
- their numbers, weights and entries' sizes (`evMem_numsOk`, `evWrite_numsOk`, ...).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Report

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem hasBit_orW (h f : w32) (hf : AntCheck.fW &&& f = W32 0) :
    AntCheck.hasBit (h ||| AntCheck.fW) f = AntCheck.hasBit h f := by
  unfold AntCheck.hasBit
  have : (h ||| AntCheck.fW) &&& f = h &&& f := by
    rw [BitVec.and_or_distrib_right, hf]; exact BitVec.or_zero
  rw [this]

theorem fieldRel_orW {α β : Type} (h f : w32) (hf : AntCheck.fW &&& f = W32 0)
    (rel : α → β → Prop) (g : α) (o : Option β) :
    AntCheck.fieldRel (h ||| AntCheck.fW) f rel g o = AntCheck.fieldRel h f rel g o := by
  cases o <;> simp only [AntCheck.fieldRel, hasBit_orW h f hf]

theorem hasBit_orW_self (h : w32) : AntCheck.hasBit (h ||| AntCheck.fW) AntCheck.fW := by
  unfold AntCheck.hasBit AntCheck.fW
  intro heq
  have := congrArg (·.getLsbD 17) heq
  simp at this

/-- `ev.W`'s value `b2i(w)`. -/
theorem sint_b2i (w : Bool) : sint.Z (W64 (if w then 1 else 0)) = if w then 1 else 0 := by
  cases w <;> rfl

/-- **Go's `mem` report** (`withByRole(stateEv("mem", hs, ents), by, role)` with `W = b2i(w)`), recorded
at the node, is the Sim's `evMem` (numbers within `2 ^ 61`, no snapshot). -/
theorem stateEv_mem (id : w64) (b r : AntCheck.Str) (hs : HardStateM) (es : List EntryM) (w : Bool)
    (ht : uint.Z hs.Term' < 2 ^ 61) (hc : uint.Z hs.Commit' < 2 ^ 61)
    (hE : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) { withByRoleM (stateEvM go!"mem" hs es) b r with
        w := some (sint.Z (W64 (if w then 1 else 0))) } =
      AntSim.evMem id b r hs.Term' hs.Vote' hs.Commit' es none w := by
  have e1 : sint.Z hs.Term' = uint.Z hs.Term' := by word
  have e2 : sint.Z hs.Commit' = uint.Z hs.Commit' := by word
  have e3 : sint.Z (firstIdx es) = AntSim.firstOf es := by
    cases es with
    | nil => simp [firstIdx, AntSim.firstOf]
    | cons e t =>
      have := (hE e List.mem_cons_self).2
      simp only [firstIdx, List.head?_cons, Option.map_some, Option.getD_some, AntSim.firstOf]
      word
  have e4 : es.map entOfE = AntSim.logOf es := by
    unfold AntSim.logOf
    apply List.map_congr_left
    intro e he
    have := (hE e he).1
    have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
    unfold entOfE AntSim.entOf
    rw [e6]
  simp only [atNode, withByRoleM, stateEvM, AntSim.evMem, e1, e2, e3, e4, sint_b2i, Option.map_none]

/-- **Go's `write` report** (`stateEv("write", hs, ents)`), recorded at the node, is the Sim's
`evWrite` (no snapshot). -/
theorem stateEv_write (id : w64) (hs : HardStateM) (es : List EntryM)
    (ht : uint.Z hs.Term' < 2 ^ 61) (hc : uint.Z hs.Commit' < 2 ^ 61)
    (hE : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) (stateEvM go!"write" hs es) =
      AntSim.evWrite id hs.Term' hs.Vote' hs.Commit' es none := by
  have e1 : sint.Z hs.Term' = uint.Z hs.Term' := by word
  have e2 : sint.Z hs.Commit' = uint.Z hs.Commit' := by word
  have e3 : sint.Z (firstIdx es) = AntSim.firstOf es := by
    cases es with
    | nil => simp [firstIdx, AntSim.firstOf]
    | cons e t =>
      have := (hE e List.mem_cons_self).2
      simp only [firstIdx, List.head?_cons, Option.map_some, Option.getD_some, AntSim.firstOf]
      word
  have e4 : es.map entOfE = AntSim.logOf es := by
    unfold AntSim.logOf
    apply List.map_congr_left
    intro e he
    have := (hE e he).1
    have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
    unfold entOfE AntSim.entOf
    rw [e6]
  simp only [atNode, stateEvM, AntSim.evWrite, e1, e2, e3, e4, Option.map_none]

theorem evMem_weight (id : w64) (b r : AntCheck.Str) (t vo c : w64) (es : List EntryM) (w : Bool) :
    (AntSim.evMem id b r t vo c es none w).weight = es.length + 2 := by
  simp [AntSim.evMem, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

theorem evWrite_weight (id : w64) (t vo c : w64) (es : List EntryM) :
    (AntSim.evWrite id t vo c es none).weight = es.length + 2 := by
  simp [AntSim.evWrite, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

theorem evWrote_weight (id : w64) : (AntSim.evWrote id).weight = 2 := by
  simp [AntSim.evWrote, AntCheck.Event.weight, AntCheck.Event.size]

theorem evMem_chgOk (id : w64) (b r : AntCheck.Str) (t vo c : w64) (es : List EntryM) (w : Bool) :
    (AntSim.evMem id b r t vo c es none w).ChgOk 0 := by
  have h := evReady_chgOk_b1 id b r t vo c es
  intro l hl e he
  exact h l (by simpa [AntCheck.Event.entryLists, AntSim.evMem, AntSim.evReady] using hl) e he

theorem evWrite_chgOk (id : w64) (t vo c : w64) (es : List EntryM) :
    (AntSim.evWrite id t vo c es none).ChgOk 0 := by
  have h := evReady_chgOk_b1 id [] [] t vo c es
  intro l hl e he
  exact h l (by simpa [AntCheck.Event.entryLists, AntSim.evWrite, AntSim.evReady] using hl) e he

theorem evWrote_chgOk (id : w64) : (AntSim.evWrote id).ChgOk 0 := by
  intro l hl e he
  simp [AntCheck.Event.entryLists, AntSim.evWrote] at hl
  subst hl; cases he

theorem evMem_numsOk {id : w64} {b r : AntCheck.Str} {ps : PState} {vo : w64}
    {es : List EntryM} (w : Bool) (hsn : AntSim.StateNums (2 ^ 61) ps) (ht : uint.Z ps.term < 2 ^ 61)
    (hes : ∀ e ∈ es, e ∈ ps.log) :
    (AntSim.evMem id b r ps.term vo ps.commit es none w).NumsOk := by
  have h := evReady_numsOk_b1 (id := id) (b := b) (r := r) (vo := vo) hsn ht hes
  simp only [AntSim.evReady, AntCheck.Event.NumsOk] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8, h9, h10, h11, h12, h13⟩
  simp only [AntSim.evMem, AntCheck.optNumOk, AntCheck.numOk, AntCheck.numBound]
  cases w <;> decide

theorem evWrite_numsOk {id : w64} {ps : PState} {vo : w64}
    {es : List EntryM} (hsn : AntSim.StateNums (2 ^ 61) ps) (ht : uint.Z ps.term < 2 ^ 61)
    (hes : ∀ e ∈ es, e ∈ ps.log) :
    (AntSim.evWrite id ps.term vo ps.commit es none).NumsOk := by
  have h := evReady_numsOk_b1 (id := id) (b := []) (r := []) (vo := vo) hsn ht hes
  simpa only [AntSim.evReady, AntSim.evWrite, AntCheck.Event.NumsOk] using h

theorem evWrote_numsOk (id : w64) : (AntSim.evWrote id).NumsOk := by
  simp [AntSim.evWrote, AntCheck.Event.NumsOk, AntCheck.optNumOk]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem fieldRO_orW {α β : Type} (h f : w32) (hf : AntCheck.fW &&& f = W32 0)
    (rep : α → β → IProp GF) (g : α) (o : Option β) :
    AntCheck.fieldRO (h ||| AntCheck.fW) f rep g o = AntCheck.fieldRO h f rep g o := by
  cases o <;> simp only [AntCheck.fieldRO, hasBit_orW h f hf]

/-- **`ev.Has |= check.FW; ev.W = x`** on a report being built: its struct, and, once both fields are
set, the report with `w` the value of `x`. -/
theorem eventOwn_setW (p : Loc) (ev : AntCheck.Event) :
    eventOwn (GF := GF) p ev ⊢ ∃ g : AntCheck.G.Event, p ↦ g ∗
      ∀ x : w64, (p ↦ ({ { g with Has' := g.Has' ||| AntCheck.fW } with W' := x } : AntCheck.G.Event) -∗
        eventOwn p { ev with w := some (sint.Z x) }) := by
  iintro Hev
  iunfold eventOwn at Hev
  icases Hev with ⟨%g, Hp, %Hg, He, Hv, Ho, Hm, Hc⟩
  iexists g
  iframe Hp
  iintro %x Hp
  iunfold eventOwn
  iexists _
  isplitl [Hp]
  · iExactEq Hp; rfl
  dsimp only
  rw [fieldRO_orW _ AntCheck.fEntries (by decide), fieldRO_orW _ AntCheck.fVoters (by decide),
    fieldRO_orW _ AntCheck.fOutgoing (by decide), fieldRO_orW _ AntCheck.fMsg (by decide),
    fieldRO_orW _ AntCheck.fCause (by decide)]
  iframe
  ipureintro
  have h1 : ∀ f : w32, AntCheck.fW &&& f = W32 0 →
      AntCheck.hasBit (g.Has' ||| AntCheck.fW) f = AntCheck.hasBit g.Has' f := fun f hf => hasBit_orW _ f hf
  obtain ⟨hE, hN, hB, hb, ha, hby, hro, ht, hvo, hc, hfi, hli, hlt, hap, hsn, -, hmo, hix, hcx⟩ := Hg
  refine ⟨hE, hN, hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1 _ (by decide)]; exact hb
  · rw [h1 _ (by decide)]; exact ha
  all_goals first
    | exact ⟨hasBit_orW_self _, rfl⟩
    | (rw [fieldRel_orW _ _ (by decide)]; assumption)
    | (simp only [AntCheck.fieldZ, AntCheck.fieldIs] at *; rw [fieldRel_orW _ _ (by decide)]; assumption)

end proof

end AntHarness
end EtcdGrove
end Perennial
