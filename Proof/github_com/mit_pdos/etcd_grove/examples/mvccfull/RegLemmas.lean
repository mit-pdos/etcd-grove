/-
The registrar's lemmas for `stream.cancel` (`Streams.lean`'s vocabulary). Lean-first (no Rocq
counterpart).

- `regOk'_mark`, `regOk'_addC`, `regOk'_cancelC`: the registry stays the stream's when an entry is
  marked cancelled (`cm`), when a marked id enters the cancel record, and at a `Cancel` of an id of
  the record.
- `mark_upd`: under `s.mu`, the mark of a registered, unmarked watcher (both halves of the
  registry, the lock's fragment updated with `ghost_map_update` and kept persistent); it was not in
  the cancel record.
- `cancel_au`: the registrar's update for `Cancel(id)` of a marked watcher: the id enters the cancel
  record; the stream was open, and the watcher registered and live if it was not in the record
  before.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EpochLemmas

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

/-- Marking an entry cancelled. -/
theorem regOk'_mark {S : StreamState} {W : GMap w64 Reg} {C : List w64} (h : regOk' S W C)
    {id : w64} {x : Reg} (hx : W !! id = some x) :
    regOk' S (<[id := { x with cm := true }]> W) C := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun id' wi hw => ?_, fun id' x' hx' => ?_, fun id' hC => ?_⟩
  · by_cases he : id = id'
    · subst he; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ he]; exact h1 id' wi hw
  · by_cases he : id = id'
    · subst he
      rw [GMap.lookup_insert] at hx'
      cases hx'
      obtain ⟨wi, hwi, hrg, hfs, hlo, hk, hlive, -⟩ := h2 id x hx
      exact ⟨wi, hwi, hrg, hfs, hlo, hk, hlive, fun _ => rfl⟩
    · rw [GMap.lookup_insert_ne _ _ he] at hx'
      exact h2 id' x' hx'
  · by_cases he : id = id'
    · subst he; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ he]; exact h3 id' hC

/-- A marked, registered id enters the cancel record. -/
theorem regOk'_addC {S : StreamState} {W : GMap w64 Reg} {C : List w64} (h : regOk' S W C)
    {id : w64} {x : Reg} (hx : W !! id = some x) (hcm : x.cm = true) :
    regOk' S W (C ++ [id]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun id' x' hx' => ?_, fun id' hC => ?_⟩
  · obtain ⟨wi, hwi, hrg, hfs, hlo, hk, hlive, hcmC⟩ := h2 id' x' hx'
    refine ⟨wi, hwi, hrg, hfs, hlo, hk, fun hn => hlive (fun hc => hn (List.mem_append_left _ hc)),
      fun hc => ?_⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact hcmC hc
    · rw [List.mem_singleton] at hc; subst hc; rw [hx] at hx'; cases hx'; exact hcm
  · rcases List.mem_append.1 hC with hc | hc
    · exact h3 id' hc
    · rw [List.mem_singleton] at hc; subst hc; rw [hx]; rfl

/-- A `Cancel` of an id of the record. -/
theorem regOk'_cancelC {S : StreamState} {W : GMap w64 Reg} {C : List w64} (h : regOk' S W C)
    {id : w64} (hC : id ∈ C) : regOk' (S.cancel id) W C := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold StreamState.cancel
  split
  · rename_i w hw
    refine ⟨fun id' wi hw' => ?_, fun id' x' hx' => ?_, h3⟩
    · by_cases he : id = id'
      · subst he; exact h1 id w hw
      · simp only at hw'; rw [GMap.lookup_insert_ne _ _ he] at hw'; exact h1 id' wi hw'
    · obtain ⟨wi, hwi, hrg, hfs, hlo, hk, hlive, hcmC⟩ := h2 id' x' hx'
      by_cases he : id = id'
      · subst he
        rw [hw] at hwi; cases hwi
        refine ⟨{ w with live := false }, by simp only; rw [GMap.lookup_insert], hrg, hfs, hlo, hk,
          fun hn => absurd hC hn, hcmC⟩
      · refine ⟨wi, by simp only; rw [GMap.lookup_insert_ne _ _ he]; exact hwi, hrg, hfs, hlo, hk,
          hlive, hcmC⟩
  · exact ⟨h1, h2, h3⟩

theorem cancel_closed (S : StreamState) (id : w64) : (S.cancel id).closed = S.closed := by
  unfold StreamState.cancel; split <;> rfl

theorem delete_insert_same (W : GMap w64 Reg) (id : w64) (x : Reg) :
    GMap.delete id (<[id := x]> W) = GMap.delete id W := by
  apply GMap.map_eq; intro k
  by_cases he : id = k
  · subst he; rw [GMap.lookup_delete, GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ he, GMap.lookup_delete_ne _ he, GMap.lookup_insert_ne _ _ he]

theorem fmap_insert_wp (W : GMap w64 Reg) (id : w64) (x x' : Reg) (hx : W !! id = some x)
    (hwp : x'.wp = x.wp) : (<[id := x']> W).fmap Reg.wp = W.fmap Reg.wp := by
  apply GMap.map_eq; intro k
  rw [GMap.lookup_fmap, GMap.lookup_fmap]
  by_cases he : id = k
  · subst he; rw [GMap.lookup_insert, hx]; simp [hwp]
  · rw [GMap.lookup_insert_ne _ _ he]

theorem isSome_insert_iff (W : GMap w64 Reg) (id : w64) (x x' : Reg) (hx : W !! id = some x)
    (k : w64) : ((<[id := x']> W) !! k).isSome = (W !! k).isSome := by
  by_cases he : id = k
  · subst he; rw [GMap.lookup_insert, hx]; rfl
  · rw [GMap.lookup_insert_ne _ _ he]

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The mark** (under `s.mu`): a registered, unmarked watcher marked in both halves of the
registry; its fragment kept persistent; it was not in the cancel record. -/
theorem mark_upd (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (σs : StreamNames) (W : GMap w64 Reg) (C : List w64) (id : w64) (x : Reg)
    (hx : W !! id = some x) (hcm : x.cm = false) :
    inv streamN (streamInv σs) ∗ regLock σs W ∗ ghostVar σs.cl (1 : Qp).half false ∗
        ghostVar σs.cn (1 : Qp).half C ⊢
      |={⊤}=> regLock σs (<[id := { x with cm := true }]> W) ∗ ghostVar σs.cl (1 : Qp).half false ∗
        ghostVar σs.cn (1 : Qp).half C ∗ id ↪[σs.reg]□ { x with cm := true } ∗ ⌜id ∉ C⌝ := by
  haveI := streamInv_timeless hpers σs
  iintro ⟨#Hinv, Hrl, Hcl, Hcn⟩
  iunfold regLock at Hrl
  icases Hrl with ⟨Hreg, Hfr⟩
  iinv Hinv with >Hi Hclose
  iunfold streamInv at Hi
  icases Hi with ⟨%S, %W', %C', HS, HScl, Hreg', Hcn', Hok⟩
  ihave %HW := ghostMapAuth_agree σs.reg _ _ _ _ $$ Hreg' Hreg
  subst W'
  ihave %HC := ghostVar_agree σs.cn _ _ _ _ $$ Hcn' Hcn
  subst C'
  ihave %Hc := ghostVar_agree σs.cl _ _ _ _ $$ HScl Hcl
  icases Hok with (%HregOk | ⟨%Hcl2, Hwr⟩)
  rotate_left
  · exfalso; rw [Hcl2] at Hc; cases Hc
  have hnC : id ∉ C := fun hC => by
    have := (HregOk.2.1 id x hx); obtain ⟨-, -, -, -, -, -, -, h⟩ := this
    rw [h hC] at hcm; cases hcm
  icases (BigSepM.bigSepM_delete (PROP := IProp GF)
    (Φ := fun id x => if x.cm then id ↪[σs.reg]□ x else id ↪[σs.reg] x) (m := W) hx).1 $$ Hfr
    with ⟨Hf, Hfr⟩
  simp only [hcm, Bool.false_eq_true, ↓reduceIte]
  ihave Hfull := (ghostMapAuth_halves σs.reg W).2 $$ [$Hreg' $Hreg]
  imod ghost_map_update { x with cm := true } $$ Hfull Hf with ⟨Hfull, Hf⟩
  imod ghostMapElem_persist $$ Hf with #Hf
  icases (ghostMapAuth_halves σs.reg _).1 $$ Hfull with ⟨Hreg', Hreg⟩
  imod Hclose $$ [HS HScl Hreg' Hcn'] with -
  · inext; iunfold streamInv
    iexists S, <[id := { x with cm := true }]> W, C
    iframe
    ileft; ipureintro; exact regOk'_mark HregOk hx
  imodintro
  iframe Hcl Hcn
  isplitl
  · iunfold regLock
    iframe Hreg
    iapply (BigSepM.bigSepM_insert_delete (PROP := IProp GF)
      (Φ := fun (id : w64) (x : Reg) => if x.cm then id ↪[σs.reg]□ x else id ↪[σs.reg] x)
      (m := W) (i := id) (x := { x with cm := true })).2
    simp only [↓reduceIte]
    iframe Hf
    iexact Hfr
  iframe Hf
  ipureintro; exact hnC

/-- **The registrar's `Cancel(id)`** of a marked watcher (`cancel`): the id enters the cancel
record (both halves); the stream was open; the watcher registered and live if it was not in the
record. -/
theorem cancel_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (σs : StreamNames) (C : List w64) (id : w64) (x : Reg) (hcm : x.cm = true) :
    inv streamN (streamInv σs) ∗ ghostVar σs.cl (1 : Qp).half false ∗
        ghostVar σs.cn (1 : Qp).half C ∗ id ↪[σs.reg]□ x ⊢
      AU <{ ∃∃ (S : StreamState), wsState (GF := GF) σs.ws S }> @ ⊤ \ ↑mvccN, ∅
      <{ wsState σs.ws (S.cancel id),
        COMM (fun (S : StreamState) => iprop(ghostVar (GF := GF) σs.cl (1 : Qp).half false ∗
          ghostVar σs.cn (1 : Qp).half (C ++ [id]) ∗
          ⌜S.closed = false ∧ (id ∉ C → ∃ w, S.ws !! id = some w ∧ w.live = true)⌝)) S }> := by
  haveI := streamInv_timeless hpers σs
  have Hm := streamN_mvccN
  iintro ⟨#Hinv, Hcl, Hcn, #Hf⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold streamInv at Hi
  icases Hi with ⟨%S, %W, %C', HS, HScl, Hreg, Hcn', Hok⟩
  ihave %Hc := ghostVar_agree σs.cl _ _ _ _ $$ HScl Hcl
  ihave %HC := ghostVar_agree σs.cn _ _ _ _ $$ Hcn' Hcn
  subst HC
  ihave %Hx := ghost_map_lookup $$ Hreg Hf
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑streamN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
  iframe HS
  isplit
  · iintro HS
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg Hcn' Hok] with -
    · inext; iunfold streamInv; iexists S, W, C'; iframe
    imodintro
    iframe
  · iintro HS
    icases Hok with (%HregOk | ⟨%Hcl2, -⟩)
    rotate_left
    · exfalso; rw [Hcl2] at Hc; cases Hc
    imod Hclose2 with -
    imod ghostVar_update_halves (C' ++ [id]) σs.cn _ _ $$ Hcn' Hcn with ⟨Hcn', Hcn⟩
    imod Hclose $$ [HS HScl Hreg Hcn'] with -
    · inext; iunfold streamInv
      iexists S.cancel id, W, C' ++ [id]
      rw [cancel_closed]
      iframe
      ileft; ipureintro
      exact regOk'_cancelC (regOk'_addC HregOk Hx hcm) (List.mem_append_right _ (List.mem_singleton_self _))
    imodintro
    iframe
    ipureintro
    refine ⟨Hc, fun hn => ?_⟩
    obtain ⟨wi, hwi, -, -, -, -, hlive, -⟩ := HregOk.2.1 id x Hx
    exact ⟨wi, hwi, hlive hn⟩

end defs

end mvccfull
end EtcdGrove
end Perennial
