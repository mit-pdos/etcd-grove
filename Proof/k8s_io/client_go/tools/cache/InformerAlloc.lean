/-
**The informer invariant from the informer's construction** (the DaemonSet run's track A; the
coordinator's decision of 2026-11-03: the invariant exists before `Start`). Lean-first.

The informer invariant `infInv γa r γf γt γi` reads the FIFO's names `γf` only through its state's
two ghost variables (`fifoSt`: `γf.st`, `γf.sy`), so they can be allocated before the FIFO is
(`RunWithContext` makes it), the FIFO's constructor taking their other halves (`fifoPre`):

* `infInv_congr`: the invariant is the same for two FIFO names with the same `st`/`sy`;
* `infInv_alloc`: at the informer's construction (the store empty, nothing listed), from a past
  state of the server whose keys are good: the invariant, for every FIFO names over the
  preallocated `st`/`sy`, and the halves its goroutines will own (the reflector's last version,
  the processing goroutine's popped deltas and store view, the FIFO's lock halves), with the
  store's indices registered for good (`γi.ix`), the not-started token's name `γns` the caller's
  (`γi.ns`);
* `infInv_readIdxAU`: a store read through the invariant (as `infInv_readLbAU`) also sees the
  registered indices in the store's `fnIds`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI Iris.ProofMode apimodel cache

/-- The FIFO's state before its first push. -/
def FQ.init [GooseExts] : FQ := ⟨[], false, 0, false, false⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The FIFO's lock's halves of its state**, preallocated (the FIFO's constructor takes them). -/
def fifoPre (st sy : GName) : IProp GF :=
  iprop(ghostVar st (1 : Qp).half FQ.init ∗ dghostVar sy (.own (1 : Qp).half) false)

/-- FIFO names over the preallocated `st`/`sy` (the other names are the FIFO's, unused by the
invariant). -/
def fifoNamesOf (st sy : GName) : FifoNames := ⟨st, 0, sy, 0, ⟨0, 0, 0, 0, 0, 0⟩⟩

/-- **The invariant depends on the FIFO's names only through `st`/`sy`.** -/
theorem infInv_congr (γa : ApiNames) (r : Res) (γf γf' : FifoNames) (γt : TsNames)
    (γi : InfNames) (h1 : γf.st = γf'.st) (h2 : γf.sy = γf'.sy) :
    infInv (GF := GF) γa r γf γt γi = infInv γa r γf' γt γi := by
  obtain ⟨a, b, c, d, e⟩ := γf
  obtain ⟨a', b', c', d', e'⟩ := γf'
  simp only at h1 h2
  subst h1 h2
  rfl

/-- **The invariant at the informer's construction**: see the file header. -/
theorem infInv_alloc (γa : ApiNames) (r : Res) (γt : TsNames) (σ0 : apimodel.St)
    (fnIds : GMap GoString Nat) (γns : GName) (E : CoPset)
    (hgood : ∀ c ∈ (σ0.tbl r).log, keyGood c.obj.key) :
    ⊢ pastSt γa σ0 -∗ storeSt γt ⟨∅, [], fnIds⟩ ={E}=∗
      ∃ (γi : InfNames) (st sy : GName), ⌜γi.ns = γns⌝ ∗
        (□ ∀ γf : FifoNames, ⌜γf.st = st ∧ γf.sy = sy⌝ -∗ infInv γa r γf γt γi) ∗
        fifoPre st sy ∗ reflLast γi none ∗
        ghostVar γi.pop (1 : Qp).half (([] : List cache.FD), false) ∗
        ghostVar γi.sw (1 : Qp).half (⟨∅, [], fnIds⟩ : cache.St) ∗
        [∗map] n ↦ j ∈ fnIds, n ↪[γi.ix]□ j := by
  iintro #Hp Hst
  imod (ghost_map_alloc_strong_empty (K := GoInterface) (V := Obj) (GF := GF) (fun _ => True)
    PredInfinite.true) with ⟨%γreg, -, Hreg⟩
  imod (ghostVar_alloc (GF := GF) (none : Option Nat)) with ⟨%γlast, Hlast⟩
  imod (ghostVar_alloc (GF := GF) ((([] : List cache.FD), false))) with ⟨%γpop, Hpop⟩
  imod (ghostVar_alloc (GF := GF) (⟨∅, [], fnIds⟩ : cache.St)) with ⟨%γsw, Hsw⟩
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γrvlb, Hlb, -⟩
  imod (dghostVar_alloc (GF := GF) (none : Option Nat)) with ⟨%γfirst, Hfirst⟩
  imod (ghost_map_alloc_strong_empty (K := GoString) (V := Nat) (GF := GF) (fun _ => True)
    PredInfinite.true) with ⟨%γix, -, Hix⟩
  imod (ghost_map_insert_persist_big (γ := γix) fnIds (GMap.map_disjoint_empty_r fnIds)) $$ Hix
    with ⟨Hix, #Hixs⟩
  imod (ghostVar_alloc (GF := GF) (FQ.init : FQ)) with ⟨%γst, Hfst⟩
  imod (dghostVar_alloc (GF := GF) false) with ⟨%γsy, Hsy⟩
  ihave ⟨Hlast1, Hlast2⟩ := (ghostVar_split_half γlast 1 (none : Option Nat)).1 $$ Hlast
  ihave ⟨Hpop1, Hpop2⟩ := (ghostVar_split_half γpop 1 ((([] : List cache.FD), false))).1 $$ Hpop
  ihave ⟨Hsw1, Hsw2⟩ := (ghostVar_split_half γsw 1 (⟨∅, [], fnIds⟩ : cache.St)).1 $$ Hsw
  ihave ⟨Hfst1, Hfst2⟩ := (ghostVar_split_half γst 1 FQ.init).1 $$ Hfst
  ihave ⟨Hsy1, Hsy2⟩ := dghostVar_split γsy false (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) $$ [Hsy]
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hsy
  ihave Hix := (show (ghostMapAuth γix 1 (fnIds ∪ ∅) : IProp GF) ⊢ ghostMapAuth γix 1 fnIds by
    rw [GMap.map_union_empty]) $$ Hix
  let γi : InfNames := ⟨γreg, γlast, γpop, γsw, γrvlb, γfirst, γix, γns⟩
  imod (inv_alloc infN E (infRes γa r (fifoNamesOf γst γsy) γt γi)) $$
    [Hreg Hst Hsw1 Hlast1 Hpop1 Hlb Hfirst Hix Hfst1 Hsy1] with #Hinv
  · inext
    unfold infRes
    iexists σ0, (⟨⟨∅, none⟩, [], [], none⟩ : InfP), FQ.init, (⟨∅, [], fnIds⟩ : cache.St),
      (∅ : Reg), ([] : List cache.FD), false, (none : Option Nat)
    unfold fifoSt syncedPart
    simp only [FQ.init, Bool.false_eq_true, ↓reduceIte, rvNat, firstDq]
    iframe
    iframe #
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨Inf.init_ok _, trivial, List.Forall₂.nil, List.Forall₂.nil, ⟨rfl, ?_⟩, ?_, hgood, ?_,
      ?_, ?_⟩
    · refine ⟨?_, ?_, fun k => Or.inr ⟨rfl, fun _ _ => rfl⟩⟩
      · intro key h
        exact (Bool.false_ne_true h).elim
      · intro key o h
        cases h
    · intro x o h
      cases h
    · exact ⟨fun _ d hd => by simp at hd, fun h => by simp at h⟩
    · exact ⟨fun d hd => by simp at hd, fun h => by simp at h⟩
    · exact ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun h => by simp at h⟩
  imodintro
  iexists γi, γst, γsy
  iframe #
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %γf %hγf
    rw [infInv_congr γa r γf (fifoNamesOf γst γsy) γt γi hγf.1 hγf.2]
    unfold infInv
    iexact Hinv
  unfold fifoPre reflLast
  iframe

/-- **A store reader's linearization point seeing the registered indices**: as `infInv_readLbAU`,
and every index registered (`n ↪[γi.ix]□ j`, `infIdx`) is in the store's `fnIds` at the state
read. The invariant holds the registry's authority over the store's `fnIds` in every state (no
store step removes an index: `storeStepFD_fnIds`, `batchStore_fnIds`), so a registration holds
for good. -/
theorem infInv_readIdxAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (n : Nat) (X : GMap GoString Nat) (K : cache.St → IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ infRvLb γi n -∗ ([∗map] nm ↦ j ∈ X, nm ↪[γi.ix]□ j) -∗
      (∀ σs, readFactsLb γa r γi σs n -∗
        ⌜∀ nm j, X !! nm = some j → σs.fnIds !! nm = some j⌝ -∗ K σs) -∗
      |={⊤ \ ∅, ∅}=> ∃ σs, storeSt γt σs ∗ (storeSt γt σs ={∅, ⊤ \ ∅}=∗ K σs) := by
  iintro #Hinv #Hn #HX HK
  iunfold infRvLb at Hn
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap, #Hobjs, Hq, Hst, Hsw, Hlast,
    Hpop, Hlb, Hfst, Hix, %Hok⟩
  ihave %hX := ghost_map_lookup_big X $$ Hix HX
  ihave ⟨%hn, Hlb, -⟩ := auth_lb_le γi.rvlb (rvNat s.store.rv) n $$ [$Hlb $Hn]
  ihave #Hlb' := monoNatLbOwn_get γi.rvlb 1 (rvNat s.store.rv) $$ Hlb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σs
  iframe Hst
  iintro Hst
  imod Hclose2 with -
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst Hix] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, pd, ap, f
    iframe
    iframe #
    ipureintro; exact Hok
  imodintro
  iapply HK
  · unfold readFactsLb
    iexists σp, s.store, R
    iframe #
    ipureintro
    exact ⟨Hok.2.2.2.2.1, Hok.1.1, hn⟩
  · ipureintro
    intro nm j h
    exact hX nm j h

end defs

end informer
end EtcdGrove
end Perennial
