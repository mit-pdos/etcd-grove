/- Lean-first (no Rocq counterpart).

`checkSingle(ctx, model, consistency, history, computePartial)` (dag.go, PR #46): the DAG search
loop, against the abstract search of `DagTheory` (`searchOwn`, the current state shared at depth
`|fs|`, the cursor `liftFrom`; `Struct` unconditionally, `Bad` or the context done). Each exit and
each branch is one `DagTheory` lemma: `isComplete` gives `sound_done` (every operation linearized,
`complete_all`), a done context answers `false`, a lift `struct_push`/`bad_push` (from
`chains.lift`'s post), a failure with an empty stack `bad_fail`, a failure otherwise
`chains.unlift` and `struct_pop`/`bad_pop` (`hinc` from `isComplete = false`). The `computePartial`
loops and the final `seq` are memory only (`longestOwn`), as v1.3.1's. The state values are shared
in a pool allocated at the start, as v1.3.1's.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.checkSingle
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newChains
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.newBitset
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__isComplete
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__lift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__unlift
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.SearchLemmas
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.DagLemmas
public import Perennial.Spec.fmt.Printf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option maxHeartbeats 4000000 in
theorem checkSingle.wp_proof
    (wp_newChains : newChains.spec (GF := GF) (hG := hG))
    (wp_newBitset : newBitset.spec (GF := GF) (hG := hG))
    (wp_isComplete : chains.isComplete.spec (GF := GF) (hG := hG))
    (wp_lift : chains.lift.spec (GF := GF) (hG := hG))
    (wp_unlift : chains.unlift.spec (GF := GF) (hG := hG))
    (wp_Printf : fmt.Printf.spec (GF := GF) (hG := hG)) :
    checkSingle.spec (GF := GF) (hG := hG) := by
  intro σ S m ctx ctxd cons ohsl h cs cp hok hwf halloc
  wp_start as ⟨#Hctx, #Hm, #Hcons, Hoh, #Hio⟩
  have hcall : CallLeRet h := hwf.2
  wp_auto
  wp_apply wp_newChains ohsl h cs cons hok hwf halloc $$ [Hoh] as %chV ⟨%st, Hr, %Hci⟩
  · iframe; iframe Hcons
  icases chainsRepr_facts chV h cs st $$ Hr with ⟨%Hfacts, Hr⟩
  obtain ⟨Hnum, Hfrl⟩ := Hfacts
  have hhl := hwf.1
  -- `serialized := newBitset(uint(ch.numOps))`
  wp_apply wp_newBitset as %lsl Hlsl
  have hnum : uint.nat chV.numOps' = h.length := by
    have := Hnum; simp only [sint.Z] at this; simp only [uint.nat]; word
  rw [hnum]
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice)) as %cm Hcm
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %ssl0 ⟨Hssl0, Hscap0⟩
  -- `state := consistency.Valid.Init(model)`
  ihave #Hcons' := Hcons
  iunfold isLinearizability at Hcons'
  icases Hcons' with ⟨-, %Hval⟩
  wp_auto
  rw [Hval, show rvalV.Init' = rvInitV from rfl, rvInitV_val]
  wp_auto
  ihave #Hm' := Hm
  iunfold isModelFilled at Hm'
  icases Hm' with ⟨#Hinit, #Hstep, #Heh⟩
  unfold initSpec
  wp_apply Hinit as %sv0 Hsv0
  -- `longest := make([]*[]int, ch.numOps)`
  have hnumz : sint.Z chV.numOps' = h.length := Hnum
  wp_apply wp_slice_make2 (V := Loc) $$ [] as %lgst ⟨Hlgst, -⟩
  · ipureintro; omega
  -- the pool of the state values' invariants
  imod (NonAtomicInvariant.alloc (GF := GF)) with ⟨%np, Htok⟩
  imod shared_alloc S np ⊤ 0 sv0 S.M.init $$ Hsv0 with #Hsv0
  have hfr0 : CandList h cs (Before h cs) [] (frOf cs st) := Hci.2.2.2.2.2.2.2.2.2.2
  have hlf0 : sint.Z (chV.frontier'.len - W64 1) = ((frOf cs st).length : Int) - 1 := by
    unfold frOf; rw [List.length_map]
    have := Hfrl; have : st.frontier.length ≤ cs.length := by
      have := nodup_of_sorted hfr0.1
      exact Nat.le_trans (List.Nodup.length_le_of_subset this (fun v hv => List.mem_range.mpr
        (Hci.2.2.2.2.2.2.2.2.2.1 v hv).1)) (by simp)
    have hcs : (cs.length : Int) ≤ 2 ^ 45 := by
      have := halloc; unfold AllocOk maxAllocBytes at this
      have hm : (cs.length : Int) * 1 ≤ cs.length * ((max h.length 6 : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    word
  -- the loop invariant
  ihave HI : (∃ (fs : List (Frame σ)) (s : σ) (fr : List Nat) (cache : List ((Nat → Prop) × σ))
      (sv : GoInterface) (lf pv : w64),
      "Hs" ∷ searchOwn S np h cs ch_ptr stack_ptr serialized_ptr cm fs fr cache ∗
      "#Hsv" ∷ shared S np fs.length sv s ∗ "state" ∷ state_ptr ↦ sv ∗
      "liftFrom" ∷ liftFrom_ptr ↦ lf ∗ "pops" ∷ pops_ptr ↦ pv ∗
      "Htok" ∷ NonAtomicInvariant.own np ⊤ ∗ "Hlongest" ∷ longestOwn lgst h.length ∗
      "%Hst" ∷ ⌜Struct S.M h cs (Before h cs) fs s fr (sint.Z lf)⌝ ∗
      "#Hgood" ∷ (⌜Bad S.M h (Before h cs) fs s fr (sint.Z lf) cache⌝ ∨ □ ctxd.PDone) : IProp GF)
    $$ [ch Hr serialized Hlsl Hcm stack Hssl0 Hscap0 state liftFrom pops Htok Hlgst]
  · iexists [], S.M.init, frOf cs st, [], sv0, chV.frontier'.len - W64 1, W64 0
    iframe
    iframe Hsv0
    isplitl [ch Hr serialized Hlsl Hcm stack Hssl0 Hscap0]
    · iunfold searchOwn
      iexists st, slice.mk ssl0 (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])), [], lsl,
        List.replicate (bsChunks h.length) (W64 0)
      simp only [named]
      isplitl [ch Hr]
      · iunfold chainsOwn; iexists chV; iframe
      isplitr
      · ipureintro; exact ⟨Hci, trivial⟩
      iframe
      isplitl []
      · unfold stackRep; simp only [List.reverse_nil]; iapply BigSepL2.bigSepL2_nil.2; iempintro
      isplitr
      · ipureintro
        refine ⟨by rw [List.length_replicate], fun i => ?_⟩
        rw [bsBit_replicate]; simp [ids]
      iunfold cacheOwn
      iexists ∅
      iframe
      iapply BigSepM.bigSepM_empty.2; iempintro
    isplitl [Hlgst]
    · rw [show sint.nat chV.numOps' = h.length by rw [snat_eq, hnumz]; simp]
      iapply longestOwn_replicate
      iexact Hlgst
    isplitr
    · ipureintro; rw [hlf0]; exact struct_init hfr0
    ileft; ipureintro; rw [hlf0]; exact bad_init
  irename «ctx» => Hctxp
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  iclear HDeadline HDone HValue HErrDone HDoneFresh HParentCC HClosedchan HErr
  have hirr : ∀ y, ¬ Before h cs y y := before_irrefl hok hcall
  have hdom : ∀ a b, Before h cs a b → a < h.length := fun a b hab => before_dom hok hab
  wp_for HI
  iunfold searchOwn at Hs
  icases Hs with ⟨%st, %ssl, %ses, %lsl, %ws, Hch, %Hci, Hstk, Hstack, Hscap, #Hses, Hlinp, Hlin, %Hws,
    Hcache⟩
  simp only [named]
  obtain ⟨Hci, Hfr⟩ := Hci
  obtain ⟨Hws1, Hws2⟩ := Hws
  wp_apply wp_isComplete ch_ptr h cs st Hci.1 Hci.2.2.2.1 $$ [Hch] as Hch
  · iframe
  by_cases hcomp : ∀ (c : Nat), c < cs.length → st.head c = (chain cs c).length
  · -- every operation linearized: the loop's end
    have hft : ¬ ((#false : val) = #true) := fun h0 => by
      have := go.intoVal_inj h0; simp at this
    simp only [eq_true hcomp, decide_true, Bool.not_true, hft, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    sorry
  · -- some operation not linearized: the loop's body
    have hinc := incomplete_some hok Hci hcomp
    simp only [eq_false hcomp, decide_false, Bool.not_false, decide_true, ↓reduceIte]
    -- `if ctx.Err() != nil { fmt.Printf(...); return false, longest }`
    try wp_auto
    wp_apply HErrU as %err Herr
    cases err
    · simp only [reduceCtorEq, ↓reduceIte]
      icases Herr with ⟨#HPD, -⟩
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %psl ⟨Hpsl, -⟩
      wp_apply wp_Printf _ _ _ _ (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int pv) fmt.ArgsWf.nil) $$ [Hpsl]
        as %n %e2 -
      · iframe
      wp_for_post
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      iright; iexact HPD
    iclear Herr
    wp_auto
    -- `ch.lift(...)`
    ihave Hs : searchOwn S np h cs ch_ptr stack_ptr serialized_ptr cm fs fr cache
      $$ [Hch Hstk Hstack Hscap Hlinp Hlin Hcache]
    · iunfold searchOwn; iexists st, ssl, ses, lsl, ws; simp only [named]
      iframe; iframe Hses; ipureintro; exact ⟨⟨Hci, Hfr⟩, Hws1, Hws2⟩
    wp_apply wp_lift σ S m ctx ctxd cons np h cs ch_ptr stack_ptr serialized_ptr cm fs fr cache sv s lf
      hok hwf halloc Hst hinc $$ [$Hctx $Hm $Hcons $Hio $Hs $Hsv $Htok $Hgood] as %nsv %ok ⟨Htok, Hres⟩
    icases Hres with (⟨%Hok, Hs, #Hb⟩ | ⟨%Hok, %y, %q, %t', %fr', Hs, #Hnsv, %Hst', #Hb'⟩)
    · -- not lifted
      subst Hok
      sorry
    · -- lifted
      subst Hok
      sorry

end proof

end porcupine
end EtcdGrove
end Perennial
