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

set_option hygiene false in
/-- `seq` made if `nil` (the copy of the stack's ids) and `longest[v.opId] = &seq`. -/
local macro "longest_update" : tactic => `(tactic| (
    wp_join iprop((∃ (sl : GoSlice) (xs : List w64),
        ((seq_ptr ↦ sl ∗ sl ↦* xs) ∨ (seq_ptr ↦□ sl ∗ sl ↦*□ xs)) ∗ ⌜sl ≠ slice.nil⌝) ∗
        ssl1 ↦* ses1 ∗ stack_ptr ↦ ssl1) at next with [Hseq Hstack Hstk] as ⟨Hseq, Hstack, Hstk⟩
    · icases Hseq with (Hs0 | ⟨%sl, %xs, #Hs, #Hsl, %Hslne⟩)
      · wp_auto
        wp_apply wp_slice_make2 (V := w64) $$ [] as %sq ⟨Hsq, -⟩
        try (· ipureintro; exact Hssl.2)
        irename : (j_ptr ↦ zero_val w64 : IProp GF) => Hiu
        ihave HF : (∃ (k' iv : w64) (vv' : stackEntry) (xs : List w64),
            "i" ∷ i_ptr ↦ k' ∗ "Hiu" ∷ j_ptr ↦ iv ∗ "w" ∷ w_ptr ↦ vv' ∗ "Hsq" ∷ sq ↦* xs ∗
            "%Hk'" ∷ ⌜0 ≤ sint.Z k' ∧ sint.Z k' ≤ sint.Z ssl1.len ∧ xs.length = ses1.length⌝ : IProp GF)
          $$ [i Hiu w Hsq]
        · iexists W64 0, _, _, _
          iframe
          ipureintro
          refine ⟨by decide, by word, ?_⟩
          rw [List.length_replicate, Hssl.1]
        wp_for HF
        obtain ⟨Hk1', Hk2', Hk3'⟩ := Hk'
        (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
        wp_if_destruct
        · have Hb : 0 ≤ sint.Z k' ∧ sint.Z k' < sint.Z ssl1.len := ⟨Hk1', Hif⟩
          simp only [Hb, _root_.and_self, ↓reduceIte]
          list_elem ses1 (sint.nat k') as ce'
          wp_apply wp_load_slice_index ssl1 (sint.Z k') ses1 (DFrac.own 1) ce' Hk1' $$ [Hstack] as Hstack
          · iframe; ipureintro; exact Hce'_lookup
          ihave %Hsql := ownSlice_len $$ Hsq
          obtain ⟨Hsql1, Hsql2⟩ := Hsql
          have Hb' : 0 ≤ sint.Z k' ∧ sint.Z k' < sint.Z sq.len := by
            constructor
            · exact Hk1'
            · have : xs.length = ses1.length := Hk3'
              word
          simp only [Hb', _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [Hsq] as Hsq
          · iframe; ipureintro; constructor <;> word
          wp_for_post
          iframe
          iexists k' + W64 1, k', ce', _
          iframe
          ipureintro
          refine ⟨by word, by word, by simp [Hk3']⟩
        · ihave %Hsql := ownSlice_len $$ Hsq
          obtain ⟨Hsql1, Hsql2⟩ := Hsql
          have hsqne : sq ≠ slice.nil := by
            intro h'
            subst h'
            have : xs.length = 0 := by simp [Hsql1, slice.nil]
            apply hlen0
            have h3 : ses1.length = 0 := by rw [← Hk3', this]
            rw [Hsesl] at h3; exact h3
          isplitr
          · itrivial
          iframe
          iexists sq, xs
          isplitl [Hs0 Hsq]
          · ileft; iframe
          ipureintro; exact hsqne
      · wp_auto
        simp only [Hslne, _root_.decide_false]
        wp_auto
        isplitr
        · ipureintro; rfl
        iframe
        iexists sl, xs
        isplitl []
        · iright; iframe Hs Hsl
        ipureintro; exact Hslne
    icases Hseq with ⟨%sl, %xs, Hsq, %Hslne⟩
    imod persist_or seq_ptr sl xs $$ Hsq with ⟨#Hs, #Hsl⟩
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hps] as Hps
    · iframe; ipureintro; constructor <;> word
    wp_for_post
    iframe
    iexists k + W64 1, ce, _
    iframe
    isplitl []
    · iapply longestElems_set ps _ seq_ptr (by word)
      iframe Hpse
      iright
      iexists sl, xs
      iframe Hs Hsl
    isplitl []
    · iright; iexists sl, xs; iframe Hs Hsl; ipureintro; exact Hslne
    ipureintro
    refine ⟨by word, by word, by simp [Hk3]⟩
  ))

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
      wp_auto
      iunfold searchOwn at Hs
      icases Hs with ⟨%st1, %ssl1, %ses1, %lsl1, %ws1, Hch, %Hci1, Hstk, Hstack, Hscap, #Hses, Hlinp, Hlin,
        %Hws1', Hcache⟩
      simp only [named]
      ihave %Hsesl := stackRep_length S np cs ses1 fs $$ Hses
      ihave %Hssl := ownSlice_len $$ Hstack
      wp_auto
      wp_if_destruct
      · -- the stack is empty: no linearization
        have hfs : fs = [] := by
          apply List.eq_nil_of_length_eq_zero
          obtain ⟨h1, h2⟩ := Hssl; rw [← Hsesl, h1]; rw [snat_eq]; simp [Hif]
        subst hfs
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %psl ⟨Hpsl, -⟩
        wp_apply wp_Printf _ _ _ _ (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int pv) fmt.ArgsWf.nil)
          $$ [Hpsl] as %n %e2 -
        · iframe
        wp_for_post
        iapply HΦ
        iframe
        iright
        isplitr
        · ipureintro; rfl
        icases Hb with (%Hb | #HPD)
        · ileft; ipureintro
          obtain ⟨y, hy, -⟩ := hinc
          exact bad_fail hirr hdom Hst Hb ⟨y, hy⟩
        · iright; iexact HPD
      · -- the stack is not empty
        have hlen0 : fs.length ≠ 0 := by
          intro h0; apply Hif
          obtain ⟨h1, h2⟩ := Hssl; rw [Hsesl, h0] at h1
          have : sint.Z ssl1.len = 0 := by rw [snat_eq] at h1; omega
          word
        -- `if computePartial { ... }`: memory only
        wp_join iprop(longestOwn lgst h.length ∗ ssl1 ↦* ses1 ∗ longest_ptr ↦ lgst ∗ stack_ptr ↦ ssl1)
          with [Hlongest Hstack longest Hstk] as ⟨Hlongest, Hstack, longest, Hstk⟩
        · iunfold longestOwn at Hlongest
          icases Hlongest with ⟨%ps0, Hps, %Hps0, #Hpse⟩
          ihave %Hlgl := ownSlice_len $$ Hps
          obtain ⟨Hlgl1, Hlgl2⟩ := Hlgl
          irename : (seq_ptr ↦ slice.nil : IProp GF) => Hseq0
          ihave HP : (∃ (k : w64) (vv : stackEntry) (ps : List Loc),
              "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "Hps" ∷ lgst ↦* ps ∗
              "#Hpse" ∷ ([∗list] p ∈ ps, longestElem (GF := GF) p) ∗
              "Hseq" ∷ (seq_ptr ↦ slice.nil ∨
                ∃ (sl : GoSlice) (xs : List w64), seq_ptr ↦□ sl ∗ sl ↦*□ xs ∗ ⌜sl ≠ slice.nil⌝) ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z ssl1.len ∧ ps.length = h.length⌝ : IProp GF)
            $$ [i v Hps Hseq0]
          · iexists W64 0, _, ps0
            iframe
            iframe Hpse
            isplitl [Hseq0]
            · ileft; iexact Hseq0
            ipureintro
            exact ⟨by decide, by word, Hps0⟩
          wp_for HP
          obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
          (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
          wp_if_destruct
          · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z ssl1.len := ⟨Hk1, Hif⟩
            simp only [Hb, _root_.and_self, ↓reduceIte]
            list_elem ses1 (sint.nat k) as ce
            have hkf : sint.nat k < fs.reverse.length := by rw [List.length_reverse, ← Hsesl]; word
            list_elem fs.reverse (sint.nat k) as f
            wp_apply wp_load_slice_index ssl1 (sint.Z k) ses1 (DFrac.own 1) ce Hk1 $$ [Hstack] as Hstack
            · iframe; ipureintro; exact Hce_lookup
            ihave %Hcent := stackRep_get S np cs ses1 fs Hce_lookup Hf_lookup $$ Hses
            have hfm : f ∈ fs := List.mem_reverse.mp (List.mem_of_getElem? Hf_lookup)
            have hfid : f.id < h.length :=
              Hci1.1.2.2.2.2.2.1 f.id (List.mem_map_of_mem hfm)
            try wp_auto
            ihave %Hpsl := ownSlice_len $$ Hps
            obtain ⟨Hpsl1, Hpsl2⟩ := Hpsl
            have Hb2 : 0 ≤ sint.Z ce.opId' ∧ sint.Z ce.opId' < sint.Z lgst.len := by
              rw [Hcent]; constructor
              · omega
              · have : f.id < ps.length := by rw [Hk3]; exact hfid
                rw [snat_eq] at Hpsl1; omega
            simp only [Hb2, _root_.and_self, ↓reduceIte]
            list_elem ps f.id as p0
            have hidx : (sint.Z ce.opId').toNat = f.id := by rw [Hcent]; simp
            wp_apply wp_load_slice_index lgst (sint.Z ce.opId') ps _ p0 Hb2.1 $$ [Hps] as Hps
            · iframe; ipureintro; rw [hidx]; exact Hp0_lookup
            ihave #Hp0 := longestElems_get ps f.id p0 Hp0_lookup $$ Hpse
            by_cases hp0 : p0 = null
            · simp only [hp0, _root_.decide_true]
              wp_auto
              longest_update
            · simp only [hp0, _root_.decide_false]
              wp_auto
              simp only [Hb2, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index lgst (sint.Z ce.opId') ps _ p0 Hb2.1 $$ [Hps] as Hps
              · iframe; ipureintro; rw [hidx]; exact Hp0_lookup
              icases Hp0 with (%hn | ⟨%sl0, %xs0, #Hp0s, #Hsl0⟩)
              · exact absurd hn hp0
              wp_auto
              by_cases hlt : sint.Z sl0.len < sint.Z ssl1.len
              · simp only [hlt, _root_.decide_true]
                wp_auto
                longest_update
              · simp only [hlt, _root_.decide_false]
                wp_auto
                wp_for_post
                iframe
                iexists k + W64 1, ce, ps
                iframe
                iframe Hpse
                ipureintro
                refine ⟨by word, by word, Hk3⟩
          · -- the loop's end
            iframe
            iunfold longestOwn
            iexists ps
            iframe Hps Hpse
            ipureintro; exact Hk3
        -- `top, unlifted_id := ch.unlift(&stack, &serialized, consistency)`
        obtain ⟨f, fs', rfl⟩ := List.exists_cons_of_ne_nil (l := fs) (fun h0 => hlen0 (by rw [h0]; rfl))
        ihave Hs : searchOwn S np h cs ch_ptr stack_ptr serialized_ptr cm (f :: fs') fr cache
          $$ [Hch Hstk Hstack Hscap Hlinp Hlin Hcache]
        · iunfold searchOwn; iexists st1, ssl1, ses1, lsl1, ws1; simp only [named]
          iframe; iframe Hses; ipureintro; exact ⟨Hci1, Hws1'⟩
        wp_apply wp_unlift σ S np cons h cs ch_ptr stack_ptr serialized_ptr cm f fs' fr cache s (sint.Z lf)
          hok hwf halloc Hst $$ [Hs] as %sv' %idx ⟨Hs, #Hsv', %Hidx⟩
        · iframe; iframe Hcons
        have hpos : f.pos < h.length := by
          obtain ⟨-, ⟨-, hcl, hp⟩, -⟩ := Hst
          have hl := (List.getElem?_eq_some_iff.mp hp).1
          have hnd : f.fr.Nodup := by
            exact hcl.1.imp fun {a b} (hk : KeyGt h cs a b) (he : a = b) => by
              subst he; exact keyGt_irrefl hk
          have : f.fr.length ≤ h.length := by
            simpa using List.Nodup.length_le_of_subset hnd
              (fun y hy => List.mem_range.mpr ((hcl.2 y).mp hy).1)
          omega
        have hidx1 : sint.Z (idx - W64 1) = (f.pos : Int) - 1 := by
          have := hhl; rw [← Hidx]; word
        wp_for_post
        iframe
        iexists f.pre
        iframe Hsv'
        isplitr
        · ipureintro; rw [hidx1]; exact struct_pop Hst
        icases Hb with (%Hb | #HPD)
        · ileft; ipureintro; rw [hidx1]; exact bad_pop hirr hdom Hst Hb hinc
        · iright; iexact HPD
    · -- lifted
      subst Hok
      sorry

end proof

end porcupine
end EtcdGrove
end Perennial
