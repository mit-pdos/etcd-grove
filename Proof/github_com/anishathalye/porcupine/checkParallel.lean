/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/checkParallel.lean`.

The context's Done proposition is `□ PD`, `PD := dghostVar γc .discard ()`, minted only by the
main thread from its token `dghostVar γc (.own 1) ()` when it cancels. While the main thread
collects verdicts it holds the token, so `checkSingle`'s third disjunct (`□ cs.PDone`) is
impossible for each verdict it receives then: a `false` verdict means a non-linearizable
partition. The verdicts travel with their goroutine's ghost token (`resultP`,
`ParallelLemmas.lean`), so `n` verdicts are from the `n` goroutines and every cell of
`longest` has been written when the `computeInfo` path reads them.
-/
module

public import Spec.github_com.anishathalye.porcupine.checkParallel
public import Spec.github_com.anishathalye.porcupine.checkSingle
public import Proof.github_com.anishathalye.porcupine.ParallelLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem checkParallel.wp_proof
    (wp_checkSingle : checkSingle.spec (GF := GF) (hG := hG)) :
    checkParallel.spec (GF := GF) (hG := hG) := by
  intro σ S m hsl sls hs cp dur Hlen Hn
  wp_start as ⟨#Hcci, #Hmf, #Hhsl, #Hparts⟩
  wp_apply wp_with_defer as %defer defer
  ihave %Hslen := ownSlice_len _ _ _ $$ Hhsl
  wp_if_destruct
  · iapply HΦ
    ipureintro
    intro _
    exact ⟨by decide, fun _ => rfl⟩
  have Hn0 : 0 < sint.Z hsl.len := by
    have : sint.Z hsl.len ≠ 0 := fun h => Hif (by word)
    omega
  have Hlen' : hs.length = sint.nat hsl.len := by rw [← Hlen]; exact Hslen.1
  imod dghostVar_alloc (GF := GF) () with ⟨%γc, Htok⟩
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(dghostVar γc DFrac.discard ()) $$ [$Hctxp $Hcci]
    as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx', -⟩
  ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
  wp_apply chan.wp_make2 (V := Bool) hsl.len as %rch %γr ⟨#Hrch, %Hcap, Hro⟩
  · ipureintro; constructor <;> word
  wp_apply wp_slice_make2 (V := GoSlice) hsl.len as %lsl ⟨Hlsl, -⟩
  · ipureintro; word
  ihave %Hllen := ownSlice_len _ _ _ $$ Hlsl
  ihave Hcells := ownSlice_replicate_cells _ _ _ $$ Hlsl
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γt, Hauth⟩
  have Hcap0 : ¬ hsl.len = W64 0 := Hif
  rw [ite_eq_right_iff.2 (fun h => absurd h Hcap0)] at *
  imod start_bag (resultP S hs γt lsl (dghostVar γc DFrac.discard ())) _ rch γr (by trivial) $$ Hrch Hro
    with #Hbag
  ipersist ctx
  ipersist model
  ipersist computeInfo
  ipersist results
  ipersist longest
  ipersist history
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => gi
  ihave HI : (∃ (j gv : w64) (sh : GoSlice) (M : GMap Nat Unit),
      "i" ∷ i_ptr ↦ j ∗ "gi" ∷ gi_ptr ↦ gv ∗ "subhistory" ∷ subhistory_ptr ↦ sh ∗
      "Hauth" ∷ ghostMapAuth γt 1 M ∗
      "%HM" ∷ ⌜∀ k : Nat, (M.lookup k).isSome = decide (k < sint.nat j)⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z hsl.len⌝ ∗
      "Hcells" ∷ [∗list] k ∈ (List.range' (sint.nat j) (sint.nat hsl.len - sint.nat j) : List Nat),
        typedPointsto (sliceIndexRef GoSlice ((k : Nat) : Int) lsl) (zero_val GoSlice) (DFrac.own 1)
      : IProp GF) $$ [i gi subhistory Hauth Hcells]
  · iexists W64 0, zero_val w64, zero_val GoSlice, ∅
    iframe
    isplitr
    · ipureintro; intro k; simp
    isplitr
    · ipureintro; word
    rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero, ← List.range_eq_range']
    iexact Hcells
  wp_for HI
  wp_if_destruct
  · have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z hsl.len := ⟨Hj.1, Hif⟩
    simp only [hb, and_self, ↓reduceIte]
    have hjn : sint.nat j < sls.length := by rw [Hslen.1]; word
    obtain ⟨slj, Hslj⟩ : ∃ x, sls[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjn⟩
    wp_apply wp_load_slice_index hsl (sint.Z j) sls _ slj hb.1 $$ [Hhsl] as -
    · iframe #; ipureintro; exact Hslj
    ihave Hpj := BigSepL.bigSepL_lookup Hslj $$ Hparts
    icases Hpj with ⟨%h, %es, %Hhes, #Hes, #Hhio⟩
    have Hsplit : sint.nat hsl.len - sint.nat j = (sint.nat hsl.len - sint.nat (j + W64 1)) + 1 := by
      word
    rw [Hsplit, List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hcells with ⟨Hcj, Hcells⟩
    have HMj : M !! (sint.nat j) = none := by
      simpa using HM (sint.nat j)
    imod ghost_map_insert (sint.nat j) () HMj $$ Hauth with ⟨Hauth, Htj⟩
    wp_apply wp_fork $$ [Hcj Htj]
    · wp_auto
      wp_apply wp_checkSingle σ S m ctx'
        { Values := ∅, Deadline := none, Done_gn := γ', PDone := dghostVar γc DFrac.discard () }
        slj es DFrac.discard h cp Hhes.2.1 (by have := Hhes.2.2; omega) $$ [] as %b %l ⟨Hdisj, Hlo⟩
      · iframe #
      have hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lsl.len := by
        simp at Hllen; constructor <;> word
      simp only [hb2, and_self, ↓reduceIte]
      rw [show sint.Z j = ((sint.nat j : Nat) : Int) by word]
      wp_apply (IntoValTyped.wp_store (t := go.int.SliceType.PointerType.SliceType)
        (sliceIndexRef GoSlice ((sint.nat j : Nat) : Int) lsl) (zero_val GoSlice) l) $$ [$Hcj] as Hcj2
      imod (typedPointsto_dfractional (GF := GF) (sliceIndexRef GoSlice ((sint.nat j : Nat) : Int) lsl) l).dfractional_persist (DFrac.own 1) $$ Hcj2
        with #Hcj
      imod longestOwn_persist _ _ $$ Hlo with #Hlo
      wp_apply wp_bag_send γr rch b (resultP S hs γt lsl (dghostVar γc DFrac.discard ()))
        $$ [$Hbag Htj Hdisj]
      · unfold resultP
        iexists sint.nat j
        iframe Htj
        isplitr
        · ipureintro; rw [Hlen']; word
        isplitr
        · unfold cellDone; iexists l; iframe #
        icases Hdisj with (%Hb | %Hb | #Hb)
        · ileft; ipureintro; exact Hb
        · iright; ileft; ipureintro; exact ⟨h, Hhes.1, Hb⟩
        · iright; iright; iexact Hb
      itrivial
    wp_for_post
    iframe
    iexists j + W64 1, j, slj, <[sint.nat j := ()]> M
    have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [Hj1]
    iframe
    ipureintro
    refine ⟨fun k => ?_, by word⟩
    simp only [GMap.lookup_insert_eq_iff]
    by_cases hk : sint.nat j = k
    · subst hk; simp
    · simp only [hk, ↓reduceIte]
      rw [HM k]
      simp only [decide_eq_decide]
      omega
  -- the goroutines are started
  have Hjn : sint.nat j = hs.length := by rw [Hlen']; word
  have HMall : ∀ k, (M !! k).isSome = decide (k < hs.length) := by intro k; rw [HM k, Hjn]
  iclear Hcells
  wp_join iprop(∃ tc : GoChan, timeout_ptr ↦ dur ∗ timeoutChan_ptr ↦ tc ∗ (⌜tc = chan.nil⌝ ∨
      ∃ γ, ⌜0 < sint.Z dur⌝ ∗ isChanBag γ tc (V := time.Time) (fun _ => iprop(True))))
    with [timeoutChan timeout] as ⟨%tc, timeout, timeoutChan, Htc⟩
  · wp_apply time.wp_After as %tch %γa #Htch
    isplitr
    · ipureintro; rfl
    iexists tch
    iframe
    iright
    iexists γa
    iframe #
    ipureintro; word
  · iexists _
    iframe
    ileft; ipureintro; rfl
  icases Htc with #Htc
  ihave HL : (∃ (c : w64) (okv donev tov : Bool) (R : List Nat),
      "count" ∷ count_ptr ↦ c ∗ "ok" ∷ ok_ptr ↦ okv ∗ "done" ∷ done_ptr ↦ donev ∗
      "timedOut" ∷ timedOut_ptr ↦ tov ∗
      "%HR" ∷ ⌜sint.Z c = R.length ∧ R.Nodup ∧ ∀ i ∈ R, i < hs.length⌝ ∗
      "Htoks" ∷ ([∗list] i ∈ R, ghostMapElem γt i (DFrac.own 1) ()) ∗
      "#Hcd" ∷ □ (∀ i, ⌜i ∈ R⌝ -∗ cellDone lsl i) ∗
      "%Hok" ∷ ⌜(∀ h ∈ hs, Linearizable S.M h) → okv = true⌝ ∗
      "%Hto" ∷ ⌜tov = true → 0 < sint.Z dur⌝ ∗
      "Hcan" ∷ ((⌜donev = false⌝ ∗ dghostVar γc (DFrac.own 1) ()) ∨
        (⌜donev = true⌝ ∗ (dghostVar γc (DFrac.own 1) () ∨ □ dghostVar γc DFrac.discard ())))
      : IProp GF) $$ [count ok done timedOut Htok]
  · iexists W64 0, true, false, false, []
    iframe
    isplitr
    · ipureintro; simp
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · imodintro; iintro %i %Hi; simp at Hi
    isplitr
    · ipureintro; intro; rfl
    isplitr
    · ipureintro; intro h; cases h
    ileft; iframe; ipureintro; rfl
  wp_for HL
  cases donev
  · icases Hcan with (⟨-, Htok⟩ | ⟨%Hc, -⟩)
    rotate_left
    · cases Hc
    simp only [Bool.not_false, decide_true, ↓reduceIte]
    wp_auto_lc 4
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, rch, γr
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
      inext
      iintro %b HP
      iunfold resultP at HP
      icases HP with ⟨%i, %Hi, Hti, #Hcdi, Hd⟩
      ihave %Hni := toks_fresh γt R i $$ Htoks Hti
      ihave ⟨%Hbv, Htok⟩ : (⌜b = true ∨ ∃ h, hs[i]? = some h ∧ ¬ Linearizable S.M h⌝ ∗
          dghostVar γc (DFrac.own 1) ()) $$ [Hd Htok]
      · icases Hd with (%Hb | %Hb | #Hpd)
        · iframe; ipureintro; exact Or.inl Hb
        · iframe; ipureintro; exact Or.inr Hb
        · iexfalso; iapply tok_pd_false $$ Htok Hpd
      have HRlt := nodup_length_lt HR.2.1 HR.2.2 Hi Hni
      wp_auto
      wp_join (v := #(okv && b)) iprop(result_ptr ↦ b) with [result] as result
      have Hok' : (∀ h ∈ hs, Linearizable S.M h) → (okv && b) = true := by
        intro Hall
        rw [Hok Hall]
        rcases Hbv with Hb | ⟨h, Hh, Hnl⟩
        · simp [Hb]
        · exact absurd (Hall h (List.mem_of_getElem? Hh)) Hnl
      generalize hk : (okv && b) = k at Hok' ⊢
      wp_join iprop(∃ dn : Bool, done_ptr ↦ dn ∗ cancel_ptr ↦ cancel ∗ count_ptr ↦ (c + W64 1) ∗
          ((⌜dn = false⌝ ∗ dghostVar γc (DFrac.own 1) ()) ∨
            (⌜dn = true⌝ ∗ (dghostVar γc (DFrac.own 1) () ∨ □ dghostVar γc DFrac.discard ()))))
        at (if: _ then _ else _) with [done Htok cancel count] as ⟨%dn, done, cancel, count, Hcan⟩
      · rcases (show (k = true) ∨ (k = false ∧ cp = true) ∨ (k = false ∧ cp = false) by
            cases k <;> cases cp <;> simp) with Hkc | ⟨Hk, Hc⟩ | ⟨Hk, Hc⟩
        all_goals first | subst Hkc | (subst Hk; subst Hc)
        rotate_right
        · -- a failed partition, not computeInfo: cancel
          wp_auto
          imod dghostVar_persist γc 1 () $$ Htok with #HPD
          wp_apply Hcancel' $$ [HPD]
          · iexact HPD
          isplitr
          · ipureintro; rfl
          iexists true
          iframe
          iright
          isplitr
          · ipureintro; rfl
          iright
          iexact HPD
        all_goals
          wp_auto
          wp_if_destruct
          · isplitr
            · ipureintro; first | rfl | trivial
            iexists true
            iframe done cancel count
            iright
            isplitr
            · ipureintro; rfl
            ileft; iexact Htok
          · isplitr
            · ipureintro; first | rfl | trivial
            iexists false
            iframe done cancel count
            ileft
            isplitr
            · ipureintro; rfl
            iexact Htok
      wp_for_post
      ihave Htoks' : ([∗list] j ∈ i :: R, ghostMapElem γt j (DFrac.own 1) ()) $$ [Hti Htoks]
      · iapply BigSepL.bigSepL_cons.2; iframe
      ihave #Hcd' : (□ ∀ j, ⌜j ∈ i :: R⌝ -∗ cellDone lsl j) $$ []
      · imodintro
        iintro %j %hj
        rcases List.mem_cons.1 hj with rfl | hj
        · iexact Hcdi
        · iapply Hcd $$ %j %hj
      iframe
      iexists c + W64 1, k, dn, tov, i :: R
      iframe
      iframe #
      ipureintro
      refine ⟨⟨?_, List.nodup_cons.2 ⟨Hni, HR.2.1⟩, ?_⟩, Hok', Hto⟩
      · have := HR.1; simp only [List.length_cons]; word
      · intro j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact Hi
        · exact HR.2.2 j hj
    iapply BigAndL.bigAndL_cons.2
    isplit
    · icases Htc with (%Hnil | ⟨%γa, %Hdpos, #Hta⟩)
      · iright
        iapply chan.nilClausePre_recv time.Time _ _ Hnil
      · ileft
        simp only [chan.blockingClausePre]
        iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tc, γa
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Hta
        iapply bag_recv_au $$ [$Hlc3 $Hlc4] Hta
        inext
        iintro %t -
        wp_auto
        imod dghostVar_persist γc 1 () $$ Htok with #HPD
        wp_apply Hcancel' $$ [HPD]
        · iexact HPD
        wp_for_post
        iframe
        iexists c, okv, true, true, R
        iframe
        iframe #
        isplitr
        · ipureintro; exact HR
        isplitr
        · ipureintro; exact Hok
        isplitr
        · ipureintro; exact fun _ => Hdpos
        iright
        isplitr
        · ipureintro; rfl
        iright; iexact HPD
    iapply BigAndL.bigAndL_nil.2
    itrivial
  done

end proof

end porcupine
end EtcdGrove
end Perennial
