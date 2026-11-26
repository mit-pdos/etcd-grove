/-
Helpers of the EPaxos kit's model and codec proofs (notes/dsv-epaxos.md): the Go values' injectivity
(`In`, `Out`), `Codec()`'s bytes of an output (`encOutV_outV`), the decoder on boxed values
(`epDec_box`), and the store's decoding facts remote's `Check` needs (`epS_pendDec`,
`epR_encOut_inj`); then the WP specs of `model.go`'s helpers, which `ModelProof.lean` composes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Kit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]

/-- `Out`'s values are injective (`Unknown` and `V` are read off by deterministic steps). -/
theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hU'] at hU
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  injection eV with eV
  injection eU with eU
  have eV' := go.intoVal_inj eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  cases x; cases y
  simp only at eV' eU'
  subst eV' eU'
  rfl

/-- `In`'s values are injective. -/
theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hO := (In.TypeAssumptions.get_Op x).isGoStep_det_internal.isGoStep_pure_det
  have hO' := (In.TypeAssumptions.get_Op y).isGoStep_det_internal.isGoStep_pure_det
  have hK := (In.TypeAssumptions.get_K x).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (In.TypeAssumptions.get_K y).isGoStep_det_internal.isGoStep_pure_det
  have hN := (In.TypeAssumptions.get_N x).isGoStep_det_internal.isGoStep_pure_det
  have hN' := (In.TypeAssumptions.get_N y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (In.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hO'] at hO
  rw [h, hK'] at hK
  rw [h, hN'] at hN
  rw [h, hV'] at hV
  have eO : Val #x.Op' = Val #y.Op' := (congrFun hO (Val #y.Op')) ▸ rfl
  have eK : Val #x.K' = Val #y.K' := (congrFun hK (Val #y.K')) ▸ rfl
  have eN : Val #x.N' = Val #y.N' := (congrFun hN (Val #y.N')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eO with eO
  injection eK with eK
  injection eN with eN
  injection eV with eV
  have eO' := go.intoVal_inj eO
  have eK' := go.intoVal_inj eK
  have eN' := go.intoVal_inj eN
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eO' eK' eN' eV'
  subst eO' eK' eN' eV'
  rfl

theorem outV_inj {u v u' v'} (h : outV u v = outV u' v') : u = u' ∧ v = v' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := out_intoVal_inj h
  simp only [Out.mk.injEq] at this
  exact this

theorem inE_inj {i j : EIn} (h : inE i = inE j) : i = j := by
  obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;> obtain ⟨k' | ⟨k', v'⟩ | ⟨k', n'⟩, hj⟩ := j <;>
    simp_all [inE, inOf]

theorem ivE_inj {i j : EIn} (h : ivE i = ivE j) : i = j := by
  simp only [ivE, inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact inE_inj (in_intoVal_inj h)

/-- `Out{u, w}`'s bytes. -/
theorem encOutV_outV (u : Bool) (w : BStr) : encOutV (outV u w.1) = encOutB u w.1 := by
  unfold encOutV
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := outV_inj h.choose_spec
    rw [← h1, ← h2]
  · rename_i h
    exact absurd ⟨(u, w), rfl⟩ h

/-- `epDec` on a boxed input and a boxed bounded `Out`. -/
theorem epDec_box (i : EIn) (u : Bool) (w : BStr) :
    epDec (ivE i, outV u w.1) = some (i, ansOf u w) := by
  unfold epDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    have e1 := ivE_inj h1
    obtain ⟨e2, e3⟩ := outV_inj h2
    have e3' := Subtype.ext e3
    rw [← e3', ← e2, ← e1]
  · next hn => exact absurd ⟨i, u, w, rfl⟩ hn

end dec

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]
variable [π : NetProtoGS]

/-- Distinct outputs have distinct bytes. -/
theorem epR_encOut_inj (γ : EpNames) (o o' : BStr)
    (h : (epR (Gg := hG.goose_globalGS) γ).encOut ((epR (Gg := hG.goose_globalGS) γ).ov o) =
      (epR (Gg := hG.goose_globalGS) γ).encOut ((epR (Gg := hG.goose_globalGS) γ).ov o')) :
    o = o' := by
  simp only [epR, encOutV_outV, encOutB] at h
  exact Subtype.ext (List.cons.inj h).2

/-- The empty answer, bounded. -/
def bEmpty : BStr := ⟨[], by simp⟩

/-- **porcupine's model is the pending-writes model** of the far side's store `epR γ`. -/
theorem epS_pendDec (γ : EpNames) :
    PendDec (epR (Gg := hG.goose_globalGS) γ) (epS (GF := GF)) :=
  .ofTotal (fun _ => rfl) {
  init := rfl
  ok s i o := linkv.pM_step epB epDec s _ i _ (epDec_box i false o)
  err s i := linkv.pM_step epB epDec s _ i _ (epDec_box i true bEmpty)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, false, o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, true, bEmpty, rfl⟩
  noObs _ := rfl }

end facts

/-! ## The helpers of `model.go` -/


section pureLen
variable [GooseExts]

theorem setE_length (kv : List Entry) (k : w64) (v : GoString) :
    (setE kv k v).length ≤ kv.length + 1 := by
  unfold setE
  rw [List.length_append]
  have := List.length_filter_le (fun e => !decide (e.K' = k)) kv
  split <;> simp <;> omega

end pureLen

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

set_option goose.wp.extras true

theorem getE_drop (L : List Entry) (k : w64) (n : Nat) (e : Entry) (he : L[n]? = some e) :
    getE (L.drop n) k = if e.K' = k then e.V' else getE (L.drop (n + 1)) k := by
  have hn : n < L.length := (List.getElem?_eq_some_iff.1 he).1
  rw [List.drop_eq_getElem_cons hn, (List.getElem?_eq_some_iff.1 he).2]
  rfl

/-- `get(kv, k)`. -/
theorem wp_get (kv : GoSlice) (L : List Entry) (k : w64) :
    {{ (kv ↦*□ L : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.get))
        (Val #kv)) (Val #k))
    {{ RET #(getE L k); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z kv.len ∧
        getE (L.drop (sint.nat i)) k = getE L k⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, Hl.2, by rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z kv.len := Hif
    list_elem L (sint.nat i) as e
    icases ownSlice_elem_acc (sint.Z i) e kv DFrac.discard L Hi.1 He_lookup $$ Hp with ⟨#He, -⟩
    rcases e with ⟨ek, ev⟩
    iStructNamed He
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z kv.len) = True := eq_true ⟨Hi.1, hlt⟩
    simp only [hb, ite_true]
    wp_auto
    have hg := getE_drop L k (sint.nat i) _ He_lookup
    by_cases hk : ek = k
    · rw [decide_eq_true hk]
      wp_auto
      simp only [hb, ite_true]
      wp_auto
      rw [forPostcondition_unseal]; unfold forPostconditionDef
      iright; iright; iright; ileft
      iexists #()
      isplitr
      · ipureintro; rfl
      dsimp only
      wp_auto
      have e : ev = getE L k := by rw [← Hi.2.2, hg]; simp [hk]
      rw [e]
      iapply HΦ
      itrivial
    · rw [decide_eq_false hk]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, ← Hi.2.2, hg]
      simp [hk]
  · have hn : sint.nat i = L.length := by
      have : ¬ sint.Z i < sint.Z kv.len := Hif
      rw [Hl.1]; word
    have e : ([] : GoString) = getE L k := by
      rw [← Hi.2.2, hn, List.drop_length]; rfl
    rw [e]
    iapply HΦ
    itrivial

theorem filter_take_succ {α : Type} (L : List α) (p : α → Bool) (n : Nat) (e : α)
    (he : L[n]? = some e) :
    (L.take (n + 1)).filter p = (L.take n).filter p ++ (if p e then [e] else []) := by
  rw [List.take_add_one, he, Option.toList_some, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]

/-- `set(kv, k, v)`: a new slice. -/
theorem wp_set (kv : GoSlice) (L : List Entry) (k : w64) (v : GoString) (hL : L.length < 2 ^ 62) :
    {{ (kv ↦*□ L : IProp GF) }}
      (App (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.set))
        (Val #kv)) (Val #k)) (Val #v))
    {{ (r : GoSlice), RET #r; r ↦* setE L k v }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make3 (V := Entry) (W64 0) (kv.len + W64 1) ⟨by decide, by word⟩
    as %q ⟨Hq, Hqc, -⟩
  (try wp_auto)
  ihave HI : (∃ (i : w64) (r : GoSlice), "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ r ∗
      "Hr" ∷ r ↦* (L.take (sint.nat i)).filter (fun e => !decide (e.K' = k)) ∗
      "Hrc" ∷ ownSliceCap Entry r (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z kv.len⌝ : IProp GF) $$ [i r Hq Hqc]
  · iexists W64 0, q
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
      List.replicate_zero]
    iframe
    ipureintro; exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z kv.len := Hif
    list_elem L (sint.nat i) as e
    icases ownSlice_elem_acc (sint.Z i) e kv DFrac.discard L Hi.1 He_lookup $$ Hp with ⟨#He, -⟩
    have hft := filter_take_succ L (fun e => !decide (e.K' = k)) (sint.nat i) e He_lookup
    rcases e with ⟨ek, ev⟩
    iStructNamed He
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z kv.len) = True := eq_true ⟨Hi.1, hlt⟩
    simp only [hb, ite_true]
    wp_auto
    by_cases hk : ek = k
    · rw [decide_eq_true hk]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, r
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, hft]
      simp only [hk, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · rw [decide_eq_false hk]
      wp_auto
      simp only [hb, ite_true]
      wp_auto
      wp_apply wp_slice_literal (V := Entry) [Entry.mk ek ev]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hr $Hrc $Hsl1] as %r' ⟨Hr, Hrc, -⟩
      wp_for_post
      iframe
      iexists i + W64 1, r'
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, hft]
      simp only [hk, decide_false, Bool.not_false, ↓reduceIte]
      iframe
      ipureintro; exact ⟨by word, by word⟩
  · have hn : sint.nat i = L.length := by
      have : ¬ sint.Z i < sint.Z kv.len := Hif
      rw [Hl.1]; word
    rw [hn, List.take_length]
    unfold setE
    by_cases hv : v = []
    · subst hv
      wp_auto
      iapply HΦ
      simp
      iexact Hr
    · rw [decide_eq_false hv]
      wp_auto
      wp_apply wp_slice_literal (V := Entry) [Entry.mk k v]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hr $Hrc $Hsl1] as %r' ⟨Hr, Hrc, -⟩
      iapply HΦ
      simp only [hv, ↓reduceIte]
      iexact Hr

theorem eraseIdx_take_succ {α : Type} (P : List α) (i j : Nat) (x : α) (hx : P[j]? = some x)
    (hij : j ≠ i) : (P.take (j + 1)).eraseIdx i = (P.take j).eraseIdx i ++ [x] := by
  rw [List.take_add_one, hx, Option.toList_some]
  have hj : j < P.length := (List.getElem?_eq_some_iff.1 hx).1
  have hl : (P.take j).length = j := by simp; omega
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rw [List.eraseIdx_of_length_le (by simp; omega), List.eraseIdx_of_length_le (by omega)]
  · rw [List.eraseIdx_append_of_lt_length (by omega)]

theorem eraseIdx_take_self {α : Type} (P : List α) (i : Nat) :
    (P.take (i + 1)).eraseIdx i = (P.take i).eraseIdx i := by
  rw [List.eraseIdx_of_length_le (l := P.take i) (by simp [Nat.min_le_left])]
  rcases Nat.lt_or_ge i P.length with h | h
  · rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
      List.eraseIdx_append_of_length_le (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt h), Nat.sub_self,
      List.eraseIdx_cons_zero, List.append_nil]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
      List.eraseIdx_of_length_le (by omega)]

/-- `without(p, i)`: a fresh slice, `p` without its element `i`. -/
theorem wp_without (p : GoSlice) (P : List In) (i : w64) (hi : 0 ≤ sint.Z i) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.without)) (Val #p))
        (Val #i))
    {{ (q : GoSlice), RET #q; q ↦* P.eraseIdx (sint.nat i) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make3 (V := In) (W64 0) p.len ⟨by decide, Hl.2⟩ as %q ⟨Hq, Hqc, -⟩
  (try wp_auto)
  ihave HI : (∃ (j : w64) (qq : GoSlice), "j" ∷ j_ptr ↦ j ∗ "r" ∷ r_ptr ↦ qq ∗
      "Hq" ∷ qq ↦* (P.take (sint.nat j)).eraseIdx (sint.nat i) ∗
      "Hqc" ∷ ownSliceCap In qq (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z p.len⌝ : IProp GF) $$ [j r Hq Hqc]
  · iexists W64 0, q
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.eraseIdx_nil,
      List.replicate_zero]
    iframe
    ipureintro; exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hj : sint.Z j < sint.Z p.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    by_cases hji : j = i
    · subst hji
      simp only [decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, qq
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, eraseIdx_take_self]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · rw [decide_eq_false hji]
      simp only [Bool.not_false]
      wp_auto
      list_elem P (sint.nat j) as e
      rw [ite_eq_left ⟨Hj.1, hj⟩]
      wp_apply wp_load_slice_index p (sint.Z j) P DFrac.discard e Hj.1 $$ [$Hp] with -
      · ipureintro; exact He_lookup
      (try wp_auto)
      wp_apply wp_slice_literal (V := In) [e]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hq $Hqc $Hsl1] as %qq' ⟨Hq, Hqc, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, qq'
      have hne : sint.nat j ≠ sint.nat i := fun h => hji (by word)
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
        eraseIdx_take_succ P _ _ e He_lookup hne]
      iframe
      ipureintro; exact ⟨by word, by word⟩
  · have hn : sint.nat j = P.length := by
      have : ¬ sint.Z j < sint.Z p.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    rw [hn, List.take_length]
    iframe
theorem wp_pushIn (p : GoSlice) (P : List In) (v : In) (hP : P.length < 2 ^ 60) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.pushIn)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := In) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ v $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq


/-- `hasPrefix(s, p)`. -/
theorem wp_hasPrefix (s q : GoString) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.hasPrefix))
        (Val #s)) (Val #q))
    {{ RET #(decide (q <+: s)); True }} := by
  wp_start as -
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hq
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hs
  wp_if_destruct
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    have hqs : q.length ≤ s.length := by
      have h1 : sint.Z (W64 (q.length : Int)) = q.length := by word
      have h2 : sint.Z (W64 (s.length : Int)) = s.length := by word
      omega
    rw [ite_eq_left ⟨by word, by word, by word⟩]
    wp_auto
    have e : decide (List.take (sint.nat (W64 (q.length : Int)) - 0) (List.drop 0 s) = q) =
        decide (q <+: s) := by
      rw [show sint.nat (W64 (q.length : Int)) = q.length by word, Nat.sub_zero, List.drop_zero]
      apply decide_eq_decide.2
      rw [List.prefix_iff_eq_take]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [e]
    iapply HΦ
    itrivial
  · have hn : ¬ q <+: s := by
      intro h
      have := h.length_le
      have h1 : sint.Z (W64 (q.length : Int)) = q.length := by word
      have h2 : sint.Z (W64 (s.length : Int)) = s.length := by word
      omega
    rw [decide_eq_false hn]
    iapply HΦ
    itrivial

theorem count_take_succ (P : List EIn) (x : EIn) (n : Nat) (e : EIn) (he : P[n]? = some e) :
    (P.take (n + 1)).count x = (P.take n).count x + (if e = x then 1 else 0) := by
  rw [List.take_add_one, he, Option.toList_some, List.count_append, List.count_singleton]
  by_cases h : e = x <;> simp [h]

/-- `countIn(p, x)`. -/
theorem wp_countIn (p : GoSlice) (P : List EIn) (x : EIn) :
    {{ (p ↦*□ P.map inE : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.countIn))
        (Val #p)) (Val #(inE x)))
    {{ RET #(W64 (P.count x)); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ W64 ((P.take (sint.nat i)).count x) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len⌝ : IProp GF) $$ [i n]
  · iexists W64 0
    iframe
    ipureintro; exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as e
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len) = True := eq_true ⟨Hi.1, hlt⟩
    simp only [hb, ite_true]
    wp_apply wp_load_slice_index p (sint.Z i) (P.map inE) DFrac.discard (inE e) Hi.1 $$ [$Hp]
      with -
    · ipureintro; rw [List.getElem?_map, He_lookup]; rfl
    by_cases hex : e = x
    · have h1 : (inE e).Op' = (inE x).Op' := by rw [hex]
      have h2 : (inE e).K' = (inE x).K' := by rw [hex]
      have h3 : (inE e).N' = (inE x).N' := by rw [hex]
      have h4 : (inE e).V' = (inE x).V' := by rw [hex]
      rw [decide_eq_true h1]
      wp_auto
      rw [decide_eq_true h2]
      wp_auto
      rw [decide_eq_true h3]
      wp_auto
      rw [decide_eq_true h4]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, count_take_succ P x _ e He_lookup,
        if_pos hex,
        show W64 ((P.take (sint.nat i)).count x : Int) + W64 1 =
          W64 (((P.take (sint.nat i)).count x + 1 : Nat) : Int) by word]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · have hne : inE e ≠ inE x := fun h => hex (inE_inj h)
      by_cases h1 : (inE e).Op' = (inE x).Op'
      · rw [decide_eq_true h1]
        wp_auto
        by_cases h2 : (inE e).K' = (inE x).K'
        · rw [decide_eq_true h2]
          wp_auto
          by_cases h3 : (inE e).N' = (inE x).N'
          · rw [decide_eq_true h3]
            wp_auto
            have h4 : (inE e).V' ≠ (inE x).V' := by
              intro h4; apply hne
              revert h1 h2 h3 h4; cases inE e; cases inE x; simp_all
            rw [decide_eq_false h4]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1
            rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, count_take_succ P x _ e He_lookup,
          if_neg hex, Nat.add_zero]
            iframe
            ipureintro; exact ⟨by word, by word⟩
          · rw [decide_eq_false h3]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1
            rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, count_take_succ P x _ e He_lookup,
          if_neg hex, Nat.add_zero]
            iframe
            ipureintro; exact ⟨by word, by word⟩
        · rw [decide_eq_false h2]
          wp_auto
          wp_for_post
          iframe
          iexists i + W64 1
          rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, count_take_succ P x _ e He_lookup,
          if_neg hex, Nat.add_zero]
          iframe
          ipureintro; exact ⟨by word, by word⟩
      · rw [decide_eq_false h1]
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, count_take_succ P x _ e He_lookup,
          if_neg hex, Nat.add_zero]
        iframe
        ipureintro; exact ⟨by word, by word⟩
  · have hn : sint.nat i = P.length := by
      have : ¬ sint.Z i < sint.Z p.len := Hif
      have := Hl.1; simp only [List.length_map] at this; rw [this]; word
    rw [hn, List.take_length]
    iapply HΦ
    itrivial

theorem all_take_succ {α : Type} (L : List α) (f : α → Bool) (n : Nat) (e : α)
    (he : L[n]? = some e) : (L.take (n + 1)).all f = ((L.take n).all f && f e) := by
  rw [List.take_add_one, he, Option.toList_some, List.all_append]
  simp

theorem all_false_of {α : Type} (L : List α) (f : α → Bool) (n : Nat) (e : α)
    (he : L[n]? = some e) (h : f e = false) : L.all f = false := by
  rw [List.all_eq_false]
  exact ⟨e, List.mem_of_getElem? he, by simp [h]⟩

theorem count_W64_inj (A B : List EIn) (x : EIn) (hA : A.length < 2 ^ 63) (hB : B.length < 2 ^ 63)
    (h : W64 (A.count x : Int) = W64 (B.count x : Int)) : A.count x = B.count x := by
  have h1 := List.count_le_length (a := x) (l := A)
  have h2 := List.count_le_length (a := x) (l := B)
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt] at this
  omega

theorem len_ne {α β : Type} (a b : GoSlice) (A : List α) (B : List β)
    (hA : A.length = sint.nat a.len) (hB : B.length = sint.nat b.len) (ha : 0 ≤ sint.Z a.len)
    (hb : 0 ≤ sint.Z b.len) (hab : ¬ a.len = b.len) : A.length ≠ B.length := by
  intro h; apply hab; rw [hA, hB] at h; word

/-- `samePend(a, b)`. -/
theorem wp_samePend (a b : GoSlice) (A B : List EIn) :
    {{ (a ↦*□ A.map inE ∗ b ↦*□ B.map inE : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.samePend))
        (Val #a)) (Val #b))
    {{ RET #(samePendG A B); True }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  simp only [List.length_map] at HA HB
  wp_auto
  by_cases hab : ¬ a.len = b.len
  · rw [decide_eq_false hab]
    wp_auto
    have : samePendG A B = false := by
      simp only [samePendG, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      left; exact len_ne a b A B HA.1 HB.1 HA.2 HB.2 hab
    rw [this]
    iapply HΦ
    itrivial
  have hab := Classical.not_not.mp hab
  rw [decide_eq_true hab]
  wp_auto
  have hAB : A.length = B.length := by rw [HA.1, HB.1, hab]
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
        (A.take (sint.nat i)).all (fun x => A.count x == B.count x) = true⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, HA.2, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z a.len := Hif
    list_elem A (sint.nat i) as e
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len) = True := eq_true ⟨Hi.1, hlt⟩
    simp only [hb, ite_true]
    wp_apply wp_load_slice_index a (sint.Z i) (A.map inE) DFrac.discard (inE e) Hi.1 $$ [$Ha]
      with -
    · ipureintro; rw [List.getElem?_map, He_lookup]; rfl
    wp_apply wp_countIn a A e $$ [$Ha]
    simp only [hb, ite_true]
    wp_apply wp_load_slice_index a (sint.Z i) (A.map inE) DFrac.discard (inE e) Hi.1 $$ [$Ha]
      with -
    · ipureintro; rw [List.getElem?_map, He_lookup]; rfl
    wp_apply wp_countIn b B e $$ [$Hb]
    by_cases hc : A.count e = B.count e
    · rw [hc]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
        all_take_succ A _ _ e He_lookup, Hi.2.2]
      simp [hc]
    · have hw : W64 (A.count e : Int) ≠ W64 (B.count e : Int) := fun h =>
        hc (count_W64_inj A B e (by rw [HA.1]; word) (by rw [HB.1]; word) h)
      rw [decide_eq_false hw]
      wp_auto
      rw [forPostcondition_unseal]; unfold forPostconditionDef
      iright; iright; iright; ileft
      iexists #()
      isplitr
      · ipureintro; rfl
      dsimp only
      wp_auto
      have : samePendG A B = false := by
        simp only [samePendG, Bool.and_eq_false_iff]
        right
        exact all_false_of A _ _ e He_lookup (by simp [hc])
      rw [this]
      iapply HΦ
      itrivial
  · have hn : sint.nat i = A.length := by
      have : ¬ sint.Z i < sint.Z a.len := Hif
      rw [HA.1]; word
    have : samePendG A B = true := by
      simp only [samePendG, Bool.and_eq_true, beq_iff_eq]
      refine ⟨hAB, ?_⟩
      have := Hi.2.2; rwa [hn, List.take_length] at this
    rw [this]
    iapply HΦ
    itrivial

/-- `sameEntries(a, b)`. -/
theorem wp_sameEntries (a b : GoSlice) (A B : List Entry) :
    {{ (a ↦*□ A ∗ b ↦*□ B : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.sameEntries))
        (Val #a)) (Val #b))
    {{ RET #(sameEntriesG A B); True }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  wp_auto
  by_cases hab : ¬ a.len = b.len
  · rw [decide_eq_false hab]
    wp_auto
    have : sameEntriesG A B = false := by
      simp only [sameEntriesG, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      left; exact len_ne a b A B HA.1 HB.1 HA.2 HB.2 hab
    rw [this]
    iapply HΦ
    itrivial
  have hab := Classical.not_not.mp hab
  rw [decide_eq_true hab]
  wp_auto
  have hAB : A.length = B.length := by rw [HA.1, HB.1, hab]
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
        (A.take (sint.nat i)).all (fun e => decide (getE B e.K' = e.V')) = true⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, HA.2, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z a.len := Hif
    list_elem A (sint.nat i) as e
    icases ownSlice_elem_acc (sint.Z i) e a DFrac.discard A Hi.1 He_lookup $$ Ha with ⟨#He, -⟩
    rcases e with ⟨ek, ev⟩
    iStructNamed He
    have hall := all_take_succ A (fun e => decide (getE B e.K' = e.V')) _ _ He_lookup
    have hfalse := all_false_of A (fun e => decide (getE B e.K' = e.V')) _ _ He_lookup
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len) = True := eq_true ⟨Hi.1, hlt⟩
    simp only [hb, ite_true]
    wp_auto
    wp_apply wp_get b B ek $$ [$Hb]
    simp only [hb, ite_true]
    wp_auto
    by_cases hc : getE B ek = ev
    · rw [decide_eq_true hc]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, hall, Hi.2.2]
      simp [hc]
    · rw [decide_eq_false hc]
      wp_auto
      rw [forPostcondition_unseal]; unfold forPostconditionDef
      iright; iright; iright; ileft
      iexists #()
      isplitr
      · ipureintro; rfl
      dsimp only
      wp_auto
      have : sameEntriesG A B = false := by
        simp only [sameEntriesG, Bool.and_eq_false_iff]
        right
        exact hfalse (by simp [hc])
      rw [this]
      iapply HΦ
      itrivial
  · have hn : sint.nat i = A.length := by
      have : ¬ sint.Z i < sint.Z a.len := Hif
      rw [HA.1]; word
    have : sameEntriesG A B = true := by
      simp only [sameEntriesG, Bool.and_eq_true, beq_iff_eq]
      refine ⟨hAB, ?_⟩
      have := Hi.2.2; rwa [hn, List.take_length] at this
    rw [this]
    iapply HΦ
    itrivial

/-- `sameConfig(x, y)`. -/
theorem wp_sameConfig (x y : Config) (g g' : GC) :
    {{ (cfgRep x g ∗ cfgRep y g' : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.sameConfig))
        (Val #x)) (Val #y))
    {{ RET #(sameConfigG g g'); True }} := by
  unfold cfgRep
  wp_start as ⟨⟨#Hxk, #Hxp⟩, ⟨#Hyk, #Hyp⟩⟩
  wp_auto
  wp_apply wp_sameEntries x.Kv' y.Kv' g.1 g'.1 $$ [$Hxk $Hyk]
  cases he : sameEntriesG g.1 g'.1
  · wp_auto
    have : sameConfigG g g' = false := by simp [sameConfigG, he]
    rw [this]
    iapply HΦ
    itrivial
  · wp_auto
    wp_apply wp_samePend x.Pend' y.Pend' g.2 g'.2 $$ [$Hxp $Hyp]
    have : sameConfigG g g' = samePendG g.2 g'.2 := by simp [sameConfigG, he]
    rw [this]
    iapply HΦ
    itrivial

theorem idx_succ (i n : w64) (h0 : 0 ≤ sint.Z i) (hlt : sint.Z i < sint.Z n) :
    0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z n ∧
      sint.nat (i + W64 1) = sint.nat i + 1 := by
  refine ⟨by word, by word, by word⟩

theorem idx_end (i n : w64) (h0 : 0 ≤ sint.Z i) (hle : sint.Z i ≤ sint.Z n)
    (h : ¬ sint.Z i < sint.Z n) : sint.nat i = sint.nat n := by word

theorem cfgsRep_nil : ⊢ cfgsRep (GF := GF) [] := by
  unfold cfgsRep
  iintro !> %p %hp
  cases hp

theorem cfgsRep_app (P Q : List (Config × GC)) :
    cfgsRep (GF := GF) P ∗ cfgsRep Q ⊢ cfgsRep (P ++ Q) := by
  unfold cfgsRep
  iintro ⟨#HP, #HQ⟩ !> %p %hp
  rcases List.mem_append.1 hp with h | h
  · iapply HP; ipureintro; exact h
  · iapply HQ; ipureintro; exact h

theorem cfgsRep_mem (P : List (Config × GC)) (p : Config × GC) (h : p ∈ P) :
    cfgsRep (GF := GF) P ⊢ cfgRep p.1 p.2 := by
  unfold cfgsRep
  iintro #HP
  iapply HP; ipureintro; exact h

theorem cfgsRep_single (x : Config) (g : GC) : cfgRep (GF := GF) x g ⊢ cfgsRep [(x, g)] := by
  unfold cfgsRep
  iintro #H !> %p %hp
  simp only [List.mem_singleton] at hp
  subst hp
  iexact H

theorem any_take_succ {α : Type} (L : List α) (f : α → Bool) (n : Nat) (e : α)
    (he : L[n]? = some e) : (L.take (n + 1)).any f = ((L.take n).any f || f e) := by
  rw [List.take_add_one, he, Option.toList_some, List.any_append]
  simp

theorem any_true_of {α : Type} (L : List α) (f : α → Bool) (n : Nat) (e : α)
    (he : L[n]? = some e) (h : f e = true) : L.any f = true := by
  rw [List.any_eq_true]
  exact ⟨e, List.mem_of_getElem? he, h⟩

/-- `member(s, c)`. -/
theorem wp_member (s : GoSlice) (dq : DFrac) (P : List (Config × GC)) (c : Config) (g : GC) :
    {{ (s ↦*{dq} P.map Prod.fst ∗ cfgsRep P ∗ cfgRep c g : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.member))
        (Val #s)) (Val #c))
    {{ RET #(memberG (P.map Prod.snd) g); s ↦*{dq} P.map Prod.fst }} := by
  wp_start as ⟨Hs, #HP, #Hc⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_map] at Hl
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len ∧
        ((P.map Prod.snd).take (sint.nat i)).any (fun x => sameConfigG x g) = false⌝ : IProp GF)
      $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, Hl.2, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z s.len := Hif
    list_elem P (sint.nat i) as pe
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len) = True := eq_true ⟨Hi.1, hlt⟩
    simp only [hb, ite_true]
    wp_apply wp_load_slice_index s (sint.Z i) (P.map Prod.fst) dq pe.1 Hi.1 $$ [$Hs] as Hs
    · ipureintro; rw [List.getElem?_map, Hpe_lookup]; rfl
    ihave #Hpe := cfgsRep_mem P pe (List.mem_of_getElem? Hpe_lookup) $$ HP
    wp_apply wp_sameConfig pe.1 c pe.2 g $$ [$Hpe $Hc]
    have hsnd : (P.map Prod.snd)[sint.nat i]? = some pe.2 := by
      rw [List.getElem?_map, Hpe_lookup]; rfl
    cases hsc : sameConfigG pe.2 g
    · wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      obtain ⟨b1, b2, b3⟩ := idx_succ i s.len Hi.1 hlt
      refine ⟨b1, b2, ?_⟩
      rw [b3, any_take_succ _ _ _ _ hsnd, Hi.2.2, hsc]
    · wp_auto
      rw [forPostcondition_unseal]; unfold forPostconditionDef
      iright; iright; iright; ileft
      iexists #()
      isplitr
      · ipureintro; rfl
      dsimp only
      wp_auto
      have : memberG (P.map Prod.snd) g = true := any_true_of _ _ _ _ hsnd hsc
      rw [this]
      iapply HΦ
      iexact Hs
  · have hn : sint.nat i = P.length := by
      have : ¬ sint.Z i < sint.Z s.len := Hif
      rw [Hl.1]; exact idx_end i s.len Hi.1 Hi.2.1 this
    have : memberG (P.map Prod.snd) g = false := by
      have := Hi.2.2
      rwa [hn, ← List.length_map (f := Prod.snd), List.take_length] at this
    rw [this]
    iapply HΦ
    iexact Hs

theorem addAllG_snoc (S cs : List GC) (c : GC) :
    addAllG S (cs ++ [c]) = if memberG (addAllG S cs) c then addAllG S cs else addAllG S cs ++ [c] := by
  unfold addAllG; rw [List.foldl_append]; rfl

/-- `addAll(s, cs)`: `s` with `cs`'s configurations it lacks appended. -/
theorem wp_addAll (s : GoSlice) (S : List (Config × GC)) (cs : GoSlice) (C : List (Config × GC)) :
    {{ (s ↦* S.map Prod.fst ∗ ownSliceCap Config s (DFrac.own 1) ∗ cfgsRep S ∗
        cs ↦*□ C.map Prod.fst ∗ cfgsRep C : IProp GF) }}
      (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.addAll))
        (Val #s)) (Val #cs))
    {{ (s' : GoSlice), RET #s'; ∃ S' : List (Config × GC),
        ⌜S'.map Prod.snd = addAllG (S.map Prod.snd) (C.map Prod.snd)⌝ ∗
        s' ↦* S'.map Prod.fst ∗ ownSliceCap Config s' (DFrac.own 1) ∗ cfgsRep S' }} := by
  wp_start as ⟨Hs, Hsc, #HS, #Hcs, #HC⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hcs
  simp only [List.length_map] at Hl
  wp_auto
  ihave HI : (∃ (i : w64) (s1 : GoSlice) (S1 : List (Config × GC)), "i" ∷ i_ptr ↦ i ∗
      "s" ∷ s_ptr ↦ s1 ∗ "Hs" ∷ s1 ↦* S1.map Prod.fst ∗
      "Hsc" ∷ ownSliceCap Config s1 (DFrac.own 1) ∗ "#HS1" ∷ cfgsRep S1 ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z cs.len ∧
        S1.map Prod.snd = addAllG (S.map Prod.snd) ((C.map Prod.snd).take (sint.nat i))⌝ : IProp GF)
      $$ [i s Hs Hsc]
  · iexists W64 0, s, S
    iframe
    isplitl []
    · iexact HS
    ipureintro
    exact ⟨by decide, Hl.2, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z cs.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    list_elem C (sint.nat i) as ce
    have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z cs.len) = True := eq_true ⟨Hi.1, hlt⟩
    have hsnd : (C.map Prod.snd)[sint.nat i]? = some ce.2 := by
      rw [List.getElem?_map, Hce_lookup]; rfl
    obtain ⟨b1, b2, b3⟩ := idx_succ i cs.len Hi.1 hlt
    simp only [hb, ite_true]
    wp_apply wp_load_slice_index cs (sint.Z i) (C.map Prod.fst) DFrac.discard ce.1 Hi.1 $$ [$Hcs]
      with -
    · ipureintro; rw [List.getElem?_map, Hce_lookup]; rfl
    ihave #Hce := cfgsRep_mem C ce (List.mem_of_getElem? Hce_lookup) $$ HC
    wp_apply wp_member s1 (DFrac.own 1) S1 ce.1 ce.2 $$ [Hs] as Hs
    · iframe Hs
      isplitl []
      · iexact HS1
      iexact Hce
    have hstep : addAllG (S.map Prod.snd) ((C.map Prod.snd).take (sint.nat i + 1)) =
        if memberG (S1.map Prod.snd) ce.2 then S1.map Prod.snd else S1.map Prod.snd ++ [ce.2] := by
      rw [List.take_add_one, hsnd, Option.toList_some, addAllG_snoc, ← Hi.2.2]
    cases hm : memberG (S1.map Prod.snd) ce.2
    · wp_auto
      simp only [hb, ite_true]
      wp_apply wp_load_slice_index cs (sint.Z i) (C.map Prod.fst) DFrac.discard ce.1 Hi.1
        $$ [$Hcs] with -
      · ipureintro; rw [List.getElem?_map, Hce_lookup]; rfl
      wp_apply wp_slice_literal (V := Config) [ce.1]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hsc $Hsl1] as %s2 ⟨Hs2, Hsc2, -⟩
      wp_for_post
      iframe
      ihave #Hce1 := cfgsRep_single ce.1 ce.2 $$ Hce
      ihave #HS2 := cfgsRep_app S1 [ce] $$ [$HS1 $Hce1]
      iexists i + W64 1, s2, S1 ++ [ce]
      iframe
      simp only [List.map_append, List.map_cons, List.map_nil]
      iframe
      isplitl []
      · iexact HS2
      ipureintro
      refine ⟨b1, b2, ?_⟩
      rw [b3, hstep, hm]
      rfl
    · wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, s1, S1
      iframe
      isplitl []
      · iexact HS1
      ipureintro
      refine ⟨b1, b2, ?_⟩
      rw [b3, hstep, hm]
      rfl
  · have hn : sint.nat i = C.length := by
      have : ¬ sint.Z i < sint.Z cs.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      rw [Hl.1]; exact idx_end i cs.len Hi.1 Hi.2.1 this
    iapply HΦ
    iexists S1
    iframe
    isplitr
    · ipureintro
      rw [Hi.2.2, hn, ← List.length_map (f := Prod.snd), List.take_length]
    iexact HS1

theorem map_eraseIdx' {α β : Type} (f : α → β) (l : List α) (j : Nat) :
    (l.eraseIdx j).map f = (l.map f).eraseIdx j := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih => cases j <;> simp_all [List.eraseIdx]

/-- The configurations `reads` returns from firing the pending put at `j`. -/
def readsAt (m : Nat) (g : GC) (k : w64) (out : GoString) (j : Nat) : List GC :=
  match g.2[j]? with
  | some p =>
    if (inE p).K' = k ∧ (inE p).V' <+: out then
      readsG m (setE g.1 k (inE p).V', g.2.eraseIdx j) (k + 1) (out.drop (inE p).V'.length)
    else []
  | none => []

theorem readsG_succ (m : Nat) (g : GC) (k : w64) (out : GoString) :
    readsG (m + 1) g k out =
      (if getE g.1 k <+: out then readsG m g (k + 1) (out.drop (getE g.1 k).length) else []) ++
      (List.range g.2.length).flatMap (readsAt m g k out) := rfl

/-- `reads(c, k, last, out)`, `m` keys (`k..last`). -/
theorem wp_reads (m : Nat) : ∀ (c : Config) (g : GC) (k last : w64) (out : GoString),
    k.toNat + m = last.toNat + 1 → last.toNat + 1 < 2 ^ 64 → g.1.length + m < 2 ^ 62 →
    {{ (cfgRep c g : IProp GF) }}
      (App (App (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.reads))
        (Val #c)) (Val #k)) (Val #last)) (Val #out))
    {{ (r : GoSlice), RET #r; ∃ R : List (Config × GC),
        ⌜R.map Prod.snd = readsG m g k out⌝ ∗ r ↦* R.map Prod.fst ∗ cfgsRep R }} := by
  induction m with
  | zero =>
    intro c g k last out hm hl hg
    wp_start as #Hc
    wp_auto
    have hlk : uint.Z last < uint.Z k := by
      have : uint.Z last = last.toNat := rfl
      have : uint.Z k = k.toNat := rfl
      omega
    rw [decide_eq_true hlk]
    wp_auto
    by_cases ho : out = []
    · subst ho
      wp_auto
      wp_apply wp_slice_literal (V := Config) [c]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      iapply HΦ
      iexists [(c, g)]
      ihave #HR := cfgsRep_single c g $$ Hc
      isplitr
      · ipureintro; simp [readsG]
      simp only [List.map_cons, List.map_nil]
      iframe
      iexact HR
    · rw [decide_eq_false ho]
      wp_auto
      iapply HΦ
      iexists []
      isplitr
      · ipureintro; simp [readsG, ho]
      isplitr
      · simp only [List.map_nil]; iapply ownSlice_nil
      iapply cfgsRep_nil
  | succ m ih =>
    intro c g k last out hm hl hg
    unfold cfgRep
    wp_start as ⟨#Hkv, #Hpd⟩
    wp_auto
    have hkl : ¬ uint.Z last < uint.Z k := by
      have : uint.Z last = last.toNat := rfl
      have : uint.Z k = k.toNat := rfl
      omega
    rw [decide_eq_false hkl]
    wp_auto
    wp_apply wp_get c.Kv' g.1 k $$ [$Hkv]
    wp_apply wp_hasPrefix out (getE g.1 k)
    have hk1 : k + W64 1 = k + 1 := rfl
    have hk1n : (k + 1).toNat + m = last.toNat + 1 := by
      have : (k + 1).toNat = k.toNat + 1 := by bv_omega
      omega
    ihave Hnil : (slice.nil ↦* ([] : List Config) : IProp GF) $$ []
    · iapply ownSlice_nil
    ihave Hnilc : (ownSliceCap Config slice.nil (DFrac.own 1) : IProp GF) $$ []
    · iapply ownSliceCap_nil
    ihave #HR0 := cfgsRep_nil (GF := GF)
    wp_if_destruct
    · have hpv : getE g.1 k <+: out := Hif
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlv
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlo
      have hvo := hpv.length_le
      have e1 : sint.nat (W64 ((getE g.1 k).length : Int)) = (getE g.1 k).length := by word
      have e2 : sint.nat (W64 (out.length : Int)) = out.length := by word
      rw [ite_eq_left ⟨by word, by word, by word⟩, e1, e2,
        List.take_of_length_le (by simp <;> omega)]
      wp_apply ih c g (k + W64 1) last _ (by rw [hk1]; exact hk1n) hl (by omega) as %r1 Hr1
      · unfold cfgRep; iframe #
      icases Hr1 with ⟨%R1, %HR1, Hr1, #HR1c⟩
      rw [show (zero_val GoSlice) = slice.nil from rfl]
      wp_apply wp_slice_append $$ [$Hnil $Hnilc $Hr1] as %r2 ⟨Hr2, Hr2c, -⟩
      ihave Hst : (∃ (r0 : GoSlice) (R0 : List (Config × GC)), r_ptr ↦ r0 ∗
          r0 ↦* R0.map Prod.fst ∗ ownSliceCap Config r0 (DFrac.own 1) ∗ cfgsRep R0 ∗
          ⌜R0.map Prod.snd = if getE g.1 k <+: out then
            readsG m g (k + 1) (out.drop (getE g.1 k).length) else []⌝ : IProp GF) $$ [r Hr2 Hr2c]
      · iexists r2, R1
        iframe
        isplitl []
        · iexact HR1c
        ipureintro
        rw [if_pos hpv, HR1, hk1]
      icases Hst with ⟨%r0, %R0, Hr, Hr0, Hr0c, #HR0', %HR0p⟩
      ihave %Hpl := ownSlice_len _ _ _ $$ Hpd
      simp only [List.length_map] at Hpl
      ihave HI : (∃ (i : w64) (r1 : GoSlice) (R1 : List (Config × GC)), "i" ∷ i_ptr ↦ i ∗
          "r" ∷ r_ptr ↦ r1 ∗ "Hr" ∷ r1 ↦* R1.map Prod.fst ∗
          "Hrc" ∷ ownSliceCap Config r1 (DFrac.own 1) ∗ "#HR1" ∷ cfgsRep R1 ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z c.Pend'.len ∧
            R1.map Prod.snd = (if getE g.1 k <+: out then
              readsG m g (k + 1) (out.drop (getE g.1 k).length) else []) ++
              (List.range (sint.nat i)).flatMap (readsAt m g k out)⌝ : IProp GF) $$ [i Hr Hr0 Hr0c]
      · iexists W64 0, r0, R0
        iframe
        isplitl []
        · iexact HR0'
        ipureintro
        exact ⟨by decide, Hpl.2, by rw [HR0p, show sint.nat (W64 0) = 0 from rfl]; simp⟩
      wp_for HI
      wp_if_destruct
      · have hlt : sint.Z i < sint.Z c.Pend'.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        list_elem g.2 (sint.nat i) as pi
        obtain ⟨b1, b2, b3⟩ := idx_succ i c.Pend'.len Hi.1 hlt
        have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z c.Pend'.len) = True := eq_true ⟨Hi.1, hlt⟩
        simp only [hb, ite_true]
        wp_apply wp_load_slice_index c.Pend' (sint.Z i) (g.2.map inE) DFrac.discard (inE pi) Hi.1
          $$ [$Hpd] with -
        · ipureintro; rw [List.getElem?_map, Hpi_lookup]; rfl
        have hra : readsAt m g k out (sint.nat i) =
            if (inE pi).K' = k ∧ (inE pi).V' <+: out then
              readsG m (setE g.1 k (inE pi).V', g.2.eraseIdx (sint.nat i)) (k + 1)
                (out.drop (inE pi).V'.length) else [] := by
          simp only [readsAt, Hpi_lookup]
        have hrange : (List.range (sint.nat i + 1)).flatMap (readsAt m g k out) =
            (List.range (sint.nat i)).flatMap (readsAt m g k out) ++ readsAt m g k out (sint.nat i) := by
          rw [List.range_succ, List.flatMap_append]; simp
        by_cases hKP : (inE pi).K' = k ∧ (inE pi).V' <+: out
        · obtain ⟨hK, hP⟩ := hKP
          rw [decide_eq_true hK]
          wp_auto
          wp_apply wp_hasPrefix out (inE pi).V'
          rw [decide_eq_true hP]
          wp_auto
          wp_apply wp_set c.Kv' g.1 k (inE pi).V' (by omega) $$ [$Hkv] as %s1 Hs1
          wp_apply wp_without c.Pend' (g.2.map inE) i Hi.1 $$ [$Hpd] as %s2 Hs2
          iapply fupd_wp
          imod ownSlice_persist _ _ _ $$ Hs1 with #Hs1
          imod ownSlice_persist _ _ _ $$ Hs2 with #Hs2
          imodintro
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlv
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlo
          have hvo := hP.length_le
          have e1 : sint.nat (W64 ((inE pi).V'.length : Int)) = (inE pi).V'.length := by word
          have e2 : sint.nat (W64 (out.length : Int)) = out.length := by word
          rw [ite_eq_left ⟨by word, by word, by word⟩, e1, e2,
            List.take_of_length_le (by simp <;> omega)]
          have hsl := setE_length g.1 k (inE pi).V'
          wp_apply ih (Config.mk s1 s2) (setE g.1 k (inE pi).V', g.2.eraseIdx (sint.nat i)) (k + W64 1) last
            (out.drop (inE pi).V'.length) (by rw [hk1]; exact hk1n) hl (by simp only; omega) as %r3 Hr3
          · unfold cfgRep
            simp only
            rw [map_eraseIdx']
            iframe #
          icases Hr3 with ⟨%R2, %HR2, Hr3, #HR2c⟩
          wp_apply wp_slice_append $$ [$Hr $Hrc $Hr3] as %r4 ⟨Hr4, Hr4c, -⟩
          wp_for_post
          iframe
          ihave #HR12 := cfgsRep_app R1 R2 $$ [$HR1 $HR2c]
          iexists i + W64 1, r4, R1 ++ R2
          simp only [List.map_append]
          iframe
          isplitl []
          · iexact HR12
          ipureintro
          refine ⟨b1, b2, ?_⟩
          rw [Hi.2.2, HR2, b3, hrange, hra, if_pos (And.intro hK hP), hk1, List.append_assoc]
        · have hra0 : readsAt m g k out (sint.nat i) = [] := by rw [hra, if_neg hKP]
          by_cases hK : (inE pi).K' = k
          · have hP : ¬ (inE pi).V' <+: out := fun hP => hKP ⟨hK, hP⟩
            rw [decide_eq_true hK]
            wp_auto
            wp_apply wp_hasPrefix out (inE pi).V'
            rw [decide_eq_false hP]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, r1, R1
            iframe
            isplitl []
            · iexact HR1
            ipureintro
            refine ⟨b1, b2, ?_⟩
            rw [b3, hrange, hra0, List.append_nil]; exact Hi.2.2
          · rw [decide_eq_false hK]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, r1, R1
            iframe
            isplitl []
            · iexact HR1
            ipureintro
            refine ⟨b1, b2, ?_⟩
            rw [b3, hrange, hra0, List.append_nil]; exact Hi.2.2
      · have hge : ¬ sint.Z i < sint.Z c.Pend'.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hn : sint.nat i = g.2.length := by
          rw [Hpl.1]; exact idx_end i c.Pend'.len Hi.1 Hi.2.1 hge
        try (rw [decide_eq_false hge])
        try (simp only [_root_.decide_true, ite_true])
        try wp_auto
        iapply HΦ
        iexists R1
        isplitr
        · ipureintro; rw [Hi.2.2, hn, readsG_succ]
        iframe
        iexact HR1

    · ihave Hst : (∃ (r0 : GoSlice) (R0 : List (Config × GC)), r_ptr ↦ r0 ∗
          r0 ↦* R0.map Prod.fst ∗ ownSliceCap Config r0 (DFrac.own 1) ∗ cfgsRep R0 ∗
          ⌜R0.map Prod.snd = if getE g.1 k <+: out then
            readsG m g (k + 1) (out.drop (getE g.1 k).length) else []⌝ : IProp GF)
          $$ [r Hnil Hnilc]
      · iexists slice.nil, []
        iframe
        isplitl []
        · iexact HR0
        ipureintro
        rw [if_neg Hif]; rfl
      icases Hst with ⟨%r0, %R0, Hr, Hr0, Hr0c, #HR0', %HR0p⟩
      ihave %Hpl := ownSlice_len _ _ _ $$ Hpd
      simp only [List.length_map] at Hpl
      ihave HI : (∃ (i : w64) (r1 : GoSlice) (R1 : List (Config × GC)), "i" ∷ i_ptr ↦ i ∗
          "r" ∷ r_ptr ↦ r1 ∗ "Hr" ∷ r1 ↦* R1.map Prod.fst ∗
          "Hrc" ∷ ownSliceCap Config r1 (DFrac.own 1) ∗ "#HR1" ∷ cfgsRep R1 ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z c.Pend'.len ∧
            R1.map Prod.snd = (if getE g.1 k <+: out then
              readsG m g (k + 1) (out.drop (getE g.1 k).length) else []) ++
              (List.range (sint.nat i)).flatMap (readsAt m g k out)⌝ : IProp GF) $$ [i Hr Hr0 Hr0c]
      · iexists W64 0, r0, R0
        iframe
        isplitl []
        · iexact HR0'
        ipureintro
        exact ⟨by decide, Hpl.2, by rw [HR0p, show sint.nat (W64 0) = 0 from rfl]; simp⟩
      wp_for HI
      wp_if_destruct
      · have hlt : sint.Z i < sint.Z c.Pend'.len := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        list_elem g.2 (sint.nat i) as pi
        obtain ⟨b1, b2, b3⟩ := idx_succ i c.Pend'.len Hi.1 hlt
        have hb : (0 ≤ sint.Z i ∧ sint.Z i < sint.Z c.Pend'.len) = True := eq_true ⟨Hi.1, hlt⟩
        simp only [hb, ite_true]
        wp_apply wp_load_slice_index c.Pend' (sint.Z i) (g.2.map inE) DFrac.discard (inE pi) Hi.1
          $$ [$Hpd] with -
        · ipureintro; rw [List.getElem?_map, Hpi_lookup]; rfl
        have hra : readsAt m g k out (sint.nat i) =
            if (inE pi).K' = k ∧ (inE pi).V' <+: out then
              readsG m (setE g.1 k (inE pi).V', g.2.eraseIdx (sint.nat i)) (k + 1)
                (out.drop (inE pi).V'.length) else [] := by
          simp only [readsAt, Hpi_lookup]
        have hrange : (List.range (sint.nat i + 1)).flatMap (readsAt m g k out) =
            (List.range (sint.nat i)).flatMap (readsAt m g k out) ++ readsAt m g k out (sint.nat i) := by
          rw [List.range_succ, List.flatMap_append]; simp
        by_cases hKP : (inE pi).K' = k ∧ (inE pi).V' <+: out
        · obtain ⟨hK, hP⟩ := hKP
          rw [decide_eq_true hK]
          wp_auto
          wp_apply wp_hasPrefix out (inE pi).V'
          rw [decide_eq_true hP]
          wp_auto
          wp_apply wp_set c.Kv' g.1 k (inE pi).V' (by omega) $$ [$Hkv] as %s1 Hs1
          wp_apply wp_without c.Pend' (g.2.map inE) i Hi.1 $$ [$Hpd] as %s2 Hs2
          iapply fupd_wp
          imod ownSlice_persist _ _ _ $$ Hs1 with #Hs1
          imod ownSlice_persist _ _ _ $$ Hs2 with #Hs2
          imodintro
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlv
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlo
          have hvo := hP.length_le
          have e1 : sint.nat (W64 ((inE pi).V'.length : Int)) = (inE pi).V'.length := by word
          have e2 : sint.nat (W64 (out.length : Int)) = out.length := by word
          rw [ite_eq_left ⟨by word, by word, by word⟩, e1, e2,
            List.take_of_length_le (by simp <;> omega)]
          have hsl := setE_length g.1 k (inE pi).V'
          wp_apply ih (Config.mk s1 s2) (setE g.1 k (inE pi).V', g.2.eraseIdx (sint.nat i)) (k + W64 1) last
            (out.drop (inE pi).V'.length) (by rw [hk1]; exact hk1n) hl (by simp only; omega) as %r3 Hr3
          · unfold cfgRep
            simp only
            rw [map_eraseIdx']
            iframe #
          icases Hr3 with ⟨%R2, %HR2, Hr3, #HR2c⟩
          wp_apply wp_slice_append $$ [$Hr $Hrc $Hr3] as %r4 ⟨Hr4, Hr4c, -⟩
          wp_for_post
          iframe
          ihave #HR12 := cfgsRep_app R1 R2 $$ [$HR1 $HR2c]
          iexists i + W64 1, r4, R1 ++ R2
          simp only [List.map_append]
          iframe
          isplitl []
          · iexact HR12
          ipureintro
          refine ⟨b1, b2, ?_⟩
          rw [Hi.2.2, HR2, b3, hrange, hra, if_pos (And.intro hK hP), hk1, List.append_assoc]
        · have hra0 : readsAt m g k out (sint.nat i) = [] := by rw [hra, if_neg hKP]
          by_cases hK : (inE pi).K' = k
          · have hP : ¬ (inE pi).V' <+: out := fun hP => hKP ⟨hK, hP⟩
            rw [decide_eq_true hK]
            wp_auto
            wp_apply wp_hasPrefix out (inE pi).V'
            rw [decide_eq_false hP]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, r1, R1
            iframe
            isplitl []
            · iexact HR1
            ipureintro
            refine ⟨b1, b2, ?_⟩
            rw [b3, hrange, hra0, List.append_nil]; exact Hi.2.2
          · rw [decide_eq_false hK]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, r1, R1
            iframe
            isplitl []
            · iexact HR1
            ipureintro
            refine ⟨b1, b2, ?_⟩
            rw [b3, hrange, hra0, List.append_nil]; exact Hi.2.2
      · have hge : ¬ sint.Z i < sint.Z c.Pend'.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hn : sint.nat i = g.2.length := by
          rw [Hpl.1]; exact idx_end i c.Pend'.len Hi.1 Hi.2.1 hge
        try (rw [decide_eq_false hge])
        try (simp only [_root_.decide_true, ite_true])
        try wp_auto
        iapply HΦ
        iexists R1
        isplitr
        · ipureintro; rw [Hi.2.2, hn, readsG_succ]
        iframe
        iexact HR1


/-- `stepConfig(c, in, Out{u, w})`. -/
theorem wp_stepConfig (c : Config) (g : GC) (i : EIn) (u : Bool) (w : GoString)
    (hg1 : g.1.length < 2 ^ 61) (hg2 : g.2.length < 2 ^ 60) :
    {{ (cfgRep c g : IProp GF) }}
      (App (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.stepConfig))
        (Val #c)) (Val #(inE i))) (Val #(Out.mk u w)))
    {{ (r : GoSlice), RET #r; ∃ R : List (Config × GC),
        ⌜R.map Prod.snd = stepCG g i u w⌝ ∗ r ↦* R.map Prod.fst ∗ cfgsRep R }} := by
  unfold cfgRep
  wp_start as ⟨#Hkv, #Hpd⟩
  obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;> cases u <;> simp only [inE, inOf]
  all_goals wp_auto
  · -- a get, answered
    have hk : k.toNat < 2 := hi
    wp_apply wp_reads 1 c g k k w rfl (by omega) (by omega) as %r Hr
    · unfold cfgRep; iframe #
    have e : stepCG g ⟨.get k, hi⟩ false w = readsG 1 g k w := rfl
    rw [e]
    iapply HΦ
    iexact Hr
  · -- a get, unknown
    ihave #Hc : cfgRep c g $$ []
    · unfold cfgRep; iframe #
    ihave #HR := cfgsRep_single c g $$ Hc
    wp_apply wp_slice_literal (V := Config) [c]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    iapply HΦ
    iexists [(c, g)]
    isplitr
    · ipureintro; simp [stepCG, isPut]
    iframe
    iexact HR
  · -- a put, answered
    by_cases hw : w = []
    · rw [decide_eq_true hw]
      wp_auto
      wp_apply wp_set c.Kv' g.1 k v (by omega) $$ [$Hkv] as %s1 Hs1
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hs1 with #Hs1
      imodintro
      ihave #Hc : cfgRep (Config.mk s1 c.Pend') (setE g.1 k v, g.2) $$ []
      · unfold cfgRep; iframe #
      ihave #HR := cfgsRep_single _ _ $$ Hc
      wp_apply wp_slice_literal (V := Config) [Config.mk s1 c.Pend']
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      iapply HΦ
      iexists [(Config.mk s1 c.Pend', (setE g.1 k v, g.2))]
      isplitr
      · ipureintro; simp [stepCG, hw]
      iframe
      iexact HR
    · rw [decide_eq_false hw]
      wp_auto
      iapply HΦ
      iexists []
      isplitr
      · ipureintro; simp [stepCG, hw]
      isplitr
      · simp only [List.map_nil]; iapply ownSlice_nil
      iapply cfgsRep_nil
  · -- a put, unknown
    wp_apply wp_pushIn c.Pend' (g.2.map inE) (In.mk (W8 0) k (W64 0) v) (by simp; omega) $$ [$Hpd]
      as %q Hq
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hq with #Hq
    imodintro
    ihave #Hc : cfgRep (Config.mk c.Kv' q) (g.1, g.2 ++ [⟨.put k v, hi⟩]) $$ []
    · unfold cfgRep; simp only [List.map_append, List.map_cons, List.map_nil, inE, inOf]; iframe #
    ihave #HR := cfgsRep_single _ _ $$ Hc
    wp_apply wp_slice_literal (V := Config) [Config.mk c.Kv' q]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    iapply HΦ
    iexists [(Config.mk c.Kv' q, (g.1, g.2 ++ [⟨.put k v, hi⟩]))]
    isplitr
    · ipureintro; simp [stepCG, isPut]
    iframe
    iexact HR
  · -- a scan, answered
    have hk : k.toNat < 2 ∧ n.toNat < 2 := hi
    have hkn : (k + n).toNat = k.toNat + n.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hno : ¬ uint.Z (k + n) < uint.Z k := by
      have : uint.Z (k + n) = (k + n).toNat := rfl
      have : uint.Z k = k.toNat := rfl
      omega
    rw [decide_eq_false hno]
    wp_auto
    wp_apply wp_reads (n.toNat + 1) c g k (k + n) w (by omega) (by omega) (by omega) as %r Hr
    · unfold cfgRep; iframe #
    have e : stepCG g ⟨.scan k n, hi⟩ false w = readsG (n.toNat + 1) g k w := rfl
    rw [e]
    iapply HΦ
    iexact Hr
  · -- a scan, unknown
    ihave #Hc : cfgRep c g $$ []
    · unfold cfgRep; iframe #
    ihave #HR := cfgsRep_single c g $$ Hc
    wp_apply wp_slice_literal (V := Config) [c]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    iapply HΦ
    iexists [(c, g)]
    isplitr
    · ipureintro; simp [stepCG, isPut]
    iframe
    iexact HR

theorem stepG_take_succ (G : List GC) (i : EIn) (u : Bool) (w : GoString) (n : Nat) (g : GC)
    (hg : G[n]? = some g) :
    (G.take (n + 1)).foldl (fun r g => addAllG r (stepCG g i u w)) [] =
      addAllG ((G.take n).foldl (fun r g => addAllG r (stepCG g i u w)) []) (stepCG g i u w) := by
  rw [List.take_add_one, hg, Option.toList_some, List.foldl_append]
  rfl

/-- `step(s, in, Out{u, w})`. -/
theorem wp_step (s : GoSlice) (P : List (Config × GC)) (i : EIn) (u : Bool) (w : GoString)
    (hP : ∀ g ∈ P.map Prod.snd, g.1.length < 2 ^ 61 ∧ g.2.length < 2 ^ 60) :
    {{ (s ↦*□ P.map Prod.fst ∗ cfgsRep P : IProp GF) }}
      (App (App (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.step))
        (Val #s)) (Val #(inE i))) (Val #(Out.mk u w)))
    {{ (ok : Bool) (r : GoSlice), RET (PairV #ok #r); ∃ R : List (Config × GC),
        ⌜R.map Prod.snd = stepG (P.map Prod.snd) i u w ∧ ok = !(stepG (P.map Prod.snd) i u w).isEmpty⌝ ∗
        r ↦* R.map Prod.fst ∗ cfgsRep R }} := by
  wp_start as ⟨#Hs, #HP⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_map] at Hl
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List Config) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnilc : (ownSliceCap Config slice.nil (DFrac.own 1) : IProp GF) $$ []
  · iapply ownSliceCap_nil
  ihave #HR0 := cfgsRep_nil (GF := GF)
  irename «in» => Hin
  ihave HI : (∃ (j : w64) (r1 : GoSlice) (R1 : List (Config × GC)), "i" ∷ i_ptr ↦ j ∗
      "r" ∷ r_ptr ↦ r1 ∗ "Hr" ∷ r1 ↦* R1.map Prod.fst ∗
      "Hrc" ∷ ownSliceCap Config r1 (DFrac.own 1) ∗ "#HR1" ∷ cfgsRep R1 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        R1.map Prod.snd = ((P.map Prod.snd).take (sint.nat j)).foldl
          (fun r g => addAllG r (stepCG g i u w)) []⌝ : IProp GF) $$ [i r Hnil Hnilc]
  · iexists W64 0, slice.nil, []
    iframe
    isplitl []
    · iexact HR0
    ipureintro
    exact ⟨by decide, Hl.2, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z j < sint.Z s.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    list_elem P (sint.nat j) as pe
    obtain ⟨b1, b2, b3⟩ := idx_succ j s.len Hj.1 hlt
    have hb : (0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len) = True := eq_true ⟨Hj.1, hlt⟩
    have hsnd : (P.map Prod.snd)[sint.nat j]? = some pe.2 := by
      rw [List.getElem?_map, Hpe_lookup]; rfl
    have hpe := hP pe.2 (List.mem_of_getElem? hsnd)
    simp only [hb, ite_true]
    wp_apply wp_load_slice_index s (sint.Z j) (P.map Prod.fst) DFrac.discard pe.1 Hj.1 $$ [$Hs]
      with -
    · ipureintro; rw [List.getElem?_map, Hpe_lookup]; rfl
    ihave #Hpe := cfgsRep_mem P pe (List.mem_of_getElem? Hpe_lookup) $$ HP
    wp_apply wp_stepConfig pe.1 pe.2 i u w hpe.1 hpe.2 $$ [$Hpe] as %q Hq
    icases Hq with ⟨%Q, %HQ, Hq, #HQc⟩
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hq with #Hq
    imodintro
    wp_apply wp_addAll r1 R1 q Q $$ [$Hr $Hrc $HR1 $Hq $HQc] as %r2 Hr2
    icases Hr2 with ⟨%R2, %HR2, Hr2, Hr2c, #HR2c⟩
    wp_for_post
    iframe
    iexists j + W64 1, r2, R2
    iframe
    isplitl []
    · iexact HR2c
    ipureintro
    refine ⟨b1, b2, ?_⟩
    rw [HR2, Hj.2.2, HQ, b3, stepG_take_succ _ _ _ _ _ _ hsnd]
  · have hge : ¬ sint.Z j < sint.Z s.len := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    have hn : sint.nat j = P.length := by
      rw [Hl.1]; exact idx_end j s.len Hj.1 Hj.2.1 hge
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    have hR : R1.map Prod.snd = stepG (P.map Prod.snd) i u w := by
      rw [Hj.2.2, hn, ← List.length_map (f := Prod.snd), List.take_length]; rfl
    have hok : decide (sint.Z (W64 0) < sint.Z r1.len) = !(stepG (P.map Prod.snd) i u w).isEmpty := by
      rw [← hR]
      obtain ⟨h1, h2⟩ := Hrl
      simp only [List.length_map] at h1
      cases R1 with
      | nil =>
        simp only [List.length_nil] at h1
        have : sint.Z r1.len = 0 := by word
        simp [this]
      | cons x R =>
        simp only [List.length_cons] at h1
        have : 0 < sint.Z r1.len := by word
        simp [this]
    rw [hok]
    iapply HΦ
    iexists R1
    iframe
    isplitr
    · ipureintro; exact ⟨hR, rfl⟩
    iexact HR1

end wp

/-! ## The configurations' bounds -/

section len
variable [GooseExts]

theorem readsG_len : ∀ (m : Nat) (g : GC) (k : w64) (out : GoString) (g' : GC),
    g' ∈ readsG m g k out → g'.1.length ≤ g.1.length + m ∧ g'.2.length ≤ g.2.length
  | 0, g, k, out, g', h => by
    simp only [readsG] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; omega
    · cases h
  | m + 1, g, k, out, g', h => by
    simp only [readsG, List.mem_append, List.mem_flatMap, List.mem_range] at h
    rcases h with h | ⟨j, hj, h⟩
    · split at h
      · have := readsG_len m g (k + 1) _ g' h; omega
      · cases h
    · cases hp : g.2[j]? with
      | none => simp [hp] at h
      | some p =>
        simp only [hp] at h
        split at h
        · have := readsG_len m _ (k + 1) _ g' h
          have h1 := setE_length g.1 k (inE p).V'
          have h2 := List.length_eraseIdx_le g.2 j
          simp only at this
          omega
        · cases h

theorem stepCG_len (g g' : GC) (i : EIn) (u : Bool) (w : GoString) (h : g' ∈ stepCG g i u w) :
    g'.1.length ≤ g.1.length + 2 ∧ g'.2.length ≤ g.2.length + 1 := by
  cases u
  · obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i
    · have := readsG_len 1 g k w g' h; omega
    · simp only [stepCG, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h
        have := setE_length g.1 k v; simp only; omega
      · cases h
    · have hn : n.toNat < 2 := hi.2
      have := readsG_len (n.toNat + 1) g k w g' h; omega
  · simp only [stepCG, ↓reduceIte] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; simp
    · simp only [List.mem_singleton] at h; subst h; omega

theorem lenOk_step (k : Nat) (G : List GC) (h : lenOk k G) (i : EIn) (u : Bool) (w : GoString) :
    lenOk (k + 1) (stepG G i u w) := by
  intro g' hg'
  obtain ⟨g, hg, hx⟩ := stepG_mem hg'
  have := stepCG_len g g' i u w hx
  have := h g hg
  omega

end len

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
