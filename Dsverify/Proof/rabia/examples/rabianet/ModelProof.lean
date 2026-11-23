/-
`Model()` (kit.go) meets the store's porcupine model spec `kvS` (notes/dsv-rabia.md; as paxos's
`ModelProof.lean`): the state's helpers `push`, `has`, `cat`, `erase`, `equalStrs`, `find`, `set`,
`equal` and `step` over read-only slices, and the pure `stepG_pSeq` (`ModelSet.lean`); the
decoder's laws and `PendDec` (porcupine's model is the pending-writes model of `kvR γ`).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.KitModel

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace rabia.examples.rabianet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.rabia
  Perennial.rabia.model

/-! ## The decoder -/

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : rabia.examples.rabianet.Assumptions]

attribute [local instance] Assumptions.In_instance Assumptions.Out_instance

theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hP := (In.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (In.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  have hK := (In.TypeAssumptions.get_K x).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (In.TypeAssumptions.get_K y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (In.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hP'] at hP
  rw [h, hK'] at hK
  rw [h, hV'] at hV
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  have eK : Val #x.K' = Val #y.K' := (congrFun hK (Val #y.K')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eP with eP
  injection eK with eK
  injection eV with eV
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  have eK' := go.intoVal_inj eK
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eP' eK' eV'
  subst eP' eK' eV'
  rfl

theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  have hP := (Out.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (Out.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  have hF := (Out.TypeAssumptions.get_Found x).isGoStep_det_internal.isGoStep_pure_det
  have hF' := (Out.TypeAssumptions.get_Found y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hU'] at hU
  rw [h, hP'] at hP
  rw [h, hF'] at hF
  rw [h, hV'] at hV
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  have eF : Val #x.Found' = Val #y.Found' := (congrFun hF (Val #y.Found')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eU with eU
  injection eP with eP
  injection eF with eF
  injection eV with eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  have eF' := GoGlobalContext.intoVal_inj_bool eF
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eU' eP' eF' eV'
  subst eU' eP' eF' eV'
  rfl

theorem inV_inj {a b : KIn} (h : inV a.1 = inV b.1) : a = b := by
  simp only [inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
  have e := in_intoVal_inj h
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  apply Subtype.ext
  simp only at e ⊢
  cases a <;> cases b <;> simp_all [inVal]
  all_goals (rename_i k v; exact absurd e (by simp [inputOk] at *))

theorem outV_eq {a b : Out} (h : interface.mkOk Out.ty #a = interface.mkOk Out.ty #b) : a = b := by
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
  exact out_intoVal_inj h

theorem outVal_inj {a b : KOut} (h : outVal a.1 = outVal b.1) : a = b := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  apply Subtype.ext; simp only at h ⊢
  cases a with
  | done => cases b with
    | done => rfl
    | got w => cases w <;> simp [outVal] at h
  | got v => cases b with
    | done => cases v <;> simp [outVal] at h
    | got w => cases v <;> cases w <;> simp_all [outVal]

theorem outVal_ne_unk (o : KOut) : outVal o.1 ≠ Out.mk true false false [] := by
  rcases o with ⟨o, _⟩
  cases o with
  | done => simp [outVal]
  | got w => cases w <;> simp [outVal]

theorem ansV_inj {a b : linkv.Ans KOut} (h : ansV a = ansV b) : a = b := by
  cases a <;> cases b <;> simp only [ansV] at h
  · rw [outVal_inj (outV_eq h)]
  · exact absurd (outV_eq h) (outVal_ne_unk _)
  · exact absurd (outV_eq h).symm (outVal_ne_unk _)
  · rfl

/-- `kvDec` on a boxed input and a boxed answer. -/
theorem kvDec_box (i : KIn) (a : linkv.Ans KOut) : kvDec (inV i.1, ansV a) = some (i, a) := by
  unfold kvDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    rw [ansV_inj h2.symm, inV_inj h1.symm]
  · next hn => exact absurd ⟨i, a, rfl⟩ hn

/-- `Out{…}`'s bytes, for a bounded value. -/
theorem encOutV_out (x : Out) (hx : x.V'.length + 9 < 2 ^ 63) :
    encOutV (interface.mkOk Out.ty #x) = encOutB x := by
  unfold encOutV
  split
  · rename_i h
    rw [← outV_eq (Classical.choose_spec h).1]
  · rename_i h
    exact absurd ⟨x, rfl, hx⟩ h

theorem outVal_len (o : KOut) : (outVal o.1).V'.length + 9 < 2 ^ 63 := by
  rcases o with ⟨o, ho⟩
  cases o with
  | done => simp [outVal]
  | got w =>
    cases w with
    | none => simp [outVal]
    | some x => simp only [outVal]; exact (show valB x from ho).2

end dec

section masks
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

theorem pendN_rabia : (↑pendN : CoPset) ⊆ ⊤ \ rabiaE := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  unfold rabiaE rabiaR
  intro h
  exact ndot_ne_disjoint nroot (show "remote" ≠ "rabia" by decide) p ⟨h1, h⟩

theorem lintestN_rabia :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (rabiaE ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · unfold rabiaE rabiaR
    intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "rabia" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

end masks

section pend
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [bvi : go.BasicIntoValInj] [package_sem : rabia.examples.rabianet.Assumptions]

/-- Distinct outputs have distinct bytes. -/
theorem kvR_encOut_inj (γ : Names) (o o' : KOut)
    (h : (kvR (Gg := hG.goose_globalGS) γ).encOut ((kvR (Gg := hG.goose_globalGS) γ).ov o) =
      (kvR (Gg := hG.goose_globalGS) γ).encOut ((kvR (Gg := hG.goose_globalGS) γ).ov o')) :
    o = o' := by
  simp only [kvR, outV] at h
  rw [encOutV_out _ (outVal_len o), encOutV_out _ (outVal_len o')] at h
  apply outVal_inj
  rcases o with ⟨o, ho⟩; rcases o' with ⟨o', ho'⟩
  simp only at h ⊢
  cases o with
  | done => cases o' with
    | done => rfl
    | got w => cases w <;> simp [outVal, encOutB] at h
  | got v => cases o' with
    | done => cases v <;> simp [outVal, encOutB] at h
    | got w => cases v <;> cases w <;> simp_all [outVal, encOutB]

/-- **porcupine's model is the pending-writes model** of the far side's store `kvR γ`. -/
theorem kvS_pendDec (γ : Names) : PendDec (kvR (Gg := hG.goose_globalGS) γ) (kvS (GF := GF)) where
  init := rfl
  ok s i o := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i (.ok o))
  err s i := linkv.pM_step kvB kvDec s _ i _ (kvDec_box i .err)
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, .ok o, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, .err, rfl⟩
  noObs _ := rfl

theorem pendCtx_kvS (γ : Names) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS (GF := GF)) γp := rfl

theorem pendLib_kvS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (kvS (GF := GF)) γp (kvS (GF := GF)).M.init := rfl

end pend

/-! ## The state's helpers -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : rabia.examples.rabianet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.rabia.examples.rabianet

set_option goose.wp.extras true

theorem wp_push (p : GoSlice) (P : List GoString) (v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! rabia.examples.rabianet.push)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %q ⟨Hq, -⟩
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

theorem wp_has (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! rabia.examples.rabianet.has)) (Val #p)) (Val #v))
    {{ RET #(decide (v ∈ P)); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ v ∉ P.take (sint.nat i)⌝ : IProp GF)
      $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, ?_⟩
    rw [h0]; simp
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi.1 $$ [Hp] as -
    · iframe Hp; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_for_post
      have : v ∈ P := Hif ▸ List.mem_of_getElem? Hx_lookup
      rw [show decide (v ∈ P) = true from decide_eq_true this]
      iapply HΦ
      itrivial
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hs, List.take_add_one, Hx_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hi.2.2, fun h => Hif h.symm⟩
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hv : v ∉ P := by
      have := Hi.2.2
      rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
        List.take_length] at this
    rw [show decide (v ∈ P) = false from decide_eq_false hv]
    iapply HΦ
    itrivial

theorem erase_take_succ (P : List GoString) (v x : GoString) (n : Nat) (hx : P[n]? = some x)
    (f : Bool) (hf : f = false → v ∉ P.take n) (hf2 : f = true → v ∈ P.take n) :
    (if (!f && decide (x = v)) then P.take n else
      (if f then (P.take n).erase v else P.take n) ++ [x]) =
    (if (f || decide (x = v)) then (P.take (n + 1)).erase v else P.take (n + 1)) := by
  rw [List.take_add_one, hx, Option.toList_some]
  cases f
  · have hv := hf rfl
    by_cases h : x = v
    · subst h
      simp [List.erase_append_right _ hv]
    · have hv' : v ∉ P.take n ++ [x] := by simp [hv, Ne.symm h]
      simp [h]
  · have hv := hf2 rfl
    simp [List.erase_append_left _ hv]

theorem wp_erase (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! rabia.examples.rabianet.erase)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* P.erase v }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) p.len (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (i : w64) (f : Bool) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ f ∗
      "q" ∷ q_ptr ↦ q ∗
      "Hq" ∷ q ↦* (if f then (P.take (sint.nat i)).erase v else P.take (sint.nat i)) ∗
      "Hcap" ∷ ownSliceCap GoString q (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ (f = false → v ∉ P.take (sint.nat i)) ∧
        (f = true → v ∈ P.take (sint.nat i))⌝ : IProp GF) $$ [i found q Hq Hcap]
  · iexists W64 0, false, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [Bool.false_eq_true, ↓reduceIte, List.take_zero]
    iframe
    ipureintro
    refine ⟨by word, by word, fun _ => by simp, fun h => by cases h⟩
  wp_for HI
  obtain ⟨Hi0, Hil, hf1, hf2⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    have e := erase_take_succ P v x (sint.nat i) Hx_lookup f hf1 hf2
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    cases f
    · wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      by_cases hxv : x = v
      · subst hxv
        simp only [Bool.not_false, decide_true, Bool.and_self, ↓reduceIte, Bool.or_true] at e
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, true, q
        rw [hs, ← e]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        refine ⟨by word, by word, ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
        rw [List.take_add_one, Hx_lookup]; simp
      · simp only [Bool.not_false, hxv, decide_false, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Bool.or_false] at e
        rw [decide_eq_false hxv]
        wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
        wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
        · iframe Hp; ipureintro; exact Hx_lookup
        wp_apply wp_slice_literal (V := GoString) [x]
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_auto
        wp_apply wp_slice_append (V := GoString) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
        wp_for_post
        iframe
        iexists i + W64 1, false, q'
        rw [hs, ← e]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        refine ⟨by word, by word, ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
        exact ⟨hf1 rfl, Ne.symm hxv⟩
    · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Bool.true_or] at e
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      wp_apply wp_slice_literal (V := GoString) [x]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := GoString) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, true, q'
      rw [hs, ← e]
      simp only [↓reduceIte]
      iframe
      ipureintro
      refine ⟨by word, by word, ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
      rw [List.take_add_one, Hx_lookup]
      simp [hf2 rfl]
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hn : sint.nat i = P.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length]
    iapply HΦ
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hv : v ∉ P := by
        have := hf1 rfl
        rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
          List.take_length] at this
      rw [List.erase_of_not_mem hv]
      iexact Hq
    · simp only [↓reduceIte]
      iexact Hq

/-! ### Entries -/

theorem ents_nil : ⊢ entsRep (GF := GF) [] [] := by
  unfold entsRep
  isplitr
  · ipureintro; simp
  · simp only [List.zip_nil_left]
    iapply BigSepL.bigSepL_nil.2
    itrivial

theorem ents_len {evs : List Entry} {es : List EntV} :
    entsRep (GF := GF) evs es ⊢ ⌜evs.length = es.length⌝ := by
  unfold entsRep
  iintro ⟨%h, -⟩
  ipureintro
  have := congrArg List.length h.1
  simpa using this

/-- An entry of `evs` holds the entry of `es` at its index. -/
theorem ents_lookup {evs : List Entry} {es : List EntV} {i : Nat} {ev : Entry}
    (h : evs[i]? = some ev) :
    entsRep (GF := GF) evs es ⊢ ∃ e, ⌜es[i]? = some e⌝ ∗ entRep ev e := by
  unfold entsRep
  iintro ⟨%hm, #Hl⟩
  have hl : evs.length = es.length := by simpa using congrArg List.length hm.1
  have hi : i < es.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 h).1
  obtain ⟨e, he⟩ : ∃ e, es[i]? = some e := ⟨es[i], List.getElem?_eq_getElem hi⟩
  have hk : ev.K' = e.k := by
    have := congrArg (fun l => l[i]?) hm.1
    simp only [List.getElem?_map, h, he, Option.map_some, Option.some.injEq] at this
    exact this
  have hc : ev.Cur' = e.cur := by
    have := congrArg (fun l => l[i]?) hm.2
    simp only [List.getElem?_map, h, he, Option.map_some, Option.some.injEq] at this
    exact this
  have hz : (evs.zip es)[i]? = some (ev, e) := List.getElem?_zip_eq_some.2 ⟨h, he⟩
  ihave ⟨#Ho, #Hp⟩ := (BigSepL.bigSepL_lookup (Φ := fun _ p => iprop(p.1.Old' ↦*□ p.2.old ∗
    p.1.Pend' ↦*□ p.2.new)) hz) $$ Hl
  iexists e
  isplitr
  · ipureintro; exact he
  unfold entRep
  iframe Ho Hp
  ipureintro; exact ⟨hk, hc⟩

theorem ents_snoc (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV) :
    entsRep (GF := GF) evs es ∗ entRep eve e ⊢ entsRep (evs ++ [eve]) (es ++ [e]) := by
  iintro ⟨Hs, He⟩
  ihave %hl := ents_len $$ Hs
  unfold entsRep entRep
  icases Hs with ⟨%hm, #Hl⟩
  icases He with ⟨%he, #Ho, #Hp⟩
  isplitr
  · ipureintro
    simp [hm.1, hm.2, he.1, he.2]
  rw [List.zip_append hl]
  iapply BigSepL.bigSepL_append.2
  iframe Hl
  simp only [List.zip_cons_cons, List.zip_nil_left]
  iapply BigSepL.bigSepL_singleton.2
  iframe Ho Hp

/-- Every entry of `e`'s key replaced by `e` (kit.go's `set`'s loop). -/
theorem ents_map (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV) :
    entsRep (GF := GF) evs es ∗ entRep eve e ⊢
      entsRep (evs.map fun x => if x.K' = eve.K' then eve else x)
        (es.map fun x => if x.k = e.k then e else x) := by
  induction evs generalizing es with
  | nil =>
    iintro ⟨Hs, -⟩
    ihave %hl := ents_len $$ Hs
    rw [List.length_nil] at hl
    rw [List.eq_nil_of_length_eq_zero hl.symm]
    simp only [List.map_nil]
    iapply ents_nil
  | cons ev evs ih =>
    cases es with
    | nil =>
      iintro ⟨Hs, -⟩
      ihave %hl := ents_len $$ Hs
      simp at hl
    | cons x xs =>
      iintro ⟨Hs, #He⟩
      ihave Hs' := Hs
      iunfold entsRep at Hs'
      icases Hs' with ⟨%hm, #Hl⟩
      rw [List.zip_cons_cons] at *
      ihave ⟨⟨#Ho, #Hp⟩, #Hrest⟩ := (BigSepL.bigSepL_cons).1 $$ Hl
      simp only [List.map_cons, List.cons.injEq] at hm
      ihave #Ht := ih xs $$ [He]
      · isplitr
        · unfold entsRep; isplitr
          · ipureintro; exact ⟨hm.1.2, hm.2.2⟩
          · iexact Hrest
        · iexact He
      unfold entRep
      icases He with ⟨%hk, #Ho', #Hp'⟩
      unfold entsRep
      icases Ht with ⟨%hm', #Hl'⟩
      have hkx : (ev.K' = eve.K') ↔ (x.k = e.k) := by rw [hm.1.1, hk.1]
      isplitr
      · ipureintro
        simp only [List.map_cons, List.cons.injEq]
        refine ⟨⟨?_, hm'.1⟩, ⟨?_, hm'.2⟩⟩
        · by_cases h : x.k = e.k
          · simp [h, hkx.2 h, hk.1]
          · have h' : ¬ ev.K' = eve.K' := fun h2 => h (hkx.1 h2)
            simp only [h, h', ↓reduceIte]; exact hm.1.1
        · by_cases h : x.k = e.k
          · simp [h, hkx.2 h, hk.2]
          · have h' : ¬ ev.K' = eve.K' := fun h2 => h (hkx.1 h2)
            simp only [h, h', ↓reduceIte]; exact hm.2.1
      simp only [List.map_cons, List.zip_cons_cons]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · by_cases h : x.k = e.k
        · simp only [h, ↓reduceIte, hkx.2 h]; iframe Ho' Hp'
        · have h' : ¬ ev.K' = eve.K' := fun h2 => h (hkx.1 h2)
          simp only [h, h', ↓reduceIte]; iframe Ho Hp
      · iexact Hl'

/-- kit.go's `set`'s result: `setE`'s entries. -/
theorem ents_set (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV) :
    entsRep (GF := GF) evs es ∗ entRep eve e ⊢
      entsRep (if evs.any (fun x => decide (x.K' = eve.K')) then
          evs.map (fun x => if x.K' = eve.K' then eve else x) else evs ++ [eve])
        (setE es e) := by
  iintro ⟨#Hs, #He⟩
  ihave #Hs' := Hs
  iunfold entsRep at Hs'
  icases Hs' with ⟨%hm, -⟩
  ihave #He' := He
  iunfold entRep at He'
  icases He' with ⟨%hk, -⟩
  have hany : evs.any (fun x => decide (x.K' = eve.K')) = es.any (fun x => decide (x.k = e.k)) := by
    have : evs.any (fun x => decide (x.K' = eve.K')) = (evs.map (·.K')).any (fun x => decide (x = eve.K')) := by
      simp [List.any_map, Function.comp_def]
    rw [this, hm.1, hk.1]; simp [List.any_map, Function.comp_def]
  unfold setE
  rw [hany]
  split
  · iapply ents_map; iframe Hs He
  · iapply ents_snoc; iframe Hs He

end proof

end rabia.examples.rabianet
end Perennial
