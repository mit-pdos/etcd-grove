/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchParts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The orchestrator's helpers (`kit.go`): `choose`, `plan`, `mine`, `Conf.encode` (with the leader
changes), `Conf.String`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchPartsDefs
public import Proof.fmt.SprintfPure
public import Perennial.Proof.fmt.Link

-- PORT: lab imports dropped: Harness.Proof.math.rand

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [math.rand.Hyps netDistGF]
variable [examples.swiftnet.Assumptions]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [math.rand.Hyps netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

theorem choose.wp_proof : choose.spec := by
  wp_start
  wp_auto
  wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 2) (by decide) as %x1 %Hx1
  wp_join iprop(∃ nv : w64, n_ptr ↦ nv ∗ ⌜nv = W64 3 ∨ nv = W64 5⌝) with [n] as ⟨%nv, n, %Hnv⟩
  · iexists _; iframe; ipureintro; right; rfl
  · iexists _; iframe; ipureintro; left; rfl
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 0, W64 2, W64 100]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %dsl ⟨Hdsl, -⟩
  wp_auto
  wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 2) (by decide) as %x2 %Hx2
  wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 3) (by decide) as %x3 %Hx3
  wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 3) (by decide) as %x4 %Hx4
  rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.uint64 #(W64 0)),
        KeyedElement none (ElementExpression go.uint64 #(W64 2)),
        KeyedElement none (ElementExpression go.uint64 #(W64 100))] = 3 from rfl] at *
  have hb : 0 ≤ sint.Z x4 ∧ sint.Z x4 < sint.Z (W64 3) := Hx4
  simp only [hb, and_self, ↓reduceIte]
  list_elem [W64 0, W64 2, W64 100] (sint.nat x4) as d
  wp_apply wp_load_slice_index _ (sint.Z x4) [W64 0, W64 2, W64 100] _ d hb.1 $$ [Hdsl] as Hdsl
  · iframe Hdsl; ipureintro; exact Hd_lookup
  ihave H := HΦ $$ %(⟨uint.nat nv, uint.nat x2, uint.nat x3, uint.nat d⟩ : Conf)
  rw [confV_nat]
  iapply H
  ipureintro
  have hd : d = W64 0 ∨ d = W64 2 ∨ d = W64 100 := by
    have h := List.mem_of_getElem? Hd_lookup
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases Hnv with rfl | rfl
    · left; rfl
    · right; rfl
  · simp only; word
  · simp only; word
  · simp only
    rcases hd with rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; rfl

theorem plan.wp_proof : plan.spec := fun c hc => by
  wp_start
  wp_auto
  wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 2) (by decide) as %x1 %Hx1
  have hcn : c.n = 3 ∨ c.n = 5 := hc.1
  ihave Hnil := ownSlice_nil (V := examples.swiftnet.change) (GF := netDistGF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := examples.swiftnet.change) (GF := netDistGF)
  ihave HI : (∃ (i : w64) (sl : GoSlice) (l : List examples.swiftnet.change),
      "i" ∷ i_ptr ↦ i ∗ "cs" ∷ cs_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* l ∗
      "Hcap" ∷ ownSliceCap examples.swiftnet.change sl (DFrac.own 1) ∗
      "%Hok" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (W64 1 + x1) ∧ l.length = sint.nat i ∧
        ∀ ch ∈ l, planOk c ch⌝ : IProp netDistGF) $$ [i cs Hnil Hcap]
  · rw [show (zero_val GoSlice) = slice.nil from rfl]
    iexists W64 0, slice.nil, []
    iframe i cs Hnil Hcap
    ipureintro
    have := Hx1
    refine ⟨by decide, ?_, rfl, by simp⟩
    word
  wp_for HI
  wp_if_destruct
  · wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 6) (by decide) as %x2 %Hx2
    have hcn' : 0 < sint.Z (W64 (c.n : Int)) := by
      rcases hcn with h | h <;> rw [h] <;> decide
    wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 (c.n : Int)) hcn' as %x3 %Hx3
    wp_apply (math.rand.Hyps.Intn (GF := netDistGF)) (W64 8 - W64 1) (by decide) as %x4 %Hx4
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType examples.swiftnet.change.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := examples.swiftnet.change) (t := examples.swiftnet.change.ty)
      [⟨x2, W64 2 + x3, W64 1 + x4⟩]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hlsl] as %nsl ⟨Hsl, Hcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    have hcn5 : c.n < 2 ^ 32 := by rcases hcn with h | h <;> rw [h] <;> decide
    refine ⟨by word, by word, by simp [Hok.2.2.1]; word, ?_⟩
    intro ch hch
    rcases List.mem_append.1 hch with h | h
    · exact Hok.2.2.2 ch h
    · simp only [List.mem_singleton] at h
      subst h
      unfold planOk toChange Change.valid
      simp only
      refine ⟨by word, by word, ?_, by word, by word⟩
      rcases hcn with h | h <;> rw [h] at Hx3 ⊢ <;> word
  · iapply HΦ $$ %sl %l [Hsl]
    iframe Hsl
    ipureintro
    refine ⟨?_, Hok.2.2.2⟩
    have := Hx1
    unfold maxChanges
    word

theorem mine.wp_proof : mine.spec := by
  intro sl dq cs c
  wp_start as Hsl
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave Hnil := ownSlice_nil (V := examples.swiftnet.change) (GF := netDistGF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := examples.swiftnet.change) (GF := netDistGF)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  ihave HI : (∃ (i : w64) (msl : GoSlice) (chv : examples.swiftnet.change),
      "i" ∷ i_ptr ↦ i ∗ "m" ∷ m_ptr ↦ msl ∗ "ch" ∷ ch_ptr ↦ chv ∗ "Hm" ∷ msl ↦* mineL (cs.take (sint.nat i)) c ∗
      "Hcap" ∷ ownSliceCap examples.swiftnet.change msl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp netDistGF) $$ [i m ch Hnil Hcap]
  · iexists W64 0, slice.nil, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero,
      show mineL [] c = [] from rfl]
    iframe i m ch Hnil Hcap
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := Hif
    have hi : sint.nat i < cs.length := by rw [Hlen.1]; word
    list_elem cs (sint.nat i) as chx
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z i) cs _ chx hb.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hchx_lookup
    have htake : cs.take (sint.nat (i + W64 1)) = cs.take (sint.nat i) ++ [chx] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hchx_lookup]; rfl
    wp_if_destruct
    · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType examples.swiftnet.change.ty))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := examples.swiftnet.change) (t := examples.swiftnet.change.ty)
        [chx]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hm Hcap Hlsl] as %nsl ⟨Hm, Hcap, -⟩
      · iframe
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      isplitl [Hm]
      · rw [htake]
        unfold mineL
        rw [List.filter_append]
        simp only [List.filter_cons, List.filter_nil, _root_.decide_true, ↓reduceIte]
        iexact Hm
      ipureintro; constructor <;> word
    · wp_for_post
      iframe
      iexists _, _, _
      iframe
      isplitl [Hm]
      · rw [htake]
        unfold mineL
        rw [List.filter_append]
        simp only [List.filter_cons, List.filter_nil, Hif, decide_false, Bool.false_eq_true,
          ↓reduceIte, List.append_nil]
        iexact Hm
      ipureintro; constructor <;> word
  · have hge : ¬ sint.Z i < sint.Z sl.len := by
      intro h; apply Hif; simp only [h, _root_.decide_true]
    have hi : sint.nat i = cs.length := by rw [Hlen.1]; word
    rw [hi, List.take_length]
    iapply HΦ
    iframe

theorem Conf.encode.wp_proof : Conf.encode.spec := by
  intro p c dq sl dq' cs hc hcs
  wp_start as ⟨Hp, Hsl⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_apply wp_slice_make2 (V := w8) (W64 9) as %b ⟨Hb, -⟩
  · ipureintro; decide
  ihave %Hbl := ownSlice_len $$ Hb
  have hbl : sint.Z b.len = 9 := by
    have h := Hbl.1; have h2 := Hbl.2
    simp only [List.length_replicate] at h
    have : sint.nat b.len = (sint.Z b.len).toNat := rfl
    omega
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by rw [hbl]; decide
  have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z b.len := by rw [hbl]; decide
  have h2 : 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z b.len := by rw [hbl]; decide
  have h3 : 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z b.len := by rw [hbl]; decide
  have h4 : 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) < sint.Z b.len := by rw [hbl]; decide
  simp only [h0, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; decide
  try wp_auto
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index b (sint.Z (W64 1)) _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; decide
  try wp_auto
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index b (sint.Z (W64 2)) _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; decide
  try wp_auto
  simp only [h3, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index b (sint.Z (W64 3)) _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; decide
  try wp_auto
  simp only [h4, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index b (sint.Z (W64 4)) _ _ $$ [Hb] as Hb
  · iframe Hb; ipureintro; simp only [List.length_set, List.length_replicate]; decide
  try wp_auto
  rename_i ui_ptr
  obtain ⟨hn, hf, hpl, hd⟩ := hc
  have hn' : c.n < 2 ^ 32 := by rcases hn with h | h <;> rw [h] <;> decide
  have hd' : c.desc < 2 ^ 32 := by rcases hd with h | h | h <;> rw [h] <;> decide
  have hsl : sint.Z sl.len = (cs.length : Int) := by
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    omega
  rw [W8_W64 _ hn', W8_W64 _ (by omega), W8_W64 _ (by omega), W8_W64 _ hd', hsl]
  have hhead : ((((((List.replicate 9 (zero_val w8)).set 0 (W8 (c.n : Int))).set 1
      (W8 (c.fastRead : Int))).set 2 (W8 (c.pool : Int))).set 3 (W8 (c.desc : Int))).set 4
      (W8 (cs.length : Int))) = encPart c (cs.map toChange) (sint.nat (W64 0)) := by
    simp only [encPart, List.length_map, maxChanges]
    rfl
  rw [hhead]
  ihave HI : (∃ (i iu : w64) (chv : examples.swiftnet.change), "i" ∷ i_ptr ↦ i ∗
      "ui" ∷ ui_ptr ↦ iu ∗ "ch" ∷ ch_ptr ↦ chv ∗
      "Hb" ∷ b ↦* encPart c (cs.map toChange) (sint.nat i) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp netDistGF)
    $$ [-HΦ Hp Hsl «$res0» b]
  · iexists W64 0, _, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := Hif
    have hi : sint.nat i < cs.length := by
      have : sint.nat i = (sint.Z i).toNat := rfl
      omega
    have hi2 : sint.nat i < maxChanges := by omega
    list_elem cs (sint.nat i) as chx
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z i) cs _ chx hb.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hchx_lookup
    have hin : sint.nat i = (sint.Z i).toNat := rfl
    have hi2' : sint.Z i < 2 := by unfold maxChanges at hi2; omega
    have hk5 : sint.Z (W64 5 + W64 2 * i) = 5 + 2 * sint.Z i := by word
    have hk6 : sint.Z (W64 6 + W64 2 * i) = 6 + 2 * sint.Z i := by word
    have hb5 : 0 ≤ sint.Z (W64 5 + W64 2 * i) ∧ sint.Z (W64 5 + W64 2 * i) < sint.Z b.len := by
      rw [hk5, hbl]; omega
    have hb6 : 0 ≤ sint.Z (W64 6 + W64 2 * i) ∧ sint.Z (W64 6 + W64 2 * i) < sint.Z b.len := by
      rw [hk6, hbl]; omega
    have hlenE : ∀ k, (encPart c (cs.map toChange) k).length = 9 := encPart_length _ _
    simp only [hb5, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index b (sint.Z (W64 5 + W64 2 * i)) _ _ $$ [Hb] as Hb
    · iframe Hb; ipureintro; rw [hk5, hlenE]; omega
    try wp_auto
    simp only [hb6, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index b (sint.Z (W64 6 + W64 2 * i)) _ _ $$ [Hb] as Hb
    · iframe Hb; ipureintro; rw [hk6, List.length_set, hlenE]; omega
    wp_for_post
    iframe
    iexists i + W64 1, _, _
    iframe
    isplitl [Hb]
    · have hstep := encPart_step c (cs.map toChange) (sint.nat i) (toChange chx) hi2
        (by rw [List.getElem?_map, Hchx_lookup]; rfl)
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, ← hstep, hk5, hk6]
      rw [show (5 + 2 * sint.Z i).toNat = 5 + 2 * sint.nat i by omega,
        show (6 + 2 * sint.Z i).toNat = 6 + 2 * sint.nat i by omega]
      simp only [toChange, W8_uint]
      iexact Hb
    ipureintro; constructor <;> word
  · have hge : ¬ sint.Z i < sint.Z sl.len := by
      intro h; apply Hif; simp [h]
    have hi : sint.nat i = cs.length := by
      have : sint.nat i = (sint.Z i).toNat := rfl
      omega
    rw [hi, encPart_done _ _ _ (by simp)]
    iapply HΦ
    iframe

theorem Conf.String.wp_proof : Conf.String.spec := fun p v dq => by
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.uint64 #v.N', interface.mkOk go.uint64 #v.FastRead',
     interface.mkOk go.uint64 #v.Pool', interface.mkOk go.uint64 #v.Desc']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply _root_.Perennial.EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"replicas %d, fast reads %d, pool level %d, max descriptor routines %d"
      [.lit go!"replicas ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", fast reads ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", pool level ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", max descriptor routines ", .dir none _root_.Perennial.fmt.verb_d]
      _ _ _ _ (by fmt_encode) (by fmt_fits)
      (.int _ _ _ _ (.uint64 _)
      (.int _ _ _ _ (.uint64 _)
        (.int _ _ _ _ (.uint64 _)
          (.int _ _ _ _ (.uint64 _) .nil))))
      $$ [Hlit] as %str ⟨-, -⟩
  · iexact Hlit
  iapply HΦ
  iframe

end proofs

end orch

end Perennial.github_com.imdea_software.swiftpaxos
