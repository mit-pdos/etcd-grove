/-
The proofs of the gryff kit's functions (`kit.go`, notes/dsv-gryff.md; dsv-paxos's `KitProof.lean`
pattern), from their callees' specs (remote's `Check`/`ServeClient`, the model's, `op`'s), taken
as hypotheses.
-/
module

public import Dsverify.Proof.math.rand.IntnPos
public import Dsverify.Proof.gryff.examples.gryffnet.KitSpecs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace gryff.examples.gryffnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Masks, injectivity, the model's decoder (pure) -/

theorem pendN_gryff : (↑pendN : CoPset) ⊆ ⊤ \ (↑gryffN : CoPset) := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  intro h
  exact ndot_ne_disjoint nroot (show "remote" ≠ "gryff" by decide) p ⟨h1, h⟩

theorem lintestN_gryff :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ ((↑gryffN : CoPset) ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "gryff" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩


section enc
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : gryff.examples.gryffnet.Assumptions]

theorem encOutV_outV (o : Out) : encOutV (outV o) = encOutB o := by
  unfold encOutV
  have h : ∃ o' : Out, outV o = outV o' := ⟨o, rfl⟩
  rw [dif_pos h]
  have := Classical.choose_spec h
  rw [← outV_inj this]

end enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : gryff.examples.gryffnet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [AllG GF]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.gryff.examples.gryffnet

set_option goose.wp.extras true

/-- Distinct outputs have distinct bytes. -/
theorem casR_encOut_inj (γ : ProtoNames) (o o' : w64)
    (h : (casR (GF := GF) γ).encOut ((casR (GF := GF) γ).ov o) =
      (casR (GF := GF) γ).encOut ((casR (GF := GF) γ).ov o')) : o = o' := by
  simp only [casR, encOutV_outV, encOutB] at h
  exact u64Le_inj (List.cons.inj h).2

/-- **porcupine's model is the pending-writes model** of the far side's store `casR γ`. -/
theorem casS_pendDec (γ : ProtoNames) : PendDec (casR (GF := GF) γ) (casS (GF := GF)) :=
  .ofTotal (fun _ => rfl) {
  init := rfl
  ok s i o := by
    show (pM casB casDec).step s (inV i, outV ⟨false, o⟩) = (pSeq casBK).step s (i, .ok o)
    rw [pM_step casB casDec s _ i _ (casDec_box i ⟨false, o⟩)]
    exact pseq_K s i (.ok o)
  err s i := by
    show (pM casB casDec).step s (inV i, outV ⟨true, W64 0⟩) = (pSeq casBK).step s (i, .err)
    rw [pM_step casB casDec s _ i _ (casDec_box i ⟨true, W64 0⟩)]
    exact pseq_K s i .err
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, ⟨false, o⟩, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, ⟨true, W64 0⟩, rfl⟩
  noObs _ := rfl }

theorem pendCtx_casS (γ : ProtoNames) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (casR γ) (casS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (casR γ) (casS (GF := GF)) γp := rfl

theorem pendLib_casS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (casS0 (GF := GF)) γp (casS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (casS (GF := GF)) γp (casS (GF := GF)).M.init := rfl

theorem subslice8_len {A : Type} (xs : List A) (lo hi : w64) (hhi : hi = lo + W64 8)
    (h : 0 ≤ sint.Z lo ∧ sint.Z lo + 8 ≤ xs.length ∧ sint.Z lo + 8 < 2 ^ 63) :
    (subslice (sint.nat lo) (sint.nat hi) xs).length = 8 := by
  subst hhi
  simp only [subslice, List.length_drop, List.length_take]
  have : sint.nat (lo + W64 8) = sint.nat lo + 8 := by word
  have h1 : ((sint.nat lo : Nat) : Int) = sint.Z lo := by word
  rw [this]; omega

theorem build24 (a b c R : List w8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (hR : R.length = 16) :
    List.take 16 (List.take 8 (a ++ R) ++ b ++ List.drop 16 (a ++ R)) ++ c ++
      List.drop 24 (List.take 8 (a ++ R) ++ b ++ List.drop 16 (a ++ R)) = a ++ b ++ c := by
  have e1 : List.take 8 (a ++ R) = a := List.take_left' ha
  rw [e1]
  have hl : (a ++ b ++ List.drop 16 (a ++ R)).length = 24 := by simp [ha, hb, hR]
  have e2 : List.take 16 (a ++ b ++ List.drop 16 (a ++ R)) = a ++ b :=
    List.take_left' (l₁ := a ++ b) (by simp [ha, hb])
  rw [List.append_assoc a b, ← List.append_assoc a b, e2]
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem sub3 (a b c : List w8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    subslice (sint.nat (W64 0)) (sint.nat (W64 8)) (a ++ b ++ c) = a ∧
    subslice (sint.nat (W64 8)) (sint.nat (W64 16)) (a ++ b ++ c) = b ∧
    subslice (sint.nat (W64 16)) (sint.nat (W64 24)) (a ++ b ++ c) = c := by
  have h0 : sint.nat (W64 0) = 0 := rfl
  have h8 : sint.nat (W64 8) = 8 := rfl
  have h16 : sint.nat (W64 16) = 16 := rfl
  have h24 : sint.nat (W64 24) = 24 := rfl
  simp only [subslice, h0, h8, h16, h24]
  refine ⟨?_, ?_, ?_⟩
  · simp [List.take_append, ha]
  · simp [List.take_append, ha, hb]
  · simp [List.take_append, List.drop_append, ha, hb, hc]
    rw [List.take_of_length_le (by omega : a.length ≤ 24), List.drop_eq_nil_of_le (by omega),
      List.take_of_length_le (by omega : c.length ≤ 8)]
    rfl

theorem restore_eq {A : Type} (xs : List A) (lo hi : Nat) (h : lo ≤ hi) :
    xs.take lo ++ subslice lo hi xs ++ xs.drop hi = xs := by
  unfold subslice
  have : xs.take lo = (xs.take hi).take lo := by rw [List.take_take]; congr 1; omega
  rw [this, List.take_append_drop, List.take_append_drop]

theorem ownSlice_app_nil (b : GoSlice) (dq : DFrac) (xs : List w8) :
    (b ↦*{dq} (xs ++ []) : IProp GF) ⊣⊢ b ↦*{dq} xs := by
  rw [List.append_nil]; exact .rfl

theorem ownSlice_congr (b : GoSlice) (dq : DFrac) {xs ys : List w8} (h : xs = ys) :
    (b ↦*{dq} xs : IProp GF) ⊢ b ↦*{dq} ys := by
  rw [h]

/-- Ownership of the bytes `[lo, lo + 8)` of a byte slice, and back with any 8 bytes. -/
theorem ownSlice_8 (b : GoSlice) (dq : DFrac) (xs : List w8) (lo hi : w64) (hhi : hi = lo + W64 8)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo + 8 ≤ sint.Z b.len ∧ sint.Z lo + 8 < 2 ^ 63) :
    (b ↦*{dq} xs : IProp GF) ⊢
      slice.slice b w8 lo hi ↦*{dq} subslice (sint.nat lo) (sint.nat hi) xs ∗
      ⌜(subslice (sint.nat lo) (sint.nat hi) xs).length = 8⌝ ∗
      (∀ ys : List w8, ⌜ys.length = 8⌝ -∗ slice.slice b w8 lo hi ↦*{dq} ys -∗
        b ↦*{dq} (xs.take (sint.nat lo) ++ ys ++ xs.drop (sint.nat hi))) := by
  subst hhi
  have h8 : sint.Z (lo + W64 8) = sint.Z lo + 8 := by word
  iintro Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  icases (ownSlice_slice lo (lo + W64 8) b dq xs ⟨hb.1, by omega, by omega⟩).1 $$ Hb
    with ⟨H0, Hm, H2⟩
  iframe Hm
  isplitr
  · ipureintro
    exact subslice8_len xs lo _ rfl ⟨hb.1, by have := Hlen.1; word, hb.2.2⟩
  iintro %ys %Hys Hm
  have hlx : sint.nat (lo + W64 8) ≤ xs.length := by have := Hlen.1; word
  have hw1 : (xs.take (sint.nat lo)).length = sint.nat lo - sint.nat (W64 0) ∧
      0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z (lo + W64 8) := by
    refine ⟨?_, by decide, hb.1, by omega⟩
    simp only [List.length_take]
    have h0 : sint.nat lo - sint.nat (W64 0) = sint.nat lo := by word
    rw [h0]; have : sint.nat lo ≤ sint.nat (lo + W64 8) := by word
    omega
  have hw2 : (xs.take (sint.nat lo) ++ ys).length = sint.nat (lo + W64 8) - sint.nat (W64 0) ∧
      0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (lo + W64 8) ∧
      sint.Z (lo + W64 8) ≤ sint.Z b.len := by
    refine ⟨?_, by decide, by omega, by omega⟩
    simp only [List.length_append, List.length_take, Hys]
    have h0 : sint.nat (lo + W64 8) - sint.nat (W64 0) = sint.nat (lo + W64 8) := by word
    rw [h0]; have : sint.nat (lo + W64 8) = sint.nat lo + 8 := by word
    omega
  ihave H01 := ownSlice_combine lo b dq _ _ (W64 0) (lo + W64 8) hw1 $$ H0 Hm
  ihave Hall := ownSlice_combine (lo + W64 8) b dq _ _ (W64 0) b.len hw2 $$ H01 H2
  iapply (ownSlice_trivial_slice b dq _).2
  iexact Hall

/-- `ClientAddrs()` returns a new slice of the client machines' addresses. -/
theorem wp_ClientAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! gryff.examples.gryffnet.ClientAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) clientAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `ServerAddrs()` returns a new slice of the server machines' addresses. -/
theorem wp_ServerAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! gryff.examples.gryffnet.ServerAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* serverAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) serverAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `attempt()`: some duration. -/
theorem wp_attempt :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! gryff.examples.gryffnet.attempt)) (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  intro c j
  wp_start
  wp_auto
  wp_if_destruct
  · repeat (first | (wp_func_call; wp_call) | wp_auto)
    iapply HΦ; itrivial
  wp_if_destruct
  · repeat (first | (wp_func_call; wp_call) | wp_auto)
    iapply HΦ; itrivial
  iapply HΦ; itrivial

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro γ
  wp_start
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk
  simp only [casR]
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 24)) as %b ⟨Hb, Hcap⟩
    · ipureintro; decide
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have hbl : sint.Z b.len = 24 := by have := Hbl.1; simp at this; word
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8) ∧
      sint.Z (W64 8) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 0) (W64 8) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_auto
    wp_apply (encoding.binary.wp_LittleEndian_PutUint64 _ _ [] i.Op' Hl8)
      $$ [Hm] as Hm
    · simp only [List.append_nil]; iexact Hm
    simp only [List.append_nil]
    ihave Hb := Hback $$ %(u64Le i.Op') %(by simp [u64Le_length]) Hm
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z (W64 16) ∧
      sint.Z (W64 16) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 8) (W64 16) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_auto
    wp_apply (encoding.binary.wp_LittleEndian_PutUint64 _ _ [] i.A' Hl8)
      $$ [Hm] as Hm
    · simp only [List.append_nil]; iexact Hm
    simp only [List.append_nil]
    ihave Hb := Hback $$ %(u64Le i.A') %(by simp [u64Le_length]) Hm
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 16) ∧ sint.Z (W64 16) ≤ sint.Z (W64 24) ∧
      sint.Z (W64 24) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 16) (W64 24) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_auto
    wp_apply (encoding.binary.wp_LittleEndian_PutUint64 _ _ [] i.B' Hl8)
      $$ [Hm] as Hm
    · simp only [List.append_nil]; iexact Hm
    simp only [List.append_nil]
    ihave Hb := Hback $$ %(u64Le i.B') %(by simp [u64Le_length]) Hm
    iapply HΦ'
    have h0 : sint.nat (W64 0) = 0 := rfl
    have h8 : sint.nat (W64 8) = 8 := rfl
    have h16 : sint.nat (W64 16) = 16 := rfl
    have h24 : sint.nat (W64 24) = 24 := rfl
    simp only [h0, h8, h16, h24, encInB, List.take_zero, List.nil_append]
    rw [build24 _ _ _ _ (u64Le_length _) (u64Le_length _) (u64Le_length _) (by simp)]
    iexact Hb
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hbl : sint.Z b.len = 24 := by
      have := Hbl.1; simp [encInB, u64Le_length] at this; word
    wp_auto
    wp_if_destruct
    rotate_left
    · exfalso; apply Hif; word
    obtain ⟨e0, e8, e16⟩ := sub3 _ _ _ (u64Le_length i.Op') (u64Le_length i.A') (u64Le_length i.B')
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8) ∧
      sint.Z (W64 8) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 0) (W64 8) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_apply (encoding.binary.wp_LittleEndian_Uint64 _ _ dq [] Hl8) $$ [Hm] as Hm
    · iapply (ownSlice_app_nil _ _ _).2 $$ Hm
    ihave Hm := (ownSlice_app_nil _ _ _).1 $$ Hm
    simp only [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 8) = 8 from rfl]
    ihave Hb := Hback $$ %(subslice 0 8 (encInB i)) %Hl8 Hm
    rw [restore_eq _ 0 8 (by decide)]
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z (W64 16) ∧
      sint.Z (W64 16) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 8) (W64 16) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_auto
    wp_apply (encoding.binary.wp_LittleEndian_Uint64 _ _ dq [] Hl8) $$ [Hm] as Hm
    · iapply (ownSlice_app_nil _ _ _).2 $$ Hm
    ihave Hm := (ownSlice_app_nil _ _ _).1 $$ Hm
    simp only [show sint.nat (W64 8) = 8 from rfl, show sint.nat (W64 16) = 16 from rfl]
    ihave Hb := Hback $$ %(subslice 8 16 (encInB i)) %Hl8 Hm
    rw [restore_eq _ 8 16 (by decide)]
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 16) ∧ sint.Z (W64 16) ≤ sint.Z (W64 24) ∧
      sint.Z (W64 24) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 16) (W64 24) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_auto
    wp_apply (encoding.binary.wp_LittleEndian_Uint64 _ _ dq [] Hl8) $$ [Hm] as Hm
    · iapply (ownSlice_app_nil _ _ _).2 $$ Hm
    ihave Hm := (ownSlice_app_nil _ _ _).1 $$ Hm
    simp only [show sint.nat (W64 16) = 16 from rfl, show sint.nat (W64 24) = 24 from rfl]
    ihave Hb := Hback $$ %(subslice 16 24 (encInB i)) %Hl8 Hm
    rw [restore_eq _ 16 24 (by decide)]
    iapply HΦ'
    ipureintro
    intro _
    have e := sub3 _ _ _ (u64Le_length i.Op') (u64Le_length i.A') (u64Le_length i.B')
    simp only [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 8) = 8 from rfl,
      show sint.nat (W64 16) = 16 from rfl, show sint.nat (W64 24) = 24 from rfl] at e
    unfold encInB
    rw [e.1, e.2.1, e.2.2, u64Le_to_word, u64Le_to_word, u64Le_to_word]
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨y, rfl⟩ : ∃ y : Out, v = outV y := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    iintro !> %Φ' - HΦ'
    rw [encOutV_outV]
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 9)) as %b ⟨Hb, Hcap⟩
    · ipureintro; decide
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hbl : sint.Z b.len = 9 := by have := Hbl.1; simp at this; word
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    cases hu : y.Unknown'
    · wp_auto
      ihave Hb := ownSlice_congr b _ (show List.replicate 9 (zero_val w8) = W8 0 :: List.replicate 8 (zero_val w8) from rfl) $$ Hb
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 9) ∧
        sint.Z (W64 9) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
      ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 1) (W64 9) rfl ⟨by decide, by word, by decide⟩ $$ Hb
      wp_auto
      wp_apply (encoding.binary.wp_LittleEndian_PutUint64 _ _ [] y.V' Hl8) $$ [Hm] as Hm
      · iapply (ownSlice_app_nil _ _ _).2 $$ Hm
      ihave Hm := (ownSlice_app_nil _ _ _).1 $$ Hm
      ihave Hb := Hback $$ %(u64Le y.V') %(u64Le_length _) Hm
      iapply HΦ'
      iapply ownSlice_congr b _ ?_ $$ Hb
      unfold encOutB
      rw [hu]
      rfl
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      ihave Hb := ownSlice_congr b _ (show (List.replicate 9 (zero_val w8)).set 0 (W8 1) = W8 1 :: List.replicate 8 (zero_val w8) from rfl) $$ Hb
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 9) ∧
        sint.Z (W64 9) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
      ihave ⟨Hm, %Hl8, Hback⟩ := ownSlice_8 b _ _ (W64 1) (W64 9) rfl ⟨by decide, by word, by decide⟩ $$ Hb
      wp_auto
      wp_apply (encoding.binary.wp_LittleEndian_PutUint64 _ _ [] y.V' Hl8) $$ [Hm] as Hm
      · iapply (ownSlice_app_nil _ _ _).2 $$ Hm
      ihave Hm := (ownSlice_app_nil _ _ _).1 $$ Hm
      ihave Hb := Hback $$ %(u64Le y.V') %(u64Le_length _) Hm
      iapply HΦ'
      iapply ownSlice_congr b _ ?_ $$ Hb
      unfold encOutB
      rw [hu]
      rfl
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨y, rfl⟩ : ∃ y : Out, v = outV y := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_outV]
    unfold encOutB
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hbl : sint.Z b.len = 9 := by have := Hbl.1; simp [u64Le_length] at this; word
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by constructor <;> word
    have hb9 : b.len = W64 9 := by word
    wp_auto
    simp only [hb9, decide_true, Bool.not_true]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if y.Unknown' then W8 1 else W8 0)
      (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases hu : y.Unknown' <;> rw [hu] at Hif <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hif <;> revert Hif <;> decide
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if y.Unknown' then W8 1 else W8 0)
      (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 9) ∧
      sint.Z (W64 9) ≤ sint.Z b.cap by refine ⟨by decide, by decide, ?_⟩; word)]
    ihave ⟨Hm, %Hl8, -⟩ := ownSlice_8 b _ _ (W64 1) (W64 9) rfl ⟨by decide, by word, by decide⟩ $$ Hb
    wp_auto
    wp_apply (encoding.binary.wp_LittleEndian_Uint64 _ _ dq [] Hl8) $$ [Hm] as Hm
    · iapply (ownSlice_app_nil _ _ _).2 $$ Hm
    iapply HΦ'
    ipureintro
    intro _
    have hs : subslice 1 9 ((if y.Unknown' = true then W8 1 else W8 0) :: u64Le y.V') = u64Le y.V' := by
      simp only [subslice, List.drop_one, List.tail]
      exact List.take_of_length_le (by simp [u64Le_length])
    rw [hs, u64Le_to_word]
    rcases y with ⟨u, V⟩
    cases u <;> rfl
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_isWrite i
    rw [show (!isWriteG i) = (!casBK.isWrite i) from rfl]
    iapply HΦ'
    itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    simp only [show (W64 0 : w64) = 0 from rfl]
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

/-- The `*gens` `g`'s lock and counters (persistent). -/
def gensOk (g : Loc) : IProp GF :=
  iprop(∃ (mu : Loc) (nsl : GoSlice), g.[gens, go!"mu"] ↦□ mu ∗ g.[gens, go!"n"] ↦□ nsl ∗
    sync.isMutex mu (∃ ns : List w64, nsl ↦* ns))

instance gensOk_persistent (g : Loc) : Persistent (gensOk (GF := GF) g) := by
  unfold gensOk; infer_instance

/-- `g.next(c)`: some input, boxed. -/
theorem wp_gens_next (g : Loc) (c : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ gensOk g }}
      (App (Val (g @!! go.GoType.PointerType gens.ty @!! go!"next")) (Val #c))
    {{ (x : In), RET #(inV x); True }} := by
  wp_start as #Hg
  iunfold gensOk at Hg
  icases Hg with ⟨%mu, %nsl, #Hmu, #Hn, #Hlk⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlk] as ⟨Hlocked, ⟨%ns, Hns⟩⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hns
  wp_if_destruct
  · wp_if_destruct
    · -- in range
      have hc : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z nsl.len := by
        constructor <;> word
      list_elem ns (sint.nat c) as n
      rw [ite_eq_left hc]
      wp_apply wp_load_slice_index nsl (sint.Z c) ns _ n hc.1 $$ [Hns] as Hns
      · iframe Hns; ipureintro; rw [show (sint.Z c).toNat = sint.nat c by word]; exact Hn_lookup
      rw [ite_eq_left hc]
      wp_apply wp_store_slice_index nsl (sint.Z c) ns (n + W64 1) $$ [Hns] as Hns
      · iframe Hns; ipureintro; word
      wp_apply sync.Mutex.wp_Unlock $$ [$Hlk $Hlocked Hns]
      · iexists _; iexact Hns
      wp_apply (Gen.wp_proof _ _) as %x -
      iapply HΦ; itrivial
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hlk $Hlocked Hns]
      · iexists _; iexact Hns
      wp_apply (Gen.wp_proof _ _) as %x -
      iapply HΦ; itrivial
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hlk $Hlocked Hns]
    · iexists _; iexact Hns
    wp_apply (Gen.wp_proof _ _) as %x -
    iapply HΦ; itrivial

theorem Orch.wp_proof (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := w64) (I := In) (O := w64)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_casS, pendLib_casS]
  wp_start as ⟨#Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_auto
  simp only [gryff.examples.gryffnet.NC]
  wp_apply (wp_slice_make2 (V := w64) (W64 6)) as %nsl ⟨Hns, -⟩
  · ipureintro; decide
  iapply fupd_wp
  imod sync.init_Mutex (∃ ns : List w64, nsl ↦* ns) ⊤ «$v0_ptr» $$ «$v0» [Hns] with #Hlk
  · inext; iexists _; iexact Hns
  iStructNamed «$r0»
  ipersist mu
  ipersist n
  ipersist g
  ihave #Hgok : gensOk (GF := GF) «$r0_ptr» $$ []
  · iunfold gensOk
    iexists «$v0_ptr», nsl
    iframe #
  imodintro
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (Codec.wp_proof γ) as %cd #Hcd
  ihave #Hrand : isPkgInit (PROP := IProp GF) pkg_id.math.rand $$ []
  · iPkgInit
  wp_apply math.rand.wp_Intn_pos (W64 4) (by decide) as %x %Hx
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 6 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (casR γ) casS γp m addrs clientAddrs cd _ (W64 1 + x) d pendN_gryff
    lintestN_gryff (casS_pendDec γ) (casR_encOut_inj γ) (fun st => casR_timeless γ st) hrb
    (by rw [hlen']; decide) (by word) (by rw [hlen']; word) 12 (by simp only [readTries]; word)
    $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    unfold EtcdGrove.lintest.genSpec
    iintro %id
    iintro !> %Φ' %Hid HΦ'
    wp_auto
    wp_apply wp_gens_next «$r0_ptr» id $$ [Hgok] as %x -
    · iframe #
    iapply HΦ'
    imodintro
    iexists x
    ipureintro; rfl
  iapply HΦ
  itrivial

/-- Client `c`'s token for remote's `ServeClient` (persistent): its `*Sys` under its lock, and
what its operations read (the kit's package, Gryff's invariants, the replica ports' protocols). -/
def clientTok (γ : GryffNames GF) (c : Nat) (sys : GoInterface) : IProp GF :=
  iprop(sysTok γ c sys ∗ isPkgInit (PROP := IProp GF) kpkg ∗ □ protoInvs γ ∗ replicaLises γ)

instance clientTok_persistent (γ : GryffNames GF) (c : Nat) (sys : GoInterface) :
    Persistent (clientTok γ c sys) := by
  unfold clientTok replicaLises; infer_instance

/-- `Op(sys, in)`: client `c`'s operation, under `Sys.mu` (remote's `opMaybe`). -/
theorem wp_Op (wp_op : op.spec (GF := GF) (hG := hG)) (γ : GryffNames GF) (c : Nat) (hc : c < 6)
    (a : GoString) :
    ⊢ opMaybe (hG := hG) (casR γ.proto) a (clientTok γ c)
        (functions gryff.examples.gryffnet.Op []) := by
  unfold opMaybe
  iintro %sys %i %Φo
  iintro !> %Φr ⟨#Htok, HU, -⟩ HΦr
  iunfold clientTok at Htok
  icases Htok with ⟨#Hst, #Hpkg, #Hinv, #Hlis⟩
  iunfold sysTok at Hst
  icases Hst with ⟨%sp, %mu, %cl, %Hsys, #Hfix, #Hlk⟩
  subst Hsys
  ihave #Hfix' := Hfix
  iunfold sysFixed at Hfix'
  icases Hfix' with ⟨%ads, #Hmu, -, -, -, -⟩
  wp_func_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlk] as ⟨Hlocked, Hst⟩
  wp_apply (wp_op γ c sp mu cl i Φo hc) $$ [HU Hst] as %v ⟨Hst, Hv⟩
  · iframe Hst HU
    iframe #
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlk $Hlocked $Hst]
  iapply HΦr
  isplitr
  · iunfold clientTok
    iunfold sysTok
    iframe Hpkg Hinv Hlis
    iexists sp, mu, cl
    iframe Hfix Hlk
    ipureintro; rfl
  icases Hv with (⟨%o, %Ho, HΦ⟩ | %Hu)
  · ileft; iexists o; iframe HΦ; ipureintro; exact Ho
  · iright; ipureintro; exact Hu

/-- `newSys(addrs, c)`: client `c`'s new `*Sys`. -/
theorem wp_newSys (c : w64) (ads : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! gryff.examples.gryffnet.newSys)) (Val #ads)) (Val #c))
    {{ (sp : Loc), RET #sp; ∃ mu cl : Loc,
        sp ↦ Sys.mk mu c ads cl false (W64 0) ∗ mu ↦ zero_val sync.Mutex ∗
        cl ↦ zero_val client }} := by
  wp_start as -
  wp_auto
  iapply HΦ
  iexists «$v0_ptr», «$v3_ptr»
  iframe

/-- Client `c`'s `*Sys`, its state under its lock, from its start resources. -/
theorem sys_init (γ : GryffNames GF) (c : Nat) (sp mu cl : Loc) (ads : GoSlice) :
    sp ↦ Sys.mk mu (W64 c) ads cl false (W64 0) ∗ mu ↦ zero_val sync.Mutex ∗
        cl ↦ zero_val client ∗ ads ↦*□ serverAddrs ∗ clientStartRes γ c ⊢
      |={⊤}=> sysFixed c sp mu cl ∗ sync.isMutex mu (sysSt γ c sp cl) := by
  iintro ⟨Hsp, Hmu, Hcl, #Hads, Hres⟩
  iStructNamed Hsp
  ipersist mu
  ipersist c
  ipersist addrs
  ipersist cl
  iunfold clientStartRes at Hres
  icases Hres with ⟨Hids, Hbud⟩
  imod sync.init_Mutex (sysSt γ c sp cl) ⊤ mu $$ Hmu [started ops Hcl Hids Hbud] with #Hlk
  · inext
    iunfold sysSt
    iexists false, (W64 0), (zero_val client)
    iframe started ops Hcl
    isplitr
    · ipureintro; decide
    iunfold clientSt
    simp only [show uint.nat (W64 0) = 0 from rfl,
      show uint.nat (zero_val client).gen' = 0 from rfl]
    iframe Hids Hbud
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, Int.le_of_eq rfl, Int.le_of_eq rfl⟩
    ileft; ipureintro; rfl
  imodintro
  iframe Hlk
  iunfold sysFixed
  iexists ads
  iframe #

theorem Client.wp_proof (wp_op : op.spec (GF := GF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := In) (O := w64)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γ c hc
  wp_start as ⟨#Hinv, #Hlis, Hres, #Hra, #Hmap⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_ServerAddrs as %ads Hads
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hads with #Hads
  imodintro
  wp_apply (wp_newSys (W64 c) ads) as %sp ⟨%mu, %cl, Hsp, Hmu, Hcl⟩
  iapply fupd_wp
  imod sys_init γ c sp mu cl ads $$ [Hsp Hmu Hcl Hres] with ⟨#Hfix, #Hlk⟩
  · iframe Hsp Hmu Hcl Hres Hads
  imodintro
  ipersist sys
  wp_apply wp_ClientAddrs as %asl Hasl
  ihave %Hal := ownSlice_len _ _ _ $$ Hasl
  have hal : clientAddrs.length = 6 := rfl
  have hb : 0 ≤ sint.Z (W64 (c : Int)) ∧ sint.Z (W64 (c : Int)) < sint.Z asl.len := by
    constructor <;> word
  simp only [hb, _root_.and_self, ↓reduceIte]
  list_elem clientAddrs c as a
  wp_apply wp_load_slice_index asl (sint.Z (W64 (c : Int))) clientAddrs _ a hb.1 $$ [Hasl] with Hasl
  · iframe; ipureintro; rw [show (sint.Z (W64 (c : Int))).toNat = c by word]; exact Ha_lookup
  have ha : a = clientAddrs.getD c [] := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst ha
  wp_auto
  wp_apply (Codec.wp_proof γ.proto) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (casR γ.proto)) _ _ _ _ cd d
    (clientTok γ c) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · iapply opMaybe_svcOp
    iapply wp_Op wp_op γ c hc
  · iintro %Φr HΦr
    wp_auto
    iapply HΦr
    iunfold clientTok
    iframe #
    iunfold sysTok
    iexists sp, mu, cl
    iframe #
    ipureintro; rfl

end proof

end gryff.examples.gryffnet

end Perennial
