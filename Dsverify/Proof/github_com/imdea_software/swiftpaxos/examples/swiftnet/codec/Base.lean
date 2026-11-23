/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Base.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Shared definitions of the codec's proofs: `restOf` (the rest of a byte slice a decoder returns,
with the way back to the whole slice), `decPost` (a decoder's postcondition: its parser's
result), `swift.CommandId`'s equality (a map key: decidable, injective `intoVal`, Go's `==` is
equality of values).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Parse
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Bytes

-- PORT: lab imports dropped: Harness.Proof.net.rpc.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section base

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

/-- The rest `r` of a byte slice `b` (holding `bs`) holds `rest`, and gives `b` back. -/
def restOf (b : GoSlice) (dq : DFrac) (bs : List w8) (r : GoSlice) (rest : List w8) : IProp GF :=
  iprop(r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs))

theorem restOf_refl (b : GoSlice) (dq : DFrac) (bs : List w8) :
    (b ↦*{dq} bs : IProp GF) ⊢ restOf b dq bs b bs := by
  iintro Hb; unfold restOf; iframe Hb; iintro H; iexact H

theorem restOf_trans (b : GoSlice) (dq : DFrac) (bs : List w8) (r1 : GoSlice) (rest1 : List w8)
    (r2 : GoSlice) (rest2 : List w8) :
    (restOf b dq bs r1 rest1 : IProp GF) -∗ (r1 ↦*{dq} rest1 -∗ restOf r1 dq rest1 r2 rest2) -∗
      restOf b dq bs r2 rest2 := by
  unfold restOf
  iintro ⟨H1, Hback1⟩ Hf
  icases Hf $$ H1 with ⟨H2, Hback2⟩
  iframe H2
  iintro H2
  iapply Hback1
  iapply Hback2 $$ H2

theorem restOf_comp (b : GoSlice) (dq : DFrac) (bs : List w8) (r1 : GoSlice) (rest1 : List w8)
    (r2 : GoSlice) (rest2 : List w8) :
    (r1 ↦*{dq} rest1 -∗ b ↦*{dq} bs : IProp GF) -∗ restOf r1 dq rest1 r2 rest2 -∗
      restOf b dq bs r2 rest2 := by
  unfold restOf
  iintro Hback1 ⟨H2, Hback2⟩
  iframe H2
  iintro H2
  iapply Hback1
  iapply Hback2 $$ H2

theorem restOf_open (b : GoSlice) (dq : DFrac) (bs : List w8) (r : GoSlice) (rest : List w8) :
    (restOf b dq bs r rest : IProp GF) ⊢ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs) := by
  unfold restOf; iintro H; iexact H

theorem restOf_close (b : GoSlice) (dq : DFrac) (bs : List w8) (r : GoSlice) (rest : List w8) :
    (r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs) : IProp GF) ⊢ restOf b dq bs r rest := by
  unfold restOf; iintro H; iexact H

theorem restOf_back (b : GoSlice) (dq : DFrac) (bs : List w8) (r : GoSlice) (rest : List w8) :
    (restOf b dq bs r rest : IProp GF) ⊢ b ↦*{dq} bs := by
  unfold restOf; iintro ⟨H, Hb⟩; iapply Hb $$ H

include sem package_sem in
theorem cmdId_intoVal_inj : Function.Injective (intoVal (V := swift.CommandId)) := by
  intro k k' h
  have h1 := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get_ClientId k).isGoStep_det_internal))
  have h1' := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get_ClientId k').isGoStep_det_internal))
  have h2 := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get_SeqNum k).isGoStep_det_internal))
  have h2' := (go.IsGoStepPureDet.isGoStep_pure_det (self :=
    (swift.CommandId.TypeAssumptions.get_SeqNum k').isGoStep_det_internal))
  rw [h] at h1 h2
  rw [h1] at h1'; rw [h2] at h2'
  have e1 := congrFun h1' (Val #k'.ClientId'); simp at e1
  have e2 := congrFun h2' (Val #k'.SeqNum'); simp at e2
  cases k; cases k'
  simp only [swift.CommandId.mk.injEq]
  exact ⟨go.intoVal_inj e1, go.intoVal_inj e2⟩

/-- The suffix `r[k:len(r)]` of a byte slice is a rest of it. -/
theorem restOf_drop (r : GoSlice) (dq : DFrac) (rest : List w8) (k : w64)
    (hk : uint.nat k ≤ rest.length) :
    (r ↦*{dq} rest : IProp GF) ⊢ restOf r dq rest (slice.slice r w8 k r.len) (rest.drop (uint.nat k)) := by
  iintro Hr
  ihave %Hl := ownSlice_len _ _ _ $$ Hr
  have hsplit : rest = rest.take (uint.nat k) ++ rest.drop (uint.nat k) := (List.take_append_drop _ _).symm
  have htl : (rest.take (uint.nat k)).length = uint.nat k := by simp; omega
  have hk' : W64 (rest.take (uint.nat k)).length = k := by rw [htl]; word
  ihave Hr' : (r ↦*{dq} (rest.take (uint.nat k) ++ rest.drop (uint.nat k)) : IProp GF) $$ [Hr]
  · rw [← hsplit]; iexact Hr
  icases net.rpc.ownSlice_drop_acc r dq _ _ $$ Hr' with ⟨-, Hsuf, Hback⟩
  rw [hk']
  unfold restOf
  iframe Hsuf
  iintro Hsuf
  ihave Hr := Hback $$ %_ %rfl Hsuf
  rw [← hsplit]
  iexact Hr

theorem restOf_drop' (r : GoSlice) (dq : DFrac) (rest : List w8) (k : w64) (rest' : List w8)
    (hk : uint.nat k ≤ rest.length) (h : rest.drop (uint.nat k) = rest') :
    (r ↦*{dq} rest : IProp GF) ⊢ restOf r dq rest (slice.slice r w8 k r.len) rest' := by
  rw [← h]; exact restOf_drop r dq rest k hk

/-- The prefix `r[0:k]` of a byte slice, and the way back. -/
theorem take_acc (r : GoSlice) (dq : DFrac) (rest : List w8) (k : w64)
    (hk : uint.nat k ≤ rest.length) :
    (r ↦*{dq} rest : IProp GF) ⊢ slice.slice r w8 (W64 0) k ↦*{dq} rest.take (uint.nat k) ∗
      (slice.slice r w8 (W64 0) k ↦*{dq} rest.take (uint.nat k) -∗ r ↦*{dq} rest) := by
  iintro Hr
  ihave %Hl := ownSlice_len _ _ _ $$ Hr
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z r.len := by
    refine ⟨by decide, by word, by word⟩
  have hs : subslice (sint.nat (W64 0)) (sint.nat k) rest = rest.take (uint.nat k) := by
    simp only [subslice]
    have : sint.nat k = uint.nat k := by word
    rw [this]; rfl
  rw [← hs]
  iapply net.rpc.ownSlice_sub_acc (W64 0) k r dq rest hb $$ Hr

/-- A decoder's postcondition: its parser `p` fails on `bs` (`ok = false`, the input back), or
gives `a` and the rest (`ok = true`, `v` holds `a`, `r` the rest). -/
def decPost {G A : Type} (p : List w8 → Option (A × List w8)) (own : G → A → IProp GF)
    (b : GoSlice) (dq : DFrac) (bs : List w8) (v : G) (r : GoSlice) (ok : Bool) : IProp GF :=
  iprop((⌜p bs = none ∧ ok = false⌝ ∗ b ↦*{dq} bs) ∨
    (∃ (a : A) (rest : List w8), ⌜p bs = some (a, rest) ∧ ok = true⌝ ∗ own v a ∗
      restOf b dq bs r rest))

/-- The ownership of a decoded value without heap parts: the value itself. -/
abbrev ownPure {A : Type} (v a : A) : IProp GF := iprop(⌜v = a⌝)

theorem wp_eq_cmdid (k k' : swift.CommandId) (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (k = k')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals swift.CommandId.ty))) (Val (PairV #k #k'))) @ s; E
        {{ Φ }} := by
  iintro HΦ
  wp_auto
  wp_if_destruct
  · have : decide (k.SeqNum' = k'.SeqNum') = decide (k = k') := by
      cases k; cases k'; simp_all
    rw [this]; iexact HΦ
  · have : decide (k = k') = false := by
      cases k; cases k'; simp_all
    rw [this]; iexact HΦ

end base

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
