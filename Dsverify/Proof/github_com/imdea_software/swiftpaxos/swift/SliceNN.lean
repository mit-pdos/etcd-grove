/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SliceNN.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`append` keeps a slice non-nil (round 14): `wp_slice_append_dfrac` with the extra fact that the
result is not `nil` when the first slice's pointer is not null (Go: `append([]T{}, …)` is never
`nil`). For `getDepAndHashes`' result (`[]CommandId{}` grown by appends): `handlePropose` tests
`pm.dep != nil`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

theorem swift.wp_slice_append_nn {st t : go.GoType} [st ↓u go.SliceType t] {V : Type} [ZeroVal V]
    [TypedPointsto (GF := netDistGF) V]
    [IntoValTyped (GF := netDistGF) V t]
    (sl : GoSlice) (vs : List V) (dq_s : DFrac) (sl2 : GoSlice) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦*{dq_s} vs ∗ ownSliceCap V sl (DFrac.own 1) ∗ sl2 ↦*{dq} vs' ∗ ⌜✓ dq_s⌝ :
        IProp netDistGF) }}
      (App (App (Val #(functions go.append [st])) (Val #sl)) (Val #sl2))
    {{ (s' : GoSlice), RET #s';
        s' ↦*{dq_s} (vs ++ vs') ∗ ownSliceCap V s' (DFrac.own 1) ∗ sl2 ↦*{dq} vs' ∗
        ⌜sl.ptr ≠ null → s' ≠ slice.nil⌝ }} := by
  wp_start_folded as ⟨Hs, Hcap, Hs2, %Hdq⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  by_cases hfit : sint.Z sl.len + sint.Z sl2.len ≤ sint.Z sl.cap
  · iapply wp_slice_append_fits sl sl2 _ ⟨Hlen.2, Hlen2.2⟩ hfit
    icases ownSliceCap_split (V := V) (sl.len + sl2.len) sl $$ [Hcap] with ⟨%vs'', Hs_new, Hcap⟩
    · iframe Hcap; ipureintro; constructor <;> word
    ihave %Hlen3 := ownSlice_len _ _ _ $$ Hs_new
    wp_apply +noauto wp_slice_copy _ _ sl2 vs' dq $$ [Hs_new Hs2] with %n ⟨%Hn, Hs_new, Hs2⟩
    · iframe Hs_new Hs2
    have hd : vs''.length = vs'.length := by
      rw [Hlen3.1]; simp only [slice.slice]; word
    rw [hd, List.take_length, List.drop_of_length_le (l := vs'') (i := vs'.length) (by omega),
      List.append_nil]
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    imod ownSlice_update_to_dfrac (GF := netDistGF) dq_s _ _ Hdq $$ Hs_new with Hs_new
    imodintro
    iapply HΦ
    iframe Hs2
    isplitl [Hs Hs_new]
    · iapply ownSlice_combine sl.len sl _ vs vs' (W64 0) (sl.len + sl2.len)
        ⟨by word, by word, by word, by word⟩ $$ [Hs] Hs_new
      iapply (ownSlice_trivial_slice sl _ vs).1 $$ Hs
    isplitl
    · iapply ownSliceCap_slice_change_first sl sl.len (W64 0) (sl.len + sl2.len) _
        ⟨by word, by word, by word, by word, by word⟩ $$ Hcap
    ipureintro
    intro hp hnil
    have := congrArg (fun s : GoSlice => s.ptr) hnil
    simp only [slice.slice, sliceIndexRef] at this
    rw [show sint.Z (W64 0) = 0 by decide, go.arrayIndexRef_0] at this
    exact hp this
  · iapply wp_slice_append_grow sl sl2 _ ⟨Hlen.2, Hlen2.2⟩ (by omega)
    iintro %nsl %Hoverflow Hnew Hnew_cap
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hsl_len
    wp_apply wp_slice_copy nsl _ sl vs dq_s $$ [Hnew Hs] with %n' ⟨%Hn', Hnew, _⟩
    · iframe Hnew Hs
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    icases (ownSlice_slice sl.len (sl.len + sl2.len) nsl _ _ ⟨by word, by word, by word⟩).1 $$ Hnew
      with ⟨Hnew1, Hnew2, _⟩
    wp_apply +noauto wp_slice_copy _ _ sl2 vs' dq $$ [Hnew2 Hs2] with %n'' ⟨%Hn'', Hnew2, Hs2⟩
    · iframe Hnew2 Hs2
    have hN : sint.nat (sl.len + sl2.len) = vs.length + vs'.length := by word
    have ha : (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
        (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length).take
          (sint.nat sl.len) = vs := by
      rw [List.length_replicate, List.take_of_length_le (l := vs) (i := sint.nat (sl.len + sl2.len)) (by omega),
        show sint.nat sl.len = vs.length from Hlen.1.symm, List.take_left]
    have hb : (subslice (sint.nat sl.len) (sint.nat (sl.len + sl2.len))
        (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
          (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length)).length =
        vs'.length := by
      simp only [subslice, List.length_drop, List.length_take, List.length_append,
        List.length_replicate]
      omega
    rw [ha, hb, List.take_length, List.drop_of_length_le (i := vs'.length) (by omega),
      List.append_nil]
    have hnl : nsl.len = sl.len + sl2.len := by word
    have hs : slice.slice nsl V (W64 0) (sl.len + sl2.len) = nsl := by
      rw [← hnl]; exact (slice_slice_trivial nsl).symm
    ihave H := ownSlice_combine sl.len nsl _ vs vs' (W64 0) (sl.len + sl2.len)
      ⟨by word, by word, by word, by word⟩ $$ Hnew1 Hnew2
    rw [hs]
    ihave %Hcl := ownSliceCap_wf _ _ $$ Hcap
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    imod ownSlice_update_to_dfrac (GF := netDistGF) dq_s _ _ Hdq $$ H with H
    imodintro
    iapply HΦ
    iframe Hs2 Hnew_cap H
    ipureintro
    intro _ hnil
    have h0 := congrArg (fun s : GoSlice => sint.Z s.len) hnil
    rw [hnl] at h0
    have : sint.Z (slice.nil : GoSlice).len = 0 := by decide
    rw [this] at h0
    have hsum : sint.Z (sl.len + sl2.len) = sint.Z sl.len + sint.Z sl2.len := by word
    simp only [hsum] at h0
    omega

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
