/- Port of election_proof/proof_readOnly__addRequest.v.

Lean notes: Rocq's `wp_slice_append_persistent` (`new/golang/theory/slice.v`, the
`DfracDiscarded` instance of `wp_slice_append_dfrac`) has no Lean counterpart in
Perennial's `Golang/Theory/Slice.lean`, which only has `wp_slice_append` (destination
owned). It is proved here as a private lemma, adapting `wp_slice_append`'s proof:
the destination is only read (slow path) or left alone (fast path, where `append`
writes into the owned capacity only). -/
import EtcdGrove.Raft.ElectionProof.Spec.readOnly__addRequest

noncomputable section

namespace Perennial

section append
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepL
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- Go's `append` onto a destination held read-only (Rocq `wp_slice_append_persistent`):
the result is read-only too, with the capacity owned. -/
private theorem wp_slice_append_persistent {st t : go.GoType} [st ↓u go.SliceType t]
    [IntoValTyped (GF := GF) V t]
    (sl : GoSlice) (vs : List V) (sl2 : GoSlice) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦*□ vs ∗ ownSliceCap V sl (DFrac.own 1) ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #sl)) (Val #sl2)) @ s; E
    {{ (s' : GoSlice), RET #s';
        s' ↦*□ (vs ++ vs') ∗ ownSliceCap V s' (DFrac.own 1) ∗ sl2 ↦*{dq} vs' }} := by
  wp_start as ⟨#Hs, Hcap, Hs2⟩
  iapply wp_fupd
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hs
  ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hs2
  wp_apply wp_sumAssumeNoOverflowSigned with %Hoverflow
  wp_if_destruct
  · rw [ite_eq_left ⟨by word, by word, Hif⟩]
    wp_auto
    rw [ite_eq_left (by (try simp only [slice.slice]); word)]
    wp_auto
    rw [slice_slice sl (W64 0) (sl.len + sl2.len) sl.len (sl.len + sl2.len) (by word)]
    have h0 : ∀ x : w64, W64 0 + x = x := fun x => by word
    simp only [h0]
    icases ownSliceCap_split (sl.len + sl2.len) sl $$ [Hcap] with ⟨%vs'', Hs_new, Hcap⟩
    · iframe Hcap; ipureintro; exact ⟨by word, Hif⟩
    ihave %Hlen3 := ownSlice_len _ _ _ $$ Hs_new
    wp_apply wp_slice_copy _ _ sl2 vs' dq $$ [Hs_new Hs2] with %n ⟨%Hn, Hs_new, Hs2⟩
    · iframe Hs_new Hs2
    have hd : vs''.length = vs'.length := by
      rw [Hlen3.1]; simp only [slice.slice]; word
    rw [hd, List.take_length, List.drop_of_length_le (l := vs'')
      (i := vs'.length) (by omega), List.append_nil]
    imod ownSlice_persist _ _ _ $$ Hs_new with #Hs_new
    iapply HΦ
    iframe Hs2
    isplitl []
    · ihave Hs0 := (ownSlice_trivial_slice sl _ vs).1 $$ Hs
      iapply ownSlice_combine sl.len sl _ vs vs' (W64 0) (sl.len + sl2.len)
        ⟨by word, by word, by word, by word⟩ $$ Hs0 Hs_new
    · iapply ownSliceCap_slice_change_first sl sl.len (W64 0) (sl.len + sl2.len) _
        ⟨Hif, by word, by word, by word, by word⟩ $$ Hcap
  · wp_apply wp_new_cap with %cap %Hcap_ge
    wp_apply wp_slice_make3 (V := V) (sl.len + sl2.len) cap ⟨by word, Hcap_ge⟩
      with %nsl ⟨Hnew, Hnew_cap, %Hcap⟩
    ihave %Hsl_wf := ownSlice_wf _ _ _ $$ Hnew
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hsl_len
    wp_apply wp_slice_copy nsl _ sl vs DFrac.discard $$ [Hnew Hs] with %n' ⟨%Hn', Hnew, _⟩
    · iframe Hnew Hs
    rw [ite_eq_left ⟨by word, by word, by rw [Hcap]; exact Hcap_ge⟩]
    wp_auto
    icases (ownSlice_slice sl.len (sl.len + sl2.len) nsl _ _ ⟨by word, by word, by word⟩).1 $$ Hnew
      with ⟨Hnew1, Hnew2, _⟩
    wp_apply wp_slice_copy _ _ sl2 vs' dq $$ [Hnew2 Hs2] with %n'' ⟨%Hn'', Hnew2, Hs2⟩
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
    imod ownSlice_persist _ _ _ $$ H with #H
    iapply HΦ
    iframe Hs2 Hnew_cap H

end append

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem readOnly.addRequest.wp_proof : readOnly.addRequest.spec (GF := GF) (hG := hG) := by
  intro ro r commitIndex req ents
  wp_start as Hown
  iNamed Hown
  unfold ownReadOnly
  iNamed Hown
  wp_auto
  ipersist «$sl0»
  wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_slice_append_persistent (V := Loc) _ _ _ _ _ $$ [$Hucr_cap $Hucr $Hsl]
    as %s' ⟨Hs', Hcap', -⟩
  iapply HΦ
  iexists { rov with unconfirmedReads' := s' }, ptrs ++ [«$sl0_ptr»]
  simp only [readonlyAdd, named]
  iframe Hro Hacks Hs' Hcap'
  isplitr
  · ipureintro; exact Hro_safe
  isplitr
  · ipureintro; exact Hro_conf
  iapply BigSepL2.bigSepL2_snoc.2
  iframe Hreqs
  unfold ownReadreq
  iexists _
  iframe «$sl0» Hents
  ipureintro
  exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
