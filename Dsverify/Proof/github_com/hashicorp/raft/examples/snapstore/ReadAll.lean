/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc/ReadAll.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
The proof of `snapstore.ReadAll`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.ReadAll

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.snapstore.ReadAll.wp_proof :
    github_com.hashicorp.raft.examples.snapstore.ReadAll.spec (GF := GF) (hG := hG) :=
  fun src R b eof => by
  wp_start as ⟨#Heof, #Hrd, HR⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ [Hpkg]
  · iPkgInit
  ihave #HE := io.eof_of_init $$ Hio
  unfold errors.newVar
  icases HE with ⟨%xe, #HE, -⟩
  icombine HE Heof gives %Hee
  subst Hee
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 512)) as %bsl ⟨Hbsl, -⟩
  · ipureintro; decide
  ihave Hout : (slice.nil ↦* ([] : List w8)) $$ []
  · iapply ownSlice_nil
  ihave Hocap : (ownSliceCap w8 slice.nil (DFrac.own 1)) $$ []
  · iapply ownSliceCap_nil
  ihave HI : (∃ (osl : GoSlice) (ob rest bufc : List w8),
      "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* ob ∗ "Hocap" ∷ ownSliceCap w8 osl (DFrac.own 1) ∗
      "buf" ∷ buf_ptr ↦ bsl ∗ "Hbuf" ∷ bsl ↦* bufc ∗ "%Hbl" ∷ ⌜bufc.length = 512⌝ ∗
      "HR" ∷ R rest ∗ "%Hb" ∷ ⌜ob ++ rest = b⌝ : IProp GF) $$ [out buf Hout Hocap Hbsl HR]
  · iexists slice.nil, [], b
    iexists _
    iframe
    ipureintro; exact ⟨by rw [List.length_replicate], rfl⟩
  wp_for HI
  ihave #Hrd2 := Hrd
  unfold streamReaderOk
  wp_bind (App (Val #(methods src.ty go!"Read" src.v)) (Val #bsl))
  iapply Hrd2 $$ %bsl %bufc %rest %_ [] HR Hbuf
  · ipureintro; omega
  iintro %n %err %Hn Hbuf HR
  wp_auto
  ihave %Hbl2 := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hbuf
  have Hlen2 : (List.take (sint.nat n) rest ++ List.drop (sint.nat n) bufc).length = 512 := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  rw [if_pos ⟨by decide, by word, by word⟩]
  icases (ownSlice_slice (W64 0) n bsl (DFrac.own 1) _ ⟨by decide, by word, by word⟩).1 $$ Hbuf
    with ⟨Hb0, Hbn, Hbr⟩
  have Hsub : subslice (sint.nat (W64 0)) (sint.nat n)
      (List.take (sint.nat n) rest ++ List.drop (sint.nat n) bufc) = rest.take (sint.nat n) := by
    rw [show sint.nat (W64 0) = 0 from rfl, subslice_from_start, List.take_append_of_le_length
      (by rw [List.length_take]; omega), List.take_take, Nat.min_self]
  rw [Hsub]
  wp_auto
  wp_apply (wp_slice_append (V := w8)) $$ [$Hout $Hocap $Hbn] as %osl' ⟨Hout, Hocap, Hbn⟩
  ihave Hbuf := (ownSlice_slice (W64 0) n bsl (DFrac.own 1) _ ⟨by decide, by word, by word⟩).2 $$ [Hb0 Hbn Hbr]
  · rw [Hsub]; iframe
  obtain ⟨Hn0, Hnb, Hnr, Herr⟩ := Hn
  rcases Herr with rfl | ⟨rfl, Hnl⟩
  · wp_auto
    wp_for_post
    iframe
    iexists osl', ob ++ List.take (sint.nat n) rest, List.drop (sint.nat n) rest, _
    iframe
    ipureintro
    refine ⟨Hlen2, ?_⟩
    rw [List.append_assoc, List.take_append_drop]; exact Hb
  · wp_auto
    wp_for_post
    iapply HΦ
    rw [List.take_of_length_le (by omega), Hb, List.drop_of_length_le (by omega)]
    iframe
  done

end proof

end Perennial
