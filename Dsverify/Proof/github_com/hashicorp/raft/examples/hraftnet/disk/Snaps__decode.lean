/-
(hraft_robust R3) The proof of `disk.(*Snaps).decode`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__uint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__bytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__done
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__decode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.decode.wp_proof
    (wp_uint64 : github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.spec (GF := GF) (hG := hG))
    (wp_bytes : github_com.hashicorp.raft.examples.hraftnet.disk.reader.bytes.spec (GF := GF) (hG := hG))
    (wp_done : github_com.hashicorp.raft.examples.hraftnet.disk.reader.done.spec (GF := GF) (hG := hG))
    (wp_decodeConfiguration :
      github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.decode.spec (GF := GF) (hG := hG) := by
  intro s b S hok
  unfold snapsMem snapsMem0 encSnap
  unfold SnapImg.Ok at hok
  rcases hS : S.latest with _ | ⟨m, bs⟩ <;> rw [hS] at hok <;> dsimp only at hok ⊢
  · wp_start as ⟨⟨%mv, %dt, %nid, Hhas, Hmeta, Hdata, Hnid, %Hp⟩, #Hb⟩
    wp_auto
    ihave Hr : readerSt «$r0_ptr» (encU64 S.nextID ++ encU64 (W64 0)) $$ [«$r0»]
    · iunfold readerSt; iexists b; iframe; iexact Hb
    wp_apply wp_uint64 $$ [$Hr] as Hr
    rw [← List.append_nil (encU64 (W64 0))]
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_done $$ [$Hr] as Hr
    iapply HΦ
    iframe
    ipureintro; rfl
  · obtain ⟨hid, hsrv, hbs, hsrvs⟩ := hok
    simp only [List.append_assoc]
    rw [← List.append_nil (encBytes bs)]
    wp_start as ⟨⟨%mv, %dt, %nid, Hhas, Hmeta, Hdata, Hnid, %Hp⟩, #Hb⟩
    wp_auto
    ihave Hr : readerSt «$r0_ptr» _ $$ [«$r0»]
    · iunfold readerSt; iexists b; iframe; iexact Hb
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_bytes _ _ _ hid $$ [$Hr] as %sid ⟨Hr, Hsid, -⟩
    wp_apply (wp_bytes_to_string sid m.id (DFrac.own 1)) $$ [$Hsid] as -
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_decodeConfiguration _ _ _ hsrv hsrvs $$ [$Hr] as %cv ⟨Hr, %svs, Hsvs, Hsvcap, %Hsvs⟩
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_bytes _ _ _ hbs $$ [$Hr] as %sd ⟨Hr, Hsd, -⟩
    ihave %Hsdl := ownSlice_len $$ Hsd
    ipersist Hsd
    ipersist Hsvs
    wp_apply wp_done $$ [$Hr] as Hr
    iapply HΦ
    iexists true, _, sd
    iframe
    isplitr
    · ipureintro; rfl
    isplitl []
    · iunfold metaRep
      isplitr
      · ipureintro
        simp only
        exact ⟨trivial, trivial, trivial, trivial, Hp, trivial, dk_w64_of_length bs sd.len Hsdl⟩
      iunfold cfgRep
      iexists svs
      iframe #
      ipureintro; exact Hsvs
    iexact Hsd

end proof

end Perennial
