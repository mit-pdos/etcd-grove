/-
(hraft_robust R3) The proof of `disk.decodeConfiguration`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__uint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.reader__bytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration

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

theorem dk_cfg_drop (ss : List SServer) (k : Nat) (sv : SServer) (rest : List w8) (h : ss[k]? = some sv) :
    (ss.drop k).flatMap encServer ++ rest = encU64 sv.suffrage ++ (encBytes sv.id ++
      (encBytes sv.addr ++ ((ss.drop (k + 1)).flatMap encServer ++ rest))) := by
  rw [dk_flatMap_drop ss encServer k sv h]; unfold encServer; simp only [List.append_assoc]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration.wp_proof
    (wp_uint64 : github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.spec (GF := GF) (hG := hG))
    (wp_bytes : github_com.hashicorp.raft.examples.hraftnet.disk.reader.bytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.decodeConfiguration.spec (GF := GF) (hG := hG) := by
  intro r ss rest hss hlens
  unfold encCfg
  rw [List.append_assoc]
  wp_start as Hr
  wp_auto
  wp_apply wp_uint64 $$ [$Hr] as Hr
  ihave HI : (∃ (i : w64) (cv : Configuration) (svs : List Server),
      "i" ∷ i_ptr ↦ i ∗ "c" ∷ c_ptr ↦ cv ∗ "Hsl" ∷ cv.Servers' ↦* svs ∗
      "Hcap" ∷ ownSliceCap Server cv.Servers' (DFrac.own 1) ∗
      "Hr" ∷ readerSt r ((ss.drop (uint.nat i)).flatMap encServer ++ rest) ∗
      "%Hsv" ∷ ⌜svs.map srvOf = ss.take (uint.nat i)⌝ ∗
      "%Hi" ∷ ⌜uint.nat i ≤ ss.length⌝ : IProp GF) $$ [i c Hr]
  · iexists W64 0, _, []
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HI
  wp_if_destruct
  · have hil : uint.nat i < ss.length := dk_ulen_lt i _ hss Hif
    list_elem ss (uint.nat i) as sv
    have hsl := hlens sv (List.mem_of_getElem? Hsv_lookup)
    iunfold readerSt at Hr
    icases Hr with ⟨%rb, Hr, #Hrb⟩
    wp_auto
    simp only [decide_true, ↓reduceIte]
    wp_auto
    ihave Hr : readerSt r ((ss.drop (uint.nat i)).flatMap encServer ++ rest) $$ [Hr]
    · iunfold readerSt; iexists rb; iframe; iexact Hrb
    ihave Hr := (show (readerSt r ((ss.drop (uint.nat i)).flatMap encServer ++ rest) : IProp GF) ⊢
      readerSt r (encU64 sv.suffrage ++ (encBytes sv.id ++
        (encBytes sv.addr ++ ((ss.drop (uint.nat i + 1)).flatMap encServer ++ rest)))) by
      rw [dk_cfg_drop ss _ sv rest Hsv_lookup]) $$ Hr
    wp_apply wp_uint64 $$ [$Hr] as Hr
    wp_apply wp_bytes _ _ _ hsl.1 $$ [$Hr] as %sid ⟨Hr, Hsid, -⟩
    wp_apply (wp_bytes_to_string sid sv.id (DFrac.own 1)) $$ [$Hsid] as -
    wp_apply wp_bytes _ _ _ hsl.2 $$ [$Hr] as %sad ⟨Hr, Hsad, -⟩
    wp_apply (wp_bytes_to_string sad sv.addr (DFrac.own 1)) $$ [$Hsad] as -
    wp_apply (wp_slice_literal (V := Server) [⟨sv.suffrage, sv.id, sv.addr⟩])
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hlit, -⟩
    wp_apply (wp_slice_append (V := Server)) $$ [$Hsl $Hcap $Hlit] as %sl2 ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, _, _
    iframe
    rw [dk_usucc i _ hss hil]
    iframe
    ipureintro
    refine ⟨?_, hil⟩
    rw [List.map_append, Hsv, List.take_add_one, Hsv_lookup]
    rfl
  · have hie := dk_ulen_eq i _ hss Hi Hif
    rw [hie, List.take_length] at Hsv
    ihave Hr := (show (readerSt r ((ss.drop (uint.nat i)).flatMap encServer ++ rest) : IProp GF) ⊢
      readerSt r rest by rw [hie, List.drop_length, List.flatMap_nil, List.nil_append]) $$ Hr
    iapply HΦ
    iframe
    ipureintro; exact Hsv

end proof

end Perennial
