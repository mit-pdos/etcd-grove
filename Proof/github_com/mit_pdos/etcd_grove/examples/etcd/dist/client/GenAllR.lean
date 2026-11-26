/- Lean-first (no Rocq counterpart). Proof of `Spec/.../dist/client/GenAllR.lean` (#50 N10a): `GenAll`'s
loop (`lib/etcdstart/GenAll.lean`'s proof), each iteration taking the time receipt of a resolution step
(`append`'s, `wp_take_receipt`) into the invariant's `⧗ i`; at the end `⧗ n`, so `n < receiptBound GF` (`receipt_lt`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.GenAllR
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode etcdstart
  github_com.mit_pdos.etcd_grove.examples.lib.etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

theorem GenAll_receipts.wp_proof (wp_Gen : Gen.spec (GF := GF) (hG := hG)) :
    GenAll_receipts.spec (GF := GF) (hG := hG) := by
  intro n ksl ks hn hk0 hk63
  wp_start as #Hk
  imod (receipt_zero (GF := GF)) with Hr0
  (try wp_auto)
  ihave HI : (∃ (j : w64) (sl : GoSlice) (ps : List wkv),
      "i" ∷ i_ptr ↦ j ∗ "all" ∷ all_ptr ↦ sl ∗ "Hs" ∷ sl ↦* ps ∗
      "Hcap" ∷ ownSliceCap wkv sl (DFrac.own 1) ∗ "Hrs" ∷ ⧗ (sint.nat j) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n ∧ ps.length = sint.nat j ∧
        ∀ p ∈ ps, GenKv ks p⌝ : IProp GF) $$ [i all Hr0]
  · iexists W64 0, slice.nil, []
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by word, by word, rfl, fun _ h => by simp at h⟩
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_Gen ksl ks hk0 hk63) as %p %Hp
    · iframe #
    wp_apply wp_slice_literal (l := [p])
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, _⟩
    simp only [go.arrayLiteralSize, List.foldl]
    -- the iteration's counted step: `append`'s resolution (`wp_if_destruct` already took `Gen`'s)
    wp_take_receipt as Hr
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hl1] as %sl' ⟨Hs, Hcap, -⟩
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    ihave Hrs := (receipt_add (GF := GF) (sint.nat j) 1).2 $$ [Hrs Hr]
    · iframe
    wp_for_post
    iframe
    iexists j + W64 1, sl', ps ++ [p]
    iframe
    rw [hj1]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp only [List.length_append, List.length_singleton, Hj.2.2.1], ?_⟩
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact Hj.2.2.2 q hq
    · exact Hp
  · (try wp_auto)
    have hjn : sint.nat j = sint.nat n := by word
    ihave %Hlt := receipt_lt (GF := GF) (sint.nat j) $$ Hrs
    iapply HΦ
    iexists ps
    iframe
    ipureintro
    refine ⟨by rw [Hj.2.2.1]; word, Hj.2.2.2, by rw [← hjn]; exact Hlt⟩

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
