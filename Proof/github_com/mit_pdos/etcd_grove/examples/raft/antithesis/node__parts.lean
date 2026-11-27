/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__parts.lean`: with `Split = 0`
none of the split orders applies, so the write is one part.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__parts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.parts.wp_proof : node.parts.spec (GF := GF) (hG := hG) := by
  intro c γ n j hp hp0 sl
  wp_start as ⟨#Hc, #Hn, Hhs, %Hsplit⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hns, #Hnsl, %HN, #Hmd, #Hiv, #Hivs⟩
  ihave Hmd' := Hmd
  iStructNamed Hmd'
  iunfold nodeRO at Hn
  icases Hn with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  wp_auto
  ihave Hnil := ownSlice_nil (V := H.part) (GF := GF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := H.part) (GF := GF)
  wp_if_destruct
  · try wp_auto
    rw [Hsplit]
    wp_auto
    wp_apply wp_slice_literal (V := H.part) [({ hs' := zero_val Loc, ents' := sl, after' := hp } : H.part)]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_slice_append (V := H.part) $$ [Hnil Hcap Hsl2] as %s3 ⟨Hs3, -, -⟩
    · iframe Hnil
      iframe Hcap
      iexact Hsl2
    iapply HΦ
    iframe Hhs
    rw [if_pos Hif, ← List.nil_append [({ hs' := null, ents' := sl, after' := hp } : H.part)]]
    iexact Hs3
  · try wp_auto
    rw [Hsplit]
    wp_auto
    wp_apply wp_slice_literal (V := H.part) [({ hs' := hp, ents' := sl, after' := hp } : H.part)]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_slice_append (V := H.part) $$ [Hnil Hcap Hsl2] as %s3 ⟨Hs3, -, -⟩
    · iframe Hnil
      iframe Hcap
      iexact Hsl2
    iapply HΦ
    iframe Hhs
    rw [if_neg Hif]
    iapply (show (s3 ↦* ([] ++ [({ hs' := hp, ents' := sl, after' := hp } : H.part)]) : IProp GF) ⊢
      s3 ↦* [({ hs' := hp, ents' := sl, after' := hp } : H.part)] by rw [List.nil_append])
    iexact Hs3

end proof

end AntHarness
end EtcdGrove
end Perennial
