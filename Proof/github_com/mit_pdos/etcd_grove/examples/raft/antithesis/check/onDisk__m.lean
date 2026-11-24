/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.m()` (B 291-359, `OnDisk.m`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__m
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.msgSeqHead
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.m.wp_proof (wp_msgSeqHead : msgSeqHead.spec (GF := GF) (hG := hG)) :
    onDisk.m.spec (GF := GF) (hG := hG) := by
  intro g x v
  wp_start as ⟨#Hx, %Hv⟩
  iunfold onDiskRO at Hx
  icases Hx with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  iunfold qitemRO at Hq
  icases Hq with ⟨#He, #Hm⟩
  wp_auto
  wp_apply wp_msgSeqHead g.q'.M' x.q.m v $$ [Hm] as %u #Hu
  · iframe Hm; ipureintro; exact Hv
  try wp_auto
  iapply HΦ; iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
