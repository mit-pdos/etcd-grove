/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.fm()` (B 291-359, `OnDisk.fm`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__m
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReqFactIn
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

theorem onDisk.fm.wp_proof (wp_m : onDisk.m.spec (GF := GF) (hG := hG))
    (wp_ReqFactIn : ReqFactIn.spec (GF := GF) (hG := hG)) :
    onDisk.fm.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  unfold OnDisk.fm at Hv
  obtain ⟨m, hm, Hv⟩ := bind_ok Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'm.method_unfold]
  try wp_auto
  wp_apply wp_m gx x m $$ [Hx] as %u #Hu
  · iframe Hx; ipureintro; exact hm
  try wp_auto
  wp_apply wp_ReqFactIn gx.ll' x.ll u m v $$ [Hll Hu] as %r #Hr
  · iframe Hll Hu; ipureintro; exact Hv
  try wp_auto
  iapply HΦ; iexact Hr

end proof

end AntCheck
end EtcdGrove
end Perennial
