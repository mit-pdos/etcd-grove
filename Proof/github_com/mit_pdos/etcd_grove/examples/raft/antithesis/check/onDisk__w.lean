/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.w()` (B 291-359, `OnDisk.w`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem onDisk.w.wp_proof : onDisk.w.spec (GF := GF) (hG := hG) := by
  intro g x
  wp_start as #Hx
  iunfold onDiskRO at Hx
  icases Hx with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  iunfold qitemRO at Hq
  icases Hq with ⟨#He, #Hm⟩
  wp_auto
  iapply HΦ
  rw [show x.w = x.q.ev from rfl]
  iexact He

end proof

end AntCheck
end EtcdGrove
end Perennial
