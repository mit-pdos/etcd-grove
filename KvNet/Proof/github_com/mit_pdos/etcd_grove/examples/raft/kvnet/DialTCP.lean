/-
The proof of `KvNet/Spec/.../kvnet/DialTCP.lean`: `net.DialTimeout`'s spec at `"tcp"`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DialTCP
public import KvNet.Spec.net.DialTimeout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions]

theorem DialTCP.wp_proof (wp_DialTimeout : net.DialTimeout.spec (GF := GF) (hG := hG)) :
    DialTCP.spec (GF := GF) (hG := hG) := by
  intro a dur et ed Qfail Qok
  wp_start as ⟨%Ha, #Het, #Hed, Hupd⟩
  wp_auto
  wp_apply wp_DialTimeout go!"tcp" (Or.inl rfl) a dur et ed Qfail Qok $$ [Hupd] as %c %err Hpost
  · iframe Het Hed Hupd
    ipureintro; exact Ha
  try wp_auto
  iapply HΦ
  iexact Hpost

end proof

end raft_kvnet
end EtcdGrove
end Perennial
