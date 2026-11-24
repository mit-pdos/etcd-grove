/-
The proof of `KvNet/Spec/.../kvnet/Request.lean`: `RequestWithin`'s spec, at the total
`timeout + requestMargin`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Request
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RequestWithin

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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem Request.wp_proof (wp_RequestWithin : RequestWithin.spec (GF := GF) (hG := hG)) :
    Request.spec (GF := GF) (hG := hG) := by
  intro addr kind tmo payload pl dqp W Rd Fl eof ed et Hpl
  wp_start as ⟨Hp, #Heof, #Hed, #Het, %Ha, Hupd⟩
  wp_auto
  wp_apply wp_RequestWithin addr kind tmo _ payload pl dqp W Rd Fl eof ed et Hpl $$ [Hp Hupd]
    as %b %ok Hpost
  · iframe Hp Heof Hed Het Hupd
    ipureintro; exact Ha
  try wp_auto
  iapply HΦ
  iexact Hpost

end proof

end raft_kvnet
end EtcdGrove
end Perennial
