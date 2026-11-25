/-
The proof of `KvRaft/Spec/.../kvraft/Request.lean`: `RequestWithin`'s spec, at the total
`timeout + requestMargin`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Request
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RequestWithin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions]

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

end kvraft
end EtcdGrove
end Perennial
