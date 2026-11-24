/-
The proof of `KvNet/Spec/.../kvnet/stopIncarnation.lean` (2026-11-24, G5) at the store's stopper
`kvStp γ vs dir` and start resource `kvNodeStart γ vs dir`: `Replica.stop` gives the generation's start
resource `kvStart` back, then the transport's `stop` (`ptStop`); `kvNodeStart` is that with the
stopper's persistent rest.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.stopIncarnation
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica__stop
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [go.IntoValInj GoString] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel
theorem stopIncarnation.wp_proof (wp_stop : Replica.stop.spec (GF := GF) (hG := hG))
    (γ : KdNames) (vs : List w64) (dir : GoString) :
    stopIncarnation.spec (GF := GF) (hG := hG) (kvStp γ vs dir) (kvNodeStart γ vs dir) := by
  intro cfg M
  iunfold stopLaw
  iintro !> %r %tv
  wp_start as Hs
  simp only [kvStp]
  icases Hs with ⟨Hrs, Hpt, %Hdir, #Hglob, #Hpeers, %Hopts⟩
  iunfold ptStop at Hpt
  icases Hpt with ⟨%i, %Hi, Hpt⟩
  subst Hi
  try wp_auto
  wp_apply wp_stop γ vs dir cfg.ID' r $$ [$Hrs] as ⟨%fl, %qc, Hst⟩
  wp_apply Hpt
  iapply HΦ
  iunfold kvNodeStart
  isplitr
  · ipureintro; exact Hdir
  iexists fl, qc
  iframe Hst Hglob Hpeers
  ipureintro; exact Hopts

end proof

end raft_kvnet
end EtcdGrove
end Perennial
