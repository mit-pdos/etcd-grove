-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Cluster__sender.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/Cluster__sender.lean`. Lean-first
(no Rocq counterpart).

The closure captures the cells of `c` and `from`, made read-only (persistent), so that it can be
called any number of times; each call is `send` (`Cluster.send`).
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Cluster__sender
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Cluster__send
public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.sender.wp_proof
    (wp_send : Cluster.send.spec (GF := GF) (hG := hG)) :
    Cluster.sender.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c src
  wp_start as ⟨#Hcc, #Hkn⟩
  iapply wp_fupd
  try wp_auto
  ipersist c
  ipersist «from»
  imodintro
  iapply HΦ
  unfold sendSpec
  imodintro
  iintro %msl %ms %Φ'
  imodintro
  iintro ⟨#Hpkg, Hmsl, Hmsok⟩ HΦ'
  try wp_auto
  wp_apply wp_send γ vs dir c src msl ms $$ [$Hcc $Hkn $Hmsl $Hmsok]
  try wp_auto
  iapply HΦ'
  itrivial

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
