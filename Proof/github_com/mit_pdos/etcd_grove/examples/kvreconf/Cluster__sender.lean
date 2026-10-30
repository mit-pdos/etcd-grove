/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__sender.lean`. Lean-first
(no Rocq counterpart).

The closure captures the cells of `c` and `from`, made read-only (persistent), so that it can be
called any number of times; each call is `send` (`Cluster.send`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__sender
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__send

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.sender.wp_proof
    (wp_send : Cluster.send.spec (GF := GF) (hG := hG)) :
    Cluster.sender.spec (GF := GF) (hG := hG) := by
  intro γr vs c src
  wp_start as ⟨#Hcc, #Hkn⟩
  iapply wp_fupd
  try wp_auto
  ipersist c
  ipersist «from»
  rw [recv_eq_func_mk]
  imodintro
  iapply HΦ
  unfold sendSpec
  imodintro
  iintro %msl %ms %Φ'
  imodintro
  iintro ⟨#Hpkg, Hmsl, Hmsok⟩ HΦ'
  try wp_auto
  wp_apply wp_send γr vs c src msl ms $$ [$Hcc $Hkn $Hmsl $Hmsok]
  try wp_auto
  iapply HΦ'
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
