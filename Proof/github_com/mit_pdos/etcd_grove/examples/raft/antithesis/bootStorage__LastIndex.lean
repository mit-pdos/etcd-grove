/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/bootStorage__LastIndex.lean`: the
`MemoryStorage`'s method, called on the wrapper's field (as kvreconf's `KvrStorageApi.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem bootStorage.LastIndex.wp_proof (wp : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG)) :
    bootStorage.LastIndex.spec (GF := GF) (hG := hG) := by
  intro s ms vs γs e
  wp_start as ⟨#Hrec, HP⟩
  iunfold bootStorRec at Hrec
  icases Hrec with ⟨%vsl, #Hms, -⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp ms γs e $$ [$Hraft HP] as %li HQ
  · iexact HP
  try wp_auto
  iapply HΦ
  iexact HQ

end proof

end AntHarness
end EtcdGrove
end Perennial
