module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot

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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KvrStor GF]

theorem Storage.Snapshot.wp_proof
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG)) :
    Storage.Snapshot.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): broken by the MemoryStorage statement changes (mode o, memStorFresh c sv)

end proof

end kvreconf
end EtcdGrove
end Perennial
