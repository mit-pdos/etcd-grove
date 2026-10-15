/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__GetContext.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.ConfChangeV2.GetContext.wp_proof :
    raftpb.ConfChangeV2.GetContext.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq m
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ
      iframe Hcs
      iunfold ownCCV2
      iexists pt, chs, ls, cs, uf
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cT Hccs Hcs Hpb
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
