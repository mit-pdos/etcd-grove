/- Port of election_proof/proof_raftLog__mustCheckOutOfBounds.v. -/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__mustCheckOutOfBounds
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__firstIndex
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastIndex

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

/-- The body reads no field of the log itself outside the two dead `Panicf` branches,
so `ownRaftLog` could stay sealed -- except for one pure fact. The last guard is
`hi > fi + (lastIndex() + 1 - fi)`, i.e. `hi > lastIndex() + 1` in `w64`; the range
premise gives `uint hi <= prev.index + |sents| + |uents| + 1 = uint li + 1` over `Int`,
which only rules the guard out if `li + 1` does not wrap. That is `Hnowrap`, inside the
predicate, so it is peeled off (and the predicate re-sealed) before the walk. -/
theorem raftLog.mustCheckOutOfBounds.wp_proof
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.mustCheckOutOfBounds.spec (GF := GF) (hG := hG) := by
  intro l ls lo hi Hrange
  wp_start as H
  iNamed H
  icases ownRaftLog_nowrap l ls $$ Hlog with ⟨%Hnw, Hlog⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_apply wp_raftLog_firstIndex _ ls $$ [$Hlog] as %fi ⟨Hlog, %Hfi⟩
  wp_if_destruct
  · exfalso; word
  wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  wp_if_destruct
  · exfalso; word
  iapply HΦ
  iframe Hlog

end proof

end EtcdGrove
end Perennial
