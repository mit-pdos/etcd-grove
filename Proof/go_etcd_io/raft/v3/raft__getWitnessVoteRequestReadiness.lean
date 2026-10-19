/-
`(*raft).getWitnessVoteRequestReadiness` on a witness-free configuration (2026-10-19, witness
support): both witnesses read `0`, so the function returns `nil` before it makes a map.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__getWitnessVoteRequestReadiness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.getWitnessVoteRequestReadiness.wp_proof :
    raft.getWitnessVoteRequestReadiness.spec (GF := GF) (hG := hG) := by
  intro c V r id s d
  wp_start as Hphys
  wp_auto
  wp_join at next with [Hphys r]
  · done
  done

end proof

end EtcdGrove
end Perennial
