/-
The trust boundary: `raftpb.MessageType.String` (names-only). Lean-first (PR etcd#21401).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom raftpb.MessageType.String.wp_proof : raftpb.MessageType.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
