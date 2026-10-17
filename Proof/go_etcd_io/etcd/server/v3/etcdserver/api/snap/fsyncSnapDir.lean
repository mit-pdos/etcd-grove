/-
The trust boundary: `snap.fsyncSnapDir` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
PR #22046 (branch `pr-verify/etcd-22046`), for `(*snap.Snapshotter).SaveDBFrom`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.fsyncSnapDir

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

axiom snap.fsyncSnapDir.wp_proof : snap.fsyncSnapDir.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
