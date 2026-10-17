/-
The trust boundary: `fileutil.Fsync(f)` (`client/pkg/fileutil/sync_linux.go`: `f.Sync()`, `fsync(2)`; names-only).
Lean-first (no Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`), see
`InvSnapshotBackend.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync

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

axiom fileutil.Fsync.wp_proof : fileutil.Fsync.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
