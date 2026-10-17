/-
The trust boundary: `os.Rename(src, dst)` (Perennial's `os` is names-only; no file-system model). Lean-first (no Rocq
counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`), see `InvSnapshotBackend.lean`.
-/
module

public import Spec.os.Rename

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

axiom os.Rename.wp_proof : os.Rename.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
