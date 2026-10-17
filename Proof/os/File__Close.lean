/-
The trust boundary: `(*os.File).Close()` (Perennial's `os` is names-only). Lean-first (no Rocq counterpart);
etcd PR #22518 (branch `pr-verify/etcd-22518`), see `InvSnapshotBackend.lean`.
-/
module

public import Spec.os.File__Close

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

axiom os.File.Close.wp_proof : os.File.Close.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
