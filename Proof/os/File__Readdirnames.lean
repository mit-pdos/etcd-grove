/-
The trust boundary: `os.File.Readdirnames` (the standard library, names-only here: no file-system model).
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046`), for
`(*snap.Snapshotter).ReleaseSnapDBs`.
-/
module

public import Spec.os.File__Readdirnames

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

axiom os.File.Readdirnames.wp_proof : os.File.Readdirnames.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
