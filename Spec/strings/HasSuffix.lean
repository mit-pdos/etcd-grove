/-
`strings.HasSuffix` (the standard library, names-only here: no file-system model). The trust boundary.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046`), for
`(*snap.Snapshotter).ReleaseSnapDBs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strings.HasSuffix(s, suffix)`: some boolean. -/
abbrev strings.HasSuffix.spec : Prop :=
  ∀ (s suffix : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val (@! _root_.Perennial.strings.HasSuffix)) (Val #s)) (Val #suffix))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
