/-
`os.IsNotExist` (the standard library, names-only here: no file-system model). The trust boundary.
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

/-- `os.IsNotExist(err)`: some boolean. -/
abbrev os.IsNotExist.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os }}
    (App (Val (@! _root_.Perennial.os.IsNotExist)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
