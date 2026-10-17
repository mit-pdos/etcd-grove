/-
`os.Remove` (the standard library, names-only here: no file-system model). The trust boundary.
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

/-- `os.Remove(p)`, which needs the right to remove `p` (`fs.removable p`: an abstract resource, see
`etcdserver/api/snap/Defs.lean`); nil or an error. -/
abbrev os.Remove.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ fs.removable p }}
    (App (Val (@! _root_.Perennial.os.Remove)) (Val #p))
  {{ (err : GoInterface), RET #err; fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
