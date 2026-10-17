/-
`snap.fsyncSnapDir` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
PR #22046 (branch `pr-verify/etcd-22046`), for `(*snap.Snapshotter).SaveDBFrom`.
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

/-- `fsyncSnapDir(dir)` (names-only): nil or an error. -/
abbrev snap.fsyncSnapDir.spec : Prop :=
  ∀ (dir : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap }}
    (App (Val #(functions go_etcd_io.etcd.server.v3.etcdserver.api.snap.fsyncSnapDir [])) (Val #dir))
  {{ (err : GoInterface), RET #err; fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
