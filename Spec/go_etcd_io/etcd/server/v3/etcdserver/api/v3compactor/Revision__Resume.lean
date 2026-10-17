/-
`(*Revision).Resume` (`revision.go`; unchanged by etcd#18472). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `rc.Resume()` on a revision compactor returns (it clears `paused` under the mutex). -/
abbrev v3compactor.Revision.Resume.spec : Prop :=
  ∀ (rc : Loc) (P : RVParams),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isRevision rc P }}
    (App (Val (rc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty @!! go!"Resume")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
