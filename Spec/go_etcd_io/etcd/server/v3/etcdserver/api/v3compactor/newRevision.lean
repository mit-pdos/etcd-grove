/-
`v3compactor.newRevision`: the trust boundary (names only: the revision compactor's constructor, which
etcd#22095 does not change). Lean-first (no Rocq counterpart).
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

/-- `newRevision(lg, clock, retention, rg, c)` returns some `*Revision` (what it does is not
stated: `New`'s spec says nothing of the revision compactor). -/
abbrev v3compactor.newRevision.spec : Prop :=
  ∀ (lg : Loc) (clk : GoInterface) (retention : w64) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision)) (Val #lg)) (Val #clk)) (Val #retention))
      (Val #rg)) (Val #c))
  {{ (p : Loc), RET #p; True }}

end spec

end EtcdGrove
end Perennial
