/-
`v3compactor.Revision.Run` (`revision.go`). Lean-first (no Rocq counterpart); the spec-first pilot
(`notes/compactor-pilot-plan.md`, phase 1: the specs, written before the proofs).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `rc.Run()`: starts the goroutine that, every 5 minutes, compacts at `Rev() - retention`, and returns.
The goroutine keeps the server's `E.R`, and calls `Compact` only at revisions C1's revision permit
allows. -/
abbrev v3compactor.Revision.Run.spec : Prop :=
  ∀ (rc : Loc) (E : CompactEnv GF) (ret : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ isRevision rc E ret ∗ E.R }}
    (App (Val (rc @!! go.GoType.PointerType v3compactor.Revision.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
