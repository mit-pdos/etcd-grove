/-
`read.Read.sendReadIndex(requestIndex)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Inv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.read

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `r.sendReadIndex(id)` with a lower bound `n` of the committed index: an error the gRPC layer
can take (raft's, or `nil`), and if `nil` the registration of `id` at `n` (`RQ id n`). The
logger's resource `LR` is given back. -/
abbrev read.Read.sendReadIndex.spec : Prop :=
  ∀ (r : Loc) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) (LR NR : IProp GF) (id n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      isReadLoopPre r γr RQ LR NR ∗ LR ∗ committedAtLeast γr n }}
    (App (Val (r @!! go.GoType.PointerType Read.ty @!! go!"sendReadIndex")) (Val #id))
  {{ (err : GoInterface), RET #err; LR ∗ applyErrIs err ∗
      (⌜err = GoInterface.nil⌝ -∗ □ RQ id n) }}

end spec

end EtcdGrove
end Perennial
