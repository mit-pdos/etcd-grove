/-
`read.Read.requestCurrentIndex(leaderChangedNotifier)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
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

/-- `r.requestCurrentIndex(lcn)` with a lower bound `n` of the committed index (and the leader-change
channel `lcn`, closed with no content): an index and an error the gRPC layer can take; if `nil`, the
index is at least `n` (a read state answering one of the call's requests, each registered at `n`).
The logger's resource `LR` is given back; the id resource `NR` comes from the server's premise
`□ |==> NR` (the id budget). -/
abbrev read.Read.requestCurrentIndex.spec : Prop :=
  ∀ (r : Loc) (γr : ReadNames) (RQ : w64 → w64 → IProp GF) (LR NR : IProp GF) (lcn : Loc)
    (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      isReadLoopPre r γr RQ LR NR ∗ LR ∗ □ (|==> NR) ∗ bcastChan lcn iprop(True) ∗
      committedAtLeast γr n }}
    (App (Val (r @!! go.GoType.PointerType Read.ty @!! go!"requestCurrentIndex")) (Val #lcn))
  {{ (ci : w64) (err : GoInterface), RET (PairV #ci #err); LR ∗ applyErrIs err ∗
      (⌜err = GoInterface.nil⌝ -∗ ⌜uint.Z n ≤ uint.Z ci⌝) }}

end spec

end EtcdGrove
end Perennial
