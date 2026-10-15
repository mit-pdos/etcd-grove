/-
`read.notifier.notify(err)` (util.go): store the error, close the channel. Lean-first (no Rocq counterpart); the request path's unit 4a, see
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

/-- `nc.notify(err)`, with the right to notify `nc`, an error the gRPC layer can take, and if it is
`nil` the loop's answer (`frozenOk`): `nc.err` becomes `err` for good and the close tells the
waiters `notified`. -/
abbrev read.notifier.notify.spec : Prop :=
  ∀ (nc : Loc) (γn : GName) (γr : ReadNames) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      notifierOwn nc γn γr ∗ applyErrIs err ∗ (⌜err = GoInterface.nil⌝ -∗ frozenOk γn γr) }}
    (App (Val (nc @!! go.GoType.PointerType notifier.ty @!! go!"notify")) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
