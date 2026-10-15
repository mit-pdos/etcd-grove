/-
`read.newNotifier()` (util.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
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

/-- `newNotifier()`: a new notifier `nc` with a fresh need `γn` at `0` (its authority), its
waiters' view (`notifierIs`) and the right to notify it (`notifierOwn`). -/
abbrev read.newNotifier.spec : Prop :=
  ∀ (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.newNotifier)) (Val #()))
  {{ (nc : Loc), RET #nc; ∃ γn : GName, notifierIs nc γn γr ∗ notifierOwn nc γn γr ∗
      monoNatAuthOwn γn 1 0 }}

end spec

end EtcdGrove
end Perennial
