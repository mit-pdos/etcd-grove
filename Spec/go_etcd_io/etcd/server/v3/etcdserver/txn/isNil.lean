/-
`txn.isNil` (`util.go`: `msg == nil || reflect.ValueOf(msg).IsNil()`). Lean-first (no Rocq
counterpart); unit P4 (2026-10-14).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `isNil(m)` of a message holding the pointer `p` (of any type `*T`): whether `p` is nil. -/
abbrev txn.isNil.spec : Prop :=
  ∀ (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.isNil))
      (Val #(interface.mkOk (go.GoType.PointerType T) #p)))
  {{ RET #(decide (p = null)); True }}

end spec

end EtcdGrove
end Perennial
