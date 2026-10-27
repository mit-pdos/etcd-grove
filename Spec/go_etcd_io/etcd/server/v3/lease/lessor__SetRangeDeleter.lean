/-
`(*lessor).SetRangeDeleter` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.SetRangeDeleter(rd)` (locked): sets the range deleter, by its owner (`rdOwn`, unit T3). -/
abbrev lease.lessor.SetRangeDeleter.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (rd0 rd : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      rdOwn γl rd0 }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"SetRangeDeleter")) (Val #rd))
  {{ RET #(); rdOwn γl rd }}

end spec

end EtcdGrove
end Perennial
