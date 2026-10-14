/-
`concurrency.stm.reset()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.reset()`: fresh, empty read and write sets. -/
abbrev stm.reset.spec : Prop :=
  ∀ (b : Loc) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ (∃ m : Loc, structFieldRef stm go!"rset" b ↦ m) ∗
      (∃ m : Loc, structFieldRef stm go!"wset" b ↦ m) }}
    (App (Val (b @!! go.GoType.PointerType stm.ty @!! go!"reset")) (Val #()))
  {{ RET #(); stmRsetOwn pfx b ∅ ∗ stmWsetOwn pfx b ∅ }}

end spec

end concurrency
end EtcdGrove
end Perennial
