/-
`backend.unsafeBegin` (`backend.go`). `b.unsafeBegin(write)`: a bbolt transaction begun on the database `b.db` (`lg.Fatal` on an error): the write transaction (with the writer's token) or a read transaction, over the committed data.
Lean-first (no Rocq counterpart); see `InvBatch.lean` and `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `b.unsafeBegin(write)`: a bbolt transaction begun on the database `b.db` (`lg.Fatal` on an error): the write transaction (with the writer's token) or a read transaction, over the committed data. -/
abbrev backend.backend.unsafeBegin.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b db : Loc) (q : Qp) (D : Data) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ bF go!"db" b ↦{DFrac.own q} db ∗ ownDB db γ.db D ∗
      (if w then wrTok γ.db else iprop(True)) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"unsafeBegin")) (Val #w))
  {{ (tx : Loc), RET #tx; bF go!"db" b ↦{DFrac.own q} db ∗ ownDB db γ.db D ∗ isDB db ∗ txDB tx db ∗
      (if w then ownWTx tx γ.db D D else iprop(txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx)) }}

end spec

end EtcdGrove
end Perennial
