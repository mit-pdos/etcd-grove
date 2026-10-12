/-
`Tx.DB_kv` (bbolt). `tx.DB()`: the transaction's database.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Tx__DB_kv.lean`. Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.DB()`: the transaction's database. -/
abbrev bbolt.Tx.DB_kv.spec : Prop :=
  ∀ (tx db : Loc) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx q ∗ txDB tx db }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"DB")) (Val #()))
  {{ RET #db; txLive tx q }}

end spec

end EtcdGrove
end Perennial
