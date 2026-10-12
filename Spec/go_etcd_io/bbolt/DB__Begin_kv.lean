/-
`DB.Begin` (bbolt). `db.Begin(writable)`: a read transaction over the committed data, or the write transaction
(its token spent), or an error.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/DB__Begin_kv.lean`. Lean-first (no Rocq
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

/-- `db.Begin(writable)`: a read transaction over the committed data, or the write transaction
(its token spent), or an error. -/
abbrev bbolt.DB.Begin.kvspec : Prop :=
  ∀ (db : Loc) (γ : DBNames) (D : Data) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ (if w then wrTok γ else iprop(True)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); ownDB db γ D ∗ isDB db ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ (if w then wrTok γ else iprop(True))) ∨
       (⌜err = GoInterface.nil⌝ ∗ txDB tx db ∗
        (if w then ownWTx tx γ D D else iprop(txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx)))) }}

end spec

end EtcdGrove
end Perennial
