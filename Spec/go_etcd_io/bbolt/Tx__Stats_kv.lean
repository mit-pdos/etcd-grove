/-
`Tx.Stats_kv` (bbolt). `tx.Stats()` of a finished transaction: some statistics.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Tx__Stats_kv.lean`. Lean-first (no Rocq
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

/-- `tx.Stats()` of a finished transaction: some statistics. -/
abbrev bbolt.Tx.Stats_kv.spec : Prop :=
  ∀ (tx : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txDone tx }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Stats")) (Val #()))
  {{ (s : TxStats), RET #s; True }}

end spec

end EtcdGrove
end Perennial
