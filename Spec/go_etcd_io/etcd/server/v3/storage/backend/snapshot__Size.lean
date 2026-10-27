/-
`Size` (the backend's `snapshot`, `backend.go`: the method its embedded `*bolt.Tx` promotes; names
only). `s.Size()`: the size of the database the snapshot's read transaction sees (bbolt's
`Tx.Size`: its high-water page id times the page size). The trust boundary (D22 S-h, 2026-10-20; an
axiom in `Proof/go_etcd_io/etcd/server/v3/storage/backend/snapshot__Size.lean`). Lean-first (no Rocq
counterpart); the vocabulary is `InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `s.Size()` of a share of an open snapshot: some number (the merged message's size field, which
the sender only logs and the transport's exact-size reader checks the stream against), the share
given back (`Size` only reads; after `Close` it would dereference the transaction's nil `meta`). -/
abbrev backend.snapshot.Size.spec : Prop :=
  ∀ (sp : Loc) (D : Data) (γ : GName) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapOpenQ sp D γ q }}
    (App (Val (sp @!! go.GoType.PointerType snapshot.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; snapOpenQ sp D γ q }}

end spec

end EtcdGrove
end Perennial
