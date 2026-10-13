/-
`backend.begin` (`backend.go`). `b.begin(write)`: `unsafeBegin` under a reader's slot of `b.mu`, then the size metrics stored.
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

/-- `b.begin(write)`: `unsafeBegin` under a reader's slot of `b.mu`, then the size metrics stored. -/
abbrev backend.backend.begin.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b db : Loc) (D : Data) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗ ownDB db γ.db D ∗ (if w then wrTok γ.db else iprop(True)) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"begin")) (Val #w))
  {{ (tx : Loc), RET #tx; sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗ ownDB db γ.db D ∗ txDB tx db ∗ (if w then ownWTx tx γ.db D D else iprop(txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx)) }}

end spec

end EtcdGrove
end Perennial
