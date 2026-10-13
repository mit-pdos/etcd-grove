/-
`batchTx.UnsafePut` (`batch_tx.go`). `t.UnsafePut(bucket, key, value)` on the writer (`unsafePut` with `seq = false`).
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

/-- `t.UnsafePut(bucket, key, value)` on the writer (`unsafePut` with `seq = false`). -/
abbrev backend.batchTx.UnsafePut.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface) (bi : BucketInfo) (key value : GoSlice) (kb vb : GoString) (dk : DFrac),
  0 < kb.length → kb.length ≤ maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ isBucket bk bi ∗ key ↦*{dk} kb ∗ value ↦*□ vb }}
    (App (App (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"UnsafePut")) (Val #bk)) (Val #key)) (Val #value))
  {{ RET #(); btW γ t (st.put bi kb vb false) ∗ key ↦*{dk} kb }}

end spec

end EtcdGrove
end Perennial
