/-
`baseReadTx.UnsafeRange(bucket, key, endKey, limit)` (`read_tx.go:75-121`): translated; internal
(the embedded receiver of both read transactions' `UnsafeRange`). Changes: as `readTx.UnsafeRange`.
Margin: as there.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`base.UnsafeRange(...)`** on a read transaction's embedded `baseReadTx`: as
`readTx.UnsafeRange`. -/
def baseReadTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BeNames) (rt base : Loc) (F : Fp) (V : Image) (bk : GoInterface) (bi : BktInfo)
    (ks es : GoSlice) (dk de : DFrac) (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ rt F V ∗ ⌜base = structFieldRef go_etcd_io.etcd.server.v3.storage.backend.readTx go!"baseReadTx" rt ∨
        base = structFieldRef go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx go!"baseReadTx" rt⌝ ∗
      bucketOk bk bi ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ⌜covers F bi.name k e⌝ ∗ ⌜bi.safe = true ∨ es = slice.nil ∨ sint.Z limit = 1⌝ }}
    (App (App (App (App (Val (base @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.baseReadTx.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #ks))
      (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); beRd γ rt F V ∗ ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ l, ⌜rdRange (V.ents bi.name) bi.safe (V.clean bi.name) k e (sint.Z limit) l⌝ ∗
        bytesListAt kl (l.map Prod.fst) ∗ bytesListAt vl (l.map Prod.snd) }}

end spec

end Backend
end EtcdGrove
end Perennial
