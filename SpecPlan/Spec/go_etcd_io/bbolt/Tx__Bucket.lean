/-
`tx.Bucket(name)` (`tx.go`): `tx.root.Bucket(name)`.

**Users.** The backend's every operation (`batch_tx.go:170, 195, 230, 255`; `read_tx.go:103`,
cached per bucket in the shared read transaction), `backend.Hash` (`:433`), defrag (`:822, 844`),
the bank (`bbolttest.go:125`). Snippets: `ReqBackendBatch`, `ReqBackendRead`, `ReqBank`.
**Proof sketch.** `Bucket.Bucket.spec` at the root (path `[]`, whose handle premise is the
transaction's own `tx.root`). **Changes.** Over paths; any
transaction (a writer with all of it: the child cache is written).
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** In a write transaction the
child's token (`bktTok`) is taken and given back at the handle returned (`bktUse`), in place of
`bktH … gs` (the per-path generation counter it replaces was unobservable state, redundant with
ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.Bucket(name)`: a handle of the top-level bucket `n`, or nil if there is none (in a write
transaction, the bucket's token given back at the handle: the cached one if there was one). -/
def Tx.Bucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (o : Option Loc) (qc : Qp)
    (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ bktTok tx γ T [n] o qc ∗ name ↦*{dq} n ∗ ⌜T.rw = true → q = 1⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      (if (T.cur.atPath [n]).any Ent.isBkt
       then iprop(⌜b ≠ Loc.null ∧ (T.rw = true → ∀ b', o = some b' → b = b')⌝ ∗
         bktUse tx γ T.rw b [n] qc)
       else iprop(⌜b = Loc.null⌝)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
