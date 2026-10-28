/-
**The writer of the KV over either store** (unit N4, D14a, `notes/decisions.md`). Lean-first (no
Rocq counterpart).

`kvWriter s γ log`: the sole writer of the committed log `log` (`soleWriter`, `SoleWriter.lean`)
and, for a watchable store over the store `s`, the writer's half of its notified log (`wlogOwn`,
`Defs.lean`); what the apply thread holds and the txn package's sole-writer statements take.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section writer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-! ## The writer -/

/-- **The writer of the KV over the store `s`** at the committed log `log`: the sole writer, for a
watchable store the writer's half of its notified log (`wlogOwn`), and the writer's fragment
(`mvcc.writerFrag`: the names `γ` are the store's current ones; D22 receiver epochs, S5b: with the
hook's facts, `hookOk`, the store's hook `hookIs` that `store.Write` takes). Not persistent. -/
def kvWriter (s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) : IProp GF :=
  iprop(soleWriter γ log ∗ wlogOwn s γ log ∗ mvcc.writerFrag γ)

/-- The writer's certificate (persistent). -/
theorem kvWriter_cert (s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) :
    kvWriter (GF := GF) s γ log ⊢ kvWriter s γ log ∗ mvcc.idxCert γ.idx log := by
  unfold kvWriter
  iintro ⟨Hsw, Hw⟩
  ihave ⟨Hsw, #Hc⟩ := soleWriter_cert γ log $$ Hsw
  iframe Hsw Hw Hc

/-- The writer's log has `NewStore`'s two revisions. -/
theorem kvWriter_len (s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) :
    kvWriter (GF := GF) s γ log ⊢ ⌜2 ≤ log.length⌝ ∗ kvWriter s γ log := by
  unfold kvWriter
  iintro ⟨Hsw, Hw⟩
  ihave ⟨%h, Hsw⟩ := soleWriter_len' γ log $$ Hsw
  iframe Hsw Hw
  ipureintro; exact h

end writer

end txn
end EtcdGrove
end Perennial
