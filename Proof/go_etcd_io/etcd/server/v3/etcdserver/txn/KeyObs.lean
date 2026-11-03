/-
**The writer's observation of the key bucket** (the merged snapshot's window, S2,
`etcdserver.mergedCreate_window`; `notes/decisions.md`, "The merged snapshot's window: the writer's
key observation"). Lean-first (no Rocq counterpart).

`kvWriter_keyObs`: the sole writer at the committed log `log` and a view of the backend's data
(`backend.viewAt`) sees the key bucket at most `bucketMap log`, and exactly `bucketMap log` when
the backend's store does not compact (`d.cm = false`). `kvWriter_noCmp`: with compaction off, a
snapshot's data records no compaction (the reader's bound `backend.fkRd` that `backend.Snapshot`
gives). Both from the writer's pin (`mvcc.writerPin`, in `wlogOwn`; M2's item 37, 2026-11-02:
until then named `sorry`s over the batch lock's late-bound resource (then `lateW`, now `lateWD`), which a restore leaves
unregistered).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Writer
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WriterPinObs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section keyObs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **The writer's observation of the key bucket**: the sole writer of the store `(s, γ)` over the
real backend `d` at the log `log` and a view `vd` of its data: every key `vd` has is `bucketMap
log`'s, at its value (thin, both modes: the compaction deletes keys physically), and `vd` is
`bucketMap log` on the key bucket when the store does not compact (the writer's pin,
`mvcc.writerPin_keyObs`). -/
theorem kvWriter_keyObs (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (vd : backend.VData) :
    kvWriter (GF := GF) s γ log ∗ backend.viewAt d.γB vd ⊢
      ⌜(∀ k v, vd.lookup (mvcc.keyName, k) = some v → (mvcc.bucketMap log).lookup k = some v) ∧
        (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap log).lookup k)⌝ := by
  iintro ⟨Hkw, Hv⟩
  iunfold kvWriter at Hkw
  icases Hkw with ⟨-, Hwl, -⟩
  iunfold wlogOwn at Hwl
  icases Hwl with ⟨-, Hpin⟩
  iapply mvcc.writerPin_keyObs γ d hk log vd $$ [$Hpin $Hv]

/-- **The writer rules out the compaction keys**: a reader's bound of the real backend's
compaction-key flag finds none when the store does not compact (`mvcc.writerPin_noCmp`). -/
theorem kvWriter_noCmp (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (log : mvcc.Log) (rv : backend.RView) :
    kvWriter (GF := GF) s γ log ∗ backend.fkRd d.γB d.P rv ⊢
      ⌜d.cm = false → backend.fkAbsRv d.P rv⌝ ∗ kvWriter s γ log := by
  iintro ⟨Hkw, Hfk⟩
  iunfold kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hf⟩
  iunfold wlogOwn at Hwl
  icases Hwl with ⟨Hw, Hpin⟩
  ihave ⟨%Habs, Hpin⟩ := mvcc.writerPin_noCmp γ d hk log rv $$ [$Hpin $Hfk]
  isplitl []
  · ipureintro; exact Habs
  iunfold kvWriter
  iframe Hsw Hf
  iunfold wlogOwn
  iframe Hw Hpin

end keyObs

end txn
end EtcdGrove
end Perennial
