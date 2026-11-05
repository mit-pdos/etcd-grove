/-
**The apply package's compaction arm: the glue** (M2, the apply side, the switch; drafted in
`M2ApplyDraft.lean`, `notes/m2-apply-plan.md`). Lean-first (no Rocq counterpart). The vocabulary
(`chainCompacts`, `cmpRevAfter`, `cmpAdmitRev`, `cmpOwn`, `cmpAnswerIs`, the chain's `cmpTriple`) is
`Chain.lean`'s. (Strict M1, 2026-11-05: the glue over today's `store.Compact`, `cmp_store_pre`, is
gone with mvcc's internals; the backend's `Compaction` calls `KV.Compact.contract` directly, over
the builder `envAus`'s compaction update, which takes the writer's half and the compaction right at
one revision: `wSt_crOwn_agree`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

namespace apply

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The writer's half and the compaction right agree on the compaction revision** (each holds a
quarter of `γs.cr`). -/
theorem wSt_crOwn_agree (γs : srvApi.KVSNames) (log : mvcc.Log) (c c' : Int) :
    srvApi.wSt (GF := GF) γs log c ∗ srvApi.crOwn γs c' ⊢
      ⌜c = c'⌝ ∗ srvApi.wSt γs log c ∗ srvApi.crOwn γs c' := by
  unfold srvApi.wSt srvApi.crOwn
  iintro ⟨⟨Hst, Hcr⟩, Hc⟩
  icombine Hcr Hc gives %H
  iframe Hst Hcr Hc
  ipureintro; exact H.2

end lemmas

end apply

end EtcdGrove
end Perennial
