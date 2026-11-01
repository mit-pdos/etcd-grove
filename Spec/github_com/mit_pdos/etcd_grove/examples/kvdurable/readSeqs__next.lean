/- Lean-first (no Rocq counterpart).

`s.next()` (kv.go): a fresh read sequence number, one counter for the cluster's every replica and
incarnation (a read's context outlives its incarnation). For the caller's replica `id` (`1 ≤ id ≤
9`) and the key `key` of its read, the number `seq` it issues moves `id`'s last read sequence number
(`γ.r.rseq`) to it, minting the read context `readCtxB id seq key` there (in the store's invariant,
`rkvInv`: `(id, seq) ↪[rmint]□ …`) and committing it, once, to the read seeing at least the committed
log `l0` the reader knows (`isReadCtx`, `readCtxAfter`: kvreconf's `kvr_mint_read`; the context is
fresh in the store's used contexts because nothing was minted at its number, 2026-11-01 stage I fix).
`ok` is false once the numbers are used up (`maxSeq`, which does not happen).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev readSeqs.next.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (s : Loc) (id : w64) (key : List w8) (l0 : List LogEntry),
  1 ≤ uint.nat id → uint.nat id ≤ 9 → (key.length : Int) < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ isReadSeqs γ s ∗
      kdCluster γ vs ∗ isCommittedLogLb γ.r.cluster l0 }}
    (App (Val (s @!! go.GoType.PointerType kReadSeqsTy @!! go!"next")) (Val #()))
  {{ (seq : w64) (ok : Bool), RET (PairV #seq #ok);
      ⌜ok = true⌝ -∗ (id, seq) ↪[γ.r.rmint]□ kvreconf.readCtxB id seq key ∗
        isReadCtx γ.r.cluster kdRaftN (kvreconf.readCtxB id seq key) (fun _ => iprop(True)) ∗
        readCtxAfter γ.r.cluster kdRaftN (kvreconf.readCtxB id seq key) l0 }}

end spec

end kvdurable
end EtcdGrove
end Perennial
