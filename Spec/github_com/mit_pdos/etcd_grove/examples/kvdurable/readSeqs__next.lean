/- Lean-first (no Rocq counterpart).

`s.next()` (kv.go): a fresh read sequence number, one counter for the cluster's every replica and
incarnation (a read's context outlives its incarnation). For the caller's replica `id` (`1 ≤ id ≤
9`), the number `seq` it issues moves `id`'s last read sequence number (`γ.r.rseq`) to it, minting
the read context `f seq` there (in the store's invariant, `rkvInv`): `(id, seq) ↪[rmint]□ f seq`.
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
  ∀ (γ : KdNames) (vs : List w64) (s : Loc) (id : w64) (f : w64 → List w8),
  1 ≤ uint.nat id → uint.nat id ≤ 9 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ isReadSeqs γ s ∗ kdCluster γ vs }}
    (App (Val (s @!! go.GoType.PointerType kReadSeqsTy @!! go!"next")) (Val #()))
  {{ (seq : w64) (ok : Bool), RET (PairV #seq #ok);
      ⌜ok = true⌝ -∗ (id, seq) ↪[γ.r.rmint]□ f seq }}

end spec

end kvdurable
end EtcdGrove
end Perennial
