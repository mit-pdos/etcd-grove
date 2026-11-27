/-
`(*consistentIndex).UnsafeSave(tx)`. Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.UnsafeSave(tx)` (by the holder of the batch transaction's lock, whose meta keys are
`TMx m r`: the index and term keys `m`, the raft-term key `r`) reads the index (the linearization point: the
caller learns it is `k` and must know that a non-zero `k` is not below the stored index, which etcd checks under
`ETCD_VERIFY`), then the term `t` and (keepfix (c)) the raft term `rt` stored with it, and writes them: the meta
keys become `metaAfterSave m k t`, the raft-term key `rtAfterSave r k rt`. (keepfix-d, 2026-11-27) The reads are
under the pair mutex, so the triple has the client's predicate (`P k t rt`, for a non-zero `k`). The writes are
`metaWriter`'s (the index's and term's puts, tokens `PTi`, `PTt`) at the raft-term key `r`, then
`metaRtWriter`'s (token `PTr`). -/
abbrev consistentIndex.UnsafeSave.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (P : w64 → w64 → w64 → IProp GF) (tx : GoInterfaceOk)
    (TMx : MetaCI → Option (w64 × w64) → IProp GF) (PTi PTt PTr : IProp GF) (m : MetaCI)
    (r : Option (w64 × w64)),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ isCI ci γ P ∗
      metaWriter tx (fun m' => TMx m' r) PTi PTt ∗ metaRtWriter tx TMx PTr ∗ TMx m r ∗ PTi ∗ PTt ∗ PTr) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ k ={∅, ⊤ \ ↑ciN}=∗
      ⌜k ≠ W64 0 → uint.Z m.1 ≤ uint.Z k⌝ ∗
        ∀ t rt : w64, (⌜k = W64 0⌝ ∨ □ P k t rt) -∗
          TMx (metaAfterSave m k t) (rtAfterSave r k rt) -∗ Φ #())) -∗
    WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeSave")) (Val #(GoInterface.ok tx))) {{ Φ }}

end spec

end EtcdGrove
end Perennial
