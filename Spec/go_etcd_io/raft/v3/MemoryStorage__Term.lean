/- `MemoryStorage.Term` (`storage.go:170`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). The contract's `Term` triple: on a range the caller holds, the range's term or `ErrCompacted` with the storage compacted past `i0`. -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.Term(i0)` for `i0` in a range `es` from `k` the caller holds (at any fraction). -/
abbrev MemoryStorage.Term.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (i0 : w64)
    (ec : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq es ∗ ⌜k ≤ uint.nat i0 ∧ uint.nat i0 < k + es.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Term")) (Val #i0))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      memLog γs k dq es ∗
      (⌜err = interface.nil ∧ (fun e : EntryM => e.Term') <$> es[uint.nat i0 - k]? = some t⌝ ∨
       (⌜err = ec⌝ ∗ memCompacted γs (uint.nat i0 + 1))) }}

end spec

end EtcdGrove
end Perennial
