/- `MemoryStorage.Entries` (`storage.go:143`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). The contract's `Entries` triple, over two pieces (a frozen prefix and an owned tail, possibly empty). -/
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

/-- `ms.Entries(lo, hi, maxSize)` within two adjacent ranges the caller holds. -/
abbrev MemoryStorage.Entries.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (k : Nat) (dq1 dq2 : DFrac) (a b : List EntryM)
    (lo hi maxSize : w64) (ec : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ⌜k ≤ uint.nat lo ∧ uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ k + a.length + b.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Entries")) (Val #lo)) (Val #hi)) (Val #maxSize))
  {{ (s : GoSlice) (es : List EntryM) (err : GoInterface), RET (PairV #s #err);
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ((⌜err = ec⌝ ∗ memCompacted γs (uint.nat lo)) ∨
       (⌜err = interface.nil⌝ ∗ entsRO s es ∗
        ⌜es ≠ [] ∧ s.cap = s.len ∧
          es <+: ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo)⌝)) }}

end spec

end EtcdGrove
end Perennial
