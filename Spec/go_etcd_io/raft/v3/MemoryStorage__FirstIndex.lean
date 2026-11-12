/- `MemoryStorage.FirstIndex` (`storage.go:199`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). The contract's `FirstIndex` triple. -/
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

/-- `ms.FirstIndex()`: past what the caller knows is compacted, and compacted up to it. -/
abbrev MemoryStorage.FirstIndex.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (c : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memCompacted γs c }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"FirstIndex")) (Val #()))
  {{ (fi : w64), RET (PairV #fi #interface.nil);
      ⌜c + 1 ≤ uint.nat fi⌝ ∗ memCompacted γs (uint.nat fi - 1) }}

end spec

end EtcdGrove
end Perennial
