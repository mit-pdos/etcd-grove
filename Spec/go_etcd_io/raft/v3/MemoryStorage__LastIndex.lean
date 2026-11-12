/- `MemoryStorage.LastIndex` (`storage.go:186`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). The contract's `LastIndex` triple (`isStorageP`). -/
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

/-- `ms.LastIndex()`: the end gives the last index exactly. -/
abbrev MemoryStorage.LastIndex.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (e : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗ memEnd γs e }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"LastIndex")) (Val #()))
  {{ (li : w64), RET (PairV #li #interface.nil); memEnd γs e ∗ ⌜uint.nat li + 1 = e⌝ }}

end spec

end EtcdGrove
end Perennial
