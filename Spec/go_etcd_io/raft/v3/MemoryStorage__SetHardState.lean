/- `MemoryStorage.SetHardState` (`storage.go:127`), specified 2026-10-12 (Lean-first: no
Rocq counterpart). -/
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.SetHardState(st)`: under the lock, the hard state is `st`; no error. It needs
only `memStorMeta` (the application's), not `ownMemoryStorage` (raft's): raft reads the
hard state only through `InitialState`, so the application may set it while raft runs,
as it does when it handles a `Ready`.

raft v3.7 (stage R3, 2026-10-15): `st` is a `*pb.HardState`, `nil` or read-only (`hsOpt`), and
the storage keeps the pointer (`ms.hardState = st`, `storage.go:140`): a hard state is never
written after it is built (D4), so caller and storage share it. -/
abbrev MemoryStorage.SetHardState.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (hs : HardStateM) (st : Loc) (hs' : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hmeta" ∷ memStorMeta ms γs hs ∗ "#Hst" ∷ hsOpt st hs' }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"SetHardState")) (Val #st))
  {{ RET #interface.nil; memStorMeta ms γs hs' }}

end spec

end EtcdGrove
end Perennial
