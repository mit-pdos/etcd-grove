/- `MemoryStorage.SetHardState` (`storage.go:127`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). As before U8 v2: over `memStorMeta`. -/
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

/-- `ms.SetHardState(st)`: under the lock, the hard state is `st`; no error. -/
abbrev MemoryStorage.SetHardState.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (hs : HardStateM) (st : Loc) (hs' : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hmeta" ∷ memStorMeta ms γs hs ∗ "#Hst" ∷ hsOpt st hs' }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"SetHardState")) (Val #st))
  {{ RET #interface.nil; memStorMeta ms γs hs' }}

end spec

end EtcdGrove
end Perennial
