/- `NewMemoryStorage` (`storage.go:113`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). A fresh storage: the lock, the dummy at `0` frozen (the client's `storLog st 0 □ [e₀]`; the design gives it owned, for the client to freeze: frozen here, since the lock keeps the dummy frozen), the end at `1`, the empty stored snapshot (the client's half), the hard state, and the allocation's fuel (`memStorFresh`, for `memStorInvP_alloc`). -/
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

/-- `NewMemoryStorage()`. -/
abbrev NewMemoryStorage.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions NewMemoryStorage [])) (Val #()))
  {{ (ms : Loc) (γs : MemStorNames), RET #ms;
      memStorLock ms γs ∗ memLog γs 0 DFrac.discard [zero_val EntryM] ∗ memEnd γs 1 ∗
      memSnapExact γs memSnapEmpty ∗ memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memStorFresh ms γs }}

end spec

end EtcdGrove
end Perennial
