/- Lean-first (no Rocq counterpart).

`s.InitialState()` (storage.go): the `MemoryStorage`'s hard state, and the snapshot's conf state, or
the bootstrap one (`boot`) if the storage has none, cloned. Detached mode only (candidate 12 §5,
P1): raft calls it at `RestartNode`, before the storage's invariant exists; `MemoryStorage`'s
`InitialState` reads its snapshot without the lock.
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
abbrev Storage.InitialState.spec : Prop :=
  ∀ (s ms bp : Loc) (γs : MemStorNames) (hs : HardStateM) (c : Nat) (sv : SnapshotM)
    (boot : ConfStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ kdStorRec s ms γs ∗ kdStorBoot s bp boot ∗
      memStorLock ms γs ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs c sv }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp hs ∗ memStorLock ms γs ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs c sv ∗
      csPts cs DFrac.discard
        (if sv.Metadata'.Index' = W64 0 then boot else sv.Metadata'.ConfState') al }}

end spec

end kvdurable
end EtcdGrove
end Perennial
