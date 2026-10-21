/- Lean-first (no Rocq counterpart).

`(*Storage).InitialState()` (kv.go:63): a fresh empty hard state and a fresh conf state
holding the voters, no error.

raft v3.7 (2026-10-16, stage R6b): the two results are pointers, `&pb.HardState{}` and
`&pb.ConfState{Voters: s.voters}`. The hard state is the zero record, read-only for good (`hsOpt`:
every cell `nil`, D4); the conf state holds the storage's voters slice (read-only, shared by the
cluster's storages) and nothing else -- its `AutoLeave` is `nil` -- and is frozen read-only for
good as the one a `Storage` lends raft (`csPts cs □ ⟨voters, [], [], [], false⟩ false`; D7's
`true`, the `AutoLeave` cell set, is what `MemoryStorage.InitialState` gives after
`EnsureConfState` and what the store's cannot: `RestartNodeW`, `Cluster.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The conf state the store's `InitialState` returns: the voters, and (2026-10-20, W4) the
witness `w` (`0`: none), nothing else. -/
abbrev kvConfState (voters : List w64) (w : w64 := W64 0) : ConfStateM :=
  ConfStateM.mk voters [] [] [] false w

/-- See the file header. -/
abbrev Storage.InitialState.spec : Prop :=
  ∀ (s : Loc) (vsl : GoSlice) (voters : List w64) (w : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      s.[RStorage, go!"voters"] ↦□ vsl ∗ vsl ↦*□ voters ∗
      -- (2026-10-20, witness support) the cluster's witness (`0`: none; W4: any)
      s.[RStorage, go!"witness"] ↦□ w }}
    (App (Val (s @!! go.GoType.PointerType rStorageTy @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      csPts cs DFrac.discard (kvConfState voters w) false }}

end spec

end kv
end EtcdGrove
end Perennial
