/- Lean-first (no Rocq counterpart).

`s.snapIndex()` (storage.go): the index of the storage's snapshot (`MemoryStorage.Snapshot`'s): in
the detached mode (`openStorage`'s storage before `RestartNode`, `memStorFresh`) the stored one's;
attached (`memStorInvP` at the storage's key), at least the known compaction point `c`.
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
abbrev Storage.snapIndex.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM)) (c : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ kdStorRec s ms γs ∗
      memStorAt ms γs J o emp ∗ memCompacted γs c }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"snapIndex")) (Val #()))
  {{ (i : w64), RET #i; ⌜c ≤ uint.nat i⌝ ∗
      (match o with
       | some (c0, sv0) => iprop(⌜i = sv0.Metadata'.Index'⌝ ∗ memStorLock ms γs ∗ memStorFresh ms γs c0 sv0)
       | none => memStorInvP ms γs J) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
