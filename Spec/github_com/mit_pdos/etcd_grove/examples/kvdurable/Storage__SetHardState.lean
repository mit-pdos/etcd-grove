/- Lean-first (no Rocq counterpart).

`s.SetHardState(hs)` (storage.go): the hard state `hs'` (at `p`, read-only) set in the image
(`imgSetHardState`), then in the `MemoryStorage` (`MemoryStorage.SetHardState`). The caller holds the
replica's `dmu`, or owns the storage before its node runs (`openStorage`).
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
abbrev Storage.SetHardState.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (hs : HardStateM) (ip : Loc) (I : StorFile) (p : Loc)
    (hs' : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ kdStorRec s ms γs ∗
      memStorMeta ms γs hs ∗ s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip I ∗ hsOpt p hs' }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"SetHardState")) (Val #p))
  {{ RET #(); memStorMeta ms γs hs' ∗ ownImage ip (imgSetHardState I hs') }}

end spec

end kvdurable
end EtcdGrove
end Perennial
