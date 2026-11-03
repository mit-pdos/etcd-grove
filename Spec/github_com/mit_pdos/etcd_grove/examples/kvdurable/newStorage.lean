/- Lean-first (no Rocq counterpart).

`newStorage(boot)` (storage.go): a new storage of the bootstrap conf state at `bp`: a new
`MemoryStorage` (`NewMemoryStorage`'s post: detached, empty, the zero hard state), its field still
owned (for the registry, `kdStor_register`), the bootstrap conf state's field read-only, and the
empty image (`imgEmpty`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev newStorage.spec : Prop :=
  ∀ (bp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.newStorage)) (Val #bp))
  {{ (s : Loc), RET #s; ∃ (ms ip : Loc) (γs : MemStorNames),
      s.[KStorage, go!"MemoryStorage"] ↦ ms ∗ s.[KStorage, go!"boot"] ↦□ bp ∗
      s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip imgEmpty ∗
      memStorLock ms γs ∗ memLog γs 0 DFrac.discard [zero_val EntryM] ∗ memEnd γs 1 ∗
      memSnapNone γs ∗ memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memStorFresh ms γs 0 memSnapEmpty }}

end spec

end kvdurable
end EtcdGrove
end Perennial
