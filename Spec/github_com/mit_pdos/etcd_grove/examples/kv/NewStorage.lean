/- Lean-first (no Rocq counterpart).

`NewStorage(voters)` (kv.go): a new storage, registered (`kvStorRec`), holding the voters
(read-only) and a new `MemoryStorage`, with what `NewMemoryStorage` gives of it (2026-10-30, stage
F of the client repair: its lock, the frozen dummy entry, its end, the never-snapshotted token, the
hard state's metadata and the fresh token; until then `ownMemoryStorage` at `memStorEmpty`, the
certificate registry and the snapshot token).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev NewStorage.spec : Prop :=
  ∀ (vsl : GoSlice) (voters : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ kvStorInv (GF := GF) ∗ vsl ↦*□ voters }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.NewStorage)) (Val #vsl))
  {{ (s : Loc), RET #s; ∃ (ms : Loc) (γs : MemStorNames),
      kvStorRec s ms γs ∗ s.[RStorage, go!"voters"] ↦□ vsl ∗
      memStorLock ms γs ∗ memLog γs 0 DFrac.discard [zero_val EntryM] ∗ memEnd γs 1 ∗
      memSnapNone γs ∗ memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memStorFresh ms γs }}

end spec

end kv
end EtcdGrove
end Perennial
