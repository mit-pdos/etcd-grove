/- Lean-first (no Rocq counterpart).

`NewStorage(voters)` (kv.go:55): a new storage, registered (`kvStorRec`), holding the
voters (read-only) and a new `MemoryStorage` (at `memStorEmpty`).
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev NewStorage.spec : Prop :=
  ∀ (vsl : GoSlice) (voters : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ kvStorInv (GF := GF) ∗ vsl ↦*□ voters }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.NewStorage)) (Val #vsl))
  {{ (s : Loc), RET #s; ∃ (ms : Loc) (γs : MemStorNames),
      kvStorRec s ms γs ∗ s.[RStorage, go!"voters"] ↦□ vsl ∗
      -- (2026-10-20, witness support) a storage of a cluster without a witness
      s.[RStorage, go!"witness"] ↦□ W64 0 ∗
      ownMemoryStorage ms γs memStorEmpty }}

end spec

end kvwitness
end EtcdGrove
end Perennial
