/- Lean-first (no Rocq counterpart).

`NewStorage(voters)` (register.go:51): a new storage, registered (`regStorRec`), holding the
voters (read-only) and a new `MemoryStorage` (at `memStorEmpty`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev NewStorage.spec : Prop :=
  ∀ (vsl : GoSlice) (voters : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ regStorInv (GF := GF) ∗ vsl ↦*□ voters }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.NewStorage)) (Val #vsl))
  {{ (s : Loc), RET #s; ∃ (ms : Loc) (γs : MemStorNames),
      regStorRec s ms γs ∗ s.[RStorage, go!"voters"] ↦□ vsl ∗
      ownMemoryStorage ms γs memStorEmpty }}

end spec

end register
end EtcdGrove
end Perennial
