/- Lean-first (no Rocq counterpart).

`NewStorage(voters)` (kv.go:55): a new storage, registered (`kvStorRec`), holding the
voters (read-only) and a new `MemoryStorage` (at `memStorEmpty`).
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

/-- See the file header. -/
abbrev NewStorage.spec : Prop :=
  ∀ (vsl : GoSlice) (voters : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ kvStorInv (GF := GF) ∗ vsl ↦*□ voters }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.NewStorage)) (Val #vsl))
  {{ (s : Loc), RET #s; ∃ (ms : Loc) (γs : MemStorNames),
      kvStorRec s ms γs ∗ s.[RStorage, go!"voters"] ↦□ vsl ∗
      ownMemoryStorage ms γs memStorEmpty ∗
      -- (D22 S-b′3, 2026-10-20) the certificate registry's authority (`NewMemoryStorage`'s)
      memCertAuth γs ∗
      -- (D22 S-r, 2026-10-21) the application's snapshot token, at the cap `2^64`
      memSnapTok ms γs memStorEmpty ∗ ⌜γs.cap = 2 ^ 64⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
