/-
`hashStorage.Hashes` (hash.go). Lean-first (no Rocq counterpart): a candidate spec only (no proof, no `spec`
yet), `notes/mvcc-api-candidate.md`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `hs.Hashes()`: a fresh copy of the stored hashes, each a hash of the store. -/
abbrev mvcc.hashStorage.Hashes.specC : Prop :=
  ∀ (hs : Loc) (γ : mvcc.MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isHashStorage hs γ }}
    (App (Val (hs @!! go.GoType.PointerType hashStorage.ty @!! go!"Hashes")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ l : List KeyValueHash, sl ↦* l ∗ [∗list] h ∈ l, mvcc.mvccHashOk γ h }}

end spec

end EtcdGrove
end Perennial
