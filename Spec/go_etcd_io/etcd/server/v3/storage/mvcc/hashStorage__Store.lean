/-
`hashStorage.Store` (`hash.go`): the trust boundary.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `hs.Store(hash)` of a hash storage with a logger (`hashStorageOk`: `Store` logs first, a nil
logger panics; audit B4b, 2026-10-18) returns (the stored hashes are not modelled). -/
abbrev mvcc.hashStorage.Store.spec : Prop :=
  ∀ (hp : Loc) (h : KeyValueHash),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.hashStorageOk hp }}
    (App (Val (hp @!! go.GoType.PointerType hashStorage.ty @!! go!"Store")) (Val #h))
  {{ RET #(); True }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `hs.Store(h)` of a hash of the store (`mvccHashOk`: the compaction job's, of the
revisions it compacted): kept (the last `hashStorageMaxSize`), so that `HashByRev` may return it.
The premise is not the code's need: it keeps `HashByRev`'s result a hash of the store, which a
stored arbitrary value would not be. -/
abbrev mvcc.hashStorage.Store.specC : Prop :=
  ∀ (hs : Loc) (γ : mvcc.MvccName) (h : KeyValueHash),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isHashStorage hs γ ∗ mvcc.mvccHashOk γ h }}
    (App (Val (hs @!! go.GoType.PointerType hashStorage.ty @!! go!"Store")) (Val #h))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
