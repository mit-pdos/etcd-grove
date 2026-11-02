/-
`hashStorage.Hash` (hash.go). Lean-first (no Rocq counterpart): a candidate spec only (no proof, no `spec`
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

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `hs.Hash()`: the backend's hash of its whole database, after its commit (serving the
request `X ⇒ Y` of its hooks, as `Commit`), and a revision. Neither is stated: the hash is of the
backend's pages (compacted revisions not yet deleted by the compaction job included), not a
function of the state, and the revision is read without `revMu`, racing with every write
(`issues/etcd-mvcc-hash-currentrev-race.md`). The backend's `Hash` has no spec yet. Not provable
as the code is: a racy load has no proof in Perennial's model; the candidate is what holds once the
read is synchronized (the issue's fix), or a trust-boundary axiom until then. -/
abbrev mvcc.hashStorage.Hash.specC : Prop :=
  ∀ (hs : Loc) (γ : mvcc.MvccName) (BP : backend.BParams) (Pk : IProp GF) (b : Loc) (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isHashStorage hs γ ∗ threadTok ∗ mvcc.mvccBackendIs γ BP Pk b ∗ X ∗ backend.commitReq (mvcc.mvccBackend γ) BP Pk b X Y }}
    (App (Val (hs @!! go.GoType.PointerType hashStorage.ty @!! go!"Hash")) (Val #()))
  {{ (h : w32) (rev : w64) (err : GoInterface), RET (PairV (PairV #h #rev) #err); threadTok ∗ Y }}

end spec

end EtcdGrove
end Perennial
