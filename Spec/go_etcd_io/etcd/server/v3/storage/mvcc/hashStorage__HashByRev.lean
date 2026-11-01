/-
`hashStorage.HashByRev` (hash.go). Lean-first (no Rocq counterpart): a candidate spec only (no proof, no `spec`
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

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `hs.HashByRev(rev)`: a hash stored for `rev` (with the current revision), or the store's
hash at `rev` (`0`: the current revision), of the revisions after the compaction revision, by the
caller's update at the store's state `σ`, unchanged:
* `0 < rev < σ.crev` (and no hash stored for it): `ErrCompacted`, revision `0`;
* `σ.rev < rev` (and none stored): `ErrFutureRev`, the current revision;
* else a hash of the store (`mvccHashOk`: of the revisions `(CompactRevision, Revision]` of its
  history, `mvccHashOk_state`) at `rev`, and the current revision, `nil`.
(A stored hash short-cuts both checks: a hash stored at a revision later compacted is still
returned.) Its value rests on crc32's (`kvHasher`'s trust boundary). -/
abbrev mvcc.hashStorage.HashByRev.specC : Prop :=
  ∀ (hs : Loc) (γ : mvcc.MvccName) (rev : w64) (Q : mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isHashStorage hs γ ∗ threadTok ∗
      AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ σ, COMM Q σ }> }}
    (App (Val (hs @!! go.GoType.PointerType hashStorage.ty @!! go!"HashByRev")) (Val #rev))
  {{ (h : KeyValueHash) (cur : w64) (err : GoInterface), RET (PairV (PairV #h #cur) #err);
      threadTok ∗ ∃ σ : mvcc.MvccState, Q σ ∗
      ((⌜err = GoInterface.nil ∧ cur = W64 (σ.rev : Int) ∧
          h.Revision' = (if rev = W64 0 then W64 (σ.rev : Int) else rev)⌝ ∗ mvcc.mvccHashOk γ h) ∨
       (⌜0 < sint.Z rev ∧ sint.Z rev < σ.crev ∧ cur = W64 0⌝ ∗
          (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝)) ∨
       (⌜(σ.rev : Int) < sint.Z rev ∧ cur = W64 (σ.rev : Int)⌝ ∗
          (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝))) }}

end spec

end EtcdGrove
end Perennial
