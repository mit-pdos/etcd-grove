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

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `hs.HashByRev(rev)`: a hash stored for `rev`, or the store's hash at `rev` (`0`: the
current revision), of the revisions after the compaction revision, by the caller's update at the
store's state `σ`, unchanged:
* `0 < rev < σ.crev` (and no hash stored for it): `ErrCompacted`, revision `0`;
* `σ.rev < rev` (and none stored): `ErrFutureRev`, the current revision;
* else a hash of the store (`mvccHashOk`, `mvccHashOk_state`) at `rev`, or for `0` at the current
  revision or a hash stored for revision `0` (`issues/etcd-mvcc-hashbyrev-zero-stored.md`), and
  the current revision, or `1` when a stored hash is answered during a `Restore`
  (`issues/etcd-mvcc-hashbyrev-restore-rev1.md`: the restore's placeholder; with the Go fix the
  post loses that case), `nil`. `Restore`'s update fires when it sets the new current revision
(before the leases are re-attached), so a `HashByRev` after it sees the new state.
A stored hash short-cuts both checks. Its value rests on crc32's (`kvHasher`'s trust boundary). -/
abbrev mvcc.hashStorage.HashByRev.specC : Prop :=
  ∀ (hs : Loc) (γ : mvcc.MvccName) (rev : w64) (Q : mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isHashStorage hs γ ∗ threadTok ∗
      AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ σ, COMM Q σ }> }}
    (App (Val (hs @!! go.GoType.PointerType hashStorage.ty @!! go!"HashByRev")) (Val #rev))
  {{ (h : KeyValueHash) (cur : w64) (err : GoInterface), RET (PairV (PairV #h #cur) #err);
      threadTok ∗ ∃ σ : mvcc.MvccState, Q σ ∗
      ((⌜err = GoInterface.nil ∧ (cur = W64 (σ.rev : Int) ∨ cur = W64 1) ∧
          (h.Revision' = rev ∨ (rev = W64 0 ∧ h.Revision' = W64 (σ.rev : Int)))⌝ ∗
          mvcc.mvccHashOk γ h) ∨
       (⌜0 < sint.Z rev ∧ sint.Z rev < σ.crev ∧ cur = W64 0⌝ ∗
          (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝)) ∨
       (⌜(σ.rev : Int) < sint.Z rev ∧ cur = W64 (σ.rev : Int)⌝ ∗
          (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝))) }}

end spec

end EtcdGrove
end Perennial
