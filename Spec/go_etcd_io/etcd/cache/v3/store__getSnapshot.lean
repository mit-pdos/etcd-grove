/-
`store.getSnapshot` (`cache/*.go`), an internal helper.
Users: `store.Get`.
Proof sketch: under the read lock: `ErrNotReady` at `0`, a negative revision errs, `0` is the latest, above the latest `ErrFutureRev`; the newest snapshot at or below (`ringBuffer.DescendLessOrEqual.spec`), none is `ErrCompacted`; its certificate and the gap after it give `snapFor` at the target.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.getSnapshot(rev)`: a snapshot answering for `rev` (the latest for `0`) and the latest revision, or an error. -/
def store.getSnapshot.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString) (r0 : Nat) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isStore s γ pfx ∗ storeRevLb s r0 ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"getSnapshot")) (Val #rev))
  {{ (p : Loc) (lrev : w64) (err : GoInterface), RET (PairV (PairV #p #lrev) #err); threadTok ∗
      (⌜err = GoInterface.nil ∧ r0 ≤ sint.Z lrev⌝ ∗ storeRevLb s (sint.Z lrev).toNat ∗
        ⌜0 ≤ sint.Z rev ∧ sint.Z rev ≤ sint.Z lrev ∧ 0 < sint.Z lrev⌝ ∗
        snapFor p γ pfx (if sint.Z rev = 0 then (sint.Z lrev).toNat else (sint.Z rev).toNat)) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
