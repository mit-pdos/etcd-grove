/-
`(*leasingKV).readySession` (`kv.go`): a session is set and not done. Proof sketch: read lock;
`session.Done()` (1d) and a non-blocking receive. Changes: from `specs-ref`'s `leasingKV__readySession.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `readySession()`: `true` only once a session is ready. -/
def leasingKV.readySession.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ threadTok }}
    (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"readySession")) (Val #()))
  {{ (b : Bool), RET #b; threadTok ∗ (⌜b = false⌝ ∨ (⌜b = true⌝ ∗ sessionReady γL)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
