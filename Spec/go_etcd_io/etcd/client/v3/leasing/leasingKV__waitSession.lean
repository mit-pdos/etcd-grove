/-
`(*leasingKV).waitSession` (`kv.go`): waits for the current `sessionc` (broadcast: closed once a
session is set), or either context. Proof sketch: a reader slot (the thread token) for the read
lock; the `select` (Perennial's broadcast channel: its close gives `sessionReady`; `ctx.Err()` of a
done context, `Context.ErrDone.spec`). Changes: from `specs-ref`'s `leasingKV__waitSession.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `waitSession(ctx)`: `nil` once a session is ready, or an error. -/
def leasingKV.waitSession.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ threadTok }}
    (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"waitSession")) (Val #ctx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ sessionReady γL) ∨ ⌜err ≠ GoInterface.nil⌝) }}

end spec

end Leasing
end EtcdGrove
end Perennial
