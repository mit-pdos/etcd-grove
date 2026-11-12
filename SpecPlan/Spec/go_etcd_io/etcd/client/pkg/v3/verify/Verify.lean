/-
`verify.Verify` (`client/pkg/v3/verify/verify.go`).

Users: `Client.Sync` (a non-empty member list); the server's assertions (2d, 2e, 3e).

Proof sketch: `IsVerificationEnabled` reads `ETCD_VERIFY` (`os.Getenv`): `verifyOff`: false, nothing
runs. Otherwise the check runs and its `false` panics: hence the alternative premise, the check's
triple returning `true`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/verify/Verify.lean` (the check always
run, returning `true`): verification off allowed (no check needed then).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.pkg.v3.verify.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Verify

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Verify(msg, f)`: no panic, verification off or `f` returning `true` (keeping `P`). -/
def Verify.spec : Prop :=
  ∀ (msg : GoString) (f : val) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify ∗ P ∗
      (verifyOff ∨ (P -∗ WP (App (Val f) (Val #())) {{ r, ∃ d : val, ⌜r = PairV #true d⌝ ∗ P }})) }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.verify.Verify)) (Val #msg)) (Val f))
  {{ RET #(); P }}

end spec

end Verify
end EtcdGrove
end Perennial
