/-
**The auth store's `Authenticate` side, as the server sees it** (C1's A4, 2026-10-31): `authnStoreOk`,
the contract `EtcdServer.Authenticate` takes on `s.AuthStore()`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The auth store's `Authenticate` side** (persistent; C1's A4, 2026-10-31): the methods
`EtcdServer.Authenticate` calls on it. `CheckPassword(name, pw)`, with the caller's reader resource
`RD` (held and given back: the real method read-locks `enabledMu` and the backend), returns some
revision and an error one the gRPC layer can take (`applyErrIs`); `GenTokenPrefix()` a prefix with
no space (`auth.tokPrefixOk`, what the admission of an `Authenticate` entry needs) and no error;
`Revision()` returns. Nothing of `CheckPassword`'s success (auth enabled, the user present at the
revision) nor of `Revision`'s verdict: the server's spec needs neither (the token's issue is the
apply thread's). Of the kind of `isReqAuth` (`InvRequest.lean`; a module of its own so that the
request path's modules do not rebuild); of the real store, `authnStoreOk_of_authInv`
(`AuthReqDerive.lean`), exported with auth on only (with auth off the store is `NewAuthStore`'s
axiom, which states no such clause). -/
def authnStoreOk (st : GoInterface) (RD : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    □ (∀ (name pw : GoString),
      {{ RD }} (App (App (Val #(methods ai.ty go!"CheckPassword" ai.v)) (Val #name)) (Val #pw))
      {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err); RD ∗ applyErrIs err }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"GenTokenPrefix" ai.v)) (Val #()))
      {{ (pre : GoString) (err : GoInterface), RET (PairV #pre #err);
          ⌜err = GoInterface.nil ∧ auth.tokPrefixOk pre⌝ }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"Revision" ai.v)) (Val #()))
      {{ (x : w64), RET #x; True }}))

instance authnStoreOk_persistent (st : GoInterface) (RD : IProp GF) :
    Persistent (authnStoreOk (GF := GF) st RD) := by
  unfold authnStoreOk; infer_instance

end defs

end EtcdGrove
end Perennial
