/-
## `(*EtcdServer).doSerialize(ctx, chk, get)` (internal helper)

**Users.** `Range`, a read-only `Txn`, `RangeStream` (`v3_server.go:150,190,368`).

**Proof sketch.** `traceutil.Get(ctx)` (4b), `AuthInfoFromCtx(ctx)` (its spec: `who`'s `AuthInfo`
at a revision, `nil`, or an invalid token, returned), `&auth.AuthInfo{}` for `nil`, `chk(ai)` (the
caller's closure: its triple `Chk`), `get()` (the caller's: `Get`), the revision re-check
(`authStore.Revision()`, 3d). Mirrors the code: the closures' specs are the caller's.

**Changes.** The old spec (`specs-ref`'s `EtcdServer__doSerialize.lean`) restated over `reqPrin`;
the race with `AuthEnable` is in its callers' `srvStep` (here: the revision is re-checked only for an
`AuthInfo` with a revision, `ai.Revision != 0`).

**Margin.** None (mirrors the code). `chk` runs on the context's `AuthInfo` (`who`'s user) or on an
empty one (`&auth.AuthInfo{}`, made read-only: nothing writes it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Check, then read**: `AuthInfoFromCtx`'s error; or `chk`'s (with `chk`'s post); or `get` run
(with its post), then `nil` or `ErrAuthOldRevision` (a refusal) if the token's auth revision changed.
`Chk`, `Get`: the closures' contracts, given by the caller. -/
def EtcdServer.doSerialize.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (chk get : GoFunc)
    (Pc : IProp GF) (Rc : GoInterface → IProp GF) (Pg Rg : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ Pc ∗
      (∀ (ai : Loc), {{ Pc ∗ threadTok ∗ ∃ (u : GoString) (rev : w64),
          ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦□ u ∗
          ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦□ rev ∗
          ⌜who = some u ∨ (u = [] ∧ rev = W64 0)⌝ }} (App (Val #chk) (Val #ai))
        {{ (e : GoInterface), RET #e; threadTok ∗ Rc e }}) ∗
      ({{ Pg ∗ threadTok }} (App (Val #get) (Val #())) {{ RET #(); threadTok ∗ Rg }}) ∗
      (Rc GoInterface.nil -∗ Pg) }}
    (App (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"doSerialize")) (Val #ctx)) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((⌜srvUnfired err⌝ ∗ Pc) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Rc err) ∨
       (Rg ∗ ⌜err = GoInterface.nil ∨ srvErrOf err .authOldRevision⌝)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
