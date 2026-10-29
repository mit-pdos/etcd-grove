/-
`newUserClient(name, pw, lg)` (`examples/authkv/authkv.go`; `notes/authkv-main-plan.md`, S3): a
client of authkv's client address `127.0.0.1:23916` that authenticates as `name` with the
password `pw`. Lean-first (no Rocq counterpart).

**The triple:** `clientv3.New.spec`'s at the configuration `newUserClient` builds (etcdctl's
timeouts, as `common.NewClient`'s, and the user name and password): given `Authenticate`
registered at the address with a reply to `(name, pw)` meeting `P` (`authTokReg`; with auth on,
`P` is `auth.tokIssued γa · name`), a new client (`isNewClient`) whose KV calls carry a token
meeting `P` or the context's own (`clientTokAt`; `clientTokAt_user` gives `userClientAt`), or an
error and `nil`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.New
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev newUserClient.spec : Prop :=
  ∀ (name pw : GoString) (lg : Loc) (V : WEnv GF) (P : GoString → IProp GF),
  lg ≠ null → name ≠ go!"" → pw ≠ go!"" → threadBound GF ≤ 2 ^ 30 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      client.ctxErrClientAll ∗ authTokReg [go!"127.0.0.1:23916"] name pw P }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.newUserClient))
      (Val #name)) (Val #pw)) (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl [go!"127.0.0.1:23916"] V ∗
        clientTokAt cl [go!"127.0.0.1:23916"] P) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end authkv
end EtcdGrove
end Perennial
