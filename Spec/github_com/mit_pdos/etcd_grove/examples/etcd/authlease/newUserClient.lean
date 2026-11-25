/-
`newUserClient(addr, name, pw, lg)` (`examples/etcd/authlease/authlease.go`; authN's, copied for auth-lease S4, 2026-11-18):
authkv's (`Spec/.../auth/newUserClient.lean`), copied into auth3 and authN for the clients of their members (each
principal's and root's at each member). Lean-first (no Rocq counterpart).

**The triple:** authkv's: `clientv3.New.spec`'s at the configuration it builds; given `Authenticate`
registered at the address with a reply to `(name, pw)` meeting `P` (`authTokReg`), a new client
whose KV calls carry a token meeting `P` or the context's own (`clientTokAt`), or an error and
`nil`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.New
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- See the file header. -/
abbrev newUserClient.spec : Prop :=
  ∀ (addr name pw : GoString) (lg : Loc) (V : WEnv GF) (P : GoString → IProp GF),
  plainEndpoint addr → threadBound GF ≤ 2 ^ 30 → strsSizeOk [name, pw] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗ levelTok 0 ∗ (-- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      client.ctxErrClientAll ∗ authTokReg [addr] name pw P) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.newUserClient))
      (Val #addr)) (Val #name)) (Val #pw)) (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl [addr] V ∗
        clientTokAt cl [addr] P) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
