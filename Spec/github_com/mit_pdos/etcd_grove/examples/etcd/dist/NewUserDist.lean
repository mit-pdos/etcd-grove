/-
`clientv3.New(cfg)` with a user name, across machines, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/NewUserDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
written in. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`New_user_dist`: `clientv3.New(cfg)` with a user name, across machines** (mirrors
`clientv3.New.spec`, whose `clientAuthPre` registration of `Authenticate` at `eps` is replaced by the
address facts of an auth-on view; `clientTokAt` dropped from the post: the contracts read the principal
from `cfg`). `New` calls `getToken`, one `Auth.Authenticate` over the balanced connection: a success
names the member `mid` that answered and its check, `CheckPassword`'s (`auth.passwordChecked`: auth
enabled, the user in a recorded state), or `ErrAuthNotEnabled`, which `getToken` turns into a success
with no token (`enabledVerdict … false`). A wrong password, an unknown user and every transport failure
are the error arm.

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/NewUserDist.lean`). Reviews (`notes/axiom-review/`): first `f7-a.md` (`d946f6cbda`: UNSOUND, the member names a free binder `A`; fixed by `Γ.au`), then `f7-rerev-a.md` (`6d9d9fd662`): SOUND, given the Serve tie (its condition C, met by the adopted `Serve_dist`, `f7-combined.md`). Unchanged since (`f7-changed-since-review.md`). -/
abbrev New_user_dist.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] [NetProtoGS] (cfg : go_etcd_io.etcd.client.v3.Config)
    (eps : List GoString) (V : WEnv GF) (Γ : DistView),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  Γ.auth = true → principalOf cfg = some cfg.Username' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ levelTok 0 ∗
      clientCfgOk cfg eps ∗ ⌜strsSizeOk [cfg.Username', cfg.Password']⌝ ∗
      membersAt (Gg := hG.goose_globalGS) eps Γ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.New)) (Val #cfg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl eps V ∗ clientF cl go!"cfg" ↦□ cfg ∗
          ∃ (mid : w64) (rev : w64), servedBy eps Γ mid ∗
            (auth.passwordChecked (.on (Γ.au mid)) cfg.Username' rev GoInterface.nil ∨
              auth.enabledVerdict (.on (Γ.au mid)) false)) ∨
        ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

/-! ### KV writes -/

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
