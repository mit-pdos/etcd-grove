/-
`(*authClient).UserAdd(ctx, name, pw)` across machines, auth on, at the cluster view (F7, `notes/etcd-dist-f7.md`; an interim trust-boundary axiom until #24's S2
client side: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthUserAddDist.lean`). Moved from the drafts of `AuthViewDist.lean`, whose definitions it is
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

/-- **`Auth_UserAdd_dist`: `(*authClient).UserAdd(ctx, name, pw)` across machines** (mirrors
`authClient.UserAdd.spec` at `etcdUserAddSpecW`: the caller's persistent history update `histAu` at the
cluster's names, the binding `userOk` of `cfg`'s principal; a success the cluster-level `adminRepliedD`,
which names the member).

An interim trust-boundary axiom (F7, the lead's approval #50 2026-11-26T06:08Z;
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthUserAddDist.lean`). Reviews (`notes/axiom-review/`): `f7-b.md` (`d946f6cbda`: NEEDS-FIX, the server's name bound missing; added), `f7-rerev-a.md` (`6d9d9fd662`) SOUND. Unchanged since (`f7-changed-since-review.md`). -/
abbrev Auth_UserAdd_dist.spec : Prop :=
  ∀ [NetProtoGS] (cl ap : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd) (name pw : GoString)
    (Q : List auth.AuthState → IProp GF),
  Γ.auth = true → γR.raft.log = Γ.kv.rlog → outTokOk (principalOf cfg) om →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      authClientAt cl ap eps V Γ cfg ∗ metadata.outMD ctx om ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗
      -- (F7 review B, 2026-11-26) the server's name bound, as the siblings and `etcdUserAddSpecW`: an
      -- over-long name makes every member that applies the entry `lg.Fatal`
      -- (`issues/etcd-auth-useradd-long-name-fatal.md`)
      ⌜strsSizeOk [name, pw] ∧ name.length ≤ backend.maxKeySize⌝ ∗
      □ (∀ um : apply.UserAddModel, ⌜um.name = name ∧ um.noPassword = false⌝ →
        histAu γR Γ.kv srvAuthSt0 (fun hm => iprop(⌜userOk (principalOf cfg) hm.username⌝))
          (irrUserAdd um) Q) }}
    (App (App (App (Val (ap @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!!
        go!"UserAdd")) (Val #(GoInterface.ok ctx))) (Val #name)) (Val #pw))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ um : apply.UserAddModel,
          ⌜um.name = name ∧ um.noPassword = false ∧ um.pwSure⌝ ∗
          adminRepliedD eps Γ γR (principalOf cfg) (irrUserAdd um) Q) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end authd
end etcd_dist
end EtcdGrove
end Perennial
