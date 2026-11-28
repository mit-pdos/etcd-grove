/-
`etcdstart.Serve(s, a)` (`examples/lib/etcdstart`) on a member machine of a distributed deployment,
against the interim address fact (`notes/putget-dist-plan.md` §12; a trust-boundary axiom until
#24's S2: `Proof/.../etcd/dist/ServeDist.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`Serve(s, a)` of a started member of the view `Γ`, at an address set for it** (see the axiom's
docstring): from today's `Serve.spec` premises for a one-member start (the logger, the method sets, the
quota, the thread and receipt bounds, `grpcRepliesFit`, `srvLevels`), the started member (its member id `mid`)
whose KV names agree with the view's (`kvCongr ρ.rd.kv Γ.kv`: what every incarnation of every member of the
cluster has, `notes/etcd-dist-plan.md` §18.3), and the address `a` set to serve etcd's table for `(Γ, mid)`
(`etcdAddrAt`), `Serve` returns.

The member is tied to the view (F7 and F2's P-L1, 2026-11-26; until then auth off only, `etcdstart.memberUp` at the
lease mode `.none`, nothing tying `Γ.ls mid`):
* with auth on, its serving resources are `etcdstart.memberUpOnL … (Γ.au mid) Γ.kv.lm (Γ.ls mid)` (`memberUpOn`'s,
  its `E.authMode = .on (Γ.au mid)`: the member's auth names the view's), its history the view's
  (`ρ.rd.kv.hist = Γ.kv.hist`: `kvCongr` leaves `hist` out; with auth on every member's history is the cluster's,
  `kvCongrOn`), and the view's auth names distinct per member;
* with auth off, `etcdstart.memberUpL … Γ.kv.lm (Γ.ls mid)` (`memberUp`'s);
* in both, the member's lessor is at the view's name `Γ.ls mid` and its lease subsystem at the view's mode `Γ.kv.lm`.
Why (F7 reviews A and C, 2026-11-26): address facts are minted for any `Γ` (`etcdAddr_set`), so without these
premises a start could publish a `Γ` whose `au`/`ls` names it allocated and owns, and refute every auth-on and
lease axiom's success arm. With them, `Γ.au mid` and `Γ.ls mid` are the serving member's real names, held
through the member's exclusive resources (`NewServer_dist`'s `authNamesFreshD γa` and `Hlslot`), so two members
cannot share them. The distinct-auth-names premise kept here is redundant given the tie; the lessor's
distinctness stays a premise of the four lease axioms. `etcdSvc`'s intended interpretation then says that an
auth-on member's entries are the `etcd*SpecOn` handlers at `T := False` (no TLS identity: `ClientCertAuthEnabled`
false in `deployment`'s configuration).

**With auth off the table's KV entries are defined** (stage B′, 2026-11-28, `S2Interim.lean`'s `etcdSvc`: the
view specs `etcd*SpecV Γ.kv`, flagged `nr`). Serving them claims, of a real auth-off member, that its KV
handlers through etcd's unary chain meet the view specs and never return a refusal (`grpcRunNRMd`): the auth
store stays disabled (no proof can call the Auth service of an auth-off view: its entries are `etcdSvcRest`'s),
and the member is a voter for its whole life (`NewServer`'s `bootCfgFresh`: a member of a new cluster's initial
membership; etcd has no voter-to-learner change). The axiom's docstring has the argument, `notes/etcdsvc-b.md`
the details. The statement's text is unchanged.

**Condition C** (re-reviews A and C, 2026-11-26): the auth-on drafts (`AuthViewDist.lean`) that read `Γ.au mid`
are sound only while *every* route that serves `etcdSvc Γ mid` for an auth-on `Γ` requires
`etcdstart.memberUpOn(L) … (Γ.au mid) …`, as this text does. No other serve axiom (an in-process `Serve`,
`grpc.Server.Serve` over a table, a later `Serve_dist` variant) may serve an auth-on `Γ` without this tie.

**Restarts are outside it** (the no-crash line only): `memberUpOnL`/`memberUpL` hold of a member's first
incarnation. A member restarted after a crash cannot re-serve at the same `Γ.ls mid`/`Γ.au mid`: the lessor slot
`lease.lessorSlot (Γ.ls mid)` closes once, at the first `NewLessor` (and `srvLeaseRd`'s restart branch is mode
`.none` only), and `authNamesFreshD (Γ.au mid)` needs the history at `[bootState]`, which has grown. Serving a
fixed `Γ` across crashes is a crash-line item.

The distinct-auth-names premise binds only auth-on views (re-review C's N2: `Γ.au` is never read with auth off,
so an auth-off start need not pad it). -/
abbrev Serve_dist.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView),
  -- with auth on, distinct auth names per member (the lease review's form; redundant given the tie below;
  -- guarded, re-review C's N2)
  (Γ.auth = true → ∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist)⌝ ∗
      -- the member's auth names `Γ.au mid` (auth on), its lessor `Γ.ls mid`, its lease mode `Γ.kv.lm`
      (if Γ.auth then etcdstart.memberUpOnL s ρ E₀ lg γn mid (Γ.au mid) Γ.kv.lm (Γ.ls mid)
        else etcdstart.memberUpL s ρ E₀ lg γn mid Γ.kv.lm (Γ.ls mid)) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
