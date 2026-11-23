/-
`ClearProxy()` (`examples/etcd/dist/env/env.go`): the process made proxy-free and `ETCD_VERIFY`-free
(`os.Unsetenv` of the six proxy variables and of `ETCD_VERIFY`), what every machine program of
`putget_safe` and `etcd_safe` calls first. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, `ClearProxy()` returns, and `ETCD_VERIFY` is off for the rest
of the run (`envVerifyOff`, which the server's verify checks take; in one process program start gives it,
`goose_adequacy_start`'s `startRights`).

**Not proved** (no proof file): `os.Unsetenv` is names-only in Perennial's translation, and its spec needs the
process environment as machine-local state (`notes/perennial-changes.md`, 2026-11-23;
`notes/putget-dist-plan.md`, section 10). Until then this spec is a named hypothesis of the theorems that use
it (`putget_safe`'s member boot, `etcd_putget_dist.MemberBootHyps`), not an axiom. The post claims only
`ETCD_VERIFY`: what the proxy variables' absence gives (no proxy dialer in net/http and grpc) is not yet
stated anywhere.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.env
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.env.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dist_env

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.env.Assumptions]

/-- See the file header. -/
abbrev ClearProxy.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.env }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.env.ClearProxy)) (Val #()))
  {{ RET #(); envVerifyOff (GF := GF) }}

end spec

end dist_env
end EtcdGrove
end Perennial
