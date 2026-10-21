/-
`newClient(eps, lg)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3a, 2026-10-20; the
endpoints a slice since 2026-10-21, failover, `notes/decisions.md` D27): `clientv3.New` of a
configuration with the endpoints `eps`, the logger `lg` and `MaxUnaryRetries: 1` (one attempt per
call: a Put is sent at most once, D21i), what linkv3's `Main` did inline for its one client.
Lean-first (no Rocq counterpart).

**The triple:** for plain endpoints (`plainEndpoints`, `clientv3.New`'s premise: at least one, each
plain), read-only, and a logger, from the package's fact: the one-attempt client of those endpoints
(`isNewClient` at any watch environment `V`, which the caller never uses, `clientKVOnce`) and
`nil`, or an error and `null` (`clientv3.New`'s two cases).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev newClient.spec : Prop :=
  ∀ (eps : GoSlice) (addrs : List GoString) (lg : Loc) (V : EtcdGrove.client.WEnv GF),
  threadBound GF ≤ 2 ^ 31 → lg ≠ null → plainEndpoints addrs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      eps ↦*□ addrs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.newClient)) (Val #eps))
      (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl addrs V ∗ clientKVOnce cl addrs) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end linkv3p
end EtcdGrove
end Perennial
