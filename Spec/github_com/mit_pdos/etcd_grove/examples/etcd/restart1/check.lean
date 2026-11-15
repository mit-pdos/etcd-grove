/-
`check(s)` (`examples/etcd/restart1/restart1.go`; restart S7.5, step f, 2026-11-14): the wait until the
restarted member knows a leader (`Leader() != 0`), one linearizable `Range` of `["k", "l")` through its
own API (`EtcdServer.Range`), in a context with the request timeout, and the check: exactly the `NPuts`
pairs `key(i) ↦ value(i)`, in order, or a panic. Lean-first (no Rocq counterpart).

**The triple:** of a started member (`etcdstart.memberUp`, the restarted one), under `restart1`'s KV
invariant at its names (`r1Inv`, the stopped incarnation's, `r1Inv_st`) and the put counter's lower
bound `NPuts` (every put fired): no panic, whatever the check returns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.KV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- See the file header. -/
abbrev check.spec : Prop :=
  ∀ (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (γc : GName),
  srvLevels (GF := GF) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
      etcdstart.memberUp s ρ E₀ lg γn id ∗ r1Inv ρ.rd.kv γc ∗ monoNatLbOwn γc r1NPuts }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.check)) (Val #s))
  {{ (b : Bool), RET #b; True }}

end spec

end etcd_restart1
end EtcdGrove
end Perennial
