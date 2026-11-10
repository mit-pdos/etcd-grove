/- Lean-first (no Rocq counterpart). The proof of `runner.newMember`: Draft, to come.

The outline: the struct allocated; the closure (`hookOk`'s triple: `applying.Load`,
`saved.Load`, `saved.Store`); the atomics' stores; the ghost names (`ghostVar`s, `monoNat`s) and
`memberCarry` at `mvccStart` (`histOkM` against `hist0`, `onceUpToAll` of the empty log);
`mvccImage_fresh.law`; `open` at `n = 0` (its `Ops ≤ k` the post's; `ops.length < 2 ^ 38` at the
empty log); the `regs` invariant.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.newMember.wp_proof
    (hfresh : mvccImage_fresh.law (GF := GF))
    (wp_open : runner.open.spec (GF := GF) (hG := hG)) :
    runner.newMember.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
