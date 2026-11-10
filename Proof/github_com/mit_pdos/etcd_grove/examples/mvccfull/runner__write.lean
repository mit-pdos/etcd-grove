/- Lean-first (no Rocq counterpart). The proof of `runner.write`: Draft, to come.

The outline: the loop's invariant is `writerOwn` (with `nv ≤ 3 · |ops|`; `writerOwn` itself keeps
`|ops| ≤ Ops`, which `restore` needs at every iteration); `pick` of `Mix.Step`; the leader's step,
only under the loop guard `l.ops < x.cfg.Ops` (case 0; `l.ops = |ops|`, so the longer log is still
at most `Ops`): `gen` at `runM ks ops |ops|` (`writerCtrs`' `nextLease`), the op appended to `x.log`
(`logOk` extended by `opValid`; every `memW` and `histW` restated at the longer log, `runM_prefix`),
`apply` leading; the follower's: `apply` with the lower bound from `histW`;
`restore`; `restart` of either; `checkLeases` of both; then the follower's loop.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__write
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restore
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restart
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases

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

theorem runner.write.wp_proof
    (wp_pick : pick.spec (GF := GF) (hG := hG))
    (wp_gen : runner.gen.spec (GF := GF) (hG := hG))
    (wp_apply : runner.apply.spec (GF := GF) (hG := hG))
    (wp_restore : runner.restore.spec (GF := GF) (hG := hG))
    (wp_restart : runner.restart.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.write.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
