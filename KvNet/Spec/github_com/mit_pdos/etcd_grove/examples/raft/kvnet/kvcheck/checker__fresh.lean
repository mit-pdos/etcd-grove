/-
`c.fresh(next)` (kvcheck.go), `next` one of the checker's counters (`&c.nextOp`, `w = false`;
`&c.nextRead`, `w = true`): under `c.mu`, the counter's next number, never issued before
(`issued γ w n`, exclusive: `issued_excl`). Once the counter is at `2^64 - 1` it never returns.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.fresh.spec : Prop :=
  ∀ (c : Loc) (γ : CheckerNames) (ls : List GoString) (w : Bool) (next : Loc),
  next = (if w then c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextRead"] else c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextOp"]) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗ isChecker c γ ls }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty @!! go!"fresh")) (Val #next))
  {{ (n : w64), RET #n; issued γ w n }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
