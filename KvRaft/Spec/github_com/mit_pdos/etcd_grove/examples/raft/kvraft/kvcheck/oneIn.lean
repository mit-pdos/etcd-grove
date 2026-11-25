/-
`oneIn(n)` (kvcheck.go): a random boolean, true with probability 1/n; for `n ≠ 0` (no
division by zero), it returns. As kvdurable's.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

/-- See the file header. -/
abbrev oneIn.spec : Prop :=
  ∀ (n : w64), n ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.oneIn)) (Val #n))
  {{ (b : Bool), RET #b; True }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
