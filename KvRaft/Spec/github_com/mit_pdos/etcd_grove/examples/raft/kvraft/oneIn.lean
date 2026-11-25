-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/oneIn.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). kvreconf's (the same Go text), ported.

`oneIn(n)` (kv.go): a random boolean (true with probability `1/n`); `n ≠ 0`, as `%` needs.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev oneIn.spec : Prop :=
  ∀ (n : w64), n ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.oneIn)) (Val #n))
  {{ (b : Bool), RET #b; True }}

end spec

end kvraft
end EtcdGrove
end Perennial
