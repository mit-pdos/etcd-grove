/- Lean-first (no Rocq counterpart).

`below(n)` (kv.go): a random number below `n`, or `0` if `n` is `0`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

/-- See the file header. -/
abbrev below.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.below)) (Val #n))
  {{ (r : w64), RET #r; ⌜(n = W64 0 → r = W64 0) ∧ (n ≠ W64 0 → uint.Z r < uint.Z n)⌝ }}

end spec

end raft_kvreconf
end EtcdGrove
end Perennial
