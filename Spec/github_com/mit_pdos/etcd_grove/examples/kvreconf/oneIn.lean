/- Lean-first (no Rocq counterpart).

`oneIn(n)` (kv.go): a random boolean (true with probability `1/n`); `n ≠ 0`, as `%` needs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev oneIn.spec : Prop :=
  ∀ (n : w64), n ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn)) (Val #n))
  {{ (b : Bool), RET #b; True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
