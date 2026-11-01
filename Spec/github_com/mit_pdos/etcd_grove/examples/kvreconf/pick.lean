/- Lean-first (no Rocq counterpart).

`pick(ids)` (reconf.go): a random element of `ids`, which is not empty.
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
abbrev pick.spec : Prop :=
  ∀ (sl : GoSlice) (ids : List w64) (dq : DFrac), ids ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗ sl ↦*{dq} ids }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.pick)) (Val #sl))
  {{ (x : w64), RET #x; sl ↦*{dq} ids ∗ ⌜x ∈ ids⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
