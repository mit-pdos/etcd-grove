/- Lean-first (no Rocq counterpart). kvreconf's.

`pick(ids)` (reconf.go): a random element of `ids`, which is not empty.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev pick.spec : Prop :=
  ∀ (sl : GoSlice) (ids : List w64) (dq : DFrac), ids ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ sl ↦*{dq} ids }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.pick)) (Val #sl))
  {{ (x : w64), RET #x; sl ↦*{dq} ids ∗ ⌜x ∈ ids⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
