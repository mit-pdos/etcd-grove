/- Lean-first (no Rocq counterpart).

`FileOf(dir, id)` (`examples/raft/kvnet/node.go`): the durable file of replica `id` in `dir`,
`dir + "/replica-" + itoa(id)` (`kdFileName`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev FileOf.spec : Prop :=
  ∀ (dir : GoString) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.FileOf)) (Val #dir))
      (Val #id))
  {{ RET #(kdFileName dir id); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
