/- kvreconf's (the same Go text), ported. Lean-first (no Rocq counterpart).

`RandomOptions()` (cluster.go): random options a cluster may run with (`kdOptsOk`, what
`StartCluster` takes): one to five voters, a window of one, four or 256 inflight messages, and a
size limit that is not zero for both sizes (the committed size is set to `4 KiB` when both
random choices are `0`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

/-- See the file header. -/
abbrev RandomOptions.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.RandomOptions)) (Val #()))
  {{ (o : KOptions), RET #o; ⌜kdOptsOk o⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
