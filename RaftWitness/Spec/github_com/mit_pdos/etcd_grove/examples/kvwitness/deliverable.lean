/- Lean-first (no Rocq counterpart).

`deliverable(m)` (cluster.go): whether the transport passes `m` on; `true` only for a
message that is `Deliverable` (`Cluster.lean`). raft v3.7 (2026-10-16, stage R6b): `m` is a
`*pb.Message` holding `st` (`msgPtsC`, at any fractions: the getters read it; `m.Entries` and
`m.Context` are read in place), given back.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev deliverable.spec : Prop :=
  ∀ (m : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗
      msgPtsC m dq dqe cap st }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.deliverable)) (Val #m))
  {{ (b : Bool), RET #b; msgPtsC m dq dqe cap st ∗ ⌜b = true → Deliverable st⌝ }}

end spec

end kvwitness
end EtcdGrove
end Perennial
