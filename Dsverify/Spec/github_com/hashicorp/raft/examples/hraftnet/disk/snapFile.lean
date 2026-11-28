/-
(hraft_robust R3) The spec of `disk.snapFile` (`snap.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SnapInv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- `snapFile(dir)`: `dir + "/snap"`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.snapFile.spec : Prop :=
  ∀ (dir : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.snapFile)) (Val #dir))
  {{ RET #(dir ++ go!"/snap"); True }}

end sec

end Perennial
