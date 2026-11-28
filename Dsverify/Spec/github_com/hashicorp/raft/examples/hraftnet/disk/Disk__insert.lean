/-
(hraft_robust R3) The spec of `disk.(*Disk).insert` (`disk.go`, `d.mu` held).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv

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

/-- `d.insert(lv)`: the image's entries with `de` (the entry `lv` holds) inserted (`insEnt`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.insert.spec : Prop :=
  ∀ (d : Loc) (I : DiskImg) (stg : w64) (lv : Log) (de : DEnt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ diskMem d I stg ∗
      entRep lv de }}
    (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"insert")) (Val #lv))
  {{ RET #(); diskMem d { I with ents := insEnt de I.ents } stg }}

end sec

end Perennial
