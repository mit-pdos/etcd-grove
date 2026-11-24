/-
`Main(area, orDir)` (wal.go): the program, `Boot(area, orDir, 0, 40)` once `dirOk` accepts both
directories (else it returns); the crash and the restart between incarnations are the machine's (the
adequacy theorem's crash semantics). Stated as `Boot`'s spec (the program's part of `TBoot`, `TRun`; the
same premises), for directories the tester's facts hold of; `MainInvalid.lean` states the other case.
Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Boot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (od : Option WalDur),
  e.orFile.Ok → tWalPathsOk e.area → (e.area, e.jr) ∈ e.R → tWalFsOk e.area →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      TRun W e γ o od }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.Main)) (Val #e.area)) (Val #e.orDir))
  {{ RET #(); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
