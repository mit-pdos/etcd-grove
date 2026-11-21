/-
`Boot(area, orDir, seed, nOps)` (wal.go) over `fsExt` (W4c U5): one incarnation of the tester. A member with
a no-op logger, the choice source of `seed` and the oracle path `orDir/state`; the oracle loaded
(`loadOracle`); the WAL `area/wal`: if `Exist` says there is none, the `panic` when the oracle says `Create`
had returned (unreachable: the oracle's relation names the WAL, whose view `Boot` first raises to named,
`tInv_named`, and `Exist`'s `false` arm admits no named WAL), else `Create` (on an error the member is down),
the fresh oracle with `created` stored and the zero contents resumed; if there is one, `restart` (on a
failure the member is down). Then at most `nOps` steps (`step`, any failure down) and, by a choice, `close`.

Stated over the program's part of `TBoot` (U5: its existential's witnesses universally quantified, the
crash tokens set aside, which the crash condition keeps): the tester's invariant and the program's halves of
the ghost state (the oracle `o` with no `Write` pending, the WAL state `od`), the WAL's area, durable's
invariant and handle, the whole call permission. The post claims nothing: the theorem is that no execution
panics (nor gets stuck), whatever the file system's crashes left (`o`, `od` any states the invariant
relates). Premises: the oracle file is well named (`e.orFile.Ok`), the WAL's paths are the area's
(`tWalPathsOk`), the area is a root (its spine, `osPathS_root`). Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__step

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
abbrev Boot.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (od : Option WalDur) (seed nOps : w64),
  e.orFile.Ok → tWalPathsOk e.area → (e.area, e.jr) ∈ e.R → tWalFsOk e.area →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      TRun W e γ o od }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.Boot)) (Val #e.area))
      (Val #e.orDir)) (Val #seed)) (Val #nOps))
  {{ (st : w64), RET #st; True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
