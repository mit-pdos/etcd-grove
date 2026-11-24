/- Lean-first (no Rocq counterpart).

`MainAt(r)` (`examples/mvccfull/start.go`, P3 of the pure-premise plan, 2026-11-24): `Main` with its
files in the directory `r`, `Run(MainConfig(r/mvccfull))`, but only if `r` fits (`dirFits`) and
nothing is at any of the run's file paths (`FilePaths` of that configuration, each `absent`);
otherwise it returns. Of a root `r` of the file system as the program finds it at start
(`rootClaimF r`, whatever its names hold), over the file extension's instances (quantified: the Link
has none) under which its steps do not fail (`backend.FsNoErrAll`): it returns (`Run`'s checks pass,
`Run.spec`). Until then the closed theorem assumed `Fs.DirFits r` and the names' absence (premises
`Hrfit`, `Habs`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run
public import Proof.runtime.RootClaim

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev MainAt.spec : Prop :=
  ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
    [os.fileStat.FieldAssumptions] [backend.FsNoErrAll]
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] (r : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      rootClaimF (GF := GF) r ∗ threadTok ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.MainAt)) (Val #r))
  {{ RET #(); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
