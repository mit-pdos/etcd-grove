/-
`storeOracle(path, o)` (oracle.go) over `fsExt` (W4c U5): the oracle file (`TEnv.orFile`, at
`tOrPath root`) made to hold the oracle `o'` the Go value `v` represents, through `durable.Write`'s two
updates on the tester's invariant (`TInv`): at the rename, the file's state holds `o'` with the
program's oracle `o` pending (both account for the WAL, `tRelI`: the caller gives `o'`'s); at the
directory's sync, nothing pending. The program's halves follow: the oracle is `o'`, the WAL state `od`
unchanged. `o'`'s encoding at most 1 GiB (`tOrSmall`: `durable.Write`'s premise; W4c U1 log, mismatch 2,
for whether the tester meets it). Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Inv
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev storeOracle.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (v : oracle) (o o' : TOracle) (od : Option WalDur) (qc : Qp),
  e.orFile.Ok → tOrSmall o' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      osCallPerm (GF := GF) (callKey e.R e.orDir) qc ∗ oracleRep v o' ∗ tOrOwn γ o none ∗ tWalOwn γ od ∗
      tRelI (W := W) e.area o' od }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle))
      (Val #(tOrPath e.orDir))) (Val #v))
  {{ RET #(); DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ osCallPerm (GF := GF) (callKey e.R e.orDir) qc ∗
      oracleRep v o' ∗ tOrOwn γ o' none ∗ tWalOwn γ od }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
