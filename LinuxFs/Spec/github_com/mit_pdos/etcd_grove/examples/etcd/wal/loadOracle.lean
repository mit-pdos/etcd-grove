/-
`loadOracle(path)` (oracle.go) over `fsExt` (W4c U5): the oracle file (`TEnv.orFile`, at
`tOrPath root`) read through `durable.Read`, whose update commits on the tester's invariant (`TInv`)
unchanged: the file holds the program's oracle `o` (`tOracleFile`, no `Write` pending), so the read
returns its encoding, which decodes to it, or no file and the fresh oracle. No panic. Lean-first (no
Rocq counterpart).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Inv
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

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
abbrev loadOracle.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (qc : Qp), e.orFile.Ok →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      osCallPerm (GF := GF) qc ∗ tOrOwn γ o none }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.loadOracle)) (Val #(tOrPath e.orDir)))
  {{ (v : oracle), RET #v; DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ osCallPerm (GF := GF) qc ∗
      oracleRep v o ∗ tOrOwn γ o none }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
