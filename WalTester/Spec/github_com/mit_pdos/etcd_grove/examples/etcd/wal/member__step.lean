/-
`(*member).step()` (wal.go) over `fsExt` (W4c U5): `fits(m.o, oracleRoom = 256)` (false: the member goes down), then
one random operation: `opEntries`, `opResend`, `opCommit`, `opTerm`, `opOwnSnap`, `opRecvSnap`, `sync`, `close`
followed by `restart`, or nothing. Stated over the running member (`memLive`, the form the operations leave): at
`Open`'s half of the call permission (`restart` needs the whole one, with `close`'s half), with what `restart`
needs beside it (the logger, the WAL directory field, the area's path and resources), which come back. `true`:
the running member at some oracle, small (`tOrSmall`: the operations stay within `fits`' room; `Boot`'s
final `close` stores it); `false` (a WAL call failed, a restart's read failed, or the oracle is full):
nothing more. Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__restart

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
abbrev member.step.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m lg : Loc) (o : TOracle) (qp : Qp),
  m ≠ null → e.orFile.Ok → tWalPathsOk e.area → PathFits (tWalDir e.area) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memLive W e γ m (1 : Qp).half o ∗ zapLoggerOk lg ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.area ∗
      osPathS (GF := GF) e.R (e.area) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"step")) (Val #()))
  {{ (b : Bool), RET #b;
      osPathS (GF := GF) e.R (e.area) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.area ∗
      if b then ∃ o' : TOracle, memLive W e γ m (1 : Qp).half o' ∗ ⌜tOrSmall o'⌝ else True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
