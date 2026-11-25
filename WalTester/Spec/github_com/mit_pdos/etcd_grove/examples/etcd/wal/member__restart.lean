/-
`(*member).restart()` (wal.go) over `fsExt` (W4c U5): `fits(m.o, 16)` (room for `restartRead`'s two opens),
`restartRead(m.lg, m.walDir, m)`; on `readOK`, the check `checkRestart(m.o, c)` (which does not panic: the
read is an image's, `tRestart_ok`), `fits(m.o, 0)`, the new oracle stored (`storeOracle`, its relation from
`tRestart_ok`), `m.w = w` and `m.resume(c)`.

`true`: the running member (`memLive`, the form the operations take) at the new oracle `o''` (`tCheckRestart`
of `o` with the restart's opens, at the read `c`), with `Open`'s half of the call permission: its candidate is
the image the WAL's model holds and accounts for the WAL (`tRestart_ok`), the raft-like fields are `resume`'s
from `c` (`tMemFields_read`), `tCheckWf` holds again (`tCheckWf_restart`), and the new oracle is small
(`fits(m.o, 0)`: `tOrSmall`, which `Boot`'s final `close` needs). `false`: the read failed (the
member is down, also when either `fits` fails: the oracle would outgrow `durable`'s 1 GiB, U1 mismatch 2,
decided 2026-11-15); the fields `restartRead` does not touch back.

Premises: `restartRead.spec`'s but its room and `tReadsBackOk` (which `tCandOk`'s `tSim` gives,
`tCandOk_readsBack`; a premise until the tenth session), and `checkRestart`'s on the oracle (`tCheckWf o`:
every candidate well formed and short). The post's `memLive` carries the fields' relation to the read
image's discipline (`tMemSim`, `tRestart_sim`). (Until 2026-11-15 the room for the opens and the new oracle's size were premises; the
two `fits` checks replace them.) Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.restartRead
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberInv

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
abbrev member.restart.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m lg w0 : Loc) (v : oracle) (o : TOracle) (cd : TCand)
    (od : Option WalDur) (qp : Qp) (t vo cm b l : w64) (tm r : Loc) (rv : rnd),
  m ≠ null → e.orFile.Ok → tWalPathsOk e.area → PathFits (tWalDir e.area) →
  cd ∈ o.cands → (∀ d, od = some d → tCandOk o cd d) →
  tCheckWf o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      tPerm (GF := GF) e 1 ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
      osPathS (GF := GF) e.R (e.area) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      WalFs.walUnlockedTok (W := W) ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.area ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w0 ∗ m.[member, go!"o"] ↦ v ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"base"] ↦ b ∗ m.[member, go!"last"] ↦ l ∗ m.[member, go!"terms"] ↦ tm ∗
      m.[member, go!"r"] ↦ r ∗ r ↦ rv ∗ oracleRep v o ∗ tOrOwn γ o none ∗ tWalOwn γ od ∗
      tRelW (W := W) e.area o cd }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"restart")) (Val #()))
  {{ (ok : Bool), RET #ok;
      osPathS (GF := GF) e.R (e.area) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.area ∗
      if ok then ∃ o'' : TOracle, ⌜(∃ (ls : List w64) (c : TContents), o'' = tCheckRestart (tWithOpens o ls) c) ∧
          tOrSmall o''⌝ ∗
        memLive W e γ m (1 : Qp).half o''
      else DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗
        ∃ v' : oracle, m.[member, go!"o"] ↦ v' }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
