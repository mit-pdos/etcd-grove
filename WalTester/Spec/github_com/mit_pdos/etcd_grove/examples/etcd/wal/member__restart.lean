/-
`(*member).restart()` (wal.go) over `fsExt` (W4c U5): `restartRead(m.lg, m.walDir, m)`; on `readOK`, the
check `checkRestart(m.o, c)` (which does not panic: the read is an image's, `tRestart_ok`), the new oracle
stored (`storeOracle`, its relation from `tRestart_ok`), `m.w = w` and `m.resume(c)`.

`true`: the running member (`memLive`, the form the operations take) at the new oracle `o''` (`tCheckRestart`
of `o` with the restart's opens, at the read `c`), with `Open`'s half of the call permission: its candidate is
the image the WAL's model holds and accounts for the WAL (`tRestart_ok`), the raft-like fields are `resume`'s
from `c` (`tMemFields_read`), `tCheckWf` holds again (`tCheckWf_restart`). `false`: the read failed (the
member is down); the fields `restartRead` does not touch back.

Premises: `restartRead.spec`'s, and `checkRestart`'s on the oracle (`tCheckWf o`: every candidate well
formed and short) and **the new oracle's size** (`tOrSmall` of `tCheckRestart` at every read and opens: the
encoding's length depends only on the candidates' histories, not on the opens' or the hard state's values,
but the bound is on the histories, so a premise). Lean-first (no Rocq counterpart).
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
    (d : WalDur) (qp : Qp) (t vo cm b l : w64) (tm r : Loc) (rv : rnd),
  e.orFile.Ok → tWalPathsOk e.root → o.created = true → cd ∈ o.cands → tCandOk o cd d → tCheckWf o →
  tReadsBackOk (d.H.map WalOpG.toM) → (tEncodeOracle o).length + 16 ≤ 0x40000000 →
  (∀ (ls : List w64) (c : TContents), tOrSmall (tCheckRestart (tWithOpens o ls) c)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      osCallPerm (GF := GF) 1 ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (tArea e.root) ∗
      osPathS (GF := GF) e.R (tArea e.root) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      WalFs.walUnlockedTok (W := W) ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.root ∗
      m.[member, go!"orPath"] ↦ tOrPath e.root ∗ m.[member, go!"w"] ↦ w0 ∗ m.[member, go!"o"] ↦ v ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"base"] ↦ b ∗ m.[member, go!"last"] ↦ l ∗ m.[member, go!"terms"] ↦ tm ∗
      m.[member, go!"r"] ↦ r ∗ r ↦ rv ∗ oracleRep v o ∗ tOrOwn γ o none ∗ tWalOwn γ (some d) ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.root) (tCandMark o cd) ∗ WalFs.walNamed (W := W) (tWalDir e.root) }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"restart")) (Val #()))
  {{ (ok : Bool), RET #ok;
      osPathS (GF := GF) e.R (tArea e.root) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.root ∗
      if ok then ∃ o'' : TOracle, ⌜∃ (ls : List w64) (c : TContents), o'' = tCheckRestart (tWithOpens o ls) c⌝ ∗
        memLive W e γ m (1 : Qp).half o''
      else DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ m.[member, go!"orPath"] ↦ tOrPath e.root ∗
        ∃ v' : oracle, m.[member, go!"o"] ↦ v' }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
