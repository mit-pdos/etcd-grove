/-
`(*member).restart()` (wal.go) over `fsExt` (W4c U5): `restartRead(m.lg, m.walDir, m)`; on `readOK`, the
check `checkRestart(m.o, c)` (which does not panic: the read is an image's, `tRestart_ok`), the new oracle
stored (`storeOracle`, its relation from `tRestart_ok`), `m.w = w` and `m.resume(c)`.

`true`: the new oracle `o''` (`tCheckRestart` of `o` with the restart's opens, at the read `c`), whose
candidate `c'` is the image the WAL's model holds (`tRead c'.h = some c`) and accounts for the WAL as a
running member's (`tMemOk`, `tMemHs`: `member.save.spec`'s premises), the open handle and the WAL's facts,
`Open`'s half of the call permission, and the raft-like fields from `c` (`member.resume.spec`'s). `false`:
the read failed (the member is down); the fields `restartRead` does not touch back.

Premises: `restartRead.spec`'s, and `checkRestart`'s on the oracle (`tCheckWf o`: every candidate well
formed and short) and **the new oracle's size** (`tOrSmall` of `tCheckRestart` at every read and opens: the
encoding's length depends only on the candidates' histories, not on the opens' or the hard state's values,
but the bound is on the histories, so a premise). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.restartRead
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Resume

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
    (d : WalDur) (qp : Qp) (t vo cm b l : w64) (tm : Loc),
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
      oracleRep v o ∗ tOrOwn γ o none ∗ tWalOwn γ (some d) ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.root) (tCandMark o cd) ∗ WalFs.walNamed (W := W) (tWalDir e.root) }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"restart")) (Val #()))
  {{ (ok : Bool), RET #ok; DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      osPathS (GF := GF) e.R (tArea e.root) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      m.[member, go!"lg"] ↦ lg ∗ m.[member, go!"walDir"] ↦ tWalDir e.root ∗
      m.[member, go!"orPath"] ↦ tOrPath e.root ∗ ∃ v' : oracle, m.[member, go!"o"] ↦ v' ∗
      if ok then ∃ (w : Loc) (c : TContents) (o'' : TOracle) (c' : TCand) (d' : WalDur),
        m.[member, go!"w"] ↦ w ∗ oracleRep v' o'' ∗ tOrOwn γ o'' none ∗ tWalOwn γ (some d') ∗
        ⌜(∃ ls, o'' = tCheckRestart (tWithOpens o ls) c) ∧ tMemOk o'' c' d' ∧ tMemHs o'' d' ∧
          tRead c'.h = some c⌝ ∗
        osCallPerm (GF := GF) (1 : Qp).half ∗
        walOpenWF (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.root) ∗
        WalFs.walPurgeW (W := W) w (tWalDir e.root) ∗ WalFs.walLenLb (W := W) w (tWalDir e.root) d'.H.length ∗
        WalFs.walNamed (W := W) (tWalDir e.root) ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.root) (tCandMark o'' c') ∗
        m.[member, go!"term"] ↦ tResumeTerm c ∗ m.[member, go!"vote"] ↦ c.hs.vote' ∗
        m.[member, go!"commit"] ↦ tResumeCommit c ∗ m.[member, go!"base"] ↦ c.baseIdx ∗
        m.[member, go!"last"] ↦ tResumeLast c ∗
        ∃ tm' : Loc, m.[member, go!"terms"] ↦ tm' ∗ tm' ↦$ tResumeTerms c
      else True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
