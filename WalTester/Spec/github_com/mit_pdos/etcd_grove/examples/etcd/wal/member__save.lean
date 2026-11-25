/-
`(*member).save(h, es)` (wal.go) over `fsExt` (W4c U5): nothing for an empty save; else the operation
appended to the oracle's `since` and stored (`storeOracle`: the appended oracle accounts for the WAL
before the call, `tSaveO1`), the entries converted (`toRaft`), `w.Save(toHS(h), res)` (its update
committed on the tester's invariant: the WAL state `d` moves to `tSaveD d h es`), then, if the save
syncs (`walMustSync` on the member's `lastHS`, which is the WAL's last hard state, `tMemHs`), the mark
moved and stored, and `lastHS` advanced. `true`: the oracle `tSaveO o h es` (Go's), the handle, the WAL
state `d'` its candidate (`tMemOk`, `tMemHs`), the candidate's mark synced, the handle's history
written to `d'`'s length (`walLenLb`, which `sync` takes; the caller's for `d` before). Premise
`tSim` of the appended history (the caller's raft discipline, `ReadsBack.lean`: the tester's invariant
carries it so that a restart's history reads back; tenth session). `false`: `Save` failed (the
handle is lost; the member stops). The stored oracle is the program's but for `lastHS` (not stored
until the next store), hence `∃ os`. Touches the member's fields `orPath`, `w`, `o`. The client's call
permission `qc` (for `storeOracle`) as in `member.sync.spec`. Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SavePure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

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
abbrev member.save.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) (h : THs) (esl : GoSlice) (es : List TEnt),
  e.orFile.Ok → tMemOk o c d → tMemHs o d → (∀ x ∈ es, tEntWf x) → uint.nat h.term' < 2 ^ 63 →
  tOrSmall (tSaveO1 o h es) → tOrSmall (tSynced (tSaveO1 o h es)) →
  tSim ((tCandHist (tSaveO1 o h es) c).map absOp) (tCandMark o c) → tCheckWf o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w ∗ m.[member, go!"o"] ↦ v ∗
      oracleRep v o ∗ tOrOwn γ os none ∗ tWalOwn γ (some d) ∗ esl ↦*□ es ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
      walOpenWFI (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) 0 ∗
      WalFs.walNamed (W := W) (tWalDir e.area) 0 ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark o c) ∗
      WalFs.walLenLb (W := W) w (tWalDir e.area) 0 d.H.length }}
    (App (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"save")) (Val #h)) (Val #esl))
  {{ (b : Bool), RET #b; DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w ∗ ∃ v' : oracle,
      m.[member, go!"o"] ↦ v' ∗ (∃ os' : TOracle, tOrOwn γ os' none) ∗
      if b then ∃ d' : WalDur, oracleRep v' (tSaveO o h es) ∗ tWalOwn γ (some d') ∗
        walOpenWFI (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) 0 ∗
        ⌜tMemOk (tSaveO o h es) c d' ∧ tMemHs (tSaveO o h es) d'⌝ ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark (tSaveO o h es) c) ∗
        WalFs.walLenLb (W := W) w (tWalDir e.area) 0 d'.H.length
      else True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
