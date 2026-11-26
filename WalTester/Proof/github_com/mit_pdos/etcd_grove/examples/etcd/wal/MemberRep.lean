/-
Lean-first (no Rocq counterpart).

# The running member's resources around a `save` (W4c U5)

`member.save.spec`'s precondition and postcondition, but for `isPkgInit` and the `save` arguments, as two
predicates, so that the specs of the operations built over `save` (`opTerm`, `opCommit`, ...) state them
once: `memSaveRes` (the invariants, the call permission, the member's fields `orPath`, `w`, `o`, the
oracle, the program's ghost halves, the open handle, the WAL's persistent facts) and `memSavePost b o h es`
(`save`'s postcondition at the oracle `o`, the hard state `h` and the entries `es`).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__save

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

/-- `opTerm`'s term: raised by one below `maxIndex = 2^62`. -/
def tNextTerm [GooseExts] (t : w64) : w64 := if uint.nat t < 2 ^ 62 then t + W64 1 else t

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- `member.save.spec`'s resources (but `isPkgInit` and the arguments). -/
def memSaveRes (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) : IProp GF :=
  iprop(osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w ∗ m.[member, go!"o"] ↦ v ∗
      oracleRep v o ∗ tOrOwn γ os none ∗ tWalOwn γ (some d) ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
      walOpenWFI (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) 0 ∗
      WalFs.walNamed (W := W) (tWalDir e.area) 0 ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark o c) ∗
      WalFs.walLenLb (W := W) w (tWalDir e.area) 0 d.H.length)

/-- `member.save.spec`'s postcondition at the oracle `o`, the hard state `h` and the entries `es`. -/
def memSavePost (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (o : TOracle) (c : TCand) (qc : Qp)
    (h : THs) (es : List TEnt) (b : Bool) : IProp GF :=
  iprop(DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w ∗ ∃ v' : oracle,
      m.[member, go!"o"] ↦ v' ∗ (∃ os' : TOracle, tOrOwn γ os' none) ∗
      if b then ∃ d' : WalDur, oracleRep v' (tSaveO o h es) ∗ tWalOwn γ (some d') ∗
        walOpenWFI (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) 0 ∗
        ⌜tMemOk (tSaveO o h es) c d' ∧ tMemHs (tSaveO o h es) d'⌝ ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark (tSaveO o h es) c) ∗
        WalFs.walLenLb (W := W) w (tWalDir e.area) 0 d'.H.length
      else True)

end rep

end etcd_wal
end EtcdGrove
end Perennial
