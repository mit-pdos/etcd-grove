/-
`(*member).saveSnap(idx, term)` (wal.go) over `fsExt` (W4c U5): the snapshot operation appended to the
oracle's `since` and stored (`tSnapO1`), `w.SaveSnapshot(&walpb.Snapshot{Index, Term, ConfState:
{Voters: [1]}})` (its update committed on the tester's invariant), then the mark moved to the end and stored
(`SaveSnapshot` syncs): `true`, `memOpPost` at `tSnapO o idx term`; `false`, `SaveSnapshot` failed (the
member stops). As `member.save.spec`, over `memSaveRes`.

**Stated, not proved**: the proof must show the snapshot record's encoding is the model's (`walSnapAt`:
`snapEnc c = Mr.encSnap md` with `absSnapMd`'s conf state), which `wal.go`'s `ConfState{Voters: []uint64{1}}`
(no `AutoLeave`) does not meet against U4's canonical form (W4c U1 mismatch 3, a user decision:
`notes/wal-fsext-w4c-plan.md`). `opRecvSnap` (and `opOwnSnap`) take it as a callee hypothesis. Lean-first
(no Rocq counterpart).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberInv

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
abbrev member.saveSnap.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) (idx term : w64),
  e.orFile.Ok → tMemOk o c d → tMemHs o d → uint.nat idx < 2 ^ 63 → uint.nat term < 2 ^ 63 →
  tOrSmall (tSnapO1 o idx term) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memSaveRes W e γ m w v o os c d qc }}
    (App (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"saveSnap")) (Val #idx)) (Val #term))
  {{ (b : Bool), RET #b; memOpPost W e γ m w (tSnapO o idx term) c qc b }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
