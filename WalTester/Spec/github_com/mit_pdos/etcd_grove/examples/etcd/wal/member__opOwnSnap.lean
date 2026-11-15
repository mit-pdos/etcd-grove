/-
`(*member).opOwnSnap()` (wal.go) over `fsExt` (W4c U5): the apply thread's own snapshot. Nothing if the commit is
at or below the base; else `saveSnap(a, terms[a])` at some `a ∈ (base, commit]`, every candidate's unlock bound
raised to its history's name bound at `a` (`tRaiseNames`), the oracle stored, `ReleaseLockTo(a)` (its update
committed on the tester's invariant, `tInv_releaseAu`), and the base moved to `a`. Stated over the running member
(`memLive`, as `opRecvSnap`): from `memLive o` with room for the snapshot record (`tOrRoom o 56`), `true` gives
`memLive o'` for an oracle `o'` at most 56 bytes longer; `false` (a WAL call failed: the member stops) gives
nothing. Lean-first (no Rocq counterpart).
-/
module

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
abbrev member.opOwnSnap.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m : Loc) (qc : Qp) (o : TOracle),
  e.orFile.Ok → tOrRoom o 56 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memLive W e γ m qc o }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"opOwnSnap")) (Val #()))
  {{ (b : Bool), RET #b; if b then ∃ o' : TOracle, memLive W e γ m qc o' ∗
      ⌜(tEncodeOracle o').length ≤ (tEncodeOracle o).length + 56⌝ else True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
