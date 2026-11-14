/-
`(*member).opRecvSnap()` (wal.go) over `fsExt` (W4c U5): the raft loop's persistence of a received
snapshot. Nothing if the last index is at `maxIndex = 2^62` or above; else `saveSnap(s, term)` at some
`s ∈ (last, last + 4]`, the raft-like fields reset to it (a fresh `terms`), up to two entries above it at
the term, `save` of the hard state (commit `s`) with them, then `sync`. Stated over the running member
(`memLive`, `MemberInv.lean`): from `memLive o` with room for the snapshot and a two-entry save
(`tOrRoom o 176`), `true` gives `memLive o'` for an oracle `o'` at most 176 bytes longer; `false` (a WAL
call failed: the member stops) gives nothing. Lean-first (no Rocq counterpart).
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
abbrev member.opRecvSnap.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m : Loc) (qc : Qp) (o : TOracle),
  e.orFile.Ok → tOrRoom o 176 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memLive W e γ m qc o }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"opRecvSnap")) (Val #()))
  {{ (b : Bool), RET #b; if b then ∃ o' : TOracle, memLive W e γ m qc o' ∗
      ⌜(tEncodeOracle o').length ≤ (tEncodeOracle o).length + 176⌝ else True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
