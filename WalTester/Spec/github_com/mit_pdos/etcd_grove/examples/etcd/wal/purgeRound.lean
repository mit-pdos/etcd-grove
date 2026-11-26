/-
`purgeRound(lg, dir, max)` (wal.go) over `fsExt` (unit `locks`, session 10): one round of
`fileutil.purgeFile`'s loop on the WAL directory `dir` (the names ending in `"wal"`, sorted, the oldest
beyond `max` removed, each only after its lock is taken), while the WAL's handle is lent to it. From the
open handle (`walOpenWF`), the caller's repeatable commit for the removals (`walPurgeAcc dir Pc`: each
removal of a segment moves the WAL's purge and read positions, `pur := max pur p` and `cut := k` with
`d.cut ≤ k ≤ p ≤ d.unl`) and its token `Pc`, the round gives the handle and the token back; nothing else
(every failure stops the round). `max` below `2^63`, so that `n+max` does not wrap. Lean-first (no Rocq
counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberInv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs WalEnc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev purgeRound.spec : Prop :=
  ∀ (W : WalGS GF) (P : WalPbIn GF) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (lg w : Loc) (dir : GoString) (i : Nat) (mx : w64) (Pc : IProp GF),
  uint.nat mx < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ WalFs.walInv (W := W) walCodec Mr R jr r ∗
      walOpenWFI (W := W) P Mr w dir i ∗ walPurgeAcc (W := W) dir i Pc ∗ Pc }}
    (App (App (App (Val (@! purgeRound)) (Val #lg)) (Val #dir)) (Val #mx))
  {{ RET #(); walOpenWFI (W := W) P Mr w dir i ∗ Pc }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
