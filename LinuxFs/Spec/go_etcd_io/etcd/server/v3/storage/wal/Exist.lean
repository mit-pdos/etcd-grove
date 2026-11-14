/-
`wal.Exist` over `fsExt` (W12 of `notes/wal-fsext-plan.md`): the main tree's axiom
`Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean` restated with plan §3's binder changes (over
`fsExt`, the WAL layer `walAreaOk`, the area's spine and `walAreaRes`, the call permission, the update at
`walAuMask`, plan §11), the lock token framed and Q4 (b)'s `false` arm (`notes/specs-only/ledger.md`,
2026-11-14). S/ = `server/storage/wal/` at the pin with the local fork patches. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean`, over the hypotheses of
`ExistCallees.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **What `Exist` may answer `false` on**: no WAL, or a fresh, unnamed one (`Create` failed after its
rename and `cleanupWAL` may have moved its directory aside; plan §11, Q4 (b)). -/
def wal.ExistFalseOk (o : Option WalDur) : Prop :=
  o = none ∨ ∃ d, o = some d ∧ d.H = [] ∧ d.named = false

/-- **`Exist(dir)`** (S/util.go:36-42, with the fork's fix `c90b03b56`): `fileutil.ReadDir(dir,
WithExt(".wal"))`; on an error, `!errors.Is(err, os.ErrNotExist)`, else whether a `.wal` name was read.
Under the area discipline (`walAreaRes`: half the area's claim on every WAL name) the area holds at `nm`
the WAL's directory, or nothing when there is no WAL (`WalsAt`, `AbsentNone`), and a WAL's directory
holds its segments at `.wal` names. So `false` means no WAL (or Q4 (b)'s fresh one); `true` claims
nothing (the reads after it fail when there is none). Logically atomic: the state is unchanged,
committed as accessed (the body linearizes before its `ReadDir`, at a ghost step; no client update
needs it inside an `os` call). With the lock token (framed: reading a present WAL's directory takes its
claim out of the parked state, `walParked_lock`, and puts it back; `notes/specs-only/ledger.md`,
2026-11-14). The `false` arm rests on a hypothesis about `ENOENT` that the current model does not give
(`ExistCallees.lean`). -/
abbrev wal.Exist.spec (C : WalCodec) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp) (Q : Option WalDur → IProp GF),
  InArea r dir nm → NameOk nm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk C Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
      WalFs.walUnlockedTok ∗
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs dir o }> @ walAuMask, ∅
        <{ WalFs.walDirIs dir o, COMM Q o }> }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Exist)) (Val #dir))
  {{ (b : Bool), RET #b; osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
      WalFs.walUnlockedTok ∗ ∃ o : Option WalDur, Q o ∗ ⌜b = false → wal.ExistFalseOk o⌝ }}

end spec

end EtcdGrove
end Perennial
