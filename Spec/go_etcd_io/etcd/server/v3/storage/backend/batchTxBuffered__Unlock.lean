/-
`Unlock` (the backend). `t.Unlock()`: the session's writes written back into the read buffer, and committed if a
delete is pending or the batch limit reached (the pre-commit hook then runs, with the hooks'
resource `Pk`). A deleting session (the new physical view thin of the old; a session that
changed nothing the readers see, `viewSame`, is one) gives the lock's resources `W ∗ Pk`; a put
session gives the clients' whole view and `Pk`, and gets the logical view back at `relog`, from
which it makes `W` (a wand: `W` may hold part of the view). A write-back's budget either way. (`Pk` is handed over up front in both cases: the
commit's hook needs it, before the new view exists.)
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.Unlock()`: the session's writes written back into the read buffer, and committed if a
delete is pending or the batch limit reached (the pre-commit hook then runs, with `Pk`). Two kinds
of session (question 2, option (a), 2026-10-29: one spec, the readers' view the logical view):
* **a deleting session** (the compaction job's; a session that changed nothing the readers see,
  `viewSame`, is its instance, `viewSame_thin`): it holds no clients' share of the view; the new
  physical view (the writer's contents) is thin of the old (`thinV`: what it deleted is registered as
  deletable), and its write buffer holds no puts to the non-hook buckets (review round 1, F8: `Unlock`
  writes the buffer back into the read buffer before committing, so such a put would be seen by
  readers between the two); it gives `W ∗ Pk ∗ Q`, and the logical view stays;
* **a put session**: it gives the clients' whole view `vd` (the logical view) and `Pk`, and gets the
  view back at `relog P vd st` (its writes over the logical view, keys compaction deleted earlier
  kept), from which it makes `W ∗ Q`; it deleted no safe-range entry the readers see (`sbKept`;
  the user's decision, 2026-11-04, probe M2: so the deleted entries stay the logical view's).
A write-back's budget either way. Not in the hook's window, with room for the commit's hook.
**A part of the tracked buckets handed in comes back idle** (decision 3, 2026-11-01, Q3:
`rbPart γ S r` in, `rbOwnIn γ S r` out, for any bucket set `S`, the caller's choice; nothing for `S`
empty, `Unlock.bare`): Go writes the session's puts back into the read buffer under
`readTx.Lock()` and, when a delete is pending, commits (`pendingDeleteOperations`,
etcd-io/etcd#17119), so a read transaction begun after it sees the writer's contents on `S`, up to
a bucket created in the session and not yet committed (`batchTxBuffered` counts a creation as
pending, not as a pending delete), which such a reader sees absent, as empty (`bktOf`); a later
write to a bucket of `S` needs the holder's part.
**Claimed buckets** (A1.5 of `auth-schema-srv`, D5 of `notes/auth-schema-srv-a1-scope.md`, 2026-11-17; one
spec, A1.8): the session is in the claimed mode (`batchLocked … true`; a client-facing session gets there by
`batchLocked_claimed`), and its writes through a claimed part (`st.cw`) are all to the buckets `Sc` of the claimed
part `rbPartR γ Sc rc` handed in. Go writes the session's puts back into the read buffer under `readTx.Lock()` and,
when a delete is pending, commits under it again (`batch_tx.go`, `Unlock` and `commit`): at each, readers'
contents of the claimed buckets move, which needs the client's halves (`rbRd`): the client hands in its accessor
(`rbAcc`, with its resource `Rr`), which `Unlock` runs at the write-back and at the commit; the client may count on
each claimed bucket moving as `unlockOk P st` allows (the writer's contents; untouched or only deleted from: kept;
put into and deleted from, at the write-back: the write-back's intermediate contents). The claimed part comes back
idle (`rbOwnInR`), and `Rr`. With no claimed bucket (`Sc = []`, `Rr = True`) this is the client-facing statement,
`Unlock.spec_free` (`UnlockBare.lean`).
(Until question 2: the put branch got `sData P st.S` back, and the first branch was `viewSame`;
a Draft `specC` had the deleting branch beside it. Until A1.8 the claimed statement was a second one,
`Unlock.specC`, beside this one.) -/
abbrev backend.batchTxBuffered.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF)
    (S : GoString → Prop) (r : GMap GoString BktData) (Sc : List GoString) (rc : GMap GoString BktData)
    (Rr : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 → Sc.Nodup →
  (∀ n, st.cw n = true → n ∈ Sc) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st true ∗ wbTok γ ∗ rbPart γ S r ∗
      rbPartR γ (fun n => n ∈ Sc) rc ∗ Rr ∗ rbAcc γ Sc (unlockOk P st) Rr ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, ⌜sbKept P st⌝ ∗ bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q ∗ rbOwnIn γ S r ∗ rbOwnInR γ (fun n => n ∈ Sc) rc ∗ Rr }}

end spec

end EtcdGrove
end Perennial
