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
  kept), from which it makes `W ∗ Q`.
A write-back's budget either way. Not in the hook's window, with room for the commit's hook.
(Until question 2: the put branch got `sData P st.S` back, and the first branch was `viewSame`;
a Draft `specC` had the deleting branch beside it.) -/
abbrev backend.batchTxBuffered.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

end spec

end EtcdGrove
end Perennial
