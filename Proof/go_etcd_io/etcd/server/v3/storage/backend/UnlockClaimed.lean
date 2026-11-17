/-
**`batchTxBuffered.Unlock` in a claimed session** (A1.5 of `auth-schema-srv`, D5 of
`notes/auth-schema-srv-a1-scope.md`, 2026-11-17): the statement for a client that claimed tracked buckets
(`rbPartR`, its readers' halves `rbRd`), proved with `batchTxBuffered.Unlock.spec` (its corollary at no
claimed bucket) in `batchTxBuffered__Unlock.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section claimed
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`t.Unlock()` in a claimed session** (A1.5, D5): `batchTxBuffered.Unlock.spec`'s statement for a
session in the claimed mode (`batchLocked … true`), whose writes through a claimed part (`st.cw`) are all to
the buckets `Sc` of the claimed part `rbPartR γ Sc rc` handed in. Go writes the session's puts back into the
read buffer under `readTx.Lock()` and, when a delete is pending, commits under it again
(`batch_tx.go`, `Unlock` and `commit`): at each, readers' contents of the claimed buckets move, which needs
the client's halves (`rbRd`): the client hands in its accessor (`rbAcc`, with its resource `Rr`), which
`Unlock` runs at the write-back and at the commit; the client may count on each claimed bucket moving as
`unlockOk P st` allows (the writer's contents; untouched or only deleted from: kept; put into and deleted
from, at the write-back: the write-back's intermediate contents). The claimed part comes back idle
(`rbOwnInR`), the unclaimed part `rbPart γ S r` as in `Unlock.spec`, and `Rr`. -/
abbrev backend.batchTxBuffered.Unlock.specC : Prop :=
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

end claimed

end EtcdGrove
end Perennial
