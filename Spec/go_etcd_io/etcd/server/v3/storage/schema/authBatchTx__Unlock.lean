/-
`(*authBatchTx).Unlock()` (`auth.go`): the backend's `Unlock`, then its `Commit` ("for defensive
purpose").
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Commit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- An `authBatchTx` over the real backend's batch transaction `t`: `batchTxBuffered.Unlock.spec`
(one write-back token, the part handed in made idle), then `batchTxBuffered.Commit.spec` (another,
the commit's requirement `X` to `Y`). -/
abbrev schema.authBatchTx.Unlock.spec : Prop :=
  ∀ (atl : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (Q : IProp GF)
    (S : GoString → Prop) (r : GMap GoString BktData) (qo : Qp) (X Y : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atl ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t : GoInterface) ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗ rbPart γ S r ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, ⌜sbKept P st⌝ ∗ bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) ∗
      wbTok γ ∗ bOpen γ qo ∗ X ∗ commitReq γ P Pk b X Y }}
    (App (Val (atl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q ∗ rbOwnIn γ S r ∗ bOpen γ qo ∗ Y }}

end spec

end EtcdGrove
end Perennial
