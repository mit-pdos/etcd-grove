/-
`(*authBatchTx).UnsafeSaveAuthRevision(rev)` (`auth.go`): the revision's 8 big-endian bytes put at
`authRevision` in the `Auth` bucket.
Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`,
"authstore-noax").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBackendReal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut

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

/-- An `authBatchTx` over the real backend's batch transaction `t`, under the lock at `st`, with the
`Auth` bucket's write resource (`rbPut`): the put of `u64Be rev` at `authRevision`
(`batchTxBuffered.UnsafePut.spec`; the bucket in the table, not safe-range, the key not a hook's
own). -/
abbrev schema.authBatchTx.UnsafeSaveAuthRevision.spec : Prop :=
  ∀ (atl : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (rev : w64),
  P.has mvcc.authBI → P.SB mvcc.authBI.name = false →
  P.hk mvcc.authBI.name schema.authRevisionKey = false → sint.Z st.pend + 1 < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ schema.abtF go!"tx" atl ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t : GoInterface) ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗
      rbPut γ P mvcc.authBI.name st.S }}
    (App (Val (atl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"UnsafeSaveAuthRevision"))
      (Val #rev))
  {{ RET #(); batchLocked γ P b (st.put mvcc.authBI schema.authRevisionKey (u64Be rev) false) ∗
      rbPut γ P mvcc.authBI.name (st.put mvcc.authBI schema.authRevisionKey (u64Be rev) false).S }}

end spec

end EtcdGrove
end Perennial
