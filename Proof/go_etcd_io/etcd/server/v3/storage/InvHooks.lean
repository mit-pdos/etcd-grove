/-
The server's backend hooks (`server/storage/hooks.go`, 2026-10-13, unit 8 of the backend).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The server's backend hook (unit 8)".

`BackendHooks.OnPreCommitUnsafe(tx)` is the backend's pre-commit hook (the backend's `hooksSpec`):
it runs the consistent index's `UnsafeSave(tx)`, then, under `confStateLock`, saves the
`confState` set by the apply thread's `SetConfState` (if dirty) into `Meta`'s key `confState`
(`schema.MustUnsafeSaveConfStateToBackend`, the trust boundary: a put through `tx.UnsafePut`).

- **The indexer's save** (`saveSpec`): the hook's contract of `ix.UnsafeSave(tx)`, with one put
  of room left (`hookSaveStep`: a hook step whose pending count stays below the hook's bound by
  one) and the `confState` key a put may write (`csDupOk`: not in the write buffer's `Meta`
  bucket, or the bucket may repeat a key, `wbDupOk`). The consistent index's save satisfies it
  (`Proof/.../etcdserver/CindexBackend.lean`, `ci_saveSpec`).
- **The hooks' state** (`isBackendHooks bh ix lg`, persistent): the indexer and the logger
  read-only, `confStateLock` guarding `confState` and `confStateDirty`. The struct `confState`
  points to is not owned here: `SetConfState` stores a fresh clone (`proto.Clone`) that no one
  writes afterwards, and `ConfState` is an axiomatized type (protobuf-go v2), whose typed
  points-to is not available without a `sorry`.
- **The parameters** (`hooksParams P`): `Meta` in the table, a hook's bucket, its `confState`
  key not one of the hook's own keys (the consistent index's), and room for a third put.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode backend

/-- `schema.MetaConfStateName`'s bytes. -/
def schema.confStateKeyBytes : GoString := go!"confState"

namespace storage

/-! ## The parameters and the indexer's save -/

/-- The backend's parameters let the hook save the `confState`: `Meta` in the table and a
hook's bucket, its `confState` key not a hook's own key, and room for one put after the
indexer's two. -/
def hooksParams (P : BParams) : Prop :=
  P.has mvcc.metaBI ∧ P.HB mvcc.metaBI.name = true ∧
    P.HK mvcc.metaBI.name schema.confStateKeyBytes = false ∧ 3 ≤ P.hookMax

/-- A put of the `confState` key in the state `st` may repeat a key only where the backend
allows it. -/
def csDupOk (st : BSess) : Prop :=
  schema.confStateKeyBytes ∉ (bkOf st.W.bks mvcc.metaBI.id).map Prod.fst ∨
    wbDupOk st mvcc.metaBI.id

/-- **What the indexer's save leaves** of the hook's run from `st`: a hook step with one
operation of room left, and a `confState` put allowed. -/
def hookSaveStep (P : BParams) (st st' : BSess) : Prop :=
  st'.C = st.C ∧ st'.R = st.R ∧ sData P st'.S = sData P st.S ∧
  (∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st'.W.bks i = bkOf st.W.bks i) ∧
  sint.Z st.pend ≤ sint.Z st'.pend ∧ sint.Z st'.pend + 1 ≤ sint.Z st.pend + P.hookMax ∧
  sint.Z st.ndel ≤ sint.Z st'.ndel ∧ st'.tx = st.tx ∧ st'.cnt = st.cnt ∧ csDupOk st'

theorem hookStep_of_save {P : BParams} {st st' : BSess} (h : hookSaveStep P st st') :
    hookStep P st st' := by
  obtain ⟨hC, hR, hS, hW, hp1, hp2, hn, htx, hc, -⟩ := h
  exact ⟨hC, hR, hS, hW, hp1, by omega, hn, htx, hc⟩

/-- A put in a hook's bucket leaves the writer's contents off the hook's buckets. -/
theorem sData_put_HB {P : BParams} {S : Data} {n k v : GoString} (h : P.HB n = true) :
    sData P (S.insert n ((bktOf S n).insert k v)) = sData P S := by
  unfold sData
  apply vData_eq_of_agree
  rw [vOf_emptyR, vOf_emptyR]
  intro n' hn' k'
  rw [dget_put]
  have : ¬ (n = n' ∧ k = k') := fun ⟨h1, _⟩ => by subst h1; rw [h] at hn'; cases hn'
  simp [this]

/-- The `confState` put after the indexer's save completes a hook step. -/
theorem hookStep_save_put {P : BParams} (hPw : P.Wf) (hP : hooksParams P) {st st' : BSess}
    {vb : GoString} (hpre : hookPre P st) (h : hookSaveStep P st st') :
    hookStep P st (st'.put mvcc.metaBI schema.confStateKeyBytes vb false) := by
  obtain ⟨hC, hR, hS, hW, hp1, hp2, hn, htx, hc, -⟩ := h
  have h58 := hpre.2.1
  have hpz' : sint.Z (st'.pend + W64 1) = sint.Z st'.pend + 1 := by word
  refine ⟨hC, hR, ?_, ?_, ?_, ?_, hn, htx, hc⟩
  · show sData P (st'.S.insert mvcc.metaBI.name
      ((bktOf st'.S mvcc.metaBI.name).insert schema.confStateKeyBytes vb)) = _
    rw [sData_put_HB hP.2.1]; exact hS
  · intro n i hni hHB
    show bkOf (wbAdd st'.W.bks mvcc.metaBI.id (schema.confStateKeyBytes, vb)) i = _
    rw [bkOf_wbAdd]
    split
    · rename_i he
      subst he
      have : n = mvcc.metaBI.name := hPw.1 _ _ _ hni hP.1
      subst this
      rw [hP.2.1] at hHB; cases hHB
    · exact hW n i hni hHB
  · show sint.Z st.pend ≤ sint.Z (st'.pend + W64 1)
    rw [hpz']; omega
  · show sint.Z (st'.pend + W64 1) ≤ _
    rw [hpz']; omega

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&bh.<f>` -/
abbrev hF (f : GoString) (bh : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.BackendHooks f bh

end fields

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **The indexer's save** in the hook's contract (`hooksSpec`'s shape), leaving room for the
`confState` put (`hookSaveStep`). -/
def saveSpec (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (ix : GoInterfaceOk) :
    IProp GF :=
  iprop(□ ∀ st : BSess,
    {{ batchLocked γ P b st ∗ Pk ∗ ⌜hookPre P st⌝ }}
      (App (Val #(methods ix.ty go!"UnsafeSave" ix.v))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t)))
    {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ ⌜hookSaveStep P st st'⌝ }})

instance saveSpec_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (ix : GoInterfaceOk) : Persistent (saveSpec γ P Pk b t ix) := by
  unfold saveSpec; infer_instance

/-- What `confStateLock` guards: the `confState` pointer and its dirty flag. -/
def csInv (bh : Loc) : IProp GF :=
  iprop(∃ (cs : Loc) (d : Bool), hF go!"confState" bh ↦ cs ∗ hF go!"confStateDirty" bh ↦ d)

/-- **The server's backend hooks** at `bh`: the indexer `ix` and the logger `lg` read-only,
`confStateLock` guarding `csInv` (persistent). -/
def isBackendHooks (bh : Loc) (ix : GoInterfaceOk) (lg : Loc) : IProp GF :=
  iprop(hF go!"indexer" bh ↦□ GoInterface.ok ix ∗ hF go!"lg" bh ↦□ lg ∗
    sync.isMutex (hF go!"confStateLock" bh) (csInv bh))

instance isBackendHooks_persistent (bh : Loc) (ix : GoInterfaceOk) (lg : Loc) :
    Persistent (isBackendHooks (GF := GF) bh ix lg) := by
  unfold isBackendHooks; infer_instance

/-- The hooks as the backend's `Hooks` interface value. -/
abbrev hooksIface (bh : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty) #bh

end defs

end storage
end EtcdGrove
end Perennial
