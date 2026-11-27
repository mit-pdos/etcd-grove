/-
The server's backend hooks (`server/storage/hooks.go`, 2026-10-13, unit 8 of the backend).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The server's backend hook (unit 8)".

`BackendHooks.OnPreCommitUnsafe(tx)` is the backend's pre-commit hook (the backend's `hooksSpec`):
it runs the consistent index's `UnsafeSave(tx)`, then, under `confStateLock`, saves the
`confState` set by the apply thread's `SetConfState` (if dirty) into `Meta`'s key `confState`
(`schema.MustUnsafeSaveConfStateToBackend`, the trust boundary: a put through `tx.UnsafePut`).

- **The indexer's save** (`saveSpec`): the hook's contract of `ix.UnsafeSave(tx)`, with one put
  of room left (`hookSaveStep`: a hook step whose pending count stays below the hook's bound by
  one). The consistent index's save satisfies it
  (`Proof/.../etcdserver/CindexBackend.lean`, `ci_saveSpec`).
- **The hooks' state** (`isBackendHooks bh ix lg`, persistent): the indexer and the logger
  read-only, `confStateLock` guarding `confState` and `confStateDirty`. The struct `confState`
  points to is nil or a read-only conf state of at most `csIdMax` ids (`csOkN`, stage S1b of
  `notes/bbolt-integration-plan.md`, 2026-11-17: what bounds the bytes the save puts):
  `SetConfState` stores a fresh clone (`proto.Clone`) that no one writes afterwards.
- **The parameters** (`hooksParams P`): `Meta` in the table, a hook's bucket, its `confState`
  key not one of the hook's own keys (the consistent index's), and room for a third put.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage
public import Proof.go_etcd_io.raft.v3.InvPb

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
hook's bucket, its `confState` key not a hook's own key, room for one put after the indexer's
three (keepfix (c): the raft-term key's), and (D22, 2026-10-23) `Meta` not a tracked bucket (`RB`). -/
def hooksParams (P : BParams) : Prop :=
  P.has mvcc.metaBI ∧ P.HB mvcc.metaBI.name = true ∧
    P.HK mvcc.metaBI.name schema.confStateKeyBytes = false ∧ 4 ≤ P.hookMax ∧
    P.RB mvcc.metaBI.name = false

/-- **What the indexer's save leaves** of the hook's run from `st`: a hook step with one
operation of room left. -/
def hookSaveStep (P : BParams) (st st' : BSess) : Prop :=
  st'.C = st.C ∧ st'.R = st.R ∧ sData P st'.S = sData P st.S ∧ rbData P st'.S = rbData P st.S ∧
  (∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st'.W.bks i = bkOf st.W.bks i) ∧
  sint.Z st.pend ≤ sint.Z st'.pend ∧ sint.Z st'.pend + 1 ≤ sint.Z st.pend + P.hookMax ∧
  sint.Z st.ndel ≤ sint.Z st'.ndel ∧ st'.tx = st.tx ∧
  (st'.cnt = st.cnt ∧ st'.dl = st.dl ∧ st'.win = st.win ∧ trkKept P st st')

theorem hookStep_of_save {P : BParams} {st st' : BSess} (h : hookSaveStep P st st') :
    hookStep P st st' := by
  obtain ⟨hC, hR, hS, hB, hW, hp1, hp2, hn, htx, hc⟩ := h
  exact ⟨hC, hR, hS, hB, hW, hp1, by omega, hn, htx, hc.1, by rw [hc.2.1], hc.2.2.1, hc.2.2.2⟩

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
  obtain ⟨hC, hR, hS, hB, hW, hp1, hp2, hn, htx, hc⟩ := h
  have h58 := hpre.2.1
  have hpz' : sint.Z (st'.pend + W64 1) = sint.Z st'.pend + 1 := by word
  refine ⟨hC, hR, ?_, ?_, ?_, ?_, ?_, hn, htx, hc.1, by
    show dlR P st'.dl = dlR P st.dl; rw [hc.2.1], hc.2.2.1,
    trkKept_put_other hPw hP.1 hP.2.2.2.2 hc.2.2.2⟩
  · show sData P (st'.S.insert mvcc.metaBI.name
      ((bktOf st'.S mvcc.metaBI.name).insert schema.confStateKeyBytes vb)) = _
    rw [sData_put_HB hP.2.1]; exact hS
  · rw [rbData_put_other _ _ _ _ _ hP.2.2.2.2]; exact hB
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
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&bh.<f>` -/
abbrev hF (f : GoString) (bh : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.BackendHooks f bh

end fields

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **The indexer's save** in the hook's contract (`hooksSpec`'s shape), leaving room for the
`confState` put (`hookSaveStep`). -/
def saveSpec (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (ix : GoInterfaceOk) :
    IProp GF :=
  iprop(□ ∀ (st : BSess) (stop : Bool) (m u : Nat),
    {{ batchLocked γ P b st ∗ Pk ∗ ⌜hookPre P st⌝ ∗ payIn γ st stop m u }}
      (App (Val #(methods ix.ty go!"UnsafeSave" ix.v))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t)))
    {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ payIn γ st stop m u ∗
        ⌜hookSaveStep P st st'⌝ }})

instance saveSpec_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (ix : GoInterfaceOk) : Persistent (saveSpec γ P Pk b t ix) := by
  unfold saveSpec; infer_instance

/-- **The indexer's save serving a commit's request** `X ⇒ Y` (D22 the stored-index window,
2026-10-23; `backend.hooksReq`'s shape): `saveSpec` with a frame the save transforms. -/
def saveReq (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc) (ix : GoInterfaceOk)
    (X Y : IProp GF) : IProp GF :=
  iprop(□ ∀ (st : BSess) (stop : Bool) (m u : Nat),
    {{ batchLocked γ P b st ∗ Pk ∗ X ∗ ⌜hookPre P st⌝ ∗ payIn γ st stop m u }}
      (App (Val #(methods ix.ty go!"UnsafeSave" ix.v))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t)))
    {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ Pk ∗ Y ∗ payIn γ st stop m u ∗
        ⌜hookSaveStep P st st'⌝ }})

instance saveReq_persistent (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (ix : GoInterfaceOk) (X Y : IProp GF) : Persistent (saveReq γ P Pk b t ix X Y) := by
  unfold saveReq; infer_instance

/-- The save with no request. -/
theorem saveReq_of_saveSpec (γ : BNames) (P : BParams) (Pk : IProp GF) (b t : Loc)
    (ix : GoInterfaceOk) :
    saveSpec γ P Pk b t ix ⊢ saveReq γ P Pk b t ix iprop(True) iprop(True) := by
  iintro #Hs
  unfold saveSpec saveReq
  iintro !> %st %stop %m %u %Φ !> ⟨Hl, HPk, -, %Hpre, Hpay⟩ HΦ
  iapply Hs $$ %st %stop %m %u [Hl HPk Hpay]
  · iframe Hl HPk Hpay
    ipureintro; exact Hpre
  iintro !> ⟨%st', Hl, HPk, Hpay, %Hst⟩
  iapply HΦ
  iexists st'
  iframe Hl HPk Hpay
  ipureintro; exact Hst

/-- **The number of ids a conf state lists** (its four lists; stage S1b, 2026-11-17): what bounds
its JSON encoding (`schema.MustUnsafeSaveConfStateToBackend`'s length bound). -/
def csIdCount (c : ConfStateM) : Nat :=
  c.Voters'.length + c.Learners'.length + c.VotersOutgoing'.length + c.LearnersNext'.length

/-- **The hooks' bound on a conf state's ids** (`2 ^ 20`, the server's bound on its voters,
`srvMemOk`; S1b): its JSON, at most `25` bytes an id and `128` more, fits a bbolt entry. -/
def csIdMax : Nat := 2 ^ 20

/-- **A conf state pointer of at most `n` ids**: nil, or read-only for good with at most `n` ids
(persistent). -/
def csOkN (n : Nat) (cs : Loc) : IProp GF :=
  iprop(⌜cs = null⌝ ∨ ∃ c : ConfStateM,
    ownCSM cs DFrac.discard c ∗ ⌜csIdCount c ≤ n⌝)

instance csOkN_persistent (n : Nat) (cs : Loc) : Persistent (csOkN (GF := GF) n cs) := by
  unfold csOkN; infer_instance

/-- What `confStateLock` guards: the `confState` pointer (nil or a conf state of at most
`csIdMax` ids) and its dirty flag. -/
def csInv (bh : Loc) : IProp GF :=
  iprop(∃ (cs : Loc) (d : Bool), hF go!"confState" bh ↦ cs ∗ hF go!"confStateDirty" bh ↦ d ∗
    csOkN csIdMax cs)

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
