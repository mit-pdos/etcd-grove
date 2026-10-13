/-
The consistent index over the real backend (2026-10-13, unit 7). Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The consistent index over the real backend (unit 7)".

The consistent index's pre-commit hook (`cindex`'s `UnsafeSave`, through
`schema.UnsafeUpdateConsistentIndex`) is proved against an abstract batch transaction
(`metaWriter tx TM PTi PTt`, `InvCindex.lean`). Here that contract is derived from the real
backend's (`InvBackend.lean`), for a run of the pre-commit hook:

- **The hook's own keys** (`ciKeys P`): the backend's parameters make the consistent index's
  two keys in `Meta` the hook's own (`P.HK`, in a hook's bucket). Their values in the writer's
  contents are a ghost variable, half the batch lock's and half the client's (`hkOwn`): the
  server's batch-lock resource holds it (`metaTM γB P mm`: the client's half at contents whose
  meta keys are `mm`), so the stored meta keys are the protocol's `mm` (`InvApply.lean`'s
  `batchLockInv`) at every commit, whatever other sessions did in between.
- **A hook's run** (`hookTM γ P b st0 γi γt`): the batch lock held from the hook's state `st0`
  (`hookPre`: the hook's window, room for two puts, and every write-buffer bucket empty or with an
  empty read-buffer bucket), with the client's half, and the puts made so far (one token each,
  `γi` for the index, `γt` for the term: at most two puts, `P.hookMax ≥ 2`). A put may repeat a
  key of an earlier commit's hook (the backend's relaxed premise, `wbDupOk`), never one of this
  run.
- **The reads** of the batch transaction (the `verify` check's `UnsafeReadConsistentIndex`)
  read the writer's contents; their slices are bbolt's, readable while the lock is held in the
  same bbolt transaction (`metaValsA` with `Acc := hookTM`).

`ci_hook_backend` is the hook's triple in `hookFnSpec`'s shape for `ci.UnsafeSave`, the server's
batch-lock resource `batchLockInv γA (metaTM γB P)` as the hooks' resource; `ci_hookFnSpec` the
`hookFnSpec` of any function that runs `ci.UnsafeSave` on its argument. The reads of `ReadTx`
(`isMetaBackend`) stay a premise: they happen only while the index is 0, at the backend's start
(`NewConsistentIndex`, `SetBackend`), and the readers' view promises nothing of the hook's
buckets.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApply
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeSave
public import Perennial.Ghost.Token
public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage backend

/-! ## The meta keys in bbolt's data -/

/-- A meta key's stored value for `x`: absent for 0, else its big-endian encoding. -/
def encMeta (x : w64) : Option GoString := if x = W64 0 then none else some (u64Be x)

/-- bbolt's data holds the meta keys `m`. -/
def metaIs (S : Data) (m : MetaCI) : Prop :=
  dget S schema.metaName schema.ciKeyBytes = encMeta m.1 ∧
    dget S schema.metaName schema.termKeyBytes = encMeta m.2

/-- The backend's parameters make the consistent index's two keys in `Meta` the hook's own
(`Meta` in the table, a hook's bucket, both keys `HK`), with room for the hook's two puts. -/
def ciKeys (P : BParams) : Prop :=
  P.has mvcc.metaBI ∧ P.HB schema.metaName = true ∧ 2 ≤ P.hookMax ∧
    P.HK schema.metaName schema.ciKeyBytes = true ∧ P.HK schema.metaName schema.termKeyBytes = true

/-- A real instance of the store makes them so (its table having `Meta`, its hook's bound at
least 2). -/
theorem ciKeys_of (d : mvcc.KBReal) (hm : d.BT.lookup mvcc.metaBI.name = some mvcc.metaBI.id)
    (hh : 2 ≤ d.hookMax) : ciKeys d.P :=
  ⟨hm, by simp only [mvcc.KBReal.P]; decide, hh, by simp only [mvcc.KBReal.P]; decide,
    by simp only [mvcc.KBReal.P]; decide⟩

theorem ci_ne_term : schema.ciKeyBytes ≠ schema.termKeyBytes := by decide

theorem ciKeys_hk {P : BParams} (hP : ciKeys P) {k : GoString}
    (hk : k = schema.ciKeyBytes ∨ k = schema.termKeyBytes) : P.hk schema.metaName k = true := by
  unfold BParams.hk
  rcases hk with rfl | rfl
  · rw [hP.2.1, hP.2.2.2.1]
  · rw [hP.2.1, hP.2.2.2.2]

/-- The hook's own keys determine the meta keys. -/
theorem metaIs_of_hkData {P : BParams} (hP : ciKeys P) {S S' : Data} {m : MetaCI}
    (h : hkData P S = hkData P S') (hm : metaIs S m) : metaIs S' m := by
  have hl := fun k => congrArg (fun d => GMap.lookup d (schema.metaName, k)) h
  have h1 := hl schema.ciKeyBytes
  have h2 := hl schema.termKeyBytes
  simp only [hkData_lookup, ciKeys_hk hP (Or.inl rfl), ciKeys_hk hP (Or.inr rfl),
    ↓reduceIte] at h1 h2
  exact ⟨h1 ▸ hm.1, h2 ▸ hm.2⟩

/-! ## A run of the pre-commit hook -/

/-- The batch lock's state `st` after a run of the hook from `st0` has put the index (`ui`) and
the term (`ut`), each at most once: only the writer's contents and the write buffer's `Meta`
bucket changed, one pending operation per put, and the `Meta` bucket of the write buffer holds
only this run's puts unless its read-buffer bucket is empty. -/
def hookRun (P : BParams) (st0 st : BSess) (ui ut : Bool) : Prop :=
  st.C = st0.C ∧ st.R = st0.R ∧ sData P st.S = sData P st0.S ∧
  (∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = bkOf st0.W.bks i) ∧
  sint.Z st.pend = sint.Z st0.pend + (if ui then 1 else 0) + (if ut then 1 else 0) ∧
  st.ndel = st0.ndel ∧ st.tx = st0.tx ∧ st.cnt = st0.cnt ∧
  (bkOf st0.R.bks mvcc.metaBI.id = [] ∨ ∀ e ∈ bkOf st.W.bks mvcc.metaBI.id,
    (e.1 = schema.ciKeyBytes ∧ ui = true) ∨ (e.1 = schema.termKeyBytes ∧ ut = true))

theorem hookRun_refl (P : BParams) (st0 : BSess) (hpre : hookPre P st0) :
    hookRun P st0 st0 false false := by
  refine ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, by simp, rfl, rfl, rfl, ?_⟩
  rcases hpre.2.2 mvcc.metaBI.id with h | h
  · right; rw [h]; simp
  · left; exact h

/-- A run of the hook is a hook step (at most two puts). -/
theorem hookStep_of_run {P : BParams} (hP : ciKeys P) {st0 st : BSess} {ui ut : Bool}
    (h : hookRun P st0 st ui ut) : hookStep P st0 st := by
  obtain ⟨hC, hR, hS, hW, hp, hn, htx, hc, -⟩ := h
  have h2 := hP.2.2.1
  refine ⟨hC, hR, hS, hW, ?_, ?_, by rw [hn]; exact Int.le_refl _, htx, hc⟩
  · rw [hp]; split <;> split <;> omega
  · rw [hp]; split <;> split <;> omega

/-- A put of one of the consistent index's keys, not put before in this run, may repeat a key
of the write buffer only where the backend allows it. -/
theorem hookRun_dup {P : BParams} {st0 st : BSess} {ui ut : Bool} {kb : GoString}
    (hpre : hookPre P st0) (h : hookRun P st0 st ui ut)
    (hk : (kb = schema.ciKeyBytes ∧ ui = false) ∨ (kb = schema.termKeyBytes ∧ ut = false)) :
    kb ∉ (bkOf st.W.bks mvcc.metaBI.id).map Prod.fst ∨ wbDupOk st mvcc.metaBI.id := by
  obtain ⟨-, hR, -, -, -, -, -, hc, hlast⟩ := h
  rcases hlast with h0 | hall
  · right; right
    refine ⟨?_, by rw [hR]; exact h0⟩
    rw [hc]; exact hpre.1
  · left
    intro hm
    obtain ⟨e, he, hek⟩ := List.mem_map.1 hm
    rcases hall e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h4] at h2; cases h2
      · rw [← hek, h1] at h3; exact ci_ne_term h3
    · rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [← hek, h1] at h3; exact ci_ne_term h3.symm
      · rw [h4] at h2; cases h2

/-- A put of one of the consistent index's keys, not put before in this run, continues it. -/
theorem hookRun_put {P : BParams} (hPw : P.Wf) (hP : ciKeys P) {st0 st : BSess} {ui ut : Bool}
    {kb vb : GoString} (h : hookRun P st0 st ui ut) (hpend : sint.Z st.pend + 1 < 2 ^ 58)
    (hk : (kb = schema.ciKeyBytes ∧ ui = false) ∨ (kb = schema.termKeyBytes ∧ ut = false)) :
    hookRun P st0 (st.put mvcc.metaBI kb vb false) (ui || decide (kb = schema.ciKeyBytes))
      (ut || decide (kb = schema.termKeyBytes)) := by
  obtain ⟨hC, hR, hS, hW, hp, hn, htx, hc, hlast⟩ := h
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  refine ⟨hC, hR, ?_, ?_, ?_, hn, htx, hc, ?_⟩
  · show sData P (st.S.insert mvcc.metaBI.name ((bktOf st.S mvcc.metaBI.name).insert kb vb)) = _
    rw [storage.sData_put_HB (n := mvcc.metaBI.name) hP.2.1]; exact hS
  · intro n i hni hHB
    show bkOf (wbAdd st.W.bks mvcc.metaBI.id (kb, vb)) i = _
    rw [bkOf_wbAdd]
    split
    · rename_i he
      subst he
      have : n = mvcc.metaBI.name := hPw.1 _ _ _ hni hP.1
      subst this
      have h1 : P.HB mvcc.metaBI.name = true := hP.2.1
      rw [h1] at hHB; cases hHB
    · exact hW n i hni hHB
  · show sint.Z (st.pend + W64 1) = _
    rw [hpz, hp]
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases ut <;> simp [ci_ne_term] <;> omega
    · cases ui <;> simp [ci_ne_term.symm] <;> omega
  · rcases hlast with h0 | hall
    · left; exact h0
    · right
      intro e he
      have he' : e ∈ bkOf st.W.bks mvcc.metaBI.id ++ [(kb, vb)] := by
        have : bkOf (st.put mvcc.metaBI kb vb false).W.bks mvcc.metaBI.id =
            bkOf st.W.bks mvcc.metaBI.id ++ [(kb, vb)] := by
          show bkOf (wbAdd st.W.bks mvcc.metaBI.id (kb, vb)) mvcc.metaBI.id = _
          rw [bkOf_wbAdd]; simp
        rw [← this]; exact he
      rcases List.mem_append.1 he' with he1 | he1
      · rcases hall e he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, by rw [h2]⟩
        · right; exact ⟨h1, by rw [h2]⟩
      · rw [List.mem_singleton] at he1
        subst he1
        rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · left; exact ⟨rfl, by simp⟩
        · right; exact ⟨rfl, by simp⟩

/-- The meta keys after a put of the index. -/
theorem metaIs_put_ci {S : Data} {m : MetaCI} {x : w64} (h : metaIs S m) (hx : x ≠ W64 0) :
    metaIs (S.insert schema.metaName ((bktOf S schema.metaName).insert schema.ciKeyBytes (u64Be x)))
      (x, m.2) := by
  unfold metaIs encMeta at *
  constructor
  · rw [dget_put]; dsimp only; rw [if_pos ⟨rfl, rfl⟩, if_neg hx]
  · rw [dget_put]; dsimp only; rw [if_neg (fun h' => ci_ne_term h'.2)]
    exact h.2

/-- The meta keys after a put of the term. -/
theorem metaIs_put_term {S : Data} {m : MetaCI} {x : w64} (h : metaIs S m) (hx : x ≠ W64 0) :
    metaIs (S.insert schema.metaName ((bktOf S schema.metaName).insert schema.termKeyBytes (u64Be x)))
      (m.1, x) := by
  unfold metaIs encMeta at *
  constructor
  · rw [dget_put]; dsimp only; rw [if_neg (fun h' => ci_ne_term h'.2.symm)]
    exact h.1
  · rw [dget_put]; dsimp only; rw [if_pos ⟨rfl, rfl⟩, if_neg hx]

/-- The meta keys after `metaAfterSave` are the mirror's: its index part is the protocol's. -/
theorem metaAfterSave_fst (m : MetaCI) (k t : w64) :
    (metaAfterSave m k t).1 = if k = W64 0 then m.1 else k := by
  unfold metaAfterSave
  by_cases h : k = W64 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The batch transaction `t` as an interface value. -/
abbrev btIface (t : Loc) : GoInterfaceOk := ⟨go.GoType.PointerType batchTxBuffered.ty, #t⟩

/-- The server's meta-keys resource over the real backend: the client's half of the hook's own
keys, at contents whose meta keys are `m`. -/
def metaTM (γ : BNames) (P : BParams) (m : MetaCI) : IProp GF :=
  iprop(∃ S : Data, hkOwn γ (hkData P S) ∗ ⌜metaIs S m⌝)

instance metaTM_timeless (γ : BNames) (P : BParams) (m : MetaCI) :
    Timeless (metaTM (GF := GF) γ P m) := by
  unfold metaTM; infer_instance

/-- The meta-keys resource agrees with the batch lock's state. -/
theorem metaTM_agree (γ : BNames) {P : BParams} (hP : ciKeys P) (b : Loc) (st : BSess)
    (m : MetaCI) :
    batchLocked (GF := GF) γ P b st ∗ metaTM γ P m ⊢
      batchLocked γ P b st ∗ hkOwn γ (hkData P st.S) ∗ ⌜metaIs st.S m⌝ := by
  unfold metaTM
  iintro ⟨Hl, %S, Hk, %Hm⟩
  icases batchLocked_hk γ P b st _ $$ [$Hl $Hk] with ⟨Hl, Hk, %Heq⟩
  rw [Heq]
  iframe Hl Hk
  ipureintro
  exact metaIs_of_hkData hP Heq Hm

/-- A run of the hook from `st0`: the batch lock held at `st` with the client's half of the
hook's own keys, the meta keys `m`, the tokens of the keys put so far. -/
def hookTM (γ : BNames) (P : BParams) (b : Loc) (st0 : BSess) (γi γt : GName) (m : MetaCI) :
    IProp GF :=
  iprop(∃ (st : BSess) (ui ut : Bool), batchLocked γ P b st ∗ hkOwn γ (hkData P st.S) ∗
    (if ui then token γi else iprop(True)) ∗ (if ut then token γt else iprop(True)) ∗
    ⌜metaIs st.S m ∧ hookRun P st0 st ui ut⌝)

end defs

/-! ## The batch transaction's meta-keys contract, of the real backend -/

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem hkPut_hk {γ : BNames} {P : BParams} {n k : GoString} {S : Data} (h : P.hk n k = true) :
    hkPut (GF := GF) γ P n k S = hkOwn γ (hkData P S) := by
  unfold hkPut; rw [h]; rfl

/-- The batch transaction's put of the index, in a run of the hook (its token spent). -/
theorem hookTM_put_ci (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st0 : BSess) (γi γt : GName)
    (hP : ciKeys P) (hpre : hookPre P st0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      metaPutSpec (btIface t) schema.ciKeyBytes (fun m x => (x, m.2))
        (hookTM γ P b st0 γi γt) (token γi) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  unfold metaPutSpec
  iintro %bk %key %val %m %x %Φ !> ⟨#HM, #Hkey, Hval, HTM, HPT, %Hx⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  unfold hookTM
  icases HTM with ⟨%st, %ui, %ut, Hl, Hhk, Hti, Htt, %Hm⟩
  obtain ⟨hm, hr⟩ := Hm
  cases ui
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    iapply token_exclusive $$ Hti HPT
  simp only [Bool.false_eq_true, ↓reduceIte]
  ihave #Hbk := mvcc.meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
  imod ownSlice_persist $$ Hval with #Hval
  have hpend : sint.Z st.pend + 1 < 2 ^ 58 := by
    have h1 := hr.2.2.2.2.1
    have h2 := hpre.2.1
    have h3 := hP.2.2.1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    revert h1
    split <;> intro h1 <;> omega
  have hSB : P.SB mvcc.metaBI.name = true → ∀ kc vc,
      (bktOf st.S mvcc.metaBI.name).lookup kc = some vc → strLt kc schema.ciKeyBytes := by
    intro h
    have := HPw.2.2.2.2 _ h
    rw [show mvcc.metaBI.name = schema.metaName from rfl, hP.2.1] at this
    cases this
  have hhk : P.hk mvcc.metaBI.name schema.ciKeyBytes = true := ciKeys_hk hP (Or.inl rfl)
  have hhk' : P.hk schema.metaName schema.ciKeyBytes = true := ciKeys_hk hP (Or.inl rfl)
  wp_apply (hPut γ P W Pk b t st bk mvcc.metaBI key val schema.ciKeyBytes (u64Be x) hP.1
      (by decide) (by decide) (hookRun_dup hpre hr (Or.inl ⟨rfl, rfl⟩)) hpend hSB)
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hval Hhk] as ⟨Hl, Hhk⟩
  · iframe #
    rw [hkPut_hk hhk]
    iexact Hhk
  iapply HΦ
  simp only [hkPut, hhk', ↓reduceIte]
  iexists (st.put mvcc.metaBI schema.ciKeyBytes (u64Be x) false), true, ut
  rw [show (st.put mvcc.metaBI schema.ciKeyBytes (u64Be x) false).S =
    st.S.insert schema.metaName ((bktOf st.S schema.metaName).insert schema.ciKeyBytes (u64Be x))
    from rfl]
  simp only [eq_self_iff_true, ↓reduceIte]
  iframe Hl Hhk HPT Htt
  ipureintro
  refine ⟨metaIs_put_ci hm Hx, ?_⟩
  have := hookRun_put (vb := u64Be x) HPw hP hr hpend (Or.inl ⟨rfl, rfl⟩)
  simpa [ci_ne_term] using this

/-- The batch transaction's put of the term, in a run of the hook (its token spent). -/
theorem hookTM_put_term (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st0 : BSess) (γi γt : GName)
    (hP : ciKeys P) (hpre : hookPre P st0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      metaPutSpec (btIface t) schema.termKeyBytes (fun m x => (m.1, x))
        (hookTM γ P b st0 γi γt) (token γt) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  unfold metaPutSpec
  iintro %bk %key %val %m %x %Φ !> ⟨#HM, #Hkey, Hval, HTM, HPT, %Hx⟩ HΦ
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  unfold hookTM
  icases HTM with ⟨%st, %ui, %ut, Hl, Hhk, Hti, Htt, %Hm⟩
  obtain ⟨hm, hr⟩ := Hm
  cases ut
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    iapply token_exclusive $$ Htt HPT
  simp only [Bool.false_eq_true, ↓reduceIte]
  ihave #Hbk := mvcc.meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
  imod ownSlice_persist $$ Hval with #Hval
  have hpend : sint.Z st.pend + 1 < 2 ^ 58 := by
    have h1 := hr.2.2.2.2.1
    have h2 := hpre.2.1
    have h3 := hP.2.2.1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    revert h1
    split <;> intro h1 <;> omega
  have hSB : P.SB mvcc.metaBI.name = true → ∀ kc vc,
      (bktOf st.S mvcc.metaBI.name).lookup kc = some vc → strLt kc schema.termKeyBytes := by
    intro h
    have := HPw.2.2.2.2 _ h
    rw [show mvcc.metaBI.name = schema.metaName from rfl, hP.2.1] at this
    cases this
  have hhk : P.hk mvcc.metaBI.name schema.termKeyBytes = true := ciKeys_hk hP (Or.inr rfl)
  have hhk' : P.hk schema.metaName schema.termKeyBytes = true := ciKeys_hk hP (Or.inr rfl)
  wp_apply (hPut γ P W Pk b t st bk mvcc.metaBI key val schema.termKeyBytes (u64Be x) hP.1
      (by decide) (by decide) (hookRun_dup hpre hr (Or.inr ⟨rfl, rfl⟩)) hpend hSB)
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hval Hhk] as ⟨Hl, Hhk⟩
  · iframe #
    rw [hkPut_hk hhk]
    iexact Hhk
  iapply HΦ
  simp only [hkPut, hhk', ↓reduceIte]
  iexists (st.put mvcc.metaBI schema.termKeyBytes (u64Be x) false), ui, true
  rw [show (st.put mvcc.metaBI schema.termKeyBytes (u64Be x) false).S =
    st.S.insert schema.metaName ((bktOf st.S schema.metaName).insert schema.termKeyBytes (u64Be x))
    from rfl]
  simp only [eq_self_iff_true, ↓reduceIte]
  iframe Hl Hhk HPT Hti
  ipureintro
  refine ⟨metaIs_put_term hm Hx, ?_⟩
  have := hookRun_put (vb := u64Be x) HPw hP hr hpend (Or.inr ⟨rfl, rfl⟩)
  simpa [ci_ne_term.symm] using this

/-- The values a read of a meta key holding `x` returns, readable as `Rd` says. -/
def metaRdVals (Rd : GoSlice → GoString → IProp GF) (vs : GoSlice) (x : w64) : IProp GF :=
  if x = W64 0 then iprop(vs ↦*□ ([] : List GoSlice))
  else iprop(∃ s : GoSlice, vs ↦*□ [s] ∗ □ Rd s (u64Be x))

theorem keyVals_enc {Rd : GoSlice → GoString → IProp GF} {ks vs : GoSlice} {B : BktData}
    {k : GoString} {x : w64} (h : B.lookup k = encMeta x) :
    mvcc.keyVals Rd ks vs B k ⊢ metaRdVals Rd vs x := by
  unfold mvcc.keyVals metaRdVals
  unfold encMeta at h
  by_cases hx : x = W64 0
  · rw [if_pos hx] at h
    rw [if_pos hx]
    simp only [h]
    iintro ⟨-, #H⟩
    iexact H
  · rw [if_neg hx] at h
    rw [if_neg hx]
    simp only [h]
    iintro ⟨%ksl, %vsl, -, -, #Hv, #Hr⟩
    iexists vsl
    iframe Hv Hr

/-- The batch transaction's read of a meta key, in a run of the hook: the writer's contents,
the value readable while the run's resource is held (bbolt's slices, valid while the lock is
held in the same transaction). -/
theorem hookTM_range (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st0 : BSess) (γi γt : GName)
    (kn : GoString) (sel : MetaCI → w64)
    (hsel : ∀ (S : Data) (m : MetaCI), metaIs S m → dget S schema.metaName kn = encMeta (sel m)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      metaRangeSpec (btIface t) kn sel ⊤ (hookTM γ P b st0 γi γt) (hookTM γ P b st0 γi γt) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  unfold metaRangeSpec
  iintro %bk %key %Φ #HM #Hkey HAU
  unfold readAU
  imod HAU with ⟨%m, HTM, Hclose⟩
  unfold hookTM
  icases HTM with ⟨%st, %ui, %ut, Hl, Hhk, Hti, Htt, %Hm⟩
  obtain ⟨hm, hr⟩ := Hm
  ihave #Hbk := mvcc.meta_isBucket hID hName hSafe bk $$ [$Hsch $HM]
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b t st bk mvcc.metaBI key slice.nil kn [] DFrac.discard DFrac.discard
      (W64 0) (by simp))
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hnil] as %ks %vs ⟨Hl, -, -, Hout, #Hcap⟩
  irevert Hout
  rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts]
  iintro Hout
  imod mvcc.kvsOutRd_keyVals st.tx ks vs _ kn $$ Hout with #Hkv
  have hv : (bktOf st.S schema.metaName).lookup kn = encMeta (sel m) := by
    rw [← dget_eq_bktOf]; exact hsel st.S m hm
  ihave #Hkv2 := keyVals_enc hv $$ Hkv
  imod Hclose $$ [Hl Hhk Hti Htt] with HΨ
  · iexists st, ui, ut
    iframe
    ipureintro; exact ⟨hm, hr⟩
  imodintro
  iapply HΨ
  unfold metaValsA metaRdVals
  by_cases h0 : sel m = W64 0
  · simp only [h0, ↓reduceIte]
    iexact Hkv2
  · simp only [h0, ↓reduceIte]
    icases Hkv2 with ⟨%vsl, #Hvs, #Hrd⟩
    iexists vsl
    iframe Hvs
    iintro !> HTM
    icases HTM with ⟨%st', %ui', %ut', Hl', Hhk', Hti', Htt', %Hm'⟩
    have htx : st'.tx = st.tx := by rw [Hm'.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]
    ihave Hc := Hcap $$ %vsl %(u64Be (sel m)) %st' Hrd Hl'
    ihave Hc2 := Hc $$ []
    · ipureintro; exact htx
    icases Hc2 with ⟨%dq', Hsl, Hcl⟩
    iexists dq'
    iframe Hsl
    iintro Hsl
    ihave Hl' := Hcl $$ Hsl
    iexists st', ui', ut'
    iframe
    ipureintro; exact Hm'

/-- The batch transaction in a run of the hook is a `metaWriter` of the run's resource. -/
theorem hookTM_writer (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st0 : BSess) (γi γt : GName)
    (hP : ciKeys P) (hpre : hookPre P st0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      metaWriter (btIface t) (hookTM γ P b st0 γi γt) (token γi) (token γt) := by
  iintro #H
  unfold metaWriter metaReader
  isplitr
  · isplitr
    · iintro !>
      iapply hookTM_range hUR hID hName hSafe γ P W Pk b t st0 γi γt schema.ciKeyBytes Prod.fst
        (fun _ _ h => h.1) $$ H
    · iintro !>
      iapply hookTM_range hUR hID hName hSafe γ P W Pk b t st0 γi γt schema.termKeyBytes Prod.snd
        (fun _ _ h => h.2) $$ H
  isplitr
  · iintro !>
    iapply hookTM_put_ci hPut hID hName hSafe γ P W Pk b t st0 γi γt hP hpre $$ H
  · iintro !>
    iapply hookTM_put_term hPut hID hName hSafe γ P W Pk b t st0 γi γt hP hpre $$ H

end proofs

/-! ## The pre-commit hook: the consistent index's `UnsafeSave` over the real backend -/

section texan
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A Texan triple from its form without the later on the continuation, for an expression that
takes a step (the continuation is framed over it). -/
theorem texan_of_strong (e : Expr) (C P Q : IProp GF) (v : val) [Persistent C]
    (he : Iris.ProgramLogic.ToVal.toVal e = none)
    (h : C ⊢ ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ Φ }}) :
    C ⊢ □ ∀ Φ, P -∗ ▷ (Q -∗ Φ v) -∗ WP e {{ Φ }} := by
  iintro #HC !> %Φ HP HΦ
  iapply (wp_wand (Φ := fun w => iprop((Q -∗ Φ v) ∗ (⌜w = v⌝ ∗ Q)))) $$ [HP HΦ]
  · iapply (wp_frame_step_l' he Std.LawfulSet.subset_refl)
    iframe HΦ
    iapply h $$ HC HP
    iintro HQ
    iframe HQ
    ipureintro; rfl
  · iintro %w ⟨HΦ, %Hw, HQ⟩
    subst Hw
    iapply HΦ $$ HQ

end texan

section hook
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
variable [cindex_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- **The consistent index's pre-commit hook over the real backend**, with the run's facts
(`hookRun`: what the server's hook needs for its `confState` put): `ci.UnsafeSave(t)`, by the
holder of the batch lock in the hook's window, with the server's batch-lock resource
(`batchLockInv`: the stored index's mirror, the meta keys as the client's half of the hook's own
keys, the lock's token), is a hook step that gives the resource back: the meta keys now hold
what the commit persists, the consistent index read at the commit (`commit_save_au`: no entry
above it has writes in the buffer, every entry at or below it has been processed). -/
theorem ci_hook_backend_run (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc)
    (hP : ciKeys P) (st : BSess) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ isCI ci γA.ci ∗ inv applyN (consInv γA) ⊢
      {{ batchLocked γ P b st ∗ batchLockInv γA (metaTM γ P) ∗ ⌜hookPre P st⌝ }}
        (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeSave"))
          (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
      {{ RET #(); ∃ (st' : BSess) (ui ut : Bool), batchLocked γ P b st' ∗
          batchLockInv γA (metaTM γ P) ∗ ⌜hookRun P st st' ui ut⌝ }} := by
  apply texan_of_strong _ _ _ _ _ (by rfl)
  iintro ⟨#Hpkg, #Hsch, #Hcpkg, #Hb, #Ht, #Hci, #Hinv⟩ %Φ ⟨Hl, Hbl, %Hpre⟩ HΦ
  iunfold batchLockInv at Hbl
  icases Hbl with ⟨%mm, Hmt, HTM, Hpend⟩
  icases metaTM_agree γ hP b st mm $$ [$Hl $HTM] with ⟨Hl, Hhk, %Hmm⟩
  imod token_alloc with ⟨%γi, Hti⟩
  imod token_alloc with ⟨%γt, Htt⟩
  ihave #Hw := hookTM_writer hPut hUR hID hName hSafe γ P W Pk b t st γi γt hP Hpre $$
    [$Hpkg $Hsch $Hb $Ht]
  ihave HTM : hookTM γ P b st γi γt mm $$ [Hl Hhk]
  · unfold hookTM
    iexists st, false, false
    iframe Hl Hhk
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr; · itrivial
    isplitr; · itrivial
    ipureintro; exact ⟨Hmm, hookRun_refl P st Hpre⟩
  iapply (hSave ci γA.ci (btIface t) (hookTM γ P b st γi γt) (token γi) (token γt) mm) $$
    [HTM Hti Htt] [Hmt Hpend HΦ]
  · iframe Hcpkg Hci Hw HTM Hti Htt
  iapply (commit_save_au γA mm) $$ Hinv Hmt Hpend
  iintro %k %s %Hmono %Hok Hmt Hpend
  isplitr
  · ipureintro; exact Hmono
  iintro %tm HTM
  unfold hookTM
  icases HTM with ⟨%st', %ui, %ut, Hl, Hhk, -, -, %Hm'⟩
  iapply HΦ
  iexists st', ui, ut
  iframe Hl
  isplitl
  · unfold batchLockInv
    iexists (metaAfterSave mm k tm)
    rw [metaAfterSave_fst]
    iframe Hmt Hpend
    unfold metaTM
    iexists st'.S
    iframe Hhk
    ipureintro; exact Hm'.1
  · ipureintro; exact Hm'.2

/-- **The consistent index's pre-commit hook over the real backend**: `ci.UnsafeSave(t)`, by the
holder of the batch lock in the hook's window, with the server's batch-lock resource
(`batchLockInv`: the stored index's mirror, the meta keys as the client's half of the hook's own
keys, the lock's token), is a hook step that gives the resource back: the meta keys now hold
what the commit persists, the consistent index read at the commit (`commit_save_au`: no entry
above it has writes in the buffer, every entry at or below it has been processed). -/
theorem ci_hook_backend (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc)
    (hP : ciKeys P) (st : BSess) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ isCI ci γA.ci ∗ inv applyN (consInv γA) ⊢
      {{ batchLocked γ P b st ∗ batchLockInv γA (metaTM γ P) ∗ ⌜hookPre P st⌝ }}
        (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeSave"))
          (Val #(interface.mkOk (go.GoType.PointerType batchTxBuffered.ty) #t)))
      {{ RET #(); ∃ st' : BSess, batchLocked γ P b st' ∗ batchLockInv γA (metaTM γ P) ∗
          ⌜hookStep P st st'⌝ }} := by
  iintro #H !> %Φ Hpre HΦ
  iapply (ci_hook_backend_run hSave hPut hUR hID hName hSafe γA ci γ P W Pk b t hP st) $$ H Hpre
  iintro !> ⟨%st', %ui, %ut, Hl, Hbl, %Hr⟩
  iapply HΦ
  iexists st'
  iframe Hl Hbl
  ipureintro; exact hookStep_of_run hP Hr

/-- The `hookFnSpec` of a hook function that runs the consistent index's `UnsafeSave` on the
batch transaction (etcd's `BackendHooks.OnPreCommitUnsafe` does that first; its `confState` part,
and the struct, are not translated: `storage/hooks.go`), the server's batch-lock resource as the
hooks' resource. -/
theorem ci_hookFnSpec (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc)
    (hP : ciKeys P) (f : GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ isCI ci γA.ci ∗ inv applyN (consInv γA) ∗
      □ (∀ (v : val) (Ψ : val → IProp GF),
          WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeSave"))
            (Val v)) {{ Ψ }} -∗
          WP (App (Val #f) (Val v)) {{ Ψ }}) ⊢
      hookFnSpec γ P (batchLockInv γA (metaTM γ P)) b t f := by
  iintro ⟨#Hpkg, #Hsch, #Hcpkg, #Hb, #Ht, #Hci, #Hinv, #Hf⟩
  unfold hookFnSpec
  iintro !> %st %Φ !> Hpre HΦ
  iapply Hf
  iapply (ci_hook_backend hSave hPut hUR hID hName hSafe γA ci γ P W Pk b t hP st) $$
    [] Hpre HΦ
  iframe #

/-- A run of the consistent index's hook leaves what the server's hook's `confState` put needs
(`storage.hookSaveStep`): a third put's room (`hookMax ≥ 3`), and the `confState` key absent
from the write buffer's `Meta` bucket or that bucket free to repeat a key. -/
theorem hookSaveStep_of_run {P : BParams} (hH : storage.hooksParams P) {st0 st : BSess}
    {ui ut : Bool} (hpre : hookPre P st0) (h : hookRun P st0 st ui ut) :
    storage.hookSaveStep P st0 st := by
  obtain ⟨hC, hR, hS, hW, hp, hn, htx, hc, hlast⟩ := h
  have h3 := hH.2.2.2
  refine ⟨hC, hR, hS, hW, ?_, ?_, by rw [hn]; exact Int.le_refl _, htx, hc, ?_⟩
  · rw [hp]; split <;> split <;> omega
  · rw [hp]; split <;> split <;> omega
  · rcases hlast with h0 | hall
    · right; right
      refine ⟨?_, by rw [hR]; exact h0⟩
      rw [hc]; exact hpre.1
    · left
      intro hm
      obtain ⟨e, he, hek⟩ := List.mem_map.1 hm
      rcases hall e he with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hek; exact absurd hek (by decide)
      · rw [h1] at hek; exact absurd hek (by decide)

/-- **The consistent index's save is the server's hook's indexer save** (`storage.saveSpec`):
over the real backend, the server's batch-lock resource the hooks' resource, for parameters
whose hook's own keys are the consistent index's (`ciKeys`) and that let the hook save the
`confState` (`hooksParams`). -/
theorem ci_saveSpec (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γA : ApplyNames) (ci : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc)
    (hP : ciKeys P) (hH : storage.hooksParams P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ isCI ci γA.ci ∗ inv applyN (consInv γA) ⊢
      storage.saveSpec γ P (batchLockInv γA (metaTM γ P)) b t
        ⟨go.GoType.PointerType consistentIndex.ty, #ci⟩ := by
  iintro #H
  unfold storage.saveSpec
  iintro !> %st %Φ !> ⟨Hl, Hbl, %Hpre⟩ HΦ
  iapply (ci_hook_backend_run hSave hPut hUR hID hName hSafe γA ci γ P W Pk b t hP st) $$ H
    [Hl Hbl]
  · iframe Hl Hbl; ipureintro; exact Hpre
  iintro !> ⟨%st', %ui, %ut, Hl, Hbl, %Hr⟩
  iapply HΦ
  iexists st'
  iframe Hl Hbl
  ipureintro; exact hookSaveStep_of_run hH Hpre Hr

end hook

end EtcdGrove
end Perennial
