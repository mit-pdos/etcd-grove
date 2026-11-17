/-
The tracked buckets' read model (stage A1 of `auth-schema-srv`, `notes/auth-schema-srv-a1-scope.md`,
step A1.1: the pure model). What a reader sees of a tracked bucket (`BParams.RB`; on the server a hook
bucket, outside `vData`), per bucket, through a batch session and its `Unlock`'s window: the session's
kind of each tracked bucket (`RbK`), the readers' contents of a bucket (`rvBkt`), the batch state's
agreement with them (`trkOk`), its preservation by the session's operations, the write-back, the
pre-commit hook (`hookStepT`) and the commit, and the readers' contents at the write-back and the commit
by kind. Go: `notes/auth-schema-srv-a1/zz_a1_trackedwindow_test.go`. Pure; where the kinds live (the
batch lock's ghost state) is A1.2's. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.FkLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## The session's kind of a tracked bucket -/

/-- **What a batch session did to a tracked bucket** since the last `Unlock`: nothing, only puts (a
creation of the bucket leaves the kind: it changes no key), only deletes (of keys, or of the bucket),
or both. A reader in the `Unlock`'s window sees a `put` bucket after the session, a `del` bucket before
it, and a `mix` bucket in neither state (`TestA1TrackedBucketWindow`, M1-M3). -/
inductive RbK
  | idle
  | put
  | del
  | mix
  deriving DecidableEq

/-- The kind after another write of kind `k`. -/
def RbK.join : RbK → RbK → RbK
  | .idle, k => k
  | k, .idle => k
  | .put, .put => .put
  | .del, .del => .del
  | _, _ => .mix

/-- The session's kinds, by bucket name. -/
abbrev TkMap := GoString → RbK

/-- Every bucket untouched (a free batch lock). -/
def tkIdle : TkMap := fun _ => .idle

/-- The kinds after a write of kind `k` to bucket `n`. -/
def tkSet (tk : TkMap) (n : GoString) (k : RbK) : TkMap :=
  fun m => if m = n then (tk n).join k else tk m

theorem tkSet_self (tk : TkMap) (n : GoString) (k : RbK) : tkSet tk n k n = (tk n).join k := by
  simp [tkSet]

theorem tkSet_ne (tk : TkMap) {n m : GoString} (k : RbK) (h : m ≠ n) : tkSet tk n k m = tk m := by
  simp [tkSet, h]

/-! ## The readers' contents of a bucket -/

/-- **The readers' contents of bucket `n`** in the readers' state `rv` (the committed data with the read
buffer over it; an absent bucket reads as empty, `TestA1CreatedBucketUncommitted`). -/
def rvBkt (P : BParams) (rv : RView) (n : GoString) : BktData :=
  ⟨fun k => vOf P rv n k,
   ⟨(vKeys P rv).map Prod.snd, fun k h => List.mem_map.2 ⟨(n, k), vOf_isSome_mem P rv n k h, rfl⟩⟩⟩

theorem rvBkt_lookup (P : BParams) (rv : RView) (n k : GoString) :
    (rvBkt P rv n).lookup k = vOf P rv n k := rfl

/-- Two readers' states that read one bucket alike have one contents of it. -/
theorem rvBkt_ext {P : BParams} {rv rv' : RView} {n : GoString}
    (h : ∀ k, vOf P rv n k = vOf P rv' n k) : rvBkt P rv n = rvBkt P rv' n := by
  apply GMap.ext; intro k; exact h k

/-- A bucket's contents read through `dget` are its `bktOf`. -/
theorem bktOf_ext_dget {B : BktData} {S : Data} {n : GoString} (h : ∀ k, B.lookup k = dget S n k) :
    B = bktOf S n := by
  apply GMap.ext; intro k; rw [h k, dget_eq_bktOf]

/-! ## The batch state's agreement with the readers on the tracked buckets -/

/-- The write buffer has nothing for bucket `n`. -/
def wEmpty (P : BParams) (W : WBuf) (n : GoString) : Prop :=
  ∀ i, P.BT.lookup n = some i → bkOf W.bks i = []

/-- An empty write-buffer bucket adds nothing to a view at that bucket. -/
theorem ovB_wEmpty {P : BParams} {W : WBuf} {n : GoString} (h : wEmpty P W n) (f : VFun) (k : GoString) :
    ovB P.BT W.bks f n k = f n k := by
  unfold ovB
  cases hi : P.BT.lookup n with
  | none => rfl
  | some i => simp [h i hi, lastVal]

/-- What a bucket of kind `k` promises: untouched, the write buffer has nothing for it and the readers
see the writer's contents; put into, the write buffer over the readers' view is the writer's contents;
deleted from, the write buffer has nothing for it (the readers see the session's start); both, nothing. -/
def kOk (P : BParams) (st : BSess) (n : GoString) : RbK → Prop
  | .idle => wEmpty P st.W n ∧ ∀ k, viewOf P st n k = dget st.S n k
  | .put => ∀ k, ovB P.BT st.W.bks (viewOf P st) n k = dget st.S n k
  | .del => wEmpty P st.W n
  | .mix => True

/-- **The batch state agrees with the readers on the tracked buckets, by the session's kinds `tk`**:
each tracked bucket as its kind promises (`kOk`); with nothing pending, the write buffer has nothing for
any tracked bucket; with no delete pending, no tracked bucket was deleted from. -/
def trkOk (P : BParams) (st : BSess) (tk : TkMap) : Prop :=
  (∀ n, P.RB n = true → kOk P st n (tk n)) ∧
  (st.pend = W64 0 → ∀ n, P.RB n = true → wEmpty P st.W n) ∧
  (st.ndel = W64 0 → ∀ n, P.RB n = true → tk n = .idle ∨ tk n = .put)

/-- **The pre-commit hook's run, with the tracked buckets' write buffer kept** (`hookStep` leaves their
contents, `rbData`; this also leaves what the write buffer holds for them, which the server's hook, a
writer of `meta` only, meets). -/
def hookStepT (P : BParams) (st st' : BSess) : Prop :=
  hookStep P st st' ∧
  ∀ n i, P.BT.lookup n = some i → P.RB n = true → bkOf st'.W.bks i = bkOf st.W.bks i

/-! ## Readers' contents from the agreement -/

/-- An untouched tracked bucket: the readers see the writer's contents. -/
theorem rvBkt_idle {P : BParams} {st : BSess} {tk : TkMap} {n : GoString} (h : trkOk P st tk)
    (hn : P.RB n = true) (hk : tk n = .idle) : rvBkt P (st.C, st.R) n = bktOf st.S n := by
  have := h.1 n hn; rw [hk] at this
  exact bktOf_ext_dget fun k => this.2 k

/-- **A free batch lock: the readers see the writer's contents on every tracked bucket.** -/
theorem rvBkt_free {P : BParams} {st : BSess} (h : trkOk P st tkIdle) {n : GoString}
    (hn : P.RB n = true) : rvBkt P (st.C, st.R) n = bktOf st.S n :=
  rvBkt_idle h hn rfl

/-- **The write-back, a bucket put into**: the readers see the writer's contents. -/
theorem rvBkt_wb_put {P : BParams} {st : BSess} {tk : TkMap} {n : GoString} (h : trkOk P st tk)
    (hn : P.RB n = true) (hk : tk n = .put) :
    rvBkt P (st.C, writebackR st.W st.R) n = bktOf st.S n := by
  have := h.1 n hn; rw [hk] at this
  apply bktOf_ext_dget; intro k
  rw [rvBkt_lookup, vOf_writeback]
  exact this k

/-- **The write-back, a bucket untouched or deleted from**: the readers' contents stay. -/
theorem rvBkt_wb_keep {P : BParams} {st : BSess} {tk : TkMap} {n : GoString} (h : trkOk P st tk)
    (hn : P.RB n = true) (hk : tk n = .idle ∨ tk n = .del) :
    rvBkt P (st.C, writebackR st.W st.R) n = rvBkt P (st.C, st.R) n := by
  have hw : wEmpty P st.W n := by
    have := h.1 n hn
    rcases hk with hk | hk <;> rw [hk] at this
    · exact this.1
    · exact this
  apply rvBkt_ext; intro k
  rw [vOf_writeback]
  exact ovB_wEmpty hw _ k

/-! ## Preservation -/

section ops
variable {P : BParams} {st : BSess} {tk : TkMap}

/-- The put's write buffer, `put` or `putSeq`, adds the entry. -/
theorem putW_bks (W : WBuf) (id : w64) (e : Ent) (seq : Bool) :
    (if seq then W.putSeq id e else W.put id e).bks = wbAdd W.bks id e := by
  cases seq <;> rfl

/-- The view through a write buffer with one entry added, at another bucket's id, is the old one. -/
theorem ovB_wbAdd_ne (hP : P.Wf) {B : GMap w64 (List Ent)} {bi : BucketInfo} (hb : P.has bi)
    {n : GoString} (hn : n ≠ bi.name) (e : Ent) (f : VFun) (k : GoString) :
    ovB P.BT (wbAdd B bi.id e) f n k = ovB P.BT B f n k := by
  unfold ovB
  cases hi : P.BT.lookup n with
  | none => rfl
  | some i =>
    have hid : bi.id ≠ i := fun e => hn (hP.1 n bi.name i hi (e ▸ hb))
    simp only [Option.bind_some, bkOf_wbAdd, hid, ↓reduceIte]

theorem wEmpty_wbAdd_ne (hP : P.Wf) {W W' : WBuf} {bi : BucketInfo} (hb : P.has bi) {n : GoString}
    (hn : n ≠ bi.name) {e : Ent} (hW : W'.bks = wbAdd W.bks bi.id e) (h : wEmpty P W n) :
    wEmpty P W' n := by
  intro i hi
  have hid : bi.id ≠ i := fun e => hn (hP.1 n bi.name i hi (e ▸ hb))
  rw [hW, bkOf_wbAdd]; simp only [hid, ↓reduceIte]; exact h i hi

/-- **A put** (`UnsafePut`, `UnsafeSeqPut`) keeps the agreement, the bucket's kind joined with `put`. -/
theorem trkOk_put (hP : P.Wf) (h : trkOk P st tk) {bi : BucketInfo} (hb : P.has bi) (k v : GoString)
    (seq : Bool) (hp0 : 0 ≤ sint.Z st.pend) (hp1 : sint.Z st.pend < 2 ^ 58) :
    trkOk P (st.put bi k v seq) (tkSet tk bi.name .put) := by
  obtain ⟨hk, -, hd⟩ := h
  have hW : (st.put bi k v seq).W.bks = wbAdd st.W.bks bi.id (k, v) := putW_bks _ _ _ _
  have hV : viewOf P (st.put bi k v seq) = viewOf P st := rfl
  refine ⟨fun n hn => ?_, fun hz => ?_, fun hz n hn => ?_⟩
  · by_cases he : n = bi.name
    · subst he
      rw [tkSet_self]
      have hkn := hk bi.name hn
      cases htk : tk bi.name <;> rw [htk] at hkn <;> simp only [RbK.join, kOk]
      · intro k'
        rw [hV, hW]
        show ovB P.BT (wbAdd st.W.bks bi.id (k, v)) (viewOf P st) bi.name k' =
          dget (st.S.insert bi.name ((bktOf st.S bi.name).insert k v)) bi.name k'
        rw [dget_put]; unfold ovB; rw [hb]
        simp only [Option.bind_some, bkOf_wbAdd, ↓reduceIte, lastVal_append_single, true_and]
        rw [hkn.1 bi.id hb]
        by_cases hkk : k = k'
        · simp [hkk]
        · simp only [hkk, ↓reduceIte]
          show (lastVal [] k').or _ = _
          simp only [lastVal, List.reverse_nil, List.find?_nil, Option.map_none, Option.none_or]
          exact hkn.2 k'
      · intro k'
        rw [hV, hW]
        show ovB P.BT (wbAdd st.W.bks bi.id (k, v)) (viewOf P st) bi.name k' =
          dget (st.S.insert bi.name ((bktOf st.S bi.name).insert k v)) bi.name k'
        rw [dget_put]
        have hk' := hkn k'
        unfold ovB at hk' ⊢; rw [hb] at hk' ⊢
        simp only [Option.bind_some, bkOf_wbAdd, ↓reduceIte, lastVal_append_single, true_and] at hk' ⊢
        by_cases hkk : k = k'
        · simp [hkk]
        · simp only [hkk, ↓reduceIte]; exact hk'
    · rw [tkSet_ne _ _ he]
      have hkn := hk n hn
      have hS : ∀ k', dget (st.put bi k v seq).S n k' = dget st.S n k' := by
        intro k'
        show dget (st.S.insert bi.name ((bktOf st.S bi.name).insert k v)) n k' = _
        rw [dget_put]; simp [Ne.symm he]
      cases htk : tk n <;> rw [htk] at hkn <;> simp only [kOk]
      · exact ⟨wEmpty_wbAdd_ne hP hb he hW hkn.1, fun k' => by rw [hV, hS]; exact hkn.2 k'⟩
      · intro k'; rw [hV, hS, hW, ovB_wbAdd_ne hP hb he]; exact hkn k'
      · exact wEmpty_wbAdd_ne hP hb he hW hkn
  · exfalso
    have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    have h0 : sint.Z (st.put bi k v seq).pend = 0 := by rw [hz]; rfl
    change sint.Z (st.pend + W64 1) = 0 at h0
    omega
  · have h' := hd hz n hn
    by_cases he : n = bi.name
    · subst he; rw [tkSet_self]; rcases h' with h' | h' <;> rw [h'] <;> simp [RbK.join]
    · rw [tkSet_ne _ _ he]; exact h'

/-- `dget` after the writer's delete of a key. -/
theorem dget_del (S : Data) (n k n' k' : GoString) :
    dget (S.insert n ((bktOf S n).delete k)) n' k' =
      if n = n' then (if k = k' then none else dget S n' k') else dget S n' k' := by
  rw [dget_insert]
  by_cases hn : n = n'
  · subst hn; simp only [↓reduceIte, GMap.lookup_delete_iff, dget_eq_bktOf]
  · simp [hn]

/-- **A delete** (`UnsafeDelete`) keeps the agreement, the bucket's kind joined with `del`. -/
theorem trkOk_del (h : trkOk P st tk) (bi : BucketInfo) (k : GoString)
    (hp0 : 0 ≤ sint.Z st.pend) (hp1 : sint.Z st.pend < 2 ^ 58) (hn0 : 0 ≤ sint.Z st.ndel)
    (hn1 : sint.Z st.ndel ≤ sint.Z st.pend) :
    trkOk P (st.del bi k) (tkSet tk bi.name .del) := by
  obtain ⟨hk, -, -⟩ := h
  have hV : viewOf P (st.del bi k) = viewOf P st := rfl
  have hW : (st.del bi k).W = st.W := rfl
  refine ⟨fun n hn => ?_, fun hz => ?_, fun hz => ?_⟩
  · by_cases he : n = bi.name
    · subst he
      rw [tkSet_self]
      have hkn := hk bi.name hn
      cases htk : tk bi.name <;> rw [htk] at hkn <;> simp only [RbK.join, kOk, hW]
      · exact hkn.1
      · exact hkn
    · rw [tkSet_ne _ _ he]
      have hkn := hk n hn
      have hS : ∀ k', dget (st.del bi k).S n k' = dget st.S n k' := by
        intro k'
        show dget (st.S.insert bi.name ((bktOf st.S bi.name).delete k)) n k' = _
        rw [dget_del]; simp [Ne.symm he]
      cases htk : tk n <;> rw [htk] at hkn <;> simp only [kOk, hW, hV, hS]
      · exact hkn
      · exact hkn
      · exact hkn
  · exfalso
    have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    have h0 : sint.Z (st.del bi k).pend = 0 := by rw [hz]; rfl
    change sint.Z (st.pend + W64 1) = 0 at h0
    omega
  · exfalso
    have : sint.Z (st.ndel + W64 1) = sint.Z st.ndel + 1 := by word
    have h0 : sint.Z (st.del bi k).ndel = 0 := by rw [hz]; rfl
    change sint.Z (st.ndel + W64 1) = 0 at h0
    omega

/-- **A bucket's creation** (`UnsafeCreateBucket`) keeps the agreement and the kinds (it changes no
key). -/
theorem trkOk_create (h : trkOk P st tk) (bi : BucketInfo)
    (hp0 : 0 ≤ sint.Z st.pend) (hp1 : sint.Z st.pend < 2 ^ 58) :
    trkOk P (st.create bi) tk := by
  obtain ⟨hk, -, hd⟩ := h
  have hS : dget (st.create bi).S = dget st.S := dget_create st.S bi.name
  refine ⟨fun n hn => ?_, fun hz => ?_, hd⟩
  · have hkn := hk n hn
    cases htk : tk n <;> rw [htk] at hkn <;> simp only [kOk]
    · exact ⟨hkn.1, fun k => by rw [hS]; exact hkn.2 k⟩
    · intro k; rw [hS]; exact hkn k
    · exact hkn
  · exfalso
    have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    have h0 : sint.Z (st.create bi).pend = 0 := by rw [hz]; rfl
    change sint.Z (st.pend + W64 1) = 0 at h0
    omega

/-- **A bucket's deletion** (`UnsafeDeleteBucket`) keeps the agreement, the bucket's kind joined with
`del`. -/
theorem trkOk_delBucket (h : trkOk P st tk) (bi : BucketInfo)
    (hp0 : 0 ≤ sint.Z st.pend) (hp1 : sint.Z st.pend < 2 ^ 58) (hn0 : 0 ≤ sint.Z st.ndel)
    (hn1 : sint.Z st.ndel ≤ sint.Z st.pend) :
    trkOk P (st.delBucket bi) (tkSet tk bi.name .del) := by
  obtain ⟨hk, -, -⟩ := h
  refine ⟨fun n hn => ?_, fun hz => ?_, fun hz => ?_⟩
  · by_cases he : n = bi.name
    · subst he
      rw [tkSet_self]
      have hkn := hk bi.name hn
      cases htk : tk bi.name <;> rw [htk] at hkn <;> simp only [RbK.join, kOk]
      · exact hkn.1
      · exact hkn
    · rw [tkSet_ne _ _ he]
      have hkn := hk n hn
      have hS : ∀ k', dget (st.delBucket bi).S n k' = dget st.S n k' := by
        intro k'
        show dget (st.S.delete bi.name) n k' = _
        unfold dget; rw [GMap.lookup_delete_ne _ (Ne.symm he)]
      have hV : viewOf P (st.delBucket bi) = viewOf P st := rfl
      have hW : (st.delBucket bi).W = st.W := rfl
      cases htk : tk n <;> rw [htk] at hkn <;> simp only [kOk, hW, hV, hS]
      · exact hkn
      · exact hkn
      · exact hkn
  · exfalso
    have : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    have h0 : sint.Z (st.delBucket bi).pend = 0 := by rw [hz]; rfl
    change sint.Z (st.pend + W64 1) = 0 at h0
    omega
  · exfalso
    have : sint.Z (st.ndel + W64 1) = sint.Z st.ndel + 1 := by word
    have h0 : sint.Z (st.delBucket bi).ndel = 0 := by rw [hz]; rfl
    change sint.Z (st.ndel + W64 1) = 0 at h0
    omega

/-- **The write-back** keeps the agreement and the kinds (the write buffer over the readers' view
becomes the readers' view). -/
theorem trkOk_wb (h : trkOk P st tk) : trkOk P (wbSt P st) tk := by
  obtain ⟨hk, -, hd⟩ := h
  have hWe : ∀ n, wEmpty P (wbSt P st).W n := fun n i _ => bkOf_writebackW st.W st.R i
  have hV : viewOf P (wbSt P st) = ovB P.BT st.W.bks (viewOf P st) := vOf_writeback P st.C st.W st.R
  have hO : ∀ f, ovB P.BT (wbSt P st).W.bks f = f :=
    fun f => ovB_empty P.BT _ f (fun i => bkOf_writebackW st.W st.R i)
  refine ⟨fun n hn => ?_, fun _ n _ => hWe n, hd⟩
  have hkn := hk n hn
  cases htk : tk n <;> rw [htk] at hkn <;> simp only [kOk]
  · refine ⟨hWe n, fun k => ?_⟩
    rw [hV, ovB_wEmpty hkn.1]; exact hkn.2 k
  · intro k; rw [hO, hV]; exact hkn k
  · exact hWe n

/-- **The pre-commit hook** (`hookStepT`) keeps the agreement and the kinds. -/
theorem trkOk_hook {st' : BSess} (h : trkOk P st tk) (hs : hookStepT P st st')
    (hp0 : 0 ≤ sint.Z st.pend) (hn0 : 0 ≤ sint.Z st.ndel) : trkOk P st' tk := by
  obtain ⟨hk, hpz, hd⟩ := h
  obtain ⟨⟨hC, hR, -, hB, -, hp1, -, hn1, -⟩, hWt⟩ := hs
  have hV : viewOf P st' = viewOf P st := by unfold viewOf; rw [hC, hR]
  have hS : ∀ n, P.RB n = true → ∀ k, dget st'.S n k = dget st.S n k := by
    intro n hn k
    have := congrArg (fun m => GMap.lookup m n) hB
    simp only [rbData_lookup, hn, ↓reduceIte] at this
    unfold dget; rw [this]
  have hWe : ∀ n, P.RB n = true → wEmpty P st.W n → wEmpty P st'.W n :=
    fun n hn h i hi => by rw [hWt n i hi hn]; exact h i hi
  have hO : ∀ n, P.RB n = true → ∀ f k, ovB P.BT st'.W.bks f n k = ovB P.BT st.W.bks f n k := by
    intro n hn f k; unfold ovB
    cases hi : P.BT.lookup n with
    | none => rfl
    | some i => simp only [Option.bind_some, hWt n i hi hn]
  refine ⟨fun n hn => ?_, fun hz n hn => ?_, fun hz => ?_⟩
  · have hkn := hk n hn
    cases htk : tk n <;> rw [htk] at hkn <;> simp only [kOk]
    · exact ⟨hWe n hn hkn.1, fun k => by rw [hV, hS n hn]; exact hkn.2 k⟩
    · intro k; rw [hO n hn, hV, hS n hn]; exact hkn k
    · exact hWe n hn hkn
  · have : st.pend = W64 0 := by
      have : sint.Z st'.pend = 0 := by rw [hz]; rfl
      word
    exact hWe n hn (hpz this n hn)
  · have : st.ndel = W64 0 := by
      have : sint.Z st'.ndel = 0 := by rw [hz]; rfl
      word
    exact hd this

/-- **The commit** (`unsafeCommit`, from `st`, the hook having run into `st'`, the tracked buckets'
write buffer empty: after a write-back, or with the lock free): every tracked bucket untouched, and the
readers see the writer's contents there (a bucket deleted from or of both kinds now too). -/
theorem trkOk_commit {st' : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt} (h : trkOk P st tk)
    (hst : sessWf P st) (hs : hookStepT P st st')
    (hWt : ∀ n, P.RB n = true → wEmpty P st.W n)
    (hC' : C' = st'.S ∨ (st'.pend = W64 0 ∧ C' = st'.C)) :
    trkOk P (commitSt st' C' tx' cnt') tkIdle ∧
      ∀ n, P.RB n = true → rvBkt P (C', st'.R.reset) n = bktOf st.S n := by
  obtain ⟨hk, -, hd⟩ := h
  obtain ⟨⟨hsC, hsR, -, hsB, -, hsp1, -, -, -⟩, hsW⟩ := hs
  have hS : ∀ n, P.RB n = true → ∀ k, dget st'.S n k = dget st.S n k := by
    intro n hn k
    have := congrArg (fun m => GMap.lookup m n) hsB
    simp only [rbData_lookup, hn, ↓reduceIte] at this
    unfold dget; rw [this]
  -- the committed data reads, on the tracked buckets, as the writer's contents before the hook
  have hCS : ∀ n, P.RB n = true → ∀ k, dget C' n k = dget st.S n k := by
    rcases hC' with rfl | ⟨hp0, rfl⟩
    · exact hS
    · intro n hn k
      have hp : st.pend = W64 0 := by
        have h1 := hst.2.2.2.2.1
        have : sint.Z st'.pend = 0 := by rw [hp0]; rfl
        word
      have hn0 : st.ndel = W64 0 := by
        have h1 := hst.2.2.2.2.2.2.1
        have h2 := hst.2.2.2.2.2.2.2.1
        have : sint.Z st.pend = 0 := by rw [hp]; rfl
        word
      have hR := hst.2.2.2.2.2.2.2.2.1 hp
      have hv : ∀ k, viewOf P st n k = dget st.S n k := by
        intro k
        have hkn := hk n hn
        rcases hd hn0 n hn with htk | htk <;> rw [htk] at hkn
        · exact hkn.2 k
        · rw [← hkn k, ovB_wEmpty (hWt n hn)]
      rw [hsC, ← hv k]
      unfold viewOf; rw [ovB_empty P.BT st.R.bks _ hR]
  have hV : viewOf P (commitSt st' C' tx' cnt') = dget C' := vOf_resetC P C' st'.R
  have hWe : ∀ n, P.RB n = true → wEmpty P (commitSt st' C' tx' cnt').W n :=
    fun n hn i hi => by
      show bkOf st'.W.bks i = []
      rw [hsW n i hi hn]; exact hWt n hn i hi
  refine ⟨⟨fun n hn => ⟨hWe n hn, fun k => ?_⟩, fun _ => hWe, fun _ _ _ => Or.inl rfl⟩, fun n hn => ?_⟩
  · rw [hV, hCS n hn]; exact (hS n hn k).symm
  · apply bktOf_ext_dget; intro k
    rw [rvBkt_lookup, vOf_resetC]; exact hCS n hn k

end ops

end backend
end EtcdGrove
end Perennial
