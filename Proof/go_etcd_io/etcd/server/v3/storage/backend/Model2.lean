/-
The pure model of the backend above its buffers (`batch_tx.go`, `read_tx.go`, `backend.go`):
the batch transaction's state, the readers' view, and what the batch lock keeps true. Lean-first
(no Rocq counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value
contract, the locks and the views".

**Buckets.** The backend's clients name a bucket by a `Bucket` value with an id and a name
(`BucketInfo`); the buffers are keyed by id, bbolt by name. `BParams.BT` is the clients' table of
buckets (name to id, injective: schema's buckets).

**Views.** A view (`VFun`) is a lookup function: bucket name, key, value. `dget D` is bbolt's
data's; `ovB BT B base` overlays the buffer buckets `B` (by id) on `base` (the newest entry of a
key in its bucket wins: `lastVal`). The readers see `viewOf st = ovB BT st.R.bks (dget st.C)`:
the committed data of the batch interval with the read buffer over it. The writer's bbolt
contents `S`, while no delete is pending, are the committed data with the read buffer then the
write buffer over it. `agreeOff HB f g`: the two views agree except on the hook's buckets `HB`.

**The batch transaction's state** (`BSess`): committed data `C`, writer contents `S`, read and
write buffers, `pending` and `pendingDeleteOperations`, and bbolt's write transaction `tx` (only a
commit changes it: the slices a range of the writer returns are valid while it is the same).
`sessWf` holds always; `freeOk` when the lock is free (no delete pending, `pending` below the
limit, the write buffer empty but for the hook's buckets: the leftovers of the last commit's
hook).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-- The backend's parameters: the clients' buckets (name to id), the buckets the pre-commit hook
writes, how many entries one run of the hook puts at most, and the configuration's batch
limit. -/
structure BParams where
  BT : GMap GoString w64
  HB : GoString → Bool
  hookMax : Nat
  limit : w64

/-- The parameters are sane: bucket ids distinct, the limit positive and small enough that the
buffers do not overflow (`bufBound`), the hook's puts few. -/
def BParams.Wf (P : BParams) : Prop :=
  (∀ n1 n2 i, P.BT.lookup n1 = some i → P.BT.lookup n2 = some i → n1 = n2) ∧
  0 < sint.Z P.limit ∧ sint.Z P.limit ≤ 2 ^ 57 ∧ P.hookMax ≤ 2 ^ 16

/-- A bucket of the table. -/
def BParams.has (P : BParams) (bi : BucketInfo) : Prop := P.BT.lookup bi.name = some bi.id

/-- A view: bucket name, key, value. -/
abbrev VFun := GoString → GoString → Option GoString

/-- bbolt's data as a view. -/
def dget (D : Data) : VFun := fun n k => (D.lookup n).bind (fun m => m.lookup k)

/-- The buffer buckets `B` (by id, through the table) over the view `base`. -/
def ovB (BT : GMap GoString w64) (B : GMap w64 (List Ent)) (base : VFun) : VFun :=
  fun n k => ((BT.lookup n).bind (fun i => lastVal (bkOf B i) k)).or (base n k)

/-- Two views agree off the hook's buckets. -/
def agreeOff (HB : GoString → Bool) (f g : VFun) : Prop :=
  ∀ n, HB n = false → ∀ k, f n k = g n k

/-- The batch lock's ghost counters of a state (`bgOk`): `k` paid commits and `c` commits since
the last write-back, `p0` the pending count at the last write-back, `e` the hook's leftovers moved
into the read buffer since the last commit. Ghost data: the session's operations and the hook keep
them; only the batch transaction's own `Unlock` and commit change them. -/
structure BCnt where
  k : Nat
  c : Nat
  p0 : Nat
  e : Nat

/-- The batch transaction's state. -/
structure BSess where
  C : Data
  S : Data
  R : RBuf
  W : WBuf
  pend : w64
  ndel : w64
  tx : Loc
  cnt : BCnt

/-- What the readers see of a state: the committed data with the read buffer over it. -/
def viewOf (P : BParams) (st : BSess) : VFun := ovB P.BT st.R.bks (dget st.C)

/-- What the readers see, as a value: the committed data of the batch interval and the read
buffer (a ghost variable holds it: a view function is not countable). -/
abbrev RView := Data × RBuf

instance rbuf_countable : Pos.Countable RBuf :=
  countableOfLeftInverse (fun r : RBuf => (r.bks, r.ver)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

/-- The view of a readers' state. -/
def vOf (P : BParams) (rv : RView) : VFun := ovB P.BT rv.2.bks (dget rv.1)

/-! ## The readers' view as a finite map -/

/-- The keys a view of `rv` can have: the committed data's, and the read buffer's (through the
table). -/
def vKeys (P : BParams) (rv : RView) : List (GoString × GoString) :=
  rv.1.toList.flatMap (fun nm => nm.2.toList.map (fun kv => (nm.1, kv.1))) ++
  P.BT.toList.flatMap (fun ni => (bkOf rv.2.bks ni.2).map (fun e => (ni.1, e.1)))

theorem lastVal_isSome_mem {l : List Ent} {k : GoString} (h : (lastVal l k).isSome) :
    ∃ e ∈ l, e.1 = k := by
  unfold lastVal at h
  cases hf : l.reverse.find? (fun e => decide (e.1 = k)) with
  | none => rw [hf] at h; simp at h
  | some e =>
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    exact ⟨e, List.mem_reverse.1 hm, by simpa using hk⟩

theorem vOf_isSome_mem (P : BParams) (rv : RView) (n k : GoString)
    (h : (vOf P rv n k).isSome) : (n, k) ∈ vKeys P rv := by
  unfold vOf ovB at h
  unfold vKeys
  rw [List.mem_append]
  cases hb : (P.BT.lookup n).bind (fun i => lastVal (bkOf rv.2.bks i) k) with
  | some v =>
    right
    obtain ⟨i, hi, hl⟩ := Option.bind_eq_some_iff.1 hb
    obtain ⟨e, he, hek⟩ := lastVal_isSome_mem (l := bkOf rv.2.bks i) (k := k) (by rw [hl]; rfl)
    rw [List.mem_flatMap]
    refine ⟨(n, i), (GMap.mem_toList _ _ _).2 hi, ?_⟩
    rw [List.mem_map]
    exact ⟨e, he, by rw [hek]⟩
  | none =>
    left
    rw [hb, Option.none_or] at h
    unfold dget at h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨m, hm, hk⟩ := Option.bind_eq_some_iff.1 hv
    rw [List.mem_flatMap]
    refine ⟨(n, m), (GMap.mem_toList _ _ _).2 hm, ?_⟩
    rw [List.mem_map]
    exact ⟨(k, v), (GMap.mem_toList _ _ _).2 hk, rfl⟩

/-- The readers' view off the hook's buckets, as a finite map from (bucket, key) to the value:
the ghost state's value (two states with one view have one `vData`). -/
def vData (P : BParams) (rv : RView) : GMap (GoString × GoString) GoString :=
  ⟨fun nk => if P.HB nk.1 then none else vOf P rv nk.1 nk.2,
   ⟨vKeys P rv, fun nk h => by
      split at h
      · simp at h
      · exact vOf_isSome_mem P rv nk.1 nk.2 h⟩⟩

/-- bbolt's data off the hook's buckets, as a finite map (what the writer's contents read as). -/
def sData (P : BParams) (S : Data) : GMap (GoString × GoString) GoString := vData P (S, ⟨∅, W64 0⟩)

/-- The buffers' buckets are the table's. -/
def idsOk (P : BParams) (B : GMap w64 (List Ent)) : Prop :=
  ∀ i es, B.lookup i = some es → ∃ n, P.BT.lookup n = some i

/-- The state's facts at any time. -/
def sessWf (P : BParams) (st : BSess) : Prop :=
  st.W.Wf ∧ st.R.Wf ∧ idsOk P st.W.bks ∧ idsOk P st.R.bks ∧
  0 ≤ sint.Z st.pend ∧ sint.Z st.pend < 2 ^ 58 ∧ 0 ≤ sint.Z st.ndel ∧
  sint.Z st.ndel ≤ sint.Z st.pend ∧
  (st.pend = W64 0 → ∀ i, bkOf st.R.bks i = []) ∧
  (st.ndel = W64 0 → agreeOff P.HB (dget st.S) (ovB P.BT st.W.bks (viewOf P st)))

/-- The state's facts when the batch lock is free. -/
def freeOk (P : BParams) (st : BSess) : Prop :=
  sessWf P st ∧ sint.Z st.pend < sint.Z P.limit ∧ st.ndel = W64 0 ∧
  ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []

/-- The session changed nothing the readers see: the writer's contents read, off the hook's
buckets, as the readers' view, and the write buffer is empty off them (so the write-back leaves
the view as it is). A session that only put in, or deleted from, the hook's buckets has it (and
any `freeOk` state: `viewSame_of_freeOk`); a delete pending is allowed (the `Unlock` then
commits, which changes no `vData`). -/
def viewSame (P : BParams) (st : BSess) : Prop :=
  vData P (st.C, st.R) = sData P st.S ∧
  ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []

/-- The buffers' sizes, bounded through the batch lock's ghost counters (`st.cnt`, and `n` the
write-back tokens out, `w` the write-backs so far, `u` the write-back after which the `run`
goroutine's last unpaid commit came: at most one unpaid commit after each write-back). A commit
does not write the write buffer back: the hook's puts stay in it (at most `hookMax` a commit,
`c` of them since the last write-back); its other entries since the last write-back are puts
(`pend - p0`). `free`: the lock is free (every session's puts written back: `p0 = pend`; a
pending operation means a write-back since `run`'s last unpaid commit). -/
def bgOk (P : BParams) (st : BSess) (free : Bool) (n w u : Nat) : Prop :=
  uint.Z st.R.ver + n + st.cnt.k < 2 ^ 40 ∧ u ≤ w ∧
  st.cnt.c ≤ st.cnt.k + 1 + (if u = w then 1 else 0) ∧
  st.cnt.p0 ≤ sint.nat st.pend ∧ (st.cnt.e = 0 ∨ st.cnt.c = 0) ∧
  st.cnt.e ≤ P.hookMax * (2 ^ 40 + 2) ∧
  (∀ i, (bkOf st.W.bks i).length ≤ sint.nat st.pend - st.cnt.p0 + P.hookMax * st.cnt.c ∧
    (bkOf st.R.bks i).length ≤ st.cnt.p0 + st.cnt.e) ∧
  (∀ nm i, P.BT.lookup nm = some i → P.HB nm = false →
    (bkOf st.W.bks i).length ≤ sint.nat st.pend - st.cnt.p0) ∧
  (free = true → st.cnt.p0 = sint.nat st.pend ∧ (st.pend ≠ W64 0 → u < w))

end backend
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## The batch transaction's operations -/

/-- A bucket's contents in bbolt's data (empty if absent). -/
def bktOf (D : Data) (n : GoString) : BktData := (D.lookup n).getD ∅

/-- `UnsafePut(bucket, k, v)` (and `UnsafeSeqPut`, with the write buffer's `putSeq`): bbolt's
writer sets the entry, the write buffer gets it, one more pending operation. -/
def BSess.put (st : BSess) (bi : BucketInfo) (k v : GoString) (seq : Bool) : BSess :=
  { st with S := st.S.insert bi.name ((bktOf st.S bi.name).insert k v),
            W := if seq then st.W.putSeq bi.id (k, v) else st.W.put bi.id (k, v),
            pend := st.pend + W64 1 }

/-- `UnsafeDelete(bucket, k)`: bbolt's writer deletes the entry (no buffer), one more pending
operation and pending delete. -/
def BSess.del (st : BSess) (bi : BucketInfo) (k : GoString) : BSess :=
  { st with S := st.S.insert bi.name ((bktOf st.S bi.name).delete k),
            pend := st.pend + W64 1, ndel := st.ndel + W64 1 }

/-- `UnsafeCreateBucket(bucket)`: the bucket, empty if it was absent. -/
def BSess.create (st : BSess) (bi : BucketInfo) : BSess :=
  { st with S := if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S,
            pend := st.pend + W64 1 }

/-- `UnsafeDeleteBucket(bucket)`: the bucket deleted (absent or not), one more pending operation
and pending delete. -/
def BSess.delBucket (st : BSess) (bi : BucketInfo) : BSess :=
  { st with S := st.S.delete bi.name, pend := st.pend + W64 1, ndel := st.ndel + W64 1 }

/-- One run of the pre-commit hook, from `st` to `st'`: the committed data and the read buffer
untouched, the writer's contents changed only in the hook's buckets, the write buffer's
other buckets untouched, at most `hookMax` operations more, bbolt's write transaction and the
batch lock's ghost counters unchanged (the hook only calls the batch transaction's operations,
which keep them). -/
def hookStep (P : BParams) (st st' : BSess) : Prop :=
  st'.C = st.C ∧ st'.R = st.R ∧ sData P st'.S = sData P st.S ∧
  (∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st'.W.bks i = bkOf st.W.bks i) ∧
  sint.Z st.pend ≤ sint.Z st'.pend ∧ sint.Z st'.pend ≤ sint.Z st.pend + P.hookMax ∧
  sint.Z st.ndel ≤ sint.Z st'.ndel ∧ st'.tx = st.tx ∧ st'.cnt = st.cnt

/-! ## Ranges -/

/-- The limit `UnsafeRange` uses: 1 for a single key (no end key), else `limit` (all of them if
`limit ≤ 0`). -/
def rangeLimit (endKey : GoString) (limit : w64) : w64 :=
  if endKey = [] then W64 1 else if sint.Z limit ≤ 0 then W64 (2 ^ 63 - 1) else limit

/-- `unsafeRange(cursor, key, endKey, limit)` over a bucket's sorted entries: from the first
entry not below `key`, the entries below `endKey`, or the one equal to `key` (no end key), at most
`limit` (all if `limit ≤ 0`). -/
def cursorRange (es : List Ent) (key endKey : GoString) (limit : w64) : List Ent :=
  let rest := es.drop (seekIdx es key)
  if endKey = [] then (rest.takeWhile (fun e => decide (e.1 = key))).take 1
  else (rest.takeWhile (fun e => decide (strLt e.1 endKey))).take
    (if sint.Z limit ≤ 0 then 2 ^ 63 - 1 else (sint.Z limit).toNat)

/-- A read transaction's `UnsafeRange(bucket, key, endKey, limit)` over the readers' state
`rv`: the read buffer's range, and, if it has fewer than the limit, bbolt's range for the rest
before it. -/
def rtRange (rv : RView) (bi : BucketInfo) (key endKey : GoString) (limit : w64) : List Ent :=
  let lim := rangeLimit endKey limit
  let bufR := bbRange (bkOf rv.2.bks bi.id) key endKey lim
  if (bufR.length : Int) = sint.Z lim then bufR
  else cursorRange (bktEnts (bktOf rv.1 bi.name)) key endKey (lim - W64 bufR.length) ++ bufR

end backend
end EtcdGrove
end Perennial
