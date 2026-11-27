/-
The key-value store with scans and pending writes, porcupine's model (`model.go`), pure
(notes/dsv-epaxos.md, the model).

* **The store** `epB`: linkv's pending-writes store (`linkv.PendSpec`) of the key-value map with
  scans (`Interface/Client.lean`'s `kvStep`), on the inputs `Gen` makes (`EIn`: `inPre`, keys below
  2, a put's value non-empty and shorter than `2^15`, a scan of at most 2 keys); its output is the
  bytes of the answer's `Out.V` (`outBytes`, bounded: `BStr`), so that the outputs' encodings are
  injective (a put's success, a get of a missing key and an empty scan are all `""`).
* **The Go model** on its pure state: a configuration `GC` is the store's entries (`[]Entry`) and the
  pending puts (as `EIn`s: the Go slice holds their `inOf`); `getE`, `setE`, `readsG` (`reads`),
  `stepCG` (`stepConfig`), `sameConfigG` (`sameConfig`), `addAllG` (`addAll`), `stepG` (`step`).
* **The bracket** `Sim G S` (as dsv-craq's): every configuration reachable from one of `G`'s is in
  `S` (`Funl`), every one in `S` is reachable from one of `G`'s stores with some of its pending puts
  pending (`Fall`), and `G`'s configurations are well formed (`GOk`). `sim_init`, `sim_step`: the
  model's step is defined exactly when `stepG`'s result is not empty, and the next set is bracketed
  by it. (Two histories may reach the same Go state with different sets: model.go's `Equal` is
  always false.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.KitVals
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.PendModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.imdea_software.swiftpaxos_epaxos
  github_com.imdea_software.swiftpaxos_epaxos.kvs

deriving instance DecidableEq for KvsInput

/-! ## The store -/

/-- The store's inputs: those `Gen` makes (`inPre`). -/
abbrev EIn := {i : KvI // inPre i}

/-- `EIn`'s `BEq` is its decidable equality's (the instance linkv's pending lists erase with). -/
@[reducible] instance (priority := high) EIn.beq : BEq EIn := instBEqOfDecidableEq

/-- The store's outputs: an answer's bytes, bounded (`Codec()` writes them after one byte). -/
abbrev BStr := {s : GoString // s.length < 2 ^ 63 - 1}

/-- `w`, bounded (or `""` if it is too long). -/
@[irreducible] def bnd (w : GoString) : BStr :=
  if h : w.length < 2 ^ 63 - 1 then ⟨w, h⟩ else ⟨[], by simp⟩

theorem bnd_of {w : GoString} (h : w.length < 2 ^ 63 - 1) : bnd w = ⟨w, h⟩ := by
  unfold bnd; simp [h]

theorem bnd_val (w : BStr) : bnd w.1 = w := bnd_of w.2

/-- A put. -/
def isPut : KvI → Bool
  | .put _ _ => true
  | _ => false

/-- **The key-value store with scans and pending puts** (linkv's pending-writes store). -/
def epB : PendSpec KvS EIn BStr where
  init := fun _ => none
  step i σ := ((kvStep i.1 σ).1, bnd (outBytes (kvStep i.1 σ).2))
  isWrite i := isPut i.1

/-- `σ` with `k` mapped to `v`. -/
def upd (σ : KvS) (k : w64) (v : GoString) : KvS := fun k' => if k' = k then some v else σ k'

theorem upd_same (σ : KvS) (k : w64) (x y : GoString) : upd (upd σ k x) k y = upd σ k y := by
  funext k'; unfold upd; by_cases h : k' = k <;> simp [h]

theorem upd_comm (σ : KvS) (k k' : w64) (x y : GoString) (h : k' ≠ k) :
    upd (upd σ k x) k' y = upd (upd σ k' y) k x := by
  funext j; unfold upd
  by_cases h1 : j = k' <;> by_cases h2 : j = k <;> simp_all

theorem upd_get (σ : KvS) (k : w64) (x : GoString) : upd σ k x k = some x := by simp [upd]

theorem upd_ne (σ : KvS) (k k' : w64) (x : GoString) (h : k' ≠ k) : upd σ k x k' = σ k' := by
  simp [upd, h]

theorem step_put {k : w64} {v : GoString} (h : inPre (.put k v)) (σ : KvS) :
    epB.step ⟨.put k v, h⟩ σ = (upd σ k v, bnd []) := rfl

theorem step_nput (i : EIn) (h : isPut i.1 = false) (σ : KvS) : (epB.step i σ).1 = σ := by
  obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;> first | rfl | simp [isPut] at h

theorem step_put' (i : EIn) {k : w64} {v : GoString} (h : i.1 = .put k v) (σ : KvS) :
    (epB.step i σ).1 = upd σ k v := by
  obtain ⟨i, hi⟩ := i; simp only at h; subst h; rfl

/-- Every value is non-empty and shorter than `2^15` (a put's). -/
def valsOk (σ : KvS) : Prop := ∀ k v, σ k = some v → v ≠ [] ∧ v.length < 2 ^ 15

theorem valsOk_step (i : EIn) {σ : KvS} (h : valsOk σ) : valsOk (epB.step i σ).1 := by
  obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i
  · exact h
  · intro k' v' h'
    simp only [step_put] at h'
    unfold upd at h'
    split at h'
    · cases h'; exact ⟨hi.2.1, hi.2.2⟩
    · exact h k' v' h'
  · exact h

/-! ## Late effects -/

theorem pin_inv {i : EIn} (hp : isPut i.1 = true) : ∃ k v, i.1 = .put k v := by
  obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i <;> simp_all [isPut]

theorem valsOk_reach {c c' : PCfg KvS EIn} (h : PReach epB c c') (hv : valsOk c.st) :
    valsOk c'.st := by
  induction h with
  | refl => exact hv
  | step hs _ ih =>
    cases hs with
    | apply j _ => exact ih (valsOk_step j hv)
    | perm p _ => exact ih hv

/-- The pending inputs stay puts. -/
theorem puts_reach {c c' : PCfg KvS EIn} (h : PReach epB c c')
    (hp : ∀ i ∈ c.pend, isPut i.1 = true) : ∀ i ∈ c'.pend, isPut i.1 = true := by
  induction h with
  | refl => exact hp
  | step hs _ ih =>
    cases hs with
    | apply j _ => exact ih fun i hi => hp i (List.mem_of_mem_erase hi)
    | perm p hq => exact ih fun i hi => hp i (hq.subset hi)

/-- A pending input that never fires rides along. -/
theorem reach_cons (i : EIn) {c c' : PCfg KvS EIn} (h : PReach epB c c') :
    PReach epB ⟨c.st, i :: c.pend⟩ ⟨c'.st, i :: c'.pend⟩ := by
  induction h with
  | refl c => exact .refl _
  | @step c c₁ c₂ hs _ ih =>
    refine PReach.trans ?_ ih
    cases hs with
    | apply j hj =>
      refine .step (.apply ⟨c.st, i :: c.pend⟩ j (List.mem_cons_of_mem _ hj)) (.single (.perm _ _ ?_))
      by_cases hij : i = j
      · subst hij
        simp only [List.erase_cons_head]
        exact (List.perm_cons_erase hj).symm
      · rw [List.erase_cons_tail (by simpa using hij)]
    | perm p hp => exact .single (.perm _ _ (hp.cons i))

/-- **A put after late effects**: the same as the put first, then the late effects at other keys
(those at its own key are overwritten: they need not be pending). -/
theorem reach_put (k : w64) (x : GoString) {c c' : PCfg KvS EIn} (h : PReach epB c c') :
    ∃ Q, Q.Subperm c.pend ∧ PReach epB ⟨upd c.st k x, Q⟩ ⟨upd c'.st k x, c'.pend⟩ := by
  induction h with
  | refl c => exact ⟨c.pend, List.Subperm.refl _, .refl _⟩
  | @step c c₁ c₂ hs _ ih =>
    obtain ⟨Q₁, hQ₁, hr⟩ := ih
    cases hs with
    | apply j hj =>
      cases hput : isPut j.1
      · refine ⟨Q₁, hQ₁.trans (List.erase_sublist ..).subperm, ?_⟩
        simpa [step_nput j hput] using hr
      · obtain ⟨k', y, hk'⟩ := pin_inv hput
        by_cases hk : k' = k
        · subst hk
          refine ⟨Q₁, hQ₁.trans (List.erase_sublist ..).subperm, ?_⟩
          simpa [step_put' j hk', upd_same] using hr
        · refine ⟨j :: Q₁, ?_, ?_⟩
          · exact ((List.subperm_cons _).2 hQ₁).trans (List.perm_cons_erase hj).symm.subperm
          · refine .step (.apply ⟨upd c.st k x, _ :: Q₁⟩ _ List.mem_cons_self) ?_
            simp only [step_put' j hk', List.erase_cons_head]
            rw [upd_comm _ _ _ _ _ hk]
            simpa [step_put' j hk'] using hr
    | perm p hp => exact ⟨Q₁, hQ₁.trans hp.subperm, hr⟩

/-- **A key after late effects**: its value before, or the value of a pending put of it, which
may be taken to have fired first (the others at the key before it are overwritten). -/
theorem reach_key (k : w64) {c c' : PCfg KvS EIn} (h : PReach epB c c') :
    c'.st k = c.st k ∨ ∃ (x : GoString) (i : EIn), c'.st k = some x ∧ i.1 = .put k x ∧
      i ∈ c.pend ∧ ∃ Q, Q.Subperm (c.pend.erase i) ∧ PReach epB ⟨upd c.st k x, Q⟩ c' := by
  induction h with
  | refl c => exact .inl rfl
  | @step c c₁ c₂ hs hr ih =>
    cases hs with
    | apply j hj =>
      cases hput : isPut j.1
      · have he := step_nput j hput c.st
        rcases ih with h1 | ⟨x, i, hx, hi, him, Q, hQ, hr'⟩
        · exact .inl (by rw [h1]; simp only [he])
        · refine .inr ⟨x, i, hx, hi, List.mem_of_mem_erase him, Q, ?_, by simpa [he] using hr'⟩
          rw [List.erase_comm] at hQ
          exact hQ.trans (List.erase_sublist ..).subperm
      · obtain ⟨k', y, hk'⟩ := pin_inv hput
        have he := step_put' j hk' c.st
        rcases ih with h1 | ⟨x, i, hx, hi, him, Q, hQ, hr'⟩
        · by_cases hk : k' = k
          · subst hk
            refine .inr ⟨y, j, ?_, hk', hj, _, List.Subperm.refl _, ?_⟩
            · simpa [he, upd_get] using h1
            · simpa [he] using hr
          · exact .inl (by simpa [he, upd_ne _ _ _ _ (Ne.symm hk)] using h1)
        · refine .inr ⟨x, i, hx, hi, List.mem_of_mem_erase him, ?_⟩
          by_cases hk : k' = k
          · subst hk
            refine ⟨Q, ?_, by simpa [he, upd_same] using hr'⟩
            rw [List.erase_comm] at hQ
            exact hQ.trans (List.erase_sublist ..).subperm
          · have hji : j ≠ i := by
              intro e; rw [← e, hk'] at hi; simp at hi; exact hk hi.1
            refine ⟨j :: Q, ?_, ?_⟩
            · rw [List.erase_comm] at hQ
              exact ((List.subperm_cons _).2 hQ).trans
                (List.perm_cons_erase (List.mem_erase_of_ne hji |>.2 hj)).symm.subperm
            · refine .step (.apply ⟨upd c.st k x, _ :: Q⟩ _ List.mem_cons_self) ?_
              simp only [step_put' j hk', List.erase_cons_head]
              rw [upd_comm _ _ _ _ _ hk]
              simpa [he] using hr'
    | perm p hp =>
      rcases ih with h1 | ⟨x, i, hx, hi, him, Q, hQ, hr'⟩
      · exact .inl h1
      · exact .inr ⟨x, i, hx, hi, hp.mem_iff.1 him, Q, hQ.trans (hp.erase i).subperm, hr'⟩

/-! ## A read's output -/

/-- The keys `k, k+1, …` (`m` of them). -/
def keysFrom (k : w64) : Nat → List w64
  | 0 => []
  | m + 1 => k :: keysFrom (k + 1) m

/-- The values of the keys `ks`, concatenated (a missing key's is `""`). -/
def catV (σ : KvS) (ks : List w64) : GoString := (ks.map fun j => (σ j).getD []).flatten

theorem catV_cons (σ : KvS) (k : w64) (ks : List w64) :
    catV σ (k :: ks) = (σ k).getD [] ++ catV σ ks := rfl

theorem catV_len (σ : KvS) (h : valsOk σ) (ks : List w64) :
    (catV σ ks).length ≤ ks.length * 2 ^ 15 := by
  induction ks with
  | nil => simp [catV]
  | cons j ks ih =>
    rw [catV_cons, List.length_append, List.length_cons]
    have : ((σ j).getD []).length ≤ 2 ^ 15 := by
      cases hj : σ j with
      | none => simp
      | some v => have := (h j v hj).2; simp; omega
    rw [Nat.succ_mul]; omega

theorem mem_keysFrom {k j : w64} {m : Nat} (h : j ∈ keysFrom k m) :
    ∃ t < m, j = k + BitVec.ofNat 64 t := by
  induction m generalizing k with
  | zero => simp [keysFrom] at h
  | succ m ih =>
    simp only [keysFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨t, ht, rfl⟩ := ih h
      refine ⟨t + 1, by omega, ?_⟩
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem self_not_mem_keysFrom (k : w64) (m : Nat) (hm : m < 2 ^ 64) :
    k ∉ keysFrom (k + 1) m := by
  intro h
  obtain ⟨t, ht, he⟩ := mem_keysFrom h
  have := congrArg BitVec.toNat he
  simp [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem scanKeys_eq (k n : w64) (h : k.toNat + n.toNat < 2 ^ 64) :
    scanKeys k n = keysFrom k (n.toNat + 1) := by
  unfold scanKeys
  rw [Nat.min_eq_left (by omega)]
  have key : ∀ (m s : Nat),
      (List.range' s m).map (BitVec.ofNat 64) = keysFrom (BitVec.ofNat 64 s) m := by
    intro m
    induction m with
    | zero => intro s; rfl
    | succ m ih =>
      intro s
      rw [List.range'_succ, List.map_cons, keysFrom, ih (s + 1)]
      congr 2
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
  rw [key, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A read's output: the keys' values concatenated. -/
theorem read_out_get (k : w64) (h : inPre (.get k)) (σ : KvS) :
    epB.step ⟨.get k, h⟩ σ = (σ, bnd (catV σ (keysFrom k 1))) := by
  simp only [epB, kvStep, keysFrom, catV, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  cases σ k <;> rfl

theorem flatten_filterMap (σ : KvS) (ks : List w64) :
    (ks.filterMap σ).flatten = catV σ ks := by
  induction ks with
  | nil => rfl
  | cons j ks ih =>
    rw [catV_cons, List.filterMap_cons]
    cases σ j <;> simp [ih]

theorem read_out_scan (k n : w64) (h : inPre (.scan k n)) (σ : KvS) :
    epB.step ⟨.scan k n, h⟩ σ = (σ, bnd (catV σ (keysFrom k (n.toNat + 1)))) := by
  simp only [epB, kvStep, outBytes]
  rw [flatten_filterMap, scanKeys_eq k n (by simp only [inPre] at h; omega)]

/-! ## The Go model on its pure state -/

section go
variable [GooseExts]

/-- A configuration of the Go model: the store's entries, and the pending puts (the Go slice
holds their `inE`). -/
abbrev GC := List Entry × List EIn

/-- A pending input's `In`. -/
def inE (i : EIn) : In := inOf i.1

/-- `get(kv, k)`. -/
def getE : List Entry → w64 → GoString
  | [], _ => []
  | e :: es, k => if e.K' = k then e.V' else getE es k

/-- `set(kv, k, v)`. -/
def setE (kv : List Entry) (k : w64) (v : GoString) : List Entry :=
  kv.filter (fun e => !decide (e.K' = k)) ++ (if v = [] then [] else [Entry.mk k v])

/-- The store a Go configuration's entries stand for (a missing key and `""` are the same). -/
def absKv (kv : List Entry) : KvS := fun k => if getE kv k = [] then none else some (getE kv k)

/-- The configuration a Go configuration stands for. -/
def absC (g : GC) : PCfg KvS EIn := ⟨absKv g.1, g.2⟩

theorem absKv_getD (kv : List Entry) (k : w64) : (absKv kv k).getD [] = getE kv k := by
  unfold absKv; split <;> simp_all

theorem getE_append (l l' : List Entry) (k : w64) :
    getE (l ++ l') k = if k ∈ l.map Entry.K' then getE l k else getE l' k := by
  induction l with
  | nil => simp [getE]
  | cons e es ih =>
    simp only [List.cons_append, getE, List.map_cons, List.mem_cons]
    by_cases h : e.K' = k
    · simp [h]
    · simp only [h, ↓reduceIte, ih]
      have : ¬ k = e.K' := fun e' => h e'.symm
      simp [this]

theorem getE_not_mem {l : List Entry} {k : w64} (h : k ∉ l.map Entry.K') : getE l k = [] := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [getE, Ne.symm h.1, ↓reduceIte, ih h.2]

theorem getE_filter (l : List Entry) (k : w64) (p : Entry → Bool)
    (hp : ∀ e, e.K' = k → p e = true) : getE (l.filter p) k = getE l k := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.K' = k
    · simp [List.filter_cons, hp e he, getE, he]
    · cases hpe : p e <;> simp [List.filter_cons, hpe, getE, he, ih]

theorem getE_setE_same (kv : List Entry) (k : w64) (v : GoString) : getE (setE kv k v) k = v := by
  unfold setE
  rw [getE_append, if_neg]
  · split <;> simp_all [getE]
  · simp

theorem getE_setE_ne (kv : List Entry) (k j : w64) (v : GoString) (h : j ≠ k) :
    getE (setE kv k v) j = getE kv j := by
  unfold setE
  rw [getE_append]
  split
  · exact getE_filter _ _ _ (fun e he => by simp [he, h])
  · rename_i hn
    have : getE kv j = [] := by
      rw [← getE_filter kv j (fun e => !decide (e.K' = k)) (fun e he => by simp [he, h])]
      exact getE_not_mem hn
    rw [this]; split <;> simp [getE, Ne.symm h]

theorem absKv_setE (kv : List Entry) (k : w64) (v : GoString) (hv : v ≠ []) :
    absKv (setE kv k v) = upd (absKv kv) k v := by
  funext j
  unfold absKv upd
  by_cases h : j = k
  · subst h; simp [getE_setE_same, hv]
  · simp [h, getE_setE_ne _ _ _ _ h]

theorem getE_mem {l : List Entry} {k : w64} (h : getE l k ≠ []) :
    ∃ e ∈ l, e.K' = k ∧ e.V' = getE l k := by
  induction l with
  | nil => exact absurd rfl h
  | cons e es ih =>
    by_cases he : e.K' = k
    · exact ⟨e, List.mem_cons_self, he, by simp [getE, he]⟩
    · simp only [getE, he, ↓reduceIte] at h ⊢
      obtain ⟨e', h1, h2, h3⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ h1, h2, h3⟩

theorem getE_of_mem {l : List Entry} (hn : (l.map Entry.K').Nodup) {e : Entry} (he : e ∈ l) :
    getE l e.K' = e.V' := by
  induction l with
  | nil => cases he
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 he with rfl | h
    · simp [getE]
    · have hne : x.K' ≠ e.K' := fun h' => hn.1 (h' ▸ List.mem_map_of_mem h)
      simp only [getE, hne, ↓reduceIte, ih hn.2 h]

/-- A well-formed Go configuration: its keys distinct, its values non-empty and bounded (puts'),
its pending inputs puts. -/
def GOk (g : GC) : Prop :=
  (g.1.map Entry.K').Nodup ∧ (∀ e ∈ g.1, e.V' ≠ [] ∧ e.V'.length < 2 ^ 15) ∧
    ∀ i ∈ g.2, isPut i.1 = true

theorem valsOk_absKv {g : GC} (h : GOk g) : valsOk (absKv g.1) := by
  intro k v hk
  unfold absKv at hk
  split at hk
  · cases hk
  · rename_i hne
    cases hk
    obtain ⟨e, he, -, hv⟩ := getE_mem hne
    rw [← hv]; exact h.2.1 e he

theorem GOk_setE {kv : List Entry} {P : List EIn} (h : GOk (kv, P)) (k : w64) (v : GoString)
    (hv : v ≠ [] ∧ v.length < 2 ^ 15) (P' : List EIn) (hP : ∀ i ∈ P', isPut i.1 = true) :
    GOk (setE kv k v, P') := by
  refine ⟨?_, ?_, hP⟩
  · unfold setE
    rw [List.map_append, List.nodup_append]
    refine ⟨(h.1.sublist ((List.filter_sublist).map _)), by split <;> simp, ?_⟩
    intro a ha b hb
    split at hb
    · cases hb
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      simp only [List.mem_filter] at he
      intro h'; simp [h'] at he
  · intro e he
    unfold setE at he
    rcases List.mem_append.1 he with h1 | h1
    · exact h.2.1 e (List.mem_filter.1 h1).1
    · split at h1
      · cases h1
      · simp only [List.mem_singleton] at h1; subst h1; exact hv

/-- `reads(c, k, last, out)` with `m` keys (`k..last`): every configuration reachable from `c` by
letting pending puts on the keys take effect (each key at most one) whose values give `out`. -/
def readsG : Nat → GC → w64 → GoString → List GC
  | 0, c, _, out => if out = [] then [c] else []
  | n + 1, c, k, out =>
    (if getE c.1 k <+: out then readsG n c (k + 1) (out.drop (getE c.1 k).length) else []) ++
    (List.range c.2.length).flatMap (fun j =>
      match c.2[j]? with
      | some p =>
        if (inE p).K' = k ∧ (inE p).V' <+: out then
          readsG n (setE c.1 k (inE p).V', c.2.eraseIdx j) (k + 1) (out.drop (inE p).V'.length)
        else []
      | none => [])

/-- `stepConfig(c, in, Out{u, w})`. -/
def stepCG (g : GC) (i : EIn) (u : Bool) (w : GoString) : List GC :=
  if u then (if isPut i.1 then [(g.1, g.2 ++ [i])] else [g])
  else match i.1 with
    | .put k v => if w = [] then [(setE g.1 k v, g.2)] else []
    | .get k => readsG 1 g k w
    | .scan k n => readsG (n.toNat + 1) g k w

/-- `sameEntries(a, b)`. -/
def sameEntriesG (a b : List Entry) : Bool :=
  a.length == b.length && a.all (fun e => decide (getE b e.K' = e.V'))

/-- `samePend(a, b)` (on the pending puts; `inE` is injective). -/
def samePendG (a b : List EIn) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

/-- `sameConfig(a, b)`. -/
def sameConfigG (a b : GC) : Bool := sameEntriesG a.1 b.1 && samePendG a.2 b.2

/-- `member(s, c)`. -/
def memberG (s : List GC) (c : GC) : Bool := s.any (fun x => sameConfigG x c)

/-- `addAll(s, cs)`. -/
def addAllG (s cs : List GC) : List GC :=
  cs.foldl (fun s c => if memberG s c then s else s ++ [c]) s

/-- `step(s, in, Out{u, w})`'s next state (its verdict: not empty). -/
def stepG (G : List GC) (i : EIn) (u : Bool) (w : GoString) : List GC :=
  G.foldl (fun r g => addAllG r (stepCG g i u w)) []

/-! ### `sameConfig` is sound -/

theorem List.Nodup.of_map' {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    exact List.nodup_cons.2 ⟨fun hx => h.1 x hx rfl, ih h.2⟩

theorem samePendG_perm {a b : List EIn} (h : samePendG a b = true) : a.Perm b := by
  simp only [samePendG, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  have hs : a.Subperm b := List.subperm_ext_iff.2 fun x hx => by
    have := h.2 x hx; omega
  exact hs.perm_of_length_le (by omega)

theorem sameEntriesG_eq {a b : List Entry} (ha : (a.map Entry.K').Nodup)
    (hb : (b.map Entry.K').Nodup) (hva : ∀ e ∈ a, e.V' ≠ [])
    (h : sameEntriesG a b = true) : absKv a = absKv b := by
  simp only [sameEntriesG, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  have hsub : a ⊆ b := by
    intro e he
    have h1 := h.2 e he
    obtain ⟨e', he', h2, h3⟩ := getE_mem (l := b) (k := e.K') (by rw [h1]; exact hva e he)
    have : e' = e := by
      cases e; cases e'; simp only at h2 h3 h1; rw [h3, h1, h2]
    exact this ▸ he'
  have hp : a.Perm b := (List.subperm_of_subset (List.Nodup.of_map' Entry.K' ha) hsub).perm_of_length_le (by omega)
  have hk : ∀ k, getE a k = getE b k := by
    intro k
    by_cases hm : k ∈ a.map Entry.K'
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      rw [getE_of_mem ha he, getE_of_mem hb (hsub he)]
    · rw [getE_not_mem hm, getE_not_mem (fun h' => hm ((hp.map _).mem_iff.2 h'))]
  funext k; simp only [absKv, hk]

/-- Two configurations `sameConfig` reports the same stand for the same configuration. -/
theorem sameConfigG_sound {a b : GC} (ha : GOk a) (hb : GOk b) (h : sameConfigG a b = true) :
    absKv a.1 = absKv b.1 ∧ a.2.Perm b.2 := by
  simp only [sameConfigG, Bool.and_eq_true] at h
  exact ⟨sameEntriesG_eq ha.1 hb.1 (fun e he => (ha.2.1 e he).1) h.1, samePendG_perm h.2⟩

/-! ### `addAll` and `step`: what the next state holds -/

theorem addAllG_mem {s cs : List GC} {x : GC} (h : x ∈ addAllG s cs) : x ∈ s ∨ x ∈ cs := by
  induction cs generalizing s with
  | nil => exact .inl h
  | cons c cs ih =>
    simp only [addAllG, List.foldl_cons] at h
    rcases ih h with h1 | h1
    · split at h1
      · exact .inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact .inl h2
        · simp only [List.mem_singleton] at h2; exact .inr (h2 ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h1)

theorem addAllG_sub {s cs : List GC} {x : GC} (h : x ∈ s) : x ∈ addAllG s cs := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih =>
    simp only [addAllG, List.foldl_cons]
    apply ih
    split
    · exact h
    · exact List.mem_append_left _ h

theorem addAllG_cover {s cs : List GC} {c : GC} (h : c ∈ cs) :
    ∃ x ∈ addAllG s cs, x = c ∨ sameConfigG x c = true := by
  induction cs generalizing s with
  | nil => cases h
  | cons c' cs ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp only [addAllG, List.foldl_cons]
      split
      · rename_i hm
        obtain ⟨x, hx, hx'⟩ := List.any_eq_true.1 hm
        exact ⟨x, addAllG_sub (by simpa using hx), .inr hx'⟩
      · exact ⟨c, addAllG_sub (List.mem_append_right _ (List.mem_singleton_self c)), .inl rfl⟩
    · exact ih h

theorem stepG_foldl_mem (G : List GC) (i : EIn) (u : Bool) (w : GoString) :
    ∀ (r : List GC) (x : GC), x ∈ G.foldl (fun r g => addAllG r (stepCG g i u w)) r →
      x ∈ r ∨ ∃ g ∈ G, x ∈ stepCG g i u w := by
  induction G with
  | nil => intro r x h; exact .inl h
  | cons g G ih =>
    intro r x h
    simp only [List.foldl_cons] at h
    rcases ih _ x h with h1 | ⟨g', hg', h1⟩
    · rcases addAllG_mem h1 with h2 | h2
      · exact .inl h2
      · exact .inr ⟨g, List.mem_cons_self, h2⟩
    · exact .inr ⟨g', List.mem_cons_of_mem _ hg', h1⟩

theorem stepG_foldl_sub (G : List GC) (i : EIn) (u : Bool) (w : GoString) :
    ∀ (r : List GC) (x : GC), x ∈ r → x ∈ G.foldl (fun r g => addAllG r (stepCG g i u w)) r := by
  induction G with
  | nil => intro r x h; exact h
  | cons g G ih => intro r x h; exact ih _ x (addAllG_sub h)

theorem stepG_mem {G : List GC} {i : EIn} {u : Bool} {w : GoString} {x : GC}
    (h : x ∈ stepG G i u w) : ∃ g ∈ G, x ∈ stepCG g i u w := by
  rcases stepG_foldl_mem G i u w [] x h with h1 | h1
  · cases h1
  · exact h1

theorem stepG_cover {G : List GC} {i : EIn} {u : Bool} {w : GoString} {g c : GC} (hg : g ∈ G)
    (hc : c ∈ stepCG g i u w) : ∃ x ∈ stepG G i u w, x = c ∨ sameConfigG x c = true := by
  unfold stepG
  generalize ([] : List GC) = r
  induction G generalizing r with
  | nil => cases hg
  | cons g' G ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hg with rfl | hg
    · obtain ⟨x, hx, hx'⟩ := addAllG_cover (s := r) hc
      exact ⟨x, stepG_foldl_sub G i u w _ x hx, hx'⟩
    · exact ih hg _

/-! ### `reads` -/

theorem eraseIdx_perm_erase {α : Type} [DecidableEq α] {l : List α} {j : Nat} {p : α}
    (h : l[j]? = some p) : (l.eraseIdx j).Perm (l.erase p) := by
  have hj : j < l.length := (List.getElem?_eq_some_iff.1 h).1
  have hp : l[j] = p := (List.getElem?_eq_some_iff.1 h).2
  have hl : l = l.take j ++ p :: l.drop (j + 1) := by
    have := List.take_append_drop j l
    rw [List.drop_eq_getElem_cons hj, hp] at this
    exact this.symm
  have h1 : (p :: l.eraseIdx j).Perm l := by
    rw [List.eraseIdx_eq_take_drop_succ]
    refine List.perm_middle.symm.trans ?_
    rw [← hl]
  exact List.Perm.cons_inv (h1.trans (List.perm_cons_erase (List.mem_of_getElem? h)))

theorem inE_put {i : EIn} {k : w64} {v : GoString} (h : i.1 = .put k v) :
    inE i = In.mk (W8 0) k (W64 0) v := by
  simp [inE, h, inOf]

/-- **What `reads` returns** is reached by late effects, and its keys' values give `out`. -/
theorem readsG_sound : ∀ (m : Nat) (g : GC) (k : w64) (out : GoString) (g' : GC),
    m < 2 ^ 64 → GOk g → g' ∈ readsG m g k out →
    GOk g' ∧ PReach epB (absC g) (absC g') ∧ catV (absKv g'.1) (keysFrom k m) = out ∧
      ∀ j, j ∉ keysFrom k m → absKv g'.1 j = absKv g.1 j
  | 0, g, k, out, g', _, hg, h => by
    simp only [readsG] at h
    split at h
    · rename_i ho
      simp only [List.mem_singleton] at h
      subst h ho
      exact ⟨hg, .refl _, rfl, fun _ _ => rfl⟩
    · cases h
  | m + 1, g, k, out, g', hm, hg, h => by
    simp only [readsG, List.mem_append, List.mem_flatMap, List.mem_range] at h
    rcases h with h | ⟨j, hj, h⟩
    · split at h
      · rename_i hpre
        obtain ⟨h1, h2, h3, h4⟩ := readsG_sound m g (k + 1) _ g' (by omega) hg h
        refine ⟨h1, h2, ?_, ?_⟩
        · rw [keysFrom, catV_cons, h3, h4 k (self_not_mem_keysFrom k m (by omega)), absKv_getD]
          obtain ⟨t, rfl⟩ := hpre
          simp
        · intro j hj
          simp only [keysFrom, List.mem_cons, not_or] at hj
          exact h4 j hj.2
      · cases h
    · obtain ⟨p, hp⟩ : ∃ p, g.2[j]? = some p := ⟨g.2[j], List.getElem?_eq_getElem hj⟩
      rw [hp] at h
      dsimp only at h
      split at h
      · rename_i hc
        have hpm : p ∈ g.2 := List.mem_of_getElem? hp
        obtain ⟨k', v, hkv⟩ := pin_inv (hg.2.2 p hpm)
        rw [inE_put hkv] at hc h
        obtain ⟨hk, hpre⟩ := hc
        simp only at hk hpre h
        subst hk
        have hpv : inPre (.put k' v) := hkv ▸ p.2
        have hd : GOk (setE g.1 k' v, g.2.eraseIdx j) :=
          GOk_setE hg k' v ⟨hpv.2.1, hpv.2.2⟩ _
            (fun i hi => hg.2.2 i (List.mem_of_mem_eraseIdx hi))
        obtain ⟨h1, h2, h3, h4⟩ := readsG_sound m _ (k' + 1) _ g' (by omega) hd h
        have hk' := self_not_mem_keysFrom k' m (by omega)
        refine ⟨h1, ?_, ?_, ?_⟩
        · refine .step (.apply (absC g) p hpm) (.step (.perm _ (g.2.eraseIdx j)
            (eraseIdx_perm_erase hp)) ?_)
          simp only [absC, step_put' p hkv]
          rw [← absKv_setE _ _ _ hpv.2.1]
          exact h2
        · rw [keysFrom, catV_cons, h3, h4 k' hk', absKv_setE _ _ _ hpv.2.1, upd_get]
          obtain ⟨t, rfl⟩ := hpre
          simp
        · intro j' hj'
          simp only [keysFrom, List.mem_cons, not_or] at hj'
          rw [h4 j' hj'.2, absKv_setE _ _ _ hpv.2.1, upd_ne _ _ _ _ hj'.1]
      · cases h

/-! ### The bracket -/

/-- The configurations reachable from a Go configuration's. -/
def Funl (g : GC) : PSet KvS EIn := fun c => PReach epB (absC g) c

/-- The configurations reachable from a Go configuration's store with some of its pending puts
pending. -/
def Fall (g : GC) : PSet KvS EIn := fun c => ∃ Q, Q.Subperm g.2 ∧ PReach epB ⟨absKv g.1, Q⟩ c

/-- **The Go state `G` brackets the model's set `S`** (see the file header). -/
def Sim (G : List GC) (S : PSet KvS EIn) : Prop :=
  (∀ g ∈ G, ∀ c, Funl g c → S c) ∧ (∀ c, S c → ∃ g ∈ G, Fall g c) ∧ ∀ g ∈ G, GOk g

theorem Fall_reach {g : GC} {c c' : PCfg KvS EIn} (h : Fall g c) (hr : PReach epB c c') :
    Fall g c' := by
  obtain ⟨Q, hQ, h⟩ := h
  exact ⟨Q, hQ, h.trans hr⟩

theorem Fall_same {g g' : GC} (hg : GOk g) (hg' : GOk g') (h : sameConfigG g g' = true)
    {c : PCfg KvS EIn} (hc : Fall g' c) : Fall g c := by
  obtain ⟨e1, e2⟩ := sameConfigG_sound hg hg' h
  obtain ⟨Q, hQ, hr⟩ := hc
  exact ⟨Q, hQ.trans e2.symm.subperm, by rw [e1]; exact hr⟩

theorem valsOk_Fall {g : GC} (hg : GOk g) {c : PCfg KvS EIn} (hc : Fall g c) : valsOk c.st := by
  obtain ⟨Q, -, hr⟩ := hc
  exact valsOk_reach hr (valsOk_absKv hg)

/-- **What `reads` may return**: a configuration reached by late effects is in some returned
one's bracket. -/
theorem readsG_complete : ∀ (m : Nat) (g : GC) (k : w64) (Q : List EIn) (c : PCfg KvS EIn),
    m < 2 ^ 64 → GOk g → Q.Subperm g.2 → PReach epB ⟨absKv g.1, Q⟩ c →
    ∃ g' ∈ readsG m g k (catV c.st (keysFrom k m)), Fall g' c
  | 0, g, k, Q, c, _, hg, hQ, hr => ⟨g, by simp [readsG, keysFrom, catV], Q, hQ, hr⟩
  | m + 1, g, k, Q, c, hm, hg, hQ, hr => by
    rw [keysFrom, catV_cons]
    rcases reach_key k hr with h1 | ⟨x, i, hx, hi, him, Q₂, hQ₂, hr₂⟩
    · obtain ⟨g', hg', hf⟩ := readsG_complete m g (k + 1) Q c (by omega) hg hQ hr
      refine ⟨g', ?_, hf⟩
      simp only [readsG, List.mem_append]
      left
      simp only [h1, absKv_getD]
      rw [if_pos (List.prefix_append _ _), List.drop_left]
      exact hg'
    · have hig : i ∈ g.2 := hQ.subset him
      have hj : g.2[g.2.idxOf i]? = some i := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨List.idxOf_lt_length_of_mem hig, List.getElem_idxOf (List.idxOf_lt_length_of_mem hig)⟩
      have hpv : inPre (.put k x) := hi ▸ i.2
      have hd : GOk (setE g.1 k x, g.2.eraseIdx (g.2.idxOf i)) :=
        GOk_setE hg k x ⟨hpv.2.1, hpv.2.2⟩ _
          (fun i hi => hg.2.2 i (List.mem_of_mem_eraseIdx hi))
      have hQd : Q₂.Subperm (g.2.eraseIdx (g.2.idxOf i)) :=
        hQ₂.trans ((hQ.erase i).trans (eraseIdx_perm_erase hj).symm.subperm)
      have hrd : PReach epB ⟨absKv (setE g.1 k x), Q₂⟩ c := by
        rw [absKv_setE _ _ _ hpv.2.1]; exact hr₂
      obtain ⟨g', hg', hf⟩ := readsG_complete m _ (k + 1) Q₂ c (by omega) hd hQd hrd
      refine ⟨g', ?_, hf⟩
      simp only [readsG, List.mem_append, List.mem_flatMap, List.mem_range]
      right
      refine ⟨g.2.idxOf i, List.idxOf_lt_length_of_mem hig, ?_⟩
      rw [hj]
      dsimp only
      rw [inE_put hi, if_pos ⟨rfl, by rw [hx]; exact List.prefix_append _ _⟩]
      simp only [hx, Option.getD_some, List.drop_left]
      exact hg'

/-! ### One configuration's step -/

/-- A porcupine answer `Out{u, w}`, as the store's. -/
def ansOf (u : Bool) (w : BStr) : Ans BStr := if u then .err else .ok w

theorem pstep_inv {c c₁ : PCfg KvS EIn} {i : EIn} {o : Ans BStr} (h : PStep epB c i o c₁) :
    (o = .ok (epB.step i c.st).2 ∧ c₁ = ⟨(epB.step i c.st).1, c.pend⟩) ∨
    (o = .err ∧ isPut i.1 = true ∧ c₁ = ⟨c.st, i :: c.pend⟩) ∨
    (o = .err ∧ isPut i.1 = false ∧ c₁ = c) := by
  cases h with
  | ok => exact .inl ⟨rfl, rfl⟩
  | errW hw _ => exact .inr (.inl ⟨rfl, hw, rfl⟩)
  | errR hw _ => exact .inr (.inr ⟨rfl, hw, rfl⟩)
  | obs _ hob _ => exact absurd hob (by simp [epB])

theorem length_keysFrom (k : w64) (m : Nat) : (keysFrom k m).length = m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => simp [keysFrom, ih]

theorem GOk_step {g g' : GC} (hg : GOk g) {i : EIn} {u : Bool} {w : GoString}
    (h : g' ∈ stepCG g i u w) : GOk g' := by
  cases u
  · obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i
    · exact (readsG_sound 1 g k w g' (by omega) hg h).1
    · simp only [stepCG, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h
        exact GOk_setE hg k v ⟨hi.2.1, hi.2.2⟩ _ hg.2.2
      · cases h
    · simp only [inPre] at hi
      exact (readsG_sound (n.toNat + 1) g k w g' (by omega) hg h).1
  · simp only [stepCG, ↓reduceIte] at h
    split at h
    · rename_i hp
      simp only [List.mem_singleton] at h; subst h
      refine ⟨hg.1, hg.2.1, fun j hj => ?_⟩
      rcases List.mem_append.1 hj with hj | hj
      · exact hg.2.2 j hj
      · simp only [List.mem_singleton] at hj; subst hj; exact hp
    · simp only [List.mem_singleton] at h; subst h; exact hg

theorem read_low {g g' : GC} (hg : GOk g) {i : EIn} {k : w64} {m : Nat} (hm : m < 2 ^ 64)
    (hst : ∀ σ, epB.step i σ = (σ, bnd (catV σ (keysFrom k m)))) {w : BStr}
    (h : g' ∈ readsG m g k w.1) {c' : PCfg KvS EIn} (hc' : Funl g' c') :
    ∃ c c₁, Funl g c ∧ PStep epB c i (.ok w) c₁ ∧ PReach epB c₁ c' := by
  obtain ⟨-, h2, h3, -⟩ := readsG_sound m g k w.1 g' hm hg h
  refine ⟨absC g', absC g', h2, ?_, hc'⟩
  have := PStep.ok (P := epB) (absC g') i rfl
  rw [hst] at this
  simpa [absC, h3, bnd_val] using this

theorem read_up {g : GC} (hg : GOk g) {i : EIn} {k : w64} {m : Nat} (hm : m ≤ 2)
    (hst : ∀ σ, epB.step i σ = (σ, bnd (catV σ (keysFrom k m)))) {w : BStr}
    {c c₁ : PCfg KvS EIn} (hc : Fall g c) (hs : PStep epB c i (.ok w) c₁) :
    ∃ g' ∈ readsG m g k w.1, Fall g' c₁ := by
  rcases pstep_inv hs with ⟨he, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · rw [hst] at he ⊢
    simp only [Ans.ok.injEq] at he
    have hlen := catV_len c.st (valsOk_Fall hg hc) (keysFrom k m)
    rw [length_keysFrom] at hlen
    rw [bnd_of (by omega)] at he
    have hw : w.1 = catV c.st (keysFrom k m) := by rw [he]
    rw [hw]
    obtain ⟨Q, hQ, hr⟩ := hc
    exact readsG_complete m g k Q c (by omega) hg hQ hr
  · cases he
  · cases he

/-- **One configuration's step, from below**: what `stepConfig` returns is reached by the step. -/
theorem cfg_low {g g' : GC} (hg : GOk g) (i : EIn) (u : Bool) (w : BStr)
    (h : g' ∈ stepCG g i u w.1) {c' : PCfg KvS EIn} (hc' : Funl g' c') :
    ∃ c c₁, Funl g c ∧ PStep epB c i (ansOf u w) c₁ ∧ PReach epB c₁ c' := by
  cases u
  · simp only [ansOf, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i
    · exact read_low hg (by omega) (fun σ => read_out_get k hi σ) h hc'
    · simp only [stepCG, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i hw
        simp only [List.mem_singleton] at h; subst h
        have hw' : w = bnd [] := by rw [← hw, bnd_val]
        refine ⟨absC g, ⟨upd (absKv g.1) k v, g.2⟩, .refl _, ?_, ?_⟩
        · have := PStep.ok (P := epB) (absC g) ⟨.put k v, hi⟩ rfl
          simpa [hw', step_put, absC] using this
        · have e := absKv_setE g.1 k v hi.2.1
          simpa [Funl, absC, e] using hc'
      · cases h
    · simp only [inPre] at hi
      exact read_low hg (by omega) (fun σ => read_out_scan k n hi σ) h hc'
  · simp only [stepCG, ansOf, ↓reduceIte] at h ⊢
    split at h
    · rename_i hp
      simp only [List.mem_singleton] at h; subst h
      exact ⟨absC g, ⟨absKv g.1, i :: g.2⟩, .refl _, .errW _ _ hp rfl,
        .step (.perm _ _ (List.perm_append_singleton _ _)) hc'⟩
    · rename_i hp
      simp only [List.mem_singleton] at h; rw [h] at hc'
      exact ⟨absC g, absC g, .refl _, .errR _ _ (by simpa [epB] using hp) rfl, hc'⟩

/-- **One configuration's step, from above**: a configuration the step reaches is in the bracket
of some configuration `stepConfig` returns. -/
theorem cfg_up {g : GC} (hg : GOk g) (i : EIn) (u : Bool) (w : BStr) {c c₁ : PCfg KvS EIn}
    (hc : Fall g c) (hs : PStep epB c i (ansOf u w) c₁) : ∃ g' ∈ stepCG g i u w.1, Fall g' c₁ := by
  cases u
  · simp only [ansOf, Bool.false_eq_true, ↓reduceIte] at hs
    obtain ⟨k | ⟨k, v⟩ | ⟨k, n⟩, hi⟩ := i
    · obtain ⟨g', h1, h2⟩ := read_up hg (by omega) (fun σ => read_out_get k hi σ) hc hs
      exact ⟨g', by simpa [stepCG] using h1, h2⟩
    · rcases pstep_inv hs with ⟨he, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
      · rw [step_put] at he ⊢
        simp only [Ans.ok.injEq] at he
        have hw : w.1 = [] := by rw [he, bnd_of (by simp)]
        obtain ⟨Q, hQ, hr⟩ := hc
        obtain ⟨Q₂, hQ₂, hr₂⟩ := reach_put k v hr
        refine ⟨(setE g.1 k v, g.2), by simp [stepCG, hw], Q₂, hQ₂.trans hQ, ?_⟩
        rw [absKv_setE _ _ _ hi.2.1]; exact hr₂
      · cases he
      · cases he
    · have hn : n.toNat + 1 ≤ 2 := by simp only [inPre] at hi; omega
      obtain ⟨g', h1, h2⟩ := read_up hg hn (fun σ => read_out_scan k n hi σ) hc hs
      exact ⟨g', by simpa [stepCG] using h1, h2⟩
  · simp only [ansOf, ↓reduceIte] at hs
    rcases pstep_inv hs with ⟨he, _⟩ | ⟨_, hp, rfl⟩ | ⟨_, hp, rfl⟩
    · cases he
    · obtain ⟨Q, hQ, hq⟩ := hc
      refine ⟨(g.1, g.2 ++ [i]), by simp [stepCG, hp], i :: Q, ?_, reach_cons i hq⟩
      exact ((List.subperm_cons _).2 hQ).trans (List.perm_append_singleton _ _).symm.subperm
    · exact ⟨g, by simp [stepCG, hp], hc⟩

/-! ### The simulation -/

theorem absKv_nil : absKv ([] : List Entry) = epB.init := by
  funext k; simp [absKv, getE, epB]

/-- `State{Config{}}` brackets the initial set. -/
theorem sim_init : Sim [([], [])] (pInit epB) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg c h
    simp only [List.mem_singleton] at hg; subst hg
    show c = ⟨epB.init, []⟩
    have h' : PReach epB ⟨epB.init, []⟩ c := by simpa [Funl, absC, absKv_nil] using h
    suffices ∀ c₀ c', PReach epB c₀ c' → c₀.pend = [] → c' = c₀ from this _ _ h' rfl
    intro c₀ c' hr
    induction hr with
    | refl => intro _; rfl
    | @step c c₁ c₂ hs _ ih =>
      intro hp
      cases hs with
      | apply j hj => simp [hp] at hj
      | perm p hq =>
        rw [hp] at hq
        have := hq.eq_nil
        subst this
        rw [ih rfl, ← hp]
  · intro c h
    refine ⟨([], []), List.mem_singleton_self _, [], List.Subperm.refl _, ?_⟩
    rw [show c = ⟨epB.init, []⟩ from h, absKv_nil]
    exact .refl _
  · intro g hg
    simp only [List.mem_singleton] at hg; subst hg
    exact ⟨List.nodup_nil, nofun, nofun⟩

/-- **The simulation**: on a bracketed set, the model allows `(i, Out{u, w})` exactly when `step`'s
next state is not empty, and that state brackets the model's next set. -/
theorem sim_step {G : List GC} {S : PSet KvS EIn} (hS : Sim G S) (i : EIn) (u : Bool)
    (w : BStr) :
    ((pSeq epB).step S (i, ansOf u w)).isSome = !(stepG G i u w.1).isEmpty ∧
    ∀ S', (pSeq epB).step S (i, ansOf u w) = some S' → Sim (stepG G i u w.1) S' := by
  have hok : ∀ x ∈ stepG G i u w.1, GOk x := fun x hx => by
    obtain ⟨g, hg, hx⟩ := stepG_mem hx
    exact GOk_step (hS.2.2 g hg) hx
  have hlow : ∀ x ∈ stepG G i u w.1, ∀ c', Funl x c' → ppost epB S i (ansOf u w) c' := by
    intro x hx c' hc'
    obtain ⟨g, hg, hx⟩ := stepG_mem hx
    obtain ⟨c, c₁, h1, h2, h3⟩ := cfg_low (hS.2.2 g hg) i u w hx hc'
    exact ⟨c, c, c₁, hS.1 g hg c h1, .refl _, h2, h3⟩
  have hup : ∀ c', ppost epB S i (ansOf u w) c' → ∃ x ∈ stepG G i u w.1, Fall x c' := by
    rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
    obtain ⟨g, hg, hf⟩ := hS.2.1 c₀ h0
    obtain ⟨g', hg', hf'⟩ := cfg_up (hS.2.2 g hg) i u w (Fall_reach hf hr) hs
    obtain ⟨x, hx, hx'⟩ := stepG_cover hg hg'
    refine ⟨x, hx, ?_⟩
    rcases hx' with rfl | hx'
    · exact Fall_reach hf' hr'
    · exact Fall_same (hok x hx) (GOk_step (hS.2.2 g hg) hg') hx' (Fall_reach hf' hr')
  have hne : (∃ c, ppost epB S i (ansOf u w) c) ↔ stepG G i u w.1 ≠ [] := by
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx, -⟩ := hup c hc
      exact List.ne_nil_of_mem hx
    · intro h
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
      exact ⟨_, hlow x hx _ (.refl _)⟩
  refine ⟨?_, ?_⟩
  · simp only [pSeq]
    by_cases h : ∃ c, ppost epB S i (ansOf u w) c
    · rw [if_pos h]
      have := hne.1 h
      cases hR : stepG G i u w.1 with
      | nil => exact absurd hR this
      | cons _ _ => rfl
    · rw [if_neg h]
      have : stepG G i u w.1 = [] := Classical.byContradiction fun h' => h (hne.2 h')
      rw [this]; rfl
  · intro S' hs
    have := pSeq_step_some hs
    subst this
    exact ⟨hlow, hup, hok⟩

end go

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
