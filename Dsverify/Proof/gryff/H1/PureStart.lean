/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureStart.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: pure facts for `StartRead` (the `range c.wops` loop: any order).
-/
module

public import Dsverify.Proof.gryff.H1.Pure
public import Dsverify.Proof.gryff.H1.Defs

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- How many of `L`'s writes (not yet in their Write2 round) are op `j`. -/
def rdCnt (L : List WriteOp) (j : w32) : Nat :=
  (L.filter (fun w => !w.sentWrite2Round && w.n == j)).length

/-- An `OngoingReqs` entry with `c` copies of the read `n` appended to `ShortReads`. -/
def rdApp (n : w32) (c : Nat) (op : OngoingOp) : OngoingOp :=
  { op with shortReads := op.shortReads ++ List.replicate c n }

/-- `or` is `or0` after the loop visited `L` (pointwise). -/
def rdChar (n : w32) (or0 or : AMap 32 OngoingOp) (L : List WriteOp) : Prop :=
  ∀ j, or.get? j = (or0.get? j).map (rdApp n (rdCnt L j))

theorem rdChar_nil (n : w32) (or0 : AMap 32 OngoingOp) : rdChar n or0 or0 [] := by
  intro j; cases or0.get? j <;> simp [rdCnt, rdApp]

theorem rdChar_sent (n : w32) (or0 or : AMap 32 OngoingOp) (L : List WriteOp) (w : WriteOp)
    (h : rdChar n or0 or L) (hs : w.sentWrite2Round = true) : rdChar n or0 or (L ++ [w]) := by
  intro j; rw [h j]; simp [rdCnt, hs]

theorem rdChar_step (n : w32) (or0 or : AMap 32 OngoingOp) (L : List WriteOp) (w : WriteOp)
    (op : OngoingOp) (h : rdChar n or0 or L) (hs : w.sentWrite2Round = false)
    (hop : or.get? w.n = some op) :
    rdChar n or0 (or.put w.n { op with shortReads := op.shortReads ++ [n] }) (L ++ [w]) := by
  intro j
  rw [amap_put_get]
  by_cases hj : j = w.n
  · subst hj
    rw [h] at hop
    cases h0 : or0.get? w.n with
    | none => rw [h0] at hop; cases hop
    | some op0 =>
      rw [h0] at hop; simp only [Option.map_some, Option.some.injEq] at hop; subst hop
      simp [rdApp, rdCnt, hs, List.replicate_succ']
  · rw [if_neg hj, h j]
    have : rdCnt (L ++ [w]) j = rdCnt L j := by
      simp [rdCnt, List.filter_append]
      intro _ h'; exact absurd h'.symm hj
    rw [this]

theorem rdChar_isSome (n : w32) (or0 or : AMap 32 OngoingOp) (L : List WriteOp)
    (h : rdChar n or0 or L) (j : w32) : (or.get? j).isSome = (or0.get? j).isSome := by
  rw [h j]; cases or0.get? j <;> rfl

theorem rdCnt_perm (L L' : List WriteOp) (hp : L.Perm L') (j : w32) : rdCnt L j = rdCnt L' j := by
  unfold rdCnt; exact (hp.filter _).length_eq

theorem rdChar_perm (n : w32) (or0 or : AMap 32 OngoingOp) (L L' : List WriteOp)
    (hp : L.Perm L') (h : rdChar n or0 or L) : rdChar n or0 or L' := by
  intro j; rw [h j, rdCnt_perm L L' hp j]

theorem filterMap_congr' {α β : Type} (f g : α → Option β) (l : List α)
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filterMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem lookup_isSome_iff {α β : Type} [DecidableEq α] (l : List (α × β)) (k : α) :
    (l.lookup k).isSome ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [List.lookup]
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    by_cases h : k = a
    · subst h; simp [List.lookup]
    · have : (k == a) = false := by simpa using h
      simp [List.lookup, this, ih, h]

/-- A list's values, looked up by its (distinct) keys. -/
theorem filterMap_lookup {α β : Type} [DecidableEq α] (l : List (α × β))
    (hnd : (l.map Prod.fst).Nodup) : (l.map Prod.fst).filterMap (fun k => l.lookup k) = l.map Prod.snd := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    simp only [List.map_cons, List.filterMap_cons, List.lookup, beq_self_eq_true]
    congr 1
    rw [← ih hnd]
    apply filterMap_congr'
    intro x hx
    have : (x == a) = false := by
      simp only [beq_eq_false_iff_ne]; rintro rfl; exact ha hx
    simp [this]

theorem keys_perm {β : Type} (l : List (w64 × β)) (hnd : (l.map Prod.fst).Nodup)
    (keys : List w64) (hk : ∀ k, k ∈ keys ↔ (AMap.get? l k).isSome) (hknd : keys.Nodup) :
    (keys.filterMap (fun k => AMap.get? l k)).Perm (l.map Prod.snd) := by
  have hp : keys.Perm (l.map Prod.fst) := by
    rw [List.perm_ext_iff_of_nodup hknd hnd]
    intro k
    rw [hk k]
    unfold AMap.get?
    exact lookup_isSome_iff l k
  have := hp.filterMap (fun k => AMap.get? l k)
  unfold AMap.get? at this ⊢
  rw [filterMap_lookup l hnd] at this
  exact this

/-- An invariant of a `for` loop in `Except` whose body always continues. -/
theorem forIn_inv {α σ ε : Type} (P : List α → σ → Prop) (body : α → σ → Except ε (ForInStep σ))
    (hstep : ∀ Lacc a s r, P Lacc s → body a s = .ok r → ∃ s', r = .yield s' ∧ P (Lacc ++ [a]) s') :
    ∀ (rest Lacc : List α) (init v : σ), P Lacc init → forIn rest init body = .ok v →
      P (Lacc ++ rest) v := by
  intro rest
  induction rest with
  | nil =>
    intro Lacc init v hP h
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simpa using hP
  | cons a t ih =>
    intro Lacc init v hP h
    simp only [List.forIn_cons, bind, Except.bind] at h
    cases hb : body a init with
    | error e => rw [hb] at h; cases h
    | ok r =>
      rw [hb] at h
      obtain ⟨s', rfl, hP'⟩ := hstep Lacc a init r hP hb
      have := ih (Lacc ++ [a]) s' v hP' h
      simpa using this

/-- What `stepClientRead` does (key 0). -/
theorem stepClientRead_inv (s s' : RState) (rid cid : w32) (d : Dep) (outs : List Out)
    (h : stepClientRead s rid cid 0 d = .ok (s', outs)) :
    s'.maxN = s.maxN + 1 ∧
    s'.rops = s.rops.put (shiftInts rid cid)
      { requestId := rid, clientId := cid, n := s.maxN + 1, maxValTag := none, readValTag := none,
        numRead1Replies := 1, numRead2Replies := 0, readsWithMaxTag := 0, sentRead2Round := false,
        determinedReadVal := false, replicasWithMaxTag := [] } ∧
    s'.wops = s.wops ∧ s'.storeVT = s.storeVT ∧
    rdChar (s.maxN + 1) (s.ongoingReqs.put (s.maxN + 1)
        { requestId := rid, clientId := cid, isRead := true, shortReads := [] })
      s'.ongoingReqs (s.wops.map Prod.snd) ∧
    (∀ w ∈ s.wops.map Prod.snd, w.sentWrite2Round = false →
      ((s.ongoingReqs.put (s.maxN + 1)
        { requestId := rid, clientId := cid, isRead := true, shortReads := [] }).get? w.n).isSome) ∧
    List.mapM (fun q => sendPeer s q
      (.read1 { requestId := rid, clientId := cid, k := 0, d := dep0, replicaId := s.id,
                vt := s.storeVT })) (([0, 1, 2] : List w32).filter (fun i => i ≠ s.id)) = some outs := by
  unfold stepClientRead at h
  simp only [bind, Except.bind, pure, Except.pure, never, disabled, dead, FailM.failNever,
    FailM.failDisabled, FailM.failDead] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i v hv
  split at h
  rotate_left
  · cases h
  rename_i outs' hmap
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have key := forIn_inv (fun (Lacc : List (w64 × WriteOp)) (σ : RState) =>
      σ.id = s.id ∧ σ.val = s.val ∧ σ.tag = s.tag ∧ σ.maxN = s.maxN + 1 ∧
      σ.rops = s.rops.put (shiftInts rid cid)
        { requestId := rid, clientId := cid, n := s.maxN + 1, maxValTag := none, readValTag := none,
          numRead1Replies := 1, numRead2Replies := 0, readsWithMaxTag := 0, sentRead2Round := false,
          determinedReadVal := false, replicasWithMaxTag := [] } ∧ σ.wops = s.wops ∧
      rdChar (s.maxN + 1) (s.ongoingReqs.put (s.maxN + 1)
        { requestId := rid, clientId := cid, isRead := true, shortReads := [] })
        σ.ongoingReqs (Lacc.map Prod.snd) ∧
      (∀ w ∈ Lacc.map Prod.snd, w.sentWrite2Round = false →
        ((s.ongoingReqs.put (s.maxN + 1)
          { requestId := rid, clientId := cid, isRead := true, shortReads := [] }).get? w.n).isSome))
      _ ?step s.wops [] _ v ?init hv
  case init =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rdChar_nil _ _, by simp⟩
  case step =>
    intro Lacc a σ r hP hb
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
    split at hb
    · rename_i hsent
      split at hb
      · rename_i op hop
        simp only [Except.ok.injEq] at hb
        subst hb
        refine ⟨_, rfl, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
        · rw [List.map_append]
          exact rdChar_step _ _ _ _ _ op h7 (by simpa using hsent) hop
        · intro w hw hs
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_singleton] at hw
          rcases hw with hw | rfl
          · exact h8 w hw hs
          · rw [← rdChar_isSome _ _ _ _ h7, hop]; rfl
      · cases hb
    · rename_i hsent
      simp only [Except.ok.injEq] at hb
      subst hb
      refine ⟨_, rfl, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
      · rw [List.map_append]
        exact rdChar_sent _ _ _ _ _ h7 (by simpa using hsent)
      · intro w hw hs
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact h8 w hw hs
        · simp at hsent; rw [hsent] at hs; cases hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := key
  have hvt : v.storeVT = s.storeVT := by
    simp only [RState.storeVT, h2, h3]
  refine ⟨h4, h5, h6, hvt, by simpa using h7, by simpa using h8, ?_⟩
  rw [h1, hvt] at hmap
  have hsp : ∀ q, sendPeer v q = sendPeer s q := by
    intro q; funext m; simp only [sendPeer, h1]
  simp only [hsp] at hmap
  exact hmap

theorem mapM_sendPeer_ne (s : RState) (m : Msg) (L : List w32) (h : ∀ q ∈ L, q ≠ s.id) :
    List.mapM (fun q => sendPeer s q m) L = sendsTo L m := by
  unfold sendsTo
  induction L with
  | nil => rfl
  | cons a t ih =>
    have ha : a ≠ s.id := h a (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    rw [List.mapM_cons, List.mapM_cons, ht]
    simp only [sendPeer, ha, ↓reduceIte]

theorem mapM_sendPeer_filter (s : RState) (m : Msg) (L : List w32) :
    List.mapM (fun q => sendPeer s q m) (L.filter (fun i => i ≠ s.id)) =
      sendsTo (L.filter (fun i => i ≠ s.id)) m :=
  mapM_sendPeer_ne s m _ (fun q hq => by simpa using (List.mem_filter.mp hq).2)

theorem w32_lt3 (iv : w32) (h0 : 0 ≤ sint.Z iv) (h3 : sint.Z iv < 3) :
    iv = W32 0 ∨ iv = W32 1 ∨ iv = W32 2 := by
  have : uint.Z iv < 3 := by word
  have h' : iv.toNat < 3 := by simp [uint.Z] at this; omega
  rcases (by omega : iv.toNat = 0 ∨ iv.toNat = 1 ∨ iv.toNat = 2) with h | h | h
  · left; apply BitVec.eq_of_toNat_eq; simp [h]
  · right; left; apply BitVec.eq_of_toNat_eq; simp [h]
  · right; right; apply BitVec.eq_of_toNat_eq; simp [h]

/-- The replicas `StartRead`'s loop has collected after `iv` iterations (all but `me`). -/
def replAfter (me iv : w32) : List w32 :=
  (([W32 0, W32 1, W32 2] : List w32).take (sint.nat iv)).filter (fun x => x ≠ me)

theorem take3_succ (iv : w32) (h0 : 0 ≤ sint.Z iv) (h3 : sint.Z iv < 3) :
    ([W32 0, W32 1, W32 2] : List w32).take (sint.nat (iv + W32 1)) =
      ([W32 0, W32 1, W32 2] : List w32).take (sint.nat iv) ++ [iv] := by
  rcases w32_lt3 iv h0 h3 with rfl | rfl | rfl <;> rfl

theorem replAfter_succ (me iv : w32) (h0 : 0 ≤ sint.Z iv) (h3 : sint.Z iv < 3) :
    replAfter me (iv + W32 1) = replAfter me iv ++ (if iv = me then [] else [iv]) := by
  unfold replAfter
  rw [take3_succ iv h0 h3, List.filter_append]
  by_cases h : iv = me <;> simp [h]

theorem replAfter_three (me : w32) :
    replAfter me (W32 3) = ([0, 1, 2] : List w32).filter (fun x => x ≠ me) := rfl

/-- What `stepClientWrite` does (key 0). -/
theorem stepClientWrite_inv (s s' : RState) (rid cid : w32) (v : w64) (d : Dep) (outs : List Out)
    (h : stepClientWrite s rid cid 0 v d = .ok (s', outs)) :
    s'.maxN = s.maxN + 1 ∧ s'.rops = s.rops ∧
    s'.wops = s.wops.put (shiftInts rid cid)
      ⟨rid, cid, s.maxN + 1, v, d, ⟨-1, tag0⟩, 0, 0, 0, 0, false, none⟩ ∧
    s'.ongoingReqs = s.ongoingReqs.put (s.maxN + 1)
      { requestId := rid, clientId := cid, isRead := false, shortReads := [] } ∧
    s'.storeVT = s.storeVT ∧
    List.mapM (fun q => sendTo q (.write1 ⟨rid, cid, 1, 0, d, s.id⟩)) ([0, 1, 2] : List w32) =
      some outs := by
  unfold stepClientWrite at h
  simp only [bind, Except.bind, pure, Except.pure, never, disabled, dead, FailM.failNever,
    FailM.failDisabled, FailM.failDead] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  rename_i outs' hmap
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, hmap⟩

end Perennial.gryff.replica2