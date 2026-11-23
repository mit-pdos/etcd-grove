/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Wire/LineBound.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
Helpers for `VsrWire.line_bound` (VsrProof/Wire/Basic.lean): the length of the codec's encoding
of a message (`VsrJson.encEvent`) as a function of its strings, its logs' lengths and its numbers,
and the bounds the invariant gives on those (operations of registered inputs, results of
registered puts, logs of views).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Frame

@[expose] public section

namespace VsrLineBound

open Perennial VsrModel VsrJson

/-! ## The encoding's length -/

theorem decN_length_le : ∀ (k n : Nat), n < 10 ^ k → (decN n).length ≤ k + 1
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rw [decN]; simp
  | k + 1, n, h => by
    rw [decN]
    split
    · simp
    · have := decN_length_le k (n / 10) (by rw [Nat.pow_succ] at h; omega)
      simp; omega

theorem decN_length_64 (n : Nat) (h : n < 2 ^ 64) : (decN n).length ≤ 21 :=
  decN_length_le 20 n (by have : (2 : Nat) ^ 64 < 10 ^ 20 := by decide
                          omega)

theorem ser_qn (n : Nat) (h : n < 2 ^ 64) : (ser (qn n)).length ≤ 23 := by
  have := decN_length_64 n h
  simp [qn, ser]; omega

theorem ser_str (s : List w8) : (ser (.str s)).length = s.length + 2 := by
  simp [ser]

theorem ser_num (n : Nat) (h : n < 2 ^ 64) : (ser (.num n)).length ≤ 21 := by
  simp [ser]; exact decN_length_64 n h

/-- A member's contribution (after a comma). -/
def memLen (p : List w8 × JV) : Nat := p.1.length + 4 + (ser p.2).length

theorem serMsT_len (l : List (List w8 × JV)) :
    (serMsT (mkObj l)).length = (l.map memLen).sum := by
  induction l with
  | nil => simp [mkObj, serMsT]
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp [mkObj, serMsT, memLen] at ih ⊢; rw [ih]; omega

theorem serMs_len_le (l : List (List w8 × JV)) :
    (serMs (mkObj l)).length ≤ (l.map memLen).sum := by
  cases l with
  | nil => simp [mkObj, serMs]
  | cons p l =>
    obtain ⟨k, v⟩ := p
    have := serMsT_len l
    simp [mkObj, serMs, memLen] at this ⊢; omega

theorem ser_obj_le (l : List (List w8 × JV)) :
    (ser (.obj (mkObj l))).length ≤ 2 + (l.map memLen).sum := by
  have := serMs_len_le l
  simp [ser]; omega

theorem serVsT_len (l : List JV) :
    (serVsT (mkArr l)).length = (l.map fun v => (ser v).length + 1).sum := by
  induction l with
  | nil => simp [mkArr, serVsT]
  | cons v l ih => simp [mkArr, serVsT] at ih ⊢; rw [ih]; omega

theorem serVs_len_le (l : List JV) :
    (serVs (mkArr l)).length ≤ (l.map fun v => (ser v).length + 1).sum := by
  cases l with
  | nil => simp [mkArr, serVs]
  | cons v l =>
    have := serVsT_len l
    simp [mkArr, serVs] at this ⊢; omega

theorem sum_le {α} (l : List α) (f : α → Nat) (C : Nat) (h : ∀ x ∈ l, f x ≤ C) :
    (l.map f).sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [Nat.succ_mul]; omega

theorem ser_logJV (e : Entry) (hb : EntryBound e) :
    (ser (logJV e)).length ≤ e.op.length + 100 := by
  have h1 := ser_qn e.cid hb.1
  have h2 := ser_qn e.req hb.2
  have h3 := ser_obj_le [(go!"data", .str e.op), (go!"client_id", qn e.cid),
    (go!"request_id", qn e.req)]
  simp [memLen, ser_str] at h3
  unfold logJV; omega

/-- A log whose operations are short and whose length is bounded. -/
def LogShort (l : List Entry) : Prop := l.length ≤ 6 * 2 ^ 28 ∧ ∀ e ∈ l, e.op.length < 2 ^ 18

theorem ser_logsJV (es : List Entry) (hs : LogShort es) (hb : ∀ e ∈ es, EntryBound e) :
    (ser (logsJV es)).length ≤ 2 ^ 50 := by
  have h1 : (ser (logsJV es)).length ≤ 2 + es.length * (2 ^ 18 + 101) := by
    have := serVs_len_le (es.map logJV)
    have h2 := sum_le es (fun e => (ser (logJV e)).length + 1) (2 ^ 18 + 101) (by
      intro e he
      have := ser_logJV e (hb e he)
      have := hs.2 e he
      omega)
    simp only [List.map_map, Function.comp_def] at this
    simp only [logsJV, ser, List.length_cons, List.length_append, List.length_nil]
    omega
  have h3 : es.length * (2 ^ 18 + 101) ≤ 6 * 2 ^ 28 * (2 ^ 18 + 101) :=
    Nat.mul_le_mul_right _ hs.1
  omega

/-- The strings and logs of a message are short. -/
def MsgShort : Msg → Prop
  | .request _ _ op => op.length < 2 ^ 18
  | .reply _ _ _ res => res.length < 2 ^ 18
  | .prepare _ _ _ e _ => e.op.length < 2 ^ 18
  | .doViewChange d => LogShort d.log
  | .startView _ _ _ logs _ => LogShort logs
  | .newState _ logs _ _ _ => LogShort logs
  | _ => True

theorem ser_payJV (m : Msg) (hb : MsgBound m) (hs : MsgShort m) :
    (ser (payJV m)).length ≤ 2 ^ 51 := by
  cases m with
  | request id cid op =>
    obtain ⟨b1, b2⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2
    have h := ser_obj_le [(go!"id", qn id), (go!"client_id", qn cid), (go!"op", .str op)]
    simp only [MsgShort] at hs
    simp [memLen, ser_str] at h
    simp only [payJV, reqJV]; omega
  | reply id cid v res =>
    obtain ⟨b1, b2, b3⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3
    have h := ser_obj_le [(go!"id", qn id), (go!"client_id", qn cid),
      (go!"view_num", qn v), (go!"result", .str res)]
    simp only [MsgShort] at hs
    simp [memLen, ser_str] at h
    simp only [payJV]; omega
  | prepare v k c e rid =>
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3; have := ser_qn _ b5
    have := ser_qn _ b4.1; have := ser_qn _ b4.2
    have hr0 := ser_obj_le [(go!"id", qn e.req), (go!"client_id", qn e.cid), (go!"op", .str e.op)]
    have hr : (ser (reqJV e.req e.cid e.op)).length ≤ _ := hr0
    have h := ser_obj_le [(go!"view_num", qn v), (go!"op_num", qn k),
      (go!"commit_num", qn c), (go!"request", reqJV e.req e.cid e.op), (go!"replica_id", qn rid)]
    simp only [MsgShort] at hs
    simp [memLen, ser_str] at h hr
    simp only [payJV]; omega
  | prepareOK v k rid =>
    obtain ⟨b1, b2, b3⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3
    have h := ser_obj_le [(go!"view_num", qn v), (go!"op_num", qn k), (go!"replica_id", qn rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | commit v c rid =>
    obtain ⟨b1, b2, b3⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3
    have h := ser_obj_le [(go!"view_num", qn v), (go!"commit_num", qn c),
      (go!"replica_id", qn rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | startViewChange v rid =>
    obtain ⟨b1, b2⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2
    have h := ser_obj_le [(go!"view_num", qn v), (go!"replica_id", qn rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | doViewChange d =>
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3; have := ser_qn _ b4
    have := ser_qn _ b5
    have := ser_logsJV d.log hs b6
    have h := ser_obj_le [(go!"view_num", qn d.view), (go!"logs", logsJV d.log),
      (go!"last_stable_view_num", qn d.lnv), (go!"op_num", qn d.log.length),
      (go!"commit_num", qn d.commit), (go!"replica_id", qn d.rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | startView v k c logs rid =>
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3; have := ser_qn _ b4
    have := ser_logsJV logs hs b5
    have h := ser_obj_le [(go!"view_num", qn v), (go!"op_num", qn k),
      (go!"commit_num", qn c), (go!"logs", logsJV logs), (go!"replica_id", qn rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | getState v k rid =>
    obtain ⟨b1, b2, b3⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3
    have h := ser_obj_le [(go!"view_num", qn v), (go!"op_num", qn k), (go!"replica_id", qn rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | newState v logs c k rid =>
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    have := ser_qn _ b1; have := ser_qn _ b2; have := ser_qn _ b3; have := ser_qn _ b4
    have := ser_logsJV logs hs b5
    have h := ser_obj_le [(go!"view_num", qn v), (go!"logs", logsJV logs),
      (go!"commit_num", qn c), (go!"op_num", qn k), (go!"replica_id", qn rid)]
    simp [memLen] at h
    simp only [payJV]; omega
  | heartbeat => simp [payJV, ser, serMs]

theorem typeN_lt (m : Msg) : typeN m < 2 ^ 64 := by
  cases m <;> simp [typeN]

theorem encEvent_len (m : Msg) (hb : MsgBound m) (hs : MsgShort m) :
    (VsrJson.encEvent m).length ≤ 2 ^ 52 := by
  unfold VsrJson.encEvent
  split
  · have h1 := ser_payJV m hb hs
    have h2 := ser_num _ (typeN_lt m)
    have h := ser_obj_le [(go!"@type", .num (typeN m)), (go!"data", payJV m)]
    simp [memLen] at h
    unfold evJV; omega
  · simp

/-! ## The invariant's bounds -/

theorem encOp_len (i : VsrModel.KvInput GoString GoString) (h : InputBounded i) :
    (encOp i).length < 2 ^ 18 := by
  cases i with
  | get k => have := h; simp [InputBounded] at this; simp [encOp]; omega
  | put k v => have := h; simp [InputBounded] at this; simp [encOp]; omega

theorem reg_bound {s : Sys} (h : Inv s) {c n : Nat} {i} (hi : s.reg c n = some i) :
    InputOk i ∧ RegBound c n i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := h; exact h11 c n i hi

theorem registered_short {s : Sys} (h : Inv s) {l : List Entry} (hl : Registered s l) :
    ∀ e ∈ l, e.op.length < 2 ^ 18 := by
  intro e he
  obtain ⟨i, hi, hop⟩ := hl e he
  rw [hop]; exact encOp_len i (reg_bound h hi).2.2.2.2.2

theorem vlog_registered {s : Sys} (h : Inv s) {v : Nat} {L : List Entry}
    (hL : s.vlog v = some L) : Registered s L := by
  obtain ⟨-, h2, h3, -⟩ := h
  have := h2 v
  rw [hL] at this
  cases hI : s.vinit v with
  | none => rw [hI] at this; simp at this
  | some I => exact (h3 v I L hI hL).2.2

theorem vlog_short {s : Sys} (h : Inv s) {v : Nat} {L : List Entry}
    (hL : s.vlog v = some L) : LogShort L :=
  ⟨vlog_length_le s h v L hL, registered_short h (vlog_registered h hL)⟩

theorem logShort_sub {l L : List Entry} (hL : LogShort L) (hlen : l.length ≤ L.length)
    (hsub : ∀ e ∈ l, e ∈ L) : LogShort l :=
  ⟨Nat.le_trans hlen hL.1, fun e he => hL.2 e (hsub e he)⟩

/-- A store reached from stores with short values by registered operations has short values. -/
theorem foldl_short (s : Sys) (h : Inv s) :
    ∀ (l : List Entry) (m : Store), Registered s l → (∀ k v, m k = some v → v.length < 2 ^ 16) →
      ∀ k v, (l.foldl (fun m e => (handle m e.op).1) m) k = some v → v.length < 2 ^ 16 := by
  intro l
  induction l with
  | nil => intro m _ hm; exact hm
  | cons e l ih =>
    intro m hl hm
    apply ih _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    obtain ⟨i, hi, hop⟩ := hl e List.mem_cons_self
    obtain ⟨hok, hrb⟩ := reg_bound h hi
    show ∀ k v, (handle m e.op).1 k = some v → v.length < 2 ^ 16
    rw [hop]
    cases i with
    | get k =>
      rw [handle_encOp m (.get k) hok.1]; exact hm
    | put k v =>
      rw [handle_encOp m (.put k v) ⟨hok.1.1, hok.2.2.1⟩]
      intro k' v' hk'
      simp only [svcStep] at hk'
      split at hk'
      · cases hk'; exact hrb.2.2.2.2.2
      · exact hm k' v' hk'

theorem outOf_short (s : Sys) (h : Inv s) (i : Nat) : (outOf s.lin i).length < 2 ^ 16 := by
  have hlinreg : Registered s s.lin := by
    obtain ⟨-, -, -, -, -, -, -, -, -, x, -⟩ := h; exact x
  unfold outOf
  cases he : s.lin[i]? with
  | none => simp
  | some e =>
    dsimp only
    obtain ⟨i', hi', hop⟩ := hlinreg e (List.mem_of_getElem? he)
    obtain ⟨hok, hrb⟩ := reg_bound h hi'
    rw [hop]
    have hst := foldl_short s h (s.lin.take i) (fun _ => none)
      (fun e he => hlinreg e (List.mem_of_mem_take he)) (fun _ _ h => by cases h)
    cases i' with
    | put k v =>
      rw [handle_encOp _ (.put k v) ⟨hok.1.1, hok.2.2.1⟩]; exact hrb.2.2.2.2.2
    | get k =>
      rw [handle_encOp _ (.get k) hok.1]
      simp only [svcStep]
      cases hk : storeOf (s.lin.take i) k with
      | none => simp
      | some v => exact hst k v hk

theorem msgValid_short (s : Sys) (h : Inv s) (m : Msg) (hm : MsgValid s m) : MsgShort m := by
  cases m with
  | request id cid op =>
    obtain ⟨i, hi, rfl⟩ := hm; exact encOp_len i (reg_bound h hi).2.2.2.2.2
  | reply id cid v res =>
    obtain ⟨i, e, -, -, -, rfl⟩ := hm; have := outOf_short s h i
    show (outOf s.lin i).length < 2 ^ 18; omega
  | prepare v k c e rid =>
    obtain ⟨L, hL, -, hLe, -⟩ := hm
    exact (vlog_short h hL).2 e (List.mem_of_getElem? hLe)
  | prepareOK => trivial
  | commit => trivial
  | startViewChange => trivial
  | doViewChange d =>
    obtain ⟨-, -, -, -, -, ⟨L, I, hL, -, hdL, -⟩, -⟩ := hm
    exact logShort_sub (vlog_short h hL) hdL.length_le (fun e he => hdL.subset he)
  | startView v k c logs rid =>
    obtain ⟨hI, -⟩ := hm
    obtain ⟨-, h2, h3, -⟩ := id h
    have := h2 v
    rw [hI] at this
    cases hL : s.vlog v with
    | none => rw [hL] at this; simp at this
    | some L =>
      have hIL := (h3 v logs L hI hL).1
      exact logShort_sub (vlog_short h hL) hIL.length_le
        (fun e he => hIL.subset he)
  | getState => trivial
  | newState v logs c k rid =>
    obtain ⟨L, hL, hk, hlk, heq⟩ := hm
    refine logShort_sub (vlog_short h hL) (Nat.le_trans hlk hk) ?_
    intro e he
    rw [heq] at he
    exact List.mem_of_mem_take (List.mem_of_mem_drop he)
  | heartbeat => trivial

/-- `VsrWire.line_bound`'s content: a valid, bounded message's encoding is short. -/
theorem encEvent_bound (s : Sys) (h : Inv s) (m : Msg) (hm : MsgValid s m) (hb : MsgBound m) :
    (VsrJson.encEvent m).length ≤ 2 ^ 52 :=
  encEvent_len m hb (msgValid_short s h m hm)

end VsrLineBound
