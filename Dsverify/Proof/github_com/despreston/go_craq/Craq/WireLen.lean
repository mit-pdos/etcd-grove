/-
The lengths of go-craq's wire values (`Wire.lean`): every request a client sends fits the frames
net/rpc's model reads (`net.rpc.maxFrameN`, 1 GiB), which Net's `Client.Call.spec` asks of the
service method and the encoded arguments. A string argument is a key the protocol handles
(`keyOk`: at most 2 bytes), a value shorter than 256 bytes (`kvOk`) or an address shorter than
256 bytes; a propagation request's keys are distinct keys the protocol handles, so it has at most
`1 + 256 + 256 ^ 2` entries (`nodup_le2_length`: they are among the strings of at most 2 bytes).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Wire
public import Net.Proof.net.rpc.Base
public import Batteries.Data.List.Perm

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.despreston.go_craq

/-! ## The strings of at most 2 bytes -/

/-- Every byte. -/
def allBytes : List w8 := (List.range 256).map (fun i : Nat => W8 (i : Int))

theorem mem_allBytes (b : w8) : b ∈ allBytes := by
  simp only [allBytes, List.mem_map, List.mem_range]
  exact ⟨uint.nat b, by word, by word⟩

def strsLe2 : List (List w8) :=
  [] :: (allBytes.map (fun a => [a]) ++ allBytes.flatMap (fun a => allBytes.map (fun b => [a, b])))

theorem mem_strsLe2 (s : List w8) (h : s.length ≤ 2) : s ∈ strsLe2 := by
  match s, h with
  | [], _ => simp [strsLe2]
  | [a], _ => simp [strsLe2, mem_allBytes]
  | [a, b], _ => simp [strsLe2, List.mem_flatMap, mem_allBytes]

theorem strsLe2_length : strsLe2.length = 65793 := by
  have h : ∀ (l : List w8) (f : w8 → List (List w8)), (∀ a, (f a).length = 256) →
      (l.flatMap f).length = 256 * l.length := by
    intro l f hf
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, hf, ih]; omega
  have hb : allBytes.length = 256 := by simp [allBytes]
  unfold strsLe2
  simp only [List.length_cons, List.length_append, List.length_map, hb]
  rw [h allBytes _ (fun a => by simp [hb]), hb]

theorem nodup_le2_length (ks : List (List w8)) (hnd : ks.Nodup) (hk : ∀ k ∈ ks, k.length ≤ 2) :
    ks.length ≤ 65793 :=
  strsLe2_length ▸ (List.subperm_of_subset hnd (fun k hk' => mem_strsLe2 k (hk k hk'))).length_le

/-! ## The encodings' lengths -/

theorem encStr_length (s : GoString) : (encStr s).length = 8 + s.length := by
  simp [encStr, u64Le_length]
theorem tagged_length (t : GoString) (b : List w8) :
    (tagged t b).length = 8 + t.length + b.length := by
  simp [tagged, encStr_length]
theorem fld_length_le (b : Bool) (body : List w8) : (fld b body).length ≤ 1 + body.length := by
  unfold fld; split <;> simp <;> omega
theorem encBytes_length (s : List w8) : (encBytes s).length = 8 + 8 * s.length := by
  unfold encBytes
  simp only [List.length_append, u64Le_length]
  have : ∀ l : List w8, ((l.map fun b => u64Le (W64 (uint.Z b))).flatten).length = 8 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatten_cons, u64Le_length] at ih ⊢; omega
  rw [this]
theorem strct_length (fs : List (List w8)) : (strct fs).length = 1 + (fs.map List.length).sum := by
  unfold strct; simp [List.length_flatten]; omega
theorem fStr_le (s : GoString) : (fStr s).length ≤ 9 + s.length := by
  have := fld_length_le (decide (s ≠ [])) (encStr s); simp only [encStr_length] at this
  unfold fStr; omega
theorem fBytes_le (s : List w8) : (fBytes s).length ≤ 9 + 8 * s.length := by
  have := fld_length_le (decide (s ≠ [])) (encBytes s); simp only [encBytes_length] at this
  unfold fBytes; omega
theorem fU64_le (x : w64) : (fU64 x).length ≤ 9 := by
  unfold fU64 encU64
  have := fld_length_le (decide (x ≠ W64 0)) (u64Le x); simp only [u64Le_length] at this
  omega
theorem fBool_le (b : Bool) : (fBool b).length ≤ 2 := by
  unfold fBool
  have := fld_length_le b (encBool b); simp only [encBool, List.length_singleton] at this ⊢
  omega


theorem encString_len (s : GoString) : (encString s).length ≤ 100 + s.length := by
  have ht : (go!"string" : GoString).length ≤ 50 := by decide
  simp only [encString, tagged_length, encStr_length]; omega
theorem encEmptyArgs_len : encEmptyArgs.length ≤ 200 := by
  have ht : (go!"github.com/despreston/go-craq/transport/netrpc.EmptyArgs" : GoString).length ≤ 100 := by decide
  simp only [encEmptyArgs, tagged_length, strct_length, List.map_nil, List.sum_nil]; omega
theorem encCommitArgs_len (k : GoString) (v : w64) : (encCommitArgs k v).length ≤ 200 + k.length := by
  have ht : (go!"github.com/despreston/go-craq/transport/netrpc.CommitArgs" : GoString).length ≤ 100 := by decide
  have := fStr_le k; have := fU64_le v
  simp only [encCommitArgs, tagged_length, strct_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
theorem encClientWriteArgs_len (k x : GoString) :
    (encClientWriteArgs k x).length ≤ 200 + k.length + 8 * x.length := by
  have ht : (go!"github.com/despreston/go-craq/transport/netrpc.ClientWriteArgs" : GoString).length ≤ 100 := by decide
  have := fStr_le k; have := fBytes_le x
  simp only [encClientWriteArgs, tagged_length, strct_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
theorem encWriteArgs_len (k x : GoString) (v : w64) :
    (encWriteArgs k x v).length ≤ 200 + k.length + 8 * x.length := by
  have ht : (go!"github.com/despreston/go-craq/transport/netrpc.WriteArgs" : GoString).length ≤ 100 := by decide
  have := fStr_le k; have := fBytes_le x; have := fU64_le v
  simp only [encWriteArgs, tagged_length, strct_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
theorem encMeta_len (m : MetaV) :
    (encMeta m).length ≤ 200 + m.prev.length + m.next.length + m.tail.length := by
  have ht : (go!"github.com/despreston/go-craq/transport.NodeMeta" : GoString).length ≤ 100 := by decide
  have := fStr_le m.prev; have := fStr_le m.next; have := fStr_le m.tail
  have := fBool_le m.isHead; have := fBool_le m.isTail
  simp only [encMeta, tagged_length, strct_length, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
theorem encPropReqL_len (es : List (GoString × w64)) (h : ∀ e ∈ es, keyOk e.1) :
    (encPropReqL es).length ≤ 200 + 18 * es.length := by
  have ht : (go!"github.com/despreston/go-craq/transport.PropagateRequest" : GoString).length ≤ 100 := by decide
  have hb : ∀ l : List (GoString × w64), (∀ e ∈ l, keyOk e.1) →
      ((l.map fun e => encStr e.1 ++ encU64 e.2).flatten).length ≤ 18 * l.length := by
    intro l hl; induction l with
    | nil => simp
    | cons e l ih =>
      have he := hl e (by simp); unfold keyOk at he
      have := ih (fun e' h' => hl e' (by simp [h']))
      simp only [List.map_cons, List.flatten_cons, List.length_append, encStr_length, encU64,
        u64Le_length, List.length_cons] at this ⊢
      omega
  have := hb es h
  simp only [encU64] at this
  simp only [encPropReqL, tagged_length, List.length_append, encU64, u64Le_length]; omega

/-! ## The frames -/

theorem encString_frame (s : GoString) (h : s.length < 256) :
    (encString s).length ≤ net.rpc.maxFrameN := by
  have := encString_len s; unfold net.rpc.maxFrameN; omega

theorem encEmptyArgs_frame : encEmptyArgs.length ≤ net.rpc.maxFrameN := by
  have := encEmptyArgs_len; unfold net.rpc.maxFrameN; omega

theorem encCommitArgs_frame (k : GoString) (v : w64) (h : keyOk k) :
    (encCommitArgs k v).length ≤ net.rpc.maxFrameN := by
  have := encCommitArgs_len k v; unfold keyOk at h; unfold net.rpc.maxFrameN; omega

theorem encClientWriteArgs_frame (k x : GoString) (h : kvOk k x) :
    (encClientWriteArgs k x).length ≤ net.rpc.maxFrameN := by
  have := encClientWriteArgs_len k x; unfold kvOk keyOk at h; unfold net.rpc.maxFrameN; omega

theorem encWriteArgs_frame (k x : GoString) (v : w64) (h : kvOk k x) :
    (encWriteArgs k x v).length ≤ net.rpc.maxFrameN := by
  have := encWriteArgs_len k x v; unfold kvOk keyOk at h; unfold net.rpc.maxFrameN; omega

theorem encMeta_frame (m : MetaV) (h : m.prev.length < 256 ∧ m.next.length < 256 ∧ m.tail.length < 256) :
    (encMeta m).length ≤ net.rpc.maxFrameN := by
  have := encMeta_len m; unfold net.rpc.maxFrameN; omega

theorem encPropReq_frame (req : GMap GoString w64) (bs : List w8) (h : encPropReq req bs)
    (hk : reqKeysOk req) : bs.length ≤ net.rpc.maxFrameN := by
  obtain ⟨es, ⟨hnd, hes⟩, rfl⟩ := h
  have hok : ∀ e ∈ es, keyOk e.1 := fun e he => hk e.1 e.2 ((hes e.1 e.2).2 he)
  have hcnt : (es.map Prod.fst).length ≤ 65793 :=
    nodup_le2_length _ hnd (fun k hk' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk'
      exact hok e he)
  have := encPropReqL_len es hok
  simp only [List.length_map] at hcnt
  unfold net.rpc.maxFrameN; omega

end github_com.despreston.go_craq

end Perennial
