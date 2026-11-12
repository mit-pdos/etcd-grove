/-
`Bucket.spill`'s root loop (U9x3, `notes/bbolt-proof-plan.md`): **the inline value `b.write()`
makes** of an inlineable child (`inlineVal`, `BktLoopStep.rinv_inline`'s value facts). Its header
(root `0`) then the leaf page `node.write` wrote (`WrittenPage.wPage` at id `0`, no overflow, no
tail): a good inline page (`inlineGood`) holding the root leaf's entries, plain, within a quarter
page (`insSize ≤ 1024`); and `node.write`'s premises (`pageFits`, the size relation).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.WrittenPage
public import Proof.go_etcd_io.bbolt.Spill.PageBuf
public import Proof.go_etcd_io.bbolt.Spill.Inlineable
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitSize

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section inlval
variable [GooseExts]

/-- The inline value `b.write()` makes of a bucket (header `ib`) whose root leaf holds `ws`. -/
def inlineVal (ib : InBucket) (ws : List WEntry) : List w8 :=
  encode ib ++ encode (hdrWritten ⟨W64 0, W16 0, W16 0, W32 0⟩ true (wsMs ws).length) ++
    pageBody true (wsMs ws)

theorem inBucketOf_prefix (ib : InBucket) (rest : List w8) : inBucketOf (encode ib ++ rest) = ib := by
  unfold inBucketOf bytesAt
  rw [List.drop_zero, List.take_left' (by simp), ByteEncoding.decode_encode]

theorem inlinePage_inlineVal (ib : InBucket) (ws : List WEntry) :
    inlinePage (inlineVal ib ws) = wPage (W64 0) true (wsMs ws) (W32 0) [] := by
  unfold inlinePage inlineVal wPage bucketHeaderSize
  rw [List.append_assoc, List.drop_left' (by simp), List.append_nil]
  rfl

theorem sum_wSz_ge (ws : List WEntry) : 16 * ws.length ≤ (ws.map wSz).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.map_cons, List.sum_cons, List.length_cons, wSz]; omega

/-- **The inline value's facts** (see the module doc). -/
theorem inlineVal_ok {ib : InBucket} {ws : List WEntry} {ins : List Inode} (h0 : ib.root' = W64 0)
    (hsort : wsSorted ws)
    (hpl : ∀ w ∈ ws, w.flags.toNat % 2 = 0 ∧ 0 < w.key.length ∧
      w.key.length + w.value.length ≤ bboltEntryMax)
    (hlens : insLens ins ws) (hlen : ins.length = ws.length) (hsz : insSize ins ≤ 1024)
    (P : Pages) (hwm : Nat) :
    (wsMs ws).length < 0xFFFF ∧ pageFits (wsMs ws) ∧
      insSize ins = 16 + (pageBody true (wsMs ws)).length ∧ insSize ins < 2 ^ 31 ∧
      bvalS P hwm (inlineVal ib ws) [] ∧
      bvalData P (inlineVal ib ws) (ws.map fun w => (w.key, w.value)) ∧
      (inlineVal ib ws).length ≤ 2 ^ 27 := by
  have hS : insSize ins = 16 + (pageBody true (wsMs ws)).length :=
    (insSize_ws ins ws hlens hlen).trans (body_ws ws).symm
  have hsum := insSize_ws ins ws hlens hlen
  have hge := sum_wSz_ge ws
  have hml : (wsMs ws).length = ws.length := wsMs_length ws
  have hn : (wsMs ws).length < 2 ^ 16 := by omega
  have hb32 : 16 + (pageBody true (wsMs ws)).length < 2 ^ 32 := by omega
  have hvlen : (inlineVal ib ws).length = 32 + (pageBody true (wsMs ws)).length := by
    unfold inlineVal; simp [ByteEncoding.encode_length]; omega
  have hroot : inBucketRoot (inlineVal ib ws) = 0 := by
    unfold inBucketRoot inlineVal
    rw [List.append_assoc, inBucketOf_prefix, h0]; rfl
  have hms : ∀ i (hi : i < (wsMs ws).length), (wsMs ws)[i] =
      ⟨ws[i].flags, ws[i].pgid, ws[i].key,
        ws[i].value⟩ := by
    intro i hi; simp [wsMs]
  have hpl' : ∀ i (hi : i < ws.length), (ws[i]).flags.toNat % 2 = 0 ∧ 0 < (ws[i]).key.length ∧
      (ws[i]).key.length + (ws[i]).value.length ≤ bboltEntryMax :=
    fun i hi => hpl _ (List.getElem_mem hi)
  have hcnt : pageCount (wPage (W64 0) true (wsMs ws) (W32 0) []) = ws.length := by
    rw [wPage_count hn, hml]
  have hleaf : ∀ i (hi : i < ws.length),
      leafKsize (wPage (W64 0) true (wsMs ws) (W32 0) []) i = ws[i].key.length ∧
      leafVsize (wPage (W64 0) true (wsMs ws) (W32 0) []) i = ws[i].value.length ∧
      leafFlags (wPage (W64 0) true (wsMs ws) (W32 0) []) i = ws[i].flags.toNat ∧
      leafKey (wPage (W64 0) true (wsMs ws) (W32 0) []) i = ws[i].key ∧
      leafValue (wPage (W64 0) true (wsMs ws) (W32 0) []) i = ws[i].value := by
    intro i hi
    obtain ⟨-, h2, h3, h4, h5, h6⟩ := wPage_leaf (id := W64 0) (ovf := W32 0) (tail := [])
      (show i < (wsMs ws).length by omega) hb32
    rw [hms i (by omega)] at h2 h3 h4 h5 h6
    exact ⟨h2, h3, h4, h5, h6⟩
  refine ⟨by omega, ⟨hn, hb32, fun m hm => ?_⟩, hS, by omega, ⟨by omega, Or.inl ⟨hroot, rfl, ?_⟩⟩,
    ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hroot h⟩, by omega⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
    intro e; have := (hpl w hw).2.1; simp only at e; rw [e] at this; simp at this
  · rw [inlinePage_inlineVal]
    refine ⟨by rw [wPage_id]; rfl, by rw [wPage_flags]; rfl,
      wPage_leafWF hn (by unfold maxAllocSize; omega) (wsMs_sorted hsort),
      by rw [wPage_length]; simp, fun i hi => ?_⟩
    rw [hcnt] at hi
    obtain ⟨h2, -, h4, -, -⟩ := hleaf i hi
    have := hpl' i hi
    rw [h2, h4]; exact ⟨this.2.1, this.1⟩
  · rw [inlinePage_inlineVal]
    unfold leafEnts
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]; exact hcnt
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨-, -, -, h5, h6⟩ := hleaf i (by simp only [List.length_map, List.length_range] at h1; exact hcnt ▸ h1)
      rw [h5, h6]
  · rw [inlinePage_inlineVal]
    intro j hj
    rw [hcnt] at hj
    obtain ⟨h2, h3, h4, -, -⟩ := hleaf j hj
    have := hpl' j hj
    rw [h2, h3, h4]; exact this

end inlval

end Spill

end bbolt
end EtcdGrove
end Perennial
