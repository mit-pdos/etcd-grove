/-
Pure lemmas for `hashMap.mergeWithExistingSpan` and `hashMap.mergeSpans`: the state of
`mergeWithExistingSpan` (`mInv`: the span `newStart..` it is about to add and the free ids left
make up the free ids and the merged ids) through its merge with the span before (`merge_prev`)
and after (`merge_next`), and the span it adds at the end (`merge_final`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.HashLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.freelist

theorem add_nowrap {a b : w64} (h : uint.Z a + uint.Z b < 2 ^ 64) :
    uint.Z (a + b) = uint.Z a + uint.Z b ∧ uint.nat (a + b) = uint.nat a + uint.nat b := by
  constructor <;> word

theorem mem_filter_not {f : List w64} {A : w64 → Prop} [DecidablePred A] (x : w64) :
    x ∈ f.filter (fun x => !decide (A x)) ↔ x ∈ f ∧ ¬ A x := by simp

theorem or_merge {P A B : Prop} (hA : A → P) : ((P ∧ ¬A) ∨ (A ∨ B)) ↔ (P ∨ B) := by
  by_cases a : A
  · exact ⟨fun _ => Or.inl (hA a), fun _ => Or.inr (Or.inl a)⟩
  · constructor
    · rintro (⟨p, -⟩ | h | h)
      · exact Or.inl p
      · exact absurd h a
      · exact Or.inr h
    · rintro (p | b)
      · exact Or.inl ⟨p, a⟩
      · exact Or.inr (Or.inr b)

/-- `mergeWithExistingSpan(start, ..)` (merging the `len` ids from `start` into `free`), with
the free ids `f` left and the span `ns`, `nsz` to add: together they make up `free` and the
merged ids; the span is not free, positive and does not wrap around. -/
def mInv (free : List w64) (start : w64) (len : Nat) (f : List w64) (ns nsz : w64) : Prop :=
  (∀ x, x ∈ f ∨ inRun ns (uint.nat nsz) x ↔ x ∈ free ∨ inRun start len x) ∧
  (∀ x, inRun ns (uint.nat nsz) x → x ∉ f) ∧ 1 ≤ uint.Z nsz ∧
  uint.Z ns + uint.Z nsz ≤ 2 ^ 64 ∧ f.length + uint.nat nsz = free.length + len ∧
  (∀ x ∈ f, x ∈ free)

theorem mInv_init {free : List w64} {start e : w64} (hle : uint.Z start ≤ uint.Z e)
    (h1 : 1 ≤ uint.Z start) (hdis : ∀ x, inRun start (uint.nat (e - start) + 1) x → x ∉ free) :
    mInv free start (uint.nat (e - start) + 1) free start (e - start + W64 1) ∧
    uint.Z start + uint.Z (e - start + W64 1) = uint.Z e + 1 := by
  have hn : uint.nat (e - start + W64 1) = uint.nat (e - start) + 1 := by word
  refine ⟨⟨fun x => by rw [hn], fun x hx => hdis x (by rw [← hn]; exact hx), by word, by word,
    by rw [hn], fun x hx => hx⟩, by word⟩

/-- Merging with the span before `start` (`backwardMap[start-1]` is its size `p`): it starts at
`start-1+1-p`, before `start`; the span to add starts there now. -/
theorem merge_prev {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free f : List w64} {start nsz p : w64} {len : Nat}
    (h : hashOK cnt sp bwm sets f) (hm : mInv free start len f start nsz)
    (hp : bwm !! (start - W64 1) = some p) (h1 : 1 ≤ uint.Z start)
    (hge1 : ∀ x ∈ free, 1 ≤ uint.Z x) :
    sp !! (start - W64 1 + W64 1 - p) = some p ∧
    uint.Z (start - W64 1 + W64 1 - p) < uint.Z start ∧
    mInv free start len
      (f.filter (fun x => !decide (inRun (start - W64 1 + W64 1 - p) (uint.nat p) x)))
      (start - p) (nsz + p) ∧
    uint.Z (start - p) + uint.Z (nsz + p) = uint.Z start + uint.Z nsz := by
  obtain ⟨hmem, hdis, hn1, hnw, hlen, hsub⟩ := hm
  obtain ⟨st', hs', hk⟩ := (h.2.2.1.1 _ p).1 hp
  obtain ⟨hp1, hpnw⟩ := h.1.1 st' p hs'
  have hnum : uint.Z st' + uint.Z p = uint.Z start := by
    have e1 : uint.Z (start - W64 1) = uint.Z start - 1 := by word
    have e2 : uint.Z (st' + p - W64 1) = uint.Z st' + uint.Z p - 1 := by word
    rw [hk, e2] at e1; omega
  have hst : start - W64 1 + W64 1 - p = st' := by word
  have hsp : start - p = st' := by word
  rw [hst, hsp]
  have hin : ∀ x, inRun st' (uint.nat p) x → x ∈ f := fun x hx => span_mem h.2.1 hs' hx
  have hst1 : 1 ≤ uint.Z st' := hge1 st' (hsub st' (hin st' (hm_inRun_self (by word))))
  obtain ⟨hz, hzn⟩ := add_nowrap (a := nsz) (b := p) (by omega)
  have hcp : (uint.nat p : Int) = uint.Z p := by word
  have hcn : (uint.nat nsz : Int) = uint.Z nsz := by word
  have hrun : ∀ x, inRun st' (uint.nat (nsz + p)) x ↔ inRun st' (uint.nat p) x ∨ inRun start (uint.nat nsz) x := by
    intro x; unfold inRun; rw [hzn]; push_cast; omega
  have hfl := filter_not_length h.2.1.1.nodup (st := st') (n := uint.nat p) (by word) hin
  have hle := span_le_len h.1 h.2.1 hs'
  refine ⟨hs', by omega, ⟨fun x => ?_, fun x hx => ?_, by word, by omega, ?_, fun x hx => ?_⟩, by omega⟩
  · rw [← hmem x, hrun x, mem_filter_not]
    exact or_merge (hin x)
  · rw [mem_filter_not]
    rcases (hrun x).1 hx with hx' | hx'
    · exact fun h' => h'.2 hx'
    · exact fun h' => hdis x hx' h'.1
  · rw [hfl, hzn]; omega
  · exact hsub x (List.mem_filter.1 hx).1

/-- Merging with the span after the merged ids (`forwardMap[e+1]` is its size `q`; `e+1` does
not wrap around, `0` not being free). -/
theorem merge_next {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free f : List w64} {start ns nsz e q : w64} {len : Nat}
    (h : hashOK cnt sp bwm sets f) (hm : mInv free start len f ns nsz)
    (hend : uint.Z ns + uint.Z nsz = uint.Z e + 1) (hns : 1 ≤ uint.Z ns) (hq : sp !! (e + W64 1) = some q)
    (hge1 : ∀ x ∈ free, 1 ≤ uint.Z x) :
    mInv free start len (f.filter (fun x => !decide (inRun (e + W64 1) (uint.nat q) x))) ns
      (nsz + q) := by
  obtain ⟨hmem, hdis, hn1, hnw, hlen, hsub⟩ := hm
  obtain ⟨hq1, hqnw⟩ := h.1.1 _ q hq
  have hin : ∀ x, inRun (e + W64 1) (uint.nat q) x → x ∈ f := fun x hx => span_mem h.2.1 hq hx
  have hn1' : 1 ≤ uint.Z (e + W64 1) := hge1 _ (hsub _ (hin _ (hm_inRun_self (st := e + W64 1) (n := uint.nat q) (by word))))
  have he1 : uint.Z (e + W64 1) = uint.Z e + 1 := by word
  obtain ⟨hz, hzn⟩ := add_nowrap (a := nsz) (b := q) (by omega)
  have hcq : (uint.nat q : Int) = uint.Z q := by word
  have hcn : (uint.nat nsz : Int) = uint.Z nsz := by word
  have hrun : ∀ x, inRun ns (uint.nat (nsz + q)) x ↔
      inRun ns (uint.nat nsz) x ∨ inRun (e + W64 1) (uint.nat q) x := by
    intro x; unfold inRun; rw [hzn]; push_cast; omega
  have hfl := filter_not_length h.2.1.1.nodup (st := e + W64 1) (n := uint.nat q) (by word) hin
  have hle := span_le_len h.1 h.2.1 hq
  refine ⟨fun x => ?_, fun x hx => ?_, by word, by omega, ?_, fun x hx => ?_⟩
  · rw [← hmem x, hrun x, mem_filter_not, Or.comm (a := inRun ns _ x)]
    exact or_merge (hin x)
  · rw [mem_filter_not]
    rcases (hrun x).1 hx with hx' | hx'
    · exact fun h' => hdis x hx' h'.1
    · exact fun h' => h'.2 hx'
  · rw [hfl, hzn]; omega
  · exact hsub x (List.mem_filter.1 hx).1

/-- Adding the span at the end: the free ids are the merged ones, sorted. -/
theorem merge_final {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free f : List w64} {start ns nsz : w64} {len : Nat}
    (h : hashOK cnt sp bwm sets f) (hm : mInv free start len f ns nsz)
    (hfnd : free.Nodup) (hlen : free.length + len < 2 ^ 63) (hnw : uint.Z start + len ≤ 2 ^ 64)
    (hdis0 : ∀ x, inRun start len x → x ∉ free) :
    hashOK (cnt + nsz) (<[ns := nsz]> sp) (<[ns - W64 1 + nsz := nsz]> bwm)
      (<[nsz := <[ns := ()]> ((sets !! nsz).getD ∅)]> sets) (sortIds (free ++ runIds start len)) := by
  obtain ⟨hmem, hdis, hn1, hnw', hlen', hsub⟩ := hm
  have hnd : (free ++ runIds start len).Nodup := by
    rw [List.nodup_append]
    refine ⟨hfnd, runIds_nodup hnw, fun a ha b hb e => ?_⟩
    subst e; exact hdis0 a ((mem_runIds hnw).1 hb) ha
  refine hashOK_add h hn1 hnw' hdis (by omega) _ (sortIds_incr hnd) (fun x => ?_)
  rw [(sortIds_perm _).mem_iff, List.mem_append, mem_runIds hnw, hmem x]

end bbolt
end EtcdGrove
end Perennial
