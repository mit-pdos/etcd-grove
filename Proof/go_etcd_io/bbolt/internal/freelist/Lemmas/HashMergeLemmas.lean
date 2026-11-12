/-
Pure lemmas for `hashMap.mergeWithExistingSpan` and `hashMap.mergeSpans`: the state of
`mergeWithExistingSpan` (`mInv`: the span `newStart..` it is about to add and the free ids left
make up the free ids and the merged ids) through its merge with the span before (`merge_prev`)
and after (`merge_next`), and the span it adds at the end (`merge_final`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashLemmas

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.freelist

theorem add_nowrap {a b : w64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat ∧ (a + b).toNat = a.toNat + b.toNat := by
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
  (∀ x, x ∈ f ∨ inRun ns (nsz.toNat) x ↔ x ∈ free ∨ inRun start len x) ∧
  (∀ x, inRun ns (nsz.toNat) x → x ∉ f) ∧ 1 ≤ nsz.toNat ∧
  ns.toNat + nsz.toNat ≤ 2 ^ 64 ∧ f.length + nsz.toNat = free.length + len ∧
  (∀ x ∈ f, x ∈ free)

theorem mInv_init {free : List w64} {start e : w64} (hle : start.toNat ≤ e.toNat)
    (h1 : 1 ≤ start.toNat) (hdis : ∀ x, inRun start ((e - start).toNat + 1) x → x ∉ free) :
    mInv free start ((e - start).toNat + 1) free start (e - start + W64 1) ∧
    start.toNat + (e - start + W64 1).toNat = e.toNat + 1 := by
  have hn : (e - start + W64 1).toNat = (e - start).toNat + 1 := by word
  refine ⟨⟨fun x => by rw [hn], fun x hx => hdis x (by rw [← hn]; exact hx), by word, by word,
    by rw [hn], fun x hx => hx⟩, by word⟩

/-- Merging with the span before `start` (`backwardMap[start-1]` is its size `p`): it starts at
`start-1+1-p`, before `start`; the span to add starts there now. -/
theorem merge_prev {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free f : List w64} {start nsz p : w64} {len : Nat}
    (h : hashOK cnt sp bwm sets f) (hm : mInv free start len f start nsz)
    (hp : bwm !! (start - W64 1) = some p) (h1 : 1 ≤ start.toNat)
    (hge1 : ∀ x ∈ free, 1 ≤ x.toNat) :
    sp !! (start - W64 1 + W64 1 - p) = some p ∧
    (start - W64 1 + W64 1 - p).toNat < start.toNat ∧
    mInv free start len
      (f.filter (fun x => !decide (inRun (start - W64 1 + W64 1 - p) (p.toNat) x)))
      (start - p) (nsz + p) ∧
    (start - p).toNat + (nsz + p).toNat = start.toNat + nsz.toNat := by
  obtain ⟨hmem, hdis, hn1, hnw, hlen, hsub⟩ := hm
  obtain ⟨st', hs', hk⟩ := (h.2.2.1.1 _ p).1 hp
  obtain ⟨hp1, hpnw⟩ := h.1.1 st' p hs'
  have hnum : st'.toNat + p.toNat = start.toNat := by
    have e1 : (start - W64 1).toNat = start.toNat - 1 := by word
    have e2 : (st' + p - W64 1).toNat = st'.toNat + p.toNat - 1 := by word
    rw [hk, e2] at e1; omega
  have hst : start - W64 1 + W64 1 - p = st' := by word
  have hsp : start - p = st' := by word
  rw [hst, hsp]
  have hin : ∀ x, inRun st' (p.toNat) x → x ∈ f := fun x hx => span_mem h.2.1 hs' hx
  have hst1 : 1 ≤ st'.toNat := hge1 st' (hsub st' (hin st' (hm_inRun_self (by word))))
  obtain ⟨hz, hzn⟩ := add_nowrap (a := nsz) (b := p) (by omega)
  have hcp : (p.toNat : Int) = p.toNat := by word
  have hcn : (nsz.toNat : Int) = nsz.toNat := by word
  have hrun : ∀ x, inRun st' ((nsz + p).toNat) x ↔ inRun st' (p.toNat) x ∨ inRun start (nsz.toNat) x := by
    intro x; unfold inRun; rw [hzn]; push_cast; omega
  have hfl := filter_not_length h.2.1.1.nodup (st := st') (n := p.toNat) (by word) hin
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
    (hend : ns.toNat + nsz.toNat = e.toNat + 1) (hns : 1 ≤ ns.toNat) (hq : sp !! (e + W64 1) = some q)
    (hge1 : ∀ x ∈ free, 1 ≤ x.toNat) :
    mInv free start len (f.filter (fun x => !decide (inRun (e + W64 1) (q.toNat) x))) ns
      (nsz + q) := by
  obtain ⟨hmem, hdis, hn1, hnw, hlen, hsub⟩ := hm
  obtain ⟨hq1, hqnw⟩ := h.1.1 _ q hq
  have hin : ∀ x, inRun (e + W64 1) (q.toNat) x → x ∈ f := fun x hx => span_mem h.2.1 hq hx
  have hn1' : 1 ≤ (e + W64 1).toNat := hge1 _ (hsub _ (hin _ (hm_inRun_self (st := e + W64 1) (n := q.toNat) (by word))))
  have he1 : (e + W64 1).toNat = e.toNat + 1 := by word
  obtain ⟨hz, hzn⟩ := add_nowrap (a := nsz) (b := q) (by omega)
  have hcq : (q.toNat : Int) = q.toNat := by word
  have hcn : (nsz.toNat : Int) = nsz.toNat := by word
  have hrun : ∀ x, inRun ns ((nsz + q).toNat) x ↔
      inRun ns (nsz.toNat) x ∨ inRun (e + W64 1) (q.toNat) x := by
    intro x; unfold inRun; rw [hzn]; push_cast; omega
  have hfl := filter_not_length h.2.1.1.nodup (st := e + W64 1) (n := q.toNat) (by word) hin
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
    (hfnd : free.Nodup) (hlen : free.length + len < 2 ^ 63) (hnw : start.toNat + len ≤ 2 ^ 64)
    (hdis0 : ∀ x, inRun start len x → x ∉ free) :
    hashOK (cnt + nsz) (<[ns := nsz]> sp) (<[ns - W64 1 + nsz := nsz]> bwm)
      (<[nsz := <[ns := ()]> ((sets !! nsz).getD ∅)]> sets) (sortPgids (free ++ runIds start len)) := by
  obtain ⟨hmem, hdis, hn1, hnw', hlen', hsub⟩ := hm
  have hnd : (free ++ runIds start len).Nodup := by
    rw [List.nodup_append]
    refine ⟨hfnd, runIds_nodup hnw, fun a ha b hb e => ?_⟩
    subst e; exact hdis0 a ((mem_runIds hnw).1 hb) ha
  refine hashOK_add h hn1 hnw' hdis (by omega) _ (sortPgids_incr hnd) (fun x => ?_)
  rw [(sortPgids_perm _).mem_iff, List.mem_append, mem_runIds hnw, hmem x]

end bbolt
end EtcdGrove
end Perennial
