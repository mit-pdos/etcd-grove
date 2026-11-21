/-
**The watch stream's key** (G2, 2026-10-30; `notes/g2-watch-auth.md`): the string
`streamKeyFromCtx` computes from a context's outgoing metadata (`client/v3/watch.go:1102-1107`),
which the watcher uses to share one gRPC stream among the watches whose contexts carry the same
metadata: `fmt.Sprintf("%+v", ...)` of the map, over its sorted finite key set (classically, for the
function-valued `GrpcMd`), with its two laws proved (2026-11-20; until then opaque, the laws
trust-boundary axioms). The key collides
(`nonissues/etcd-watch-stream-key-collision.md`); the laws hold only where it does not. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- Go's `%+v` of a `[]string`: `[v1 v2 ...]`, the values joined by spaces. -/
def fmtStrSlice (vs : List GoString) : GoString := go!"[" ++ [W8 32].intercalate vs ++ go!"]"

/-- A map entry as `%+v` prints it: `k:[v1 v2 ...]`. -/
def fmtMdEntry (m : GoString → Option (List GoString)) (k : GoString) : GoString :=
  k ++ go!":" ++ fmtStrSlice ((m k).getD [])

open Classical in
/-- The keys of the metadata `m` in the order `fmt` prints them (`internal/fmtsort`: strings by
`<`, bytewise): its finite support, sorted. A function with an infinite support is no Go map; it gets
`none`. -/
noncomputable def mdSortedKeys (m : GoString → Option (List GoString)) : Option (List GoString) :=
  if h : ∃ l : List GoString, ∀ k, (m k).isSome → k ∈ l then
    some ((((Classical.choose h).filter (fun k => (m k).isSome)).eraseDups).mergeSort
      (fun a b => decide (a ≤ b)))
  else none

/-- **The key `streamKeyFromCtx` computes from the outgoing metadata `m`**
(the `md` of `metadata.outMD ctx md`: what `FromOutgoingContext` returns): Go's
`fmt.Sprintf("%+v", map[string][]string(md))` (`map[k1:[v1 v2] k2:[...]]`, keys sorted, entries
and each value list joined by spaces) when there is metadata, `""` when there is none
(`client/v3/watch.go:1102-1107`). (2026-11-20: defined; until then opaque, with the two laws below
trust-boundary axioms. A function with an infinite support, no Go map, prints `map[ ]`: any value
with a space would do.) -/
noncomputable def streamKeyOf : GrpcMd → GoString
  | none => go!""
  | some m => match mdSortedKeys m with
    | some ks => go!"map[" ++ [W8 32].intercalate (ks.map (fmtMdEntry m)) ++ go!"]"
    | none => go!"map[ ]"

theorem streamKeyOf_some (m : GoString → Option (List GoString)) :
    ∃ x, streamKeyOf (some m) = go!"map[" ++ x ++ go!"]" := by
  cases h : mdSortedKeys m with
  | none => exact ⟨[W8 32], by simp [streamKeyOf, h]⟩
  | some ks => exact ⟨[W8 32].intercalate (ks.map (fmtMdEntry m)), by simp [streamKeyOf, h]⟩

/-- **Only "no metadata" gives the empty key** (G2's (c); proved 2026-11-20, a trust-boundary axiom
until then): any map, even an empty one, prints as `map[...]`, which is not `""`. -/
theorem streamKeyOf_none [GooseExts] (m : GrpcMd) : streamKeyOf m = streamKeyOf none → m = none := by
  intro h
  cases m with
  | none => rfl
  | some f =>
    obtain ⟨x, hx⟩ := streamKeyOf_some f
    rw [hx] at h
    simp [streamKeyOf] at h

theorem eraseDups_all_eq {α : Type} [BEq α] [LawfulBEq α] (l : List α) (k : α) (hne : l ≠ [])
    (hall : ∀ x ∈ l, x = k) : l.eraseDups = [k] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a rest =>
    have ha : a = k := hall a (List.mem_cons_self ..)
    subst ha
    rw [List.eraseDups_cons]
    have : rest.filter (fun b => !b == a) = [] :=
      List.filter_eq_nil_iff.2 (fun x hx => by simp [hall x (List.mem_cons_of_mem _ hx)])
    rw [this]; rfl

/-- The support of `mdAdd none k v` is `[k]`. -/
theorem mdSortedKeys_single (k v : GoString) :
    mdSortedKeys (fun k' => if k' = k then some [v] else none) = some [k] := by
  unfold mdSortedKeys
  have h : ∃ l : List GoString, ∀ k', ((fun k' => if k' = k then some [v] else none) k').isSome → k' ∈ l :=
    ⟨[k], fun k' hk => by by_cases e : k' = k <;> simp_all⟩
  rw [dite_eq_left_of_eq_true (eq_true h)]
  have hm : k ∈ Classical.choose h := Classical.choose_spec h k (by simp)
  have hf : ((Classical.choose h).filter
      (fun k' => ((fun k' => if k' = k then some [v] else none) k').isSome)).eraseDups = [k] := by
    apply eraseDups_all_eq
    · intro he
      have : k ∈ ((Classical.choose h).filter
          (fun k' => ((fun k' => if k' = k then some [v] else none) k').isSome)) :=
        List.mem_filter.2 ⟨hm, by simp⟩
      rw [he] at this; simp at this
    · intro x hx
      rw [List.mem_filter] at hx
      by_cases e : x = k
      · exact e
      · simp [e] at hx
  rw [hf, List.mergeSort_singleton]

/-- No space in a string. -/
def noSp (s : GoString) : Prop := W8 32 ∉ s

theorem intercalate_sp_noSp {l : List GoString} (h : noSp ([W8 32].intercalate l)) :
    l.length ≤ 1 := by
  match l, h with
  | [], _ => simp
  | [_], _ => simp
  | a :: b :: rest, h =>
    exfalso; apply h
    simp [List.intercalate_cons_cons]

/-- **A one-entry map's key determines its entry's values** (G2's (c); proved 2026-11-20, a
trust-boundary axiom until then), for a key `k`, a non-empty value `v` (Go prints `[]` and `[""]`
alike) and a key and value free of ` `, `:`, `[` and `]`: the printed `map[k:[v]]` has no space, so
the other map has one entry with one value (Go joins entries and values with spaces), and its key and
value are then read back from the only `:`. (`hk`, a lower-case key, is not needed.) -/
theorem streamKeyOf_single [GooseExts] (m : GrpcMd) (k v : GoString) (hk : metadata.lowerKey k)
    (hs : ∀ b ∈ k ++ v, b ∉ [W8 32, W8 58, W8 91, W8 93]) (hv : v ≠ go!"") :
    streamKeyOf m = streamKeyOf (metadata.mdAdd none k v) → metadata.mdVals m k = [v] := by
  intro h
  have hadd : metadata.mdAdd none k v = some (fun k' => if k' = k then some [v] else none) := by
    unfold metadata.mdAdd; congr 1
  have hE : streamKeyOf (metadata.mdAdd none k v) =
      go!"map[" ++ (k ++ go!":" ++ (go!"[" ++ v ++ go!"]")) ++ go!"]" := by
    rw [hadd]; simp [streamKeyOf, mdSortedKeys_single, fmtMdEntry, fmtStrSlice]
  rw [hE] at h
  have hkv : ∀ b ∈ k, b ≠ W8 32 ∧ b ≠ W8 58 := fun b hb => by
    have := hs b (List.mem_append_left _ hb); simp at this; exact ⟨this.1, this.2.1⟩
  have hvv : ∀ b ∈ v, b ≠ W8 32 ∧ b ≠ W8 58 := fun b hb => by
    have := hs b (List.mem_append_right _ hb); simp at this; exact ⟨this.1, this.2.1⟩
  cases m with
  | none => simp [streamKeyOf] at h
  | some f =>
    cases hks : mdSortedKeys f with
    | some ks =>
      simp only [streamKeyOf, hks] at h
      have h' := List.append_cancel_left (List.append_cancel_right h)
      -- no space on the right
      have hns : noSp ([W8 32].intercalate (ks.map (fmtMdEntry f))) := by
        rw [h']; unfold noSp; intro hm
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with ((hm | hm) | (hm | hm) | hm)
        · exact (hkv _ hm).1 rfl
        · exact absurd hm (by decide)
        · exact absurd hm (by decide)
        · exact (hvv _ hm).1 rfl
        · exact absurd hm (by decide)
      have hlen := intercalate_sp_noSp hns
      rw [List.length_map] at hlen
      match ks, h', hlen with
      | [], h', _ => simp at h'
      | [a], h', _ =>
        simp only [List.map_cons, List.map_nil, List.intercalate_singleton, fmtMdEntry,
          fmtStrSlice] at h'
        -- `a = k`: the only `:` on the right is after `k`
        have key : ∀ (a k r r' : List w8), (∀ b ∈ k, b ≠ W8 58) → W8 58 ∉ r' →
            a ++ W8 58 :: r = k ++ W8 58 :: r' → a = k ∧ r = r' := by
          intro a k r r' hk hr' he
          induction k generalizing a with
          | nil =>
            cases a with
            | nil => simpa using he
            | cons x a' =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
              exact absurd (he.2 ▸ List.mem_append_right _ (List.mem_cons_self ..)) hr'
          | cons y k' ih =>
            cases a with
            | nil =>
              simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
              exact absurd he.1.symm (hk y (List.mem_cons_self ..))
            | cons x a' =>
              simp only [List.cons_append, List.cons.injEq] at he
              obtain ⟨rfl, he⟩ := he
              have := ih a' (fun b hb => hk b (List.mem_cons_of_mem _ hb)) he
              exact ⟨by rw [this.1], this.2⟩
        have h'' : a ++ W8 58 :: (go!"[" ++ [W8 32].intercalate ((f a).getD []) ++ go!"]") =
            k ++ W8 58 :: (go!"[" ++ v ++ go!"]") := by simpa using h'
        obtain ⟨rfl, hr⟩ := key a k _ _ (fun b hb => (hkv b hb).2)
          (by intro hm; simp only [List.mem_append] at hm
              rcases hm with (hm | hm) | hm
              · simp at hm
              · exact (hvv _ hm).2 rfl
              · simp at hm) h''
        have hJ := List.append_cancel_left (List.append_cancel_right hr)
        have hns2 : noSp ([W8 32].intercalate ((f a).getD [])) := by
          rw [hJ]; intro hm; exact (hvv _ hm).1 rfl
        have hl2 := intercalate_sp_noSp hns2
        unfold metadata.mdVals
        simp only [Option.bind_some]
        match hfa : (f a).getD [], hJ, hl2 with
        | [], hJ, _ => exact absurd hJ.symm (by simpa using hv)
        | [w], hJ, _ => simp at hJ; rw [hJ]
    | none =>
      simp only [streamKeyOf, hks] at h
      have := congrArg List.length h
      simp at this
      have : v.length ≠ 0 := by simpa using hv
      omega

end EtcdGrove
end Perennial
