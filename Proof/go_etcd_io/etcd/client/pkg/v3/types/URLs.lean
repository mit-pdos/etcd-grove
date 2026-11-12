/-
**A member's peer URL strings** (rafthttp stage 6a, D39): the form `http://host:port` whose
`url.Parse` gives a URL with only its scheme and host set, what `types.NewURLs` returns for the
transport's peers (`Spec/go_etcd_io/etcd/client/pkg/v3/types/NewURLs.lean`). Decidable, so a
closed theorem's directory is checked by `decide`. Lean-first.
-/
module

public import Proof.net.http.Boundary

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- A host byte: a letter, a digit, `.` or `-`. -/
def types.hostByte (c : w8) : Prop :=
  (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨
    c.toNat = 46 ∨ c.toNat = 45

instance (c : w8) : Decidable (types.hostByte c) := by unfold types.hostByte; infer_instance

/-- A digit. -/
def types.digitByte (c : w8) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

instance (c : w8) : Decidable (types.digitByte c) := by unfold types.digitByte; infer_instance

/-- **`host:port`**: a non-empty host of host bytes, one `:`, a non-empty port of digits (what
`net.SplitHostPort` accepts, without IPv6 brackets). -/
def types.plainHostPort (h : GoString) : Prop :=
  let i := h.idxOf (58 : w8)
  0 < i ∧ i + 1 < h.length ∧ (∀ c ∈ h.take i, types.hostByte c) ∧
    (∀ c ∈ h.drop (i + 1), types.digitByte c)

instance (h : GoString) : Decidable (types.plainHostPort h) := by
  unfold types.plainHostPort; infer_instance

/-- **A plain peer URL string**: `http://host:port`. -/
def types.plainPeerURL (s : GoString) : Prop :=
  go!"http://".isPrefixOf s = true ∧ types.plainHostPort (s.drop 7)

instance (s : GoString) : Decidable (types.plainPeerURL s) := by
  unfold types.plainPeerURL; infer_instance

section url
variable [GooseExts] [GoGlobalContext]

/-- **A URL `url.Parse` gives of a plain peer URL string**: scheme `http`, the host, nothing
else (rafthttp's `urlPlain`, with its `urlHostOk`), and `http://` and its host are the string. -/
def types.parsedPeerURL (s : GoString) (u : _root_.Perennial.net.url.URL) : Prop :=
  u.Scheme' = go!"http" ∧ u.Opaque' = "" ∧ u.User' = null ∧ u.Fragment' = "" ∧
    u.RawQuery' = "" ∧ u.RawPath' = "" ∧ u.RawFragment' = "" ∧ u.ForceQuery' = false ∧
    u.OmitHost' = false ∧ u.Path' = "" ∧ http.urlHostOk u.Host' ∧ s = go!"http://" ++ u.Host'

end url

example : types.plainPeerURL go!"http://127.0.0.1:2380" := by decide

/-- A byte of a plain `host:port` is a host byte, `:` or a digit (2026-10-27, D22 J-T, W8). -/
theorem types.plainHostPort_mem (h : GoString) (hp : types.plainHostPort h) (c : w8)
    (hc : c ∈ h) : types.hostByte c ∨ c = 58 ∨ types.digitByte c := by
  unfold types.plainHostPort at hp
  generalize hi : h.idxOf 58 = i at hp
  obtain ⟨h0, h1, ht, hd⟩ := hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  rcases Nat.lt_trichotomy j i with hlt | heq | hgt
  · left
    exact ht _ (List.mem_iff_getElem.2 ⟨j, by rw [List.length_take]; omega,
      by rw [List.getElem_take]⟩)
  · right; left; subst heq
    have hlt : h.idxOf 58 < h.length := by omega
    have := List.getElem_idxOf hlt
    simp only [hi] at this
    exact this
  · right; right
    exact hd _ (List.mem_iff_getElem.2 ⟨j - (i + 1), by rw [List.length_drop]; omega,
      by rw [List.getElem_drop]; congr 1; omega⟩)

/-- A plain `host:port` is non-empty and of bytes `url.URL.String` writes unescaped. -/
theorem types.plainHostPort_noEscape (h : GoString) (hp : types.plainHostPort h) :
    h ≠ [] ∧ ∀ c ∈ h, http.hostByteNoEscape c := by
  refine ⟨fun e => by subst e; exact absurd hp.2.1 (by simp), fun c hc => ?_⟩
  rcases types.plainHostPort_mem h hp c hc with hb | rfl | hd
  · unfold types.hostByte at hb; unfold http.hostByteNoEscape; omega
  · unfold http.hostByteNoEscape; right; right; right; right; right; rfl
  · unfold types.digitByte at hd; unfold http.hostByteNoEscape; omega

/-- A plain peer URL string has no `,` (the separator of the `X-PeerURLs` header). -/
theorem types.plainPeerURL_noComma (s : GoString) (hp : types.plainPeerURL s) :
    (44 : w8) ∉ s := by
  obtain ⟨hpre, hhp⟩ := hp
  intro hc
  have hs : s = go!"http://" ++ s.drop 7 := by
    have h := List.isPrefixOf_iff_prefix.1 hpre
    obtain ⟨t, ht⟩ := h
    rw [← ht]; simp
  rw [hs] at hc
  rcases List.mem_append.1 hc with h | h
  · revert h; decide
  · rcases types.plainHostPort_mem _ hhp 44 h with hb | hb | hb
    · unfold types.hostByte at hb; revert hb; decide
    · revert hb; decide
    · unfold types.digitByte at hb; revert hb; decide

end EtcdGrove
end Perennial
