/-
**A member's peer URL strings** (rafthttp stage 6a, D34): the form `http://host:port` whose
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
variable [FfiSyntax] [GoGlobalContext]

/-- **A URL `url.Parse` gives of a plain peer URL string**: scheme `http`, the host, nothing
else (rafthttp's `urlPlain`, with its `urlHostOk`), and `http://` and its host are the string. -/
def types.parsedPeerURL (s : GoString) (u : _root_.Perennial.net.url.URL) : Prop :=
  u.Scheme' = go!"http" ∧ u.Opaque' = "" ∧ u.User' = null ∧ u.Fragment' = "" ∧
    u.RawQuery' = "" ∧ u.RawPath' = "" ∧ u.RawFragment' = "" ∧ u.ForceQuery' = false ∧
    u.OmitHost' = false ∧ u.Path' = "" ∧ http.urlHostOk u.Host' ∧ s = go!"http://" ++ u.Host'

end url

example : types.plainPeerURL go!"http://127.0.0.1:2380" := by decide

end EtcdGrove
end Perennial
