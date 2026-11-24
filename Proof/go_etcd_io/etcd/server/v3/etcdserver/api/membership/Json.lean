/-
The JSON the encoding/json model writes for membership's record types (#24 J2): jsongen's
same-package methods (`JSONModelMarshal`, `JSONModelMarshalPtr`, generated into `json_model_gen.go`
by `etc/goose.py`'s `jsonmodel_roots`) as Lean functions of the value and of its URL slices' strings.
What `json.Marshal` of a `Member` returns (`memberJson`) is what `EtcdServer.AddMember`'s and
bootstrap's `json.Marshal` write into a conf change's context (#34: `ctxs = json.Marshal` of each
member). Mirrors of the generated Go code (`jenc_Member`, ...); the claim that these are real
encoding/json's bytes is jsongen's (tested by `examples/models/jsonetcd/jsonmodel_forks.py`). Pure.
-/
module

public import Net.Proof.models_lab.jsoncodec.Quote
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.membership

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open models_lab.jsoncodec Classical

/-- The strings `xs`, each as a JSON string, separated by `,`. -/
def membership.jsonStrs : List GoString → List w8
  | [] => []
  | [x] => jsonQuote x
  | x :: xs => jsonQuote x ++ [W8 44] ++ membership.jsonStrs xs

theorem membership.jsonStrs_cons (x : GoString) (rest : List GoString) :
    membership.jsonStrs (x :: rest) =
      jsonQuote x ++ (if rest = [] then [] else [W8 44] ++ membership.jsonStrs rest) := by
  cases rest <;> simp [membership.jsonStrs]

/-- The strings' JSON grows by one string (after a `,` unless it is the first). -/
theorem membership.jsonStrs_take_succ (xs : List GoString) (k : Nat) (h : k < xs.length) :
    membership.jsonStrs (xs.take (k + 1)) =
      membership.jsonStrs (xs.take k) ++ (if k = 0 then [] else [W8 44]) ++ jsonQuote xs[k] := by
  induction xs generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp [membership.jsonStrs]
    | succ k =>
      have hk : k < xs.length := by simp at h; omega
      have hne : xs.take (k + 1) ≠ [] := by
        intro h'; have := congrArg List.length h'; rw [List.length_take, List.length_nil] at this; omega
      rw [List.take_succ_cons, List.take_succ_cons, List.getElem_cons_succ,
        membership.jsonStrs_cons, membership.jsonStrs_cons]
      simp only [hne, ↓reduceIte]
      rw [ih k hk]
      by_cases hk0 : k = 0
      · subst hk0; simp [membership.jsonStrs]
      · have hne2 : xs.take k ≠ [] := by
          intro h'; have := congrArg List.length h'; rw [List.length_take, List.length_nil] at this; omega
        simp only [hne2, hk0, ↓reduceIte]; simp

/-- `jenc_S_string` of a `[]string` holding `xs`: `null` if it is nil, else a JSON array. -/
def membership.jsonStrSlice (isNil : Bool) (xs : List GoString) : List w8 :=
  if isNil then go!"null" else [W8 91] ++ membership.jsonStrs xs ++ [W8 93]

/-- A string's length (below `2 ^ 63`) is `0` as a word exactly when it is empty. -/
theorem membership.strlen_w64_iff (s : GoString) (h : s.length < 2 ^ 63) :
    W64 (s.length : Int) = W64 0 ↔ s = [] := by
  constructor
  · intro e; have : s.length = 0 := by word
    exact List.eq_nil_of_length_eq_zero this
  · intro e; subst e; rfl

/-- A slice holding `xs` has length `0` exactly when `xs` is empty. -/
theorem membership.slicelen_w64_iff (sl : GoSlice) (xs : List GoString)
    (h : xs.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) : sl.len = W64 0 ↔ xs = [] := by
  constructor
  · intro e; rw [e] at h; apply List.eq_nil_of_length_eq_zero; rw [h.1]; rfl
  · intro e; subst e; simp at h; word

section json
variable [GooseExts]

/-- The members of a `Member`'s JSON object (its flattened fields: `id`, `peerURLs`, `isLearner`
omitted when false, `name` omitted when empty, `clientURLs` omitted when empty), the URL slices
holding `ps` and `cs`. -/
def membership.memberFieldsJson (m : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (ps cs : List GoString) : List w8 :=
  go!"\"id\":" ++ decU64 m.ID' ++ go!",\"peerURLs\":" ++
    membership.jsonStrSlice (decide (m.RaftAttributes'.PeerURLs' = slice.nil)) ps ++
    (if m.RaftAttributes'.IsLearner' then go!",\"isLearner\":true" else []) ++
    (if m.Attributes'.Name' = [] then [] else go!",\"name\":" ++ jsonQuote m.Attributes'.Name') ++
    (if cs = [] then [] else go!",\"clientURLs\":" ++
      membership.jsonStrSlice (decide (m.Attributes'.ClientURLs' = slice.nil)) cs)

/-- **`json.Marshal` of a `Member`** (value or pointer), its URL slices holding `ps` and `cs`. -/
def membership.memberJson (m : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (ps cs : List GoString) : List w8 :=
  [W8 123] ++ membership.memberFieldsJson m ps cs ++ [W8 125]

/-- **`json.Marshal` of a `ConfigChangeContext`**: the embedded member's fields, then `isPromote`. -/
def membership.ccJson (c : go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext)
    (ps cs : List GoString) : List w8 :=
  [W8 123] ++ membership.memberFieldsJson c.Member' ps cs ++ go!",\"isPromote\":" ++
    (if c.IsPromote' then go!"true" else go!"false") ++ [W8 125]

end json

end EtcdGrove
end Perennial
