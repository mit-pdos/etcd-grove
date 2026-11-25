/-
What the encoding/json model decodes into a `membership.ConfigChangeContext` (#24 J2 batch 2b), as
Lean functions of the bytes: `membership.ccDecode`, and from it `membership.ccContextOf` (the
member's id and `IsPromote`) and `membership.ccMemberOf` (the member), opaque until 2026-11-24.

They mirror the generated decoder (`jdec_ConfigChangeContext`, `jdecMember_ConfigChangeContext`,
`jdec_S_string`, membership's `json_model_gen.go`, over `models.lab/jsoncodec`'s helpers) on the
inputs whose decoding is proved, and are `none` elsewhere: a compact JSON object (no whitespace) of
distinct members, each an exact field name (`id`, `peerURLs`, `isLearner`, `name`, `clientURLs`,
`isPromote`) with a value of the field's kind (`id` a decimal number below `2 ^ 64`, a URL list an
array of strings or `null`, a flag `true` or `false`, the name a string), every string plain
(`JsonScan.okB`: printable ASCII but `"` and `\`, the subset the model's `jsoncodec.Str` decodes)
and the whole one value to the scanner (`JsonScan.scanL`: the model's `Valid`). Decoded into a
zero `ConfigChangeContext` (what both callers pass), a field the object omits stays zero. On other
inputs (whitespace, other or case-folded keys, `null` scalars, escapes, duplicates, type errors) the
model may still decode, but these functions claim nothing (`none`, and the specs over them take
`ccContextOf bs = some _` as a premise). Pure.
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.Lits
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.MemberModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Classical

/-- A JSON member's value, in the decoded subset. -/
inductive membership.JVal where
  | num (n : Nat)
  | str (s : List w8)
  | bool (b : Bool)
  | null
  | arr (xs : List (List w8))

/-- A plain string's JSON: its bytes between quotes. -/
def membership.jquoted (s : List w8) : List w8 := 34#8 :: (s ++ [34#8])

/-- Plain strings' JSON, separated by `,`. -/
def membership.jstrs : List (List w8) → List w8
  | [] => []
  | [x] => membership.jquoted x
  | x :: xs => membership.jquoted x ++ 44#8 :: membership.jstrs xs

/-- A value's JSON. -/
def membership.JVal.json : membership.JVal → List w8
  | .num n => JsonScan.decN n
  | .str s => membership.jquoted s
  | .bool true => go!"true"
  | .bool false => go!"false"
  | .null => go!"null"
  | .arr xs => 91#8 :: (membership.jstrs xs ++ [93#8])

/-- An object's members' JSON (`"key":value`, separated by `,`). -/
def membership.jmembers : List (List w8 × membership.JVal) → List w8
  | [] => []
  | [(k, v)] => membership.jquoted k ++ 58#8 :: v.json
  | (k, v) :: ms => membership.jquoted k ++ 58#8 :: (v.json ++ 44#8 :: membership.jmembers ms)

/-- An object's JSON. -/
def membership.jobj (ms : List (List w8 × membership.JVal)) : List w8 :=
  123#8 :: (membership.jmembers ms ++ [125#8])

/-- A decoded `ConfigChangeContext`: its member and `IsPromote`. -/
structure membership.CcM where
  m : apply.MemberM
  promote : Bool

/-- The zero `ConfigChangeContext` (what `new(ConfigChangeContext)` holds). -/
def membership.ccZero : membership.CcM :=
  ⟨⟨W64 0, [], false, [], []⟩, false⟩

/-- Plain strings (`JsonScan.okB` bytes). -/
def membership.plainStr (s : List w8) : Prop := ∀ c ∈ s, JsonScan.okB c

/-- A URL list's value: an array of plain strings, or `null` (the nil slice). -/
def membership.strsOf : membership.JVal → Option (List (List w8))
  | .arr xs => if ∀ x ∈ xs, membership.plainStr x then some xs else none
  | .null => some []
  | _ => none

/-- **One member `k: v` decoded into `r`** (`jdecMember_ConfigChangeContext` at an exact field
name): `none` outside the decoded subset. -/
def membership.ccSet (k : List w8) (v : membership.JVal) (r : membership.CcM) :
    Option membership.CcM :=
  if k = go!"id" then
    match v with
    | .num n => if n < 2 ^ 64 then some { r with m := { r.m with id := W64 (n : Int) } } else none
    | _ => none
  else if k = go!"peerURLs" then
    (membership.strsOf v).map fun xs => { r with m := { r.m with peerURLs := xs } }
  else if k = go!"isLearner" then
    match v with
    | .bool b => some { r with m := { r.m with isLearner := b } }
    | _ => none
  else if k = go!"name" then
    match v with
    | .str s => if membership.plainStr s then some { r with m := { r.m with name := s } } else none
    | _ => none
  else if k = go!"clientURLs" then
    (membership.strsOf v).map fun xs => { r with m := { r.m with clientURLs := xs } }
  else if k = go!"isPromote" then
    match v with
    | .bool b => some { r with promote := b }
    | _ => none
  else none

/-- The members decoded in order into `r`. -/
def membership.ccFold : List (List w8 × membership.JVal) → membership.CcM → Option membership.CcM
  | [], r => some r
  | (k, v) :: ms, r => (membership.ccSet k v r).bind (membership.ccFold ms)

/-- `ms` is an object the decoded subset covers: distinct keys, each member decoded. -/
def membership.ccObjOk (ms : List (List w8 × membership.JVal)) : Prop :=
  (ms.map Prod.fst).Nodup ∧ (membership.ccFold ms membership.ccZero).isSome

/-- **What the encoding/json model decodes `bs` into, in a zero `ConfigChangeContext`** (see the
file header): `some` exactly when `bs` is one value to the scanner and the JSON of an object
`ccObjOk` covers; then that object's decoding. -/
def membership.ccDecode (bs : List w8) : Option membership.CcM :=
  if h : JsonScan.scanL bs true = (0, bs.length) ∧
      ∃ ms, membership.ccObjOk ms ∧ membership.jobj ms = bs then
    membership.ccFold (Classical.choose h.2) membership.ccZero
  else none

/-- **`json.Unmarshal` of a conf change's context into a `membership.ConfigChangeContext`**
(audit phase B3, 2026-10-18; a definition since 2026-11-24, `ccDecode`): the member's `ID` and
`IsPromote` when the bytes decode, `none` when they do not or are outside the decoded subset
(where `applyConfChange` and `ValidateConfigurationChange` take them to decode). -/
def membership.ccContextOf (bs : List w8) : Option (w64 × Bool) :=
  (membership.ccDecode bs).map fun r => (r.m.id, r.promote)

/-- **The member a conf change's context unmarshals to** (`json.Unmarshal` into a
`membership.ConfigChangeContext`'s embedded `Member`; a definition since 2026-11-24, `ccDecode`;
moved to `SrvRaftLog` from `InvRest`, 2026-11-04, for `ccApplyOk`): what `applyConfChange`'s
`AddMember` saves. The zero member when the bytes do not decode. -/
def membership.ccMemberOf (bs : List w8) : apply.MemberM :=
  ((membership.ccDecode bs).getD membership.ccZero).m

/-! ## Facts -/

theorem membership.ccDecode_some {bs : List w8} {r : membership.CcM}
    (h : membership.ccDecode bs = some r) :
    JsonScan.scanL bs true = (0, bs.length) ∧
      ∃ ms, membership.ccObjOk ms ∧ membership.jobj ms = bs ∧
        membership.ccFold ms membership.ccZero = some r := by
  unfold membership.ccDecode at h
  split at h
  · rename_i hh
    exact ⟨hh.1, _, (Classical.choose_spec hh.2).1, (Classical.choose_spec hh.2).2, h⟩
  · cases h

theorem membership.ccContextOf_some {bs : List w8} {id : w64} {prom : Bool}
    (h : membership.ccContextOf bs = some (id, prom)) :
    ∃ r, membership.ccDecode bs = some r ∧ r.m.id = id ∧ r.promote = prom ∧
      membership.ccMemberOf bs = r.m := by
  unfold membership.ccContextOf at h
  cases hd : membership.ccDecode bs with
  | none => rw [hd] at h; cases h
  | some r =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨r, rfl, h.1, h.2, by unfold membership.ccMemberOf; rw [hd]; rfl⟩

theorem membership.jstrs_cons (x : List w8) (xs : List (List w8)) :
    membership.jstrs (x :: xs) =
      membership.jquoted x ++ (if xs = [] then [] else 44#8 :: membership.jstrs xs) := by
  cases xs <;> simp [membership.jstrs]

theorem membership.jmembers_cons (k : List w8) (v : membership.JVal)
    (ms : List (List w8 × membership.JVal)) :
    membership.jmembers ((k, v) :: ms) =
      membership.jquoted k ++ 58#8 :: (v.json ++ (if ms = [] then [] else 44#8 :: membership.jmembers ms)) := by
  cases ms <;> simp [membership.jmembers]

/-- A member `ccSet` decodes has a plain key (one of the six field names). -/
theorem membership.ccSet_key_plain {k : List w8} {v : membership.JVal} {r r' : membership.CcM}
    (h : membership.ccSet k v r = some r') : membership.plainStr k := by
  unfold membership.ccSet at h
  by_cases h1 : k = go!"id"
  · subst h1; unfold membership.plainStr JsonScan.okB; decide
  rw [if_neg h1] at h
  by_cases h2 : k = go!"peerURLs"
  · subst h2; unfold membership.plainStr JsonScan.okB; decide
  rw [if_neg h2] at h
  by_cases h3 : k = go!"isLearner"
  · subst h3; unfold membership.plainStr JsonScan.okB; decide
  rw [if_neg h3] at h
  by_cases h4 : k = go!"name"
  · subst h4; unfold membership.plainStr JsonScan.okB; decide
  rw [if_neg h4] at h
  by_cases h5 : k = go!"clientURLs"
  · subst h5; unfold membership.plainStr JsonScan.okB; decide
  rw [if_neg h5] at h
  by_cases h6 : k = go!"isPromote"
  · subst h6; unfold membership.plainStr JsonScan.okB; decide
  rw [if_neg h6] at h
  cases h

end EtcdGrove
end Perennial
