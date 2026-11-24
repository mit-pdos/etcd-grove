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

/-- `jenc_S_string` of a `[]string` holding `xs`: `null` if it is nil, else a JSON array. -/
def membership.jsonStrSlice (isNil : Bool) (xs : List GoString) : List w8 :=
  if isNil then go!"null" else [W8 91] ++ membership.jsonStrs xs ++ [W8 93]

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
