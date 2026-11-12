/-
**A cluster member, as a value** (`apply.MemberM`): moved out of `RestModel.lean` (D43 M5b,
2026-10-26) so that the membership package's predicates (`membership.memberAt`, the cluster's
in-memory members) can name it without importing the apply model. Lean-first.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

/-- **A cluster member, as a value** (`membership.Member`: its id, its `RaftAttributes`' peer
URLs and learner flag, its `Attributes`' name and client URLs): what `json.Unmarshal` of a
member's JSON gives (the members' records and a conf change's context are the members' JSON). -/
structure MemberM where
  id : w64
  peerURLs : List GoString
  isLearner : Bool
  name : GoString
  clientURLs : List GoString
  deriving Inhabited

end apply
end EtcdGrove
end Perennial
