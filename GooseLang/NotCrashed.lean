/-
**The crash token as this repository uses it.** The crash-token update (`ncfupd`, `|NC={E1,E2}=>`),
`wp_ncfupd`, `wp_ncfupd_post`, `wp_atomic_nc` and `wp_notCrashed_acc` are Perennial's
(`Perennial/GooseLang/NotCrashed.lean`, `7ad4f91b1`; until the merge of `lean` on 2026-11-21 a
local copy lived here, `notes/perennial-changes.md`). What is left is a notation, `notCrashedG`.
-/
module

public import Perennial.GooseLang.NotCrashed

@[expose] public section

namespace Perennial

/-- **The generation's `notCrashed`, at the program's own ghost state** (`gooseAllG`, the state
interpretation's): what `wp_ncfupd` hands out. A client that also assumes its own `[AllG GF]`
(kvdurable) names the token by this, so that its `notCrashed` is the one raft's specs mention
(a notation, so that the proof mode sees the same term). -/
scoped notation "notCrashedG" => @notCrashed _ GooseGlobalGS.gooseAllG GooseLocalGS.goose_crashGS

end Perennial
