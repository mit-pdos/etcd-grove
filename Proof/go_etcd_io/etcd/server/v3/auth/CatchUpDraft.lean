/-
**The auth store's catch-up at a snapshot install (Draft; `notes/snapshot-auth-on-plan.md`, Q1 (b)).**
No `axiom`, no `sorry`.

With auth on, a member that installs a snapshot jumps from the auth state of its applied prefix `A`
to the image's, the state after `A'`, skipping the admin entries between. The server's tie of the
store's history to the log (`authHistTie`) keeps the history a prefix of the committed log's admin
states, so the skipped states are appended to the history, then the image's. Under candidate (ii)
("record first", the user's decision 4 of 2026-11-01) the append is ghost-only and comes before
`Recover` (`auth.authCatchUpFirst`, `SnapAuthOnDraft.lean`); this file keeps its one lemma,
`authHist_appendL`, the list form of `authHist_append`. (Candidate (i)'s catch-up inside
`setRevision`, `setRevision.specN`, was dropped with it: review R1's F11.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section ghost
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **`authHist_append` for a list** of states. -/
theorem auth.authHist_appendL (γa : AuthNames) (hs L : List AuthState)
    (hk : ∀ st ∈ L, permKeysOk st) : authHist (GF := GF) γa hs ∗ authHistRev γa hs ⊢
      |==> (authHist γa (hs ++ L) ∗ authHistRev γa (hs ++ L)) := by
  unfold authHist
  iintro ⟨⟨H, %Hk⟩, Hr⟩
  ihave H := (authHist_full γa hs).2 $$ [H Hr]
  · iframe H Hr
  imod (monoListAuthOwn_update_app (γ := γa.hist) (l := hs) L) $$ H with ⟨H, -⟩
  icases (authHist_full γa (hs ++ L)).1 $$ H with ⟨H, Hr⟩
  imodintro
  iframe H Hr
  ipureintro
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Hk x hx
  · exact hk x hx

end ghost

end EtcdGrove
end Perennial
