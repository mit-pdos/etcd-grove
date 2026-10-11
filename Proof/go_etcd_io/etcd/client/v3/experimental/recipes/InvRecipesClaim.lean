/-
The claim of a key at a mod revision (`client.go`'s `deleteRevKey`), the queue's linchpin: a claim
of `(key, rev)` succeeds at most at one revision (`revKeyDeleted_same_rev`). Lean-first (no Rocq
counterpart); see `decisions.md`, "Recipes: the client contracts reused, the queue's claim, two
prefixes as one".

From the history laws alone (`etcdState_revs`, `etcdState_create_persist`): if `(key, rev)` were
claimed at `r1 < r2`, the key-value the second claim saw at `r2 - 1` (mod revision `rev`, so
created at or before `rev < r1`) would have lived through `r1` (`etcdState_create_persist`), where
the first claim left `key` absent.

What the lemma does not say: that two transactions cannot both be at the same revision. The
client contract (`txnCommitResult`) gives each commit a revision and etcd's states around it, not
an exclusive token for the revision; so two dequeuers cannot be told apart from their claims
alone, and the queue's "dequeued at most once" needs, on top of this lemma, that a written
revision is one transaction's (a ghost token per written revision in the contract).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section claim
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- One direction of `revKeyDeleted_same_rev`: a claim of `(key, rev)` at `r1` excludes one at a
later `r2`. -/
theorem revKeyDeleted_not_lt (pfx key : GoString) (rev r1 r2 : w64)
    (hlt : sint.Z r1 < sint.Z r2) :
    revKeyDeleted (GF := GF) pfx key rev r1 ∗ revKeyDeleted pfx key rev r2 ⊢ ⌜False⌝ := by
  unfold revKeyDeleted
  iintro ⟨⟨%s1, %s1', #H1, #H1', %Hp1⟩, ⟨%s2, %s2', #H2, #H2', %Hp2⟩⟩
  ihave %Hrv1 := etcdState_revs (r1 - W64 1) pfx s1 $$ H1
  ihave %Hrv2 := etcdState_revs (r2 - W64 1) pfx s2 $$ H2
  ihave %Hcp := etcdState_create_persist (r2 - W64 1) r1 pfx s2 s1' $$ [$H2 $H1']
  ipureintro
  obtain ⟨hr1, ⟨v1, hv1, -, hm1⟩, habs1⟩ := Hp1
  obtain ⟨hr2, ⟨v2, hv2, hk2, hm2⟩, -⟩ := Hp2
  obtain ⟨-, -, hle1, -⟩ := Hrv1 v1 hv1
  obtain ⟨-, hcm2, -, -⟩ := Hrv2 v2 hv2
  have e1 : sint.Z (r1 - W64 1) = sint.Z r1 - 1 := by word
  have e2 : sint.Z (r2 - W64 1) = sint.Z r2 - 1 := by word
  rw [hm1] at hle1
  rw [hm2] at hcm2
  obtain ⟨v', hv', hk', -⟩ := Hcp v2 hv2 (by omega) (by omega)
  exact habs1 v' hv' (by rw [hk', hk2])

/-- **A claim happens once**: two successful claims of the same `(key, rev)` (`deleteRevKey`'s
`true`, `revKeyDeleted`) are at the same revision. -/
theorem revKeyDeleted_same_rev (pfx key : GoString) (rev r1 r2 : w64) :
    revKeyDeleted (GF := GF) pfx key rev r1 ∗ revKeyDeleted pfx key rev r2 ⊢ ⌜r1 = r2⌝ := by
  iintro ⟨#H1, #H2⟩
  rcases Int.lt_trichotomy (sint.Z r1) (sint.Z r2) with h | h | h
  · ihave %F := revKeyDeleted_not_lt pfx key rev r1 r2 h $$ [$H1 $H2]
    exact F.elim
  · ipureintro; word
  · ihave %F := revKeyDeleted_not_lt pfx key rev r2 r1 h $$ [$H2 $H1]
    exact F.elim

end claim

end recipes
end EtcdGrove
end Perennial
