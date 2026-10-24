/-
**The auth mode's tag** (the auth plan's A4, 2026-10-24; `notes/decisions.md`, "A4 of the auth
plan"). Lean-first (no Rocq counterpart).

A server's auth mode (`AuthMode`: `off`, `any`, `on γa`) is a field of its apply environment
(`apply.AEnv.authMode`), which the watch stream's specification (`v3rpc.watchDn`, over the
store's names `γ : mvcc.WsNames` and the stream's) cannot name. `modeTag γtag M` records the mode
under a ghost name the server chooses when it creates its watchable store (`mvcc.WsNames.tag`,
`newWatchableStore`'s `γtag`): persistent, two tags of one name agree (`modeTag_agree`). The
server's contract (`v3rpc.watchSrvOk`, from `NewServer`'s `srvWatchBuilt`) holds
`modeTag γ.tag E.authMode`; a registered watcher's description (`v3rpc.ctrlWatcher`) holds the
class of its interval in the mode some tag of `γ.tag` names, which is the server's.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode

/-- `AuthMode` as `Option (Option (GName × GName × GName × GName))` (`off`, `any`, `on γa` by its
names): for the ghost variable. -/
def AuthMode.enc : AuthMode → Option (Option (GName × GName × GName × GName))
  | .off => none
  | .any => some none
  | .on γa => some (some (γa.hist, γa.cur, γa.tok, γa.fresh))

def AuthMode.dec : Option (Option (GName × GName × GName × GName)) → AuthMode
  | none => .off
  | some none => .any
  | some (some (h, c, t, f)) => .on ⟨h, c, t, f⟩

theorem AuthMode.dec_enc (M : AuthMode) : AuthMode.dec (AuthMode.enc M) = M := by
  cases M <;> rfl

instance AuthMode.countable : Pos.Countable AuthMode :=
  countableOfLeftInverse AuthMode.enc AuthMode.dec AuthMode.dec_enc

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- **The tag `γtag` names the mode `M`** (persistent; see the file header). -/
def modeTag (γtag : GName) (M : AuthMode) : IProp GF := dghostVar γtag DFrac.discard M

instance modeTag_persistent (γtag : GName) (M : AuthMode) : Persistent (modeTag (GF := GF) γtag M) := by
  unfold modeTag; infer_instance

/-- A tag for the mode `M`, under a fresh name. -/
theorem modeTag_alloc (M : AuthMode) : ⊢ |==> ∃ γtag : GName, modeTag (GF := GF) γtag M := by
  imod dghostVar_alloc (GF := GF) M with ⟨%γ, H⟩
  imod dghostVar_persist γ 1 M $$ H with #H
  iexists γ
  unfold modeTag
  iexact H

/-- Two tags of one name name one mode. -/
theorem modeTag_agree (γtag : GName) (M M' : AuthMode) :
    ⊢ modeTag (GF := GF) γtag M -∗ modeTag γtag M' -∗ ⌜M = M'⌝ := by
  unfold modeTag
  iintro H1 H2
  iapply (dghostVar_agree γtag M DFrac.discard M' DFrac.discard) $$ H1 H2

end ghost

end auth
end EtcdGrove
end Perennial
