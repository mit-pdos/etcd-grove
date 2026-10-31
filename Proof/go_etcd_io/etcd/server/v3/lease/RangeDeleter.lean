/-
The lessor's range deleter as its owner holds it (the lease-revoke plan, R2, D4-3, 2026-10-31).
Lean-first (no Rocq counterpart).

`rdAt γl s`: the owner's half of `le.rd` (`rdOwn`) at a deleter that, at every watchable store over
the inner store `s` (whatever its names), is that store's `Write` (`mvcc.rdIs`). `lessor.Revoke`
reads the field by it and gives it back. Here, not in `apply`, since its producers are the lessor's
and mvcc's constructors (the review's F5); nothing gives it yet (`mvcc.New`/`newWatchableStore` give
the deleter's contract at their own names only, and the snapshot's `Recover` replaces the deleter:
both are L3c's).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [lease_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The lessor's range deleter, held** (not persistent): the owner's half of `le.rd` at a
deleter that is the `Write` of every watchable store over the inner store `s`. -/
def rdAt (γl : GName) (s : Loc) : IProp GF :=
  iprop(∃ rd : GoFunc, rdOwn γl rd ∗
    □ ∀ (ws : Loc) (γw : mvcc.WsNames), mvcc.isWatchableStore ws s γw -∗ mvcc.rdIs rd ws s γw)

/-- `rdAt` from the owner's half at a deleter that is every such store's `Write`. -/
theorem rdAt_intro (γl : GName) (s : Loc) (rd : GoFunc) :
    rdOwn γl rd ∗
      □ (∀ (ws : Loc) (γw : mvcc.WsNames), mvcc.isWatchableStore ws s γw -∗ mvcc.rdIs rd ws s γw) ⊢
      rdAt (GF := GF) γl s := by
  iintro ⟨Ho, #Hd⟩
  iunfold rdAt
  iexists rd
  iframe Ho Hd

/-- `rdAt`'s deleter, with its contract at every watchable store over `s`. -/
theorem rdAt_elim (γl : GName) (s : Loc) :
    rdAt (GF := GF) γl s ⊢ ∃ rd : GoFunc, rdOwn γl rd ∗
      □ (∀ (ws : Loc) (γw : mvcc.WsNames), mvcc.isWatchableStore ws s γw -∗ mvcc.rdIs rd ws s γw) := by
  iintro Hr
  iunfold rdAt at Hr
  iexact Hr

/-- **`rdAt` opened at the watchable store `ws`**: the owner's half at a deleter that is `ws`'s
`Write`, and the way back. -/
theorem rdAt_open (γl : GName) (s ws : Loc) (γw : mvcc.WsNames) :
    rdAt (GF := GF) γl s ∗ mvcc.isWatchableStore ws s γw ⊢
      ∃ rd : GoFunc, rdOwn γl rd ∗ mvcc.rdIs rd ws s γw ∗ (rdOwn γl rd -∗ rdAt γl s) := by
  iintro ⟨Hr, #Hws⟩
  iunfold rdAt at Hr
  icases Hr with ⟨%rd, Ho, #Hd⟩
  iexists rd
  iframe Ho
  isplitr
  · iapply Hd $$ Hws
  iintro Ho
  iunfold rdAt
  iexists rd
  iframe Ho Hd

end defs

end lease
end EtcdGrove
end Perennial
