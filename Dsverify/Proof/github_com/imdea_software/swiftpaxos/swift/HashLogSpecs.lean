/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLogSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`HashLog`'s internal specs (the replica group's; not frozen), over `ownHashLog`
(Proof/swift/HashLogDefs.lean):
* `NewHashLog()`: a fresh log (`HL.init`).
* `l.update(x, s, h, save)` (`HL.updateTo`): `x` pending: it leaves the list, and if `s` is above
  `synced` the log is re-based on `h` (of path `P`); `x` not pending: saved for a later `Append`
  if `save`, else re-based if `s` is above `synced`. The hash is recomputed.
* `l.Update(x, s, h)`: `update(x, s, h, true)`.
* `l.Append(c, x)` (`HL.append`), `x` not pending: with a saved update for `x`, that update is
  applied (`update(…, false)`) and its hash returned (of its path); else `x` joins the pending
  list and the result is the start-marked hash of `base ++ pending ++ [x]`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.hlog

/-- `update(x, s, h, save)`'s effect, `h` the hash of the path `P`. -/
def HL.updateTo (σ : HL) (x : sp.CmdId) (s : w64) (h : sp.Hash) (P : List sp.CmdId)
    (save : Bool) : HL :=
  if x ∈ σ.pending then
    if sint.Z σ.synced < sint.Z s then
      { σ with pending := σ.pending.erase x, synced := s, base := P }
    else { σ with pending := σ.pending.erase x }
  else if save then { σ with upd := fun y => if y = x then some ⟨s, h, P⟩ else σ.upd y }
  else if sint.Z s ≤ sint.Z σ.synced then σ
  else { σ with synced := s, base := P }

/-- `Append(c, x)`'s effect and the path of the hash it returns. -/
def HL.append (σ : HL) (x : sp.CmdId) : HL × List sp.CmdId :=
  match σ.upd x with
  | some e =>
    (HL.updateTo (σ.clearUpd x) x e.seq e.hash e.path false, e.path)
  | none => ({ σ with pending := σ.pending ++ [x] }, σ.base ++ σ.pending ++ [x])

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- `NewHashLog()`. -/
abbrev NewHashLog.spec : Prop :=
  {{ (True : IProp netDistGF) }}
    (App (Val (@! swift.NewHashLog)) (Val #()))
  {{ (l : Loc), RET #l; ownHashLog l HL.init }}

/-- `l.update(x, s, h, save)`. -/
abbrev HashLog.update.spec : Prop :=
  ∀ (l : Loc) (σ : HL) (x : swift.CommandId) (s : w64) (h : swift.SHash) (P : List sp.CmdId)
    (save : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 ∗ ownHashLog l σ ∗
      sp.startHash P h.H'.arr }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType swift.HashLog.ty @!! go!"update"))
      (Val #x)) (Val #s)) (Val #h)) (Val #save))
  {{ RET #(); ownHashLog l (σ.updateTo (toCmdId x) s h.H'.arr P save) }}

/-- `l.Update(x, s, h)`. -/
abbrev HashLog.Update.spec : Prop :=
  ∀ (l : Loc) (σ : HL) (x : swift.CommandId) (s : w64) (h : swift.SHash) (P : List sp.CmdId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 ∗ ownHashLog l σ ∗
      sp.startHash P h.H'.arr }}
    (App (App (App (Val (l @!! go.GoType.PointerType swift.HashLog.ty @!! go!"Update"))
      (Val #x)) (Val #s)) (Val #h))
  {{ RET #(); ownHashLog l (σ.updateTo (toCmdId x) s h.H'.arr P true) }}

/-- `l.Append(c, x)`, `x` not pending. -/
abbrev HashLog.Append.spec : Prop :=
  ∀ (l : Loc) (σ : HL) (c : state.Command) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 ∗ ownHashLog l σ ∗
      ⌜toCmdId x ∉ σ.pending⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType swift.HashLog.ty @!! go!"Append"))
      (Val #c)) (Val #x))
  {{ (r : swift.SHash), RET #r; ownHashLog l (σ.append (toCmdId x)).1 ∗
      sp.startHash (σ.append (toCmdId x)).2 r.H'.arr }}

end specs

end swift.hlog

end Perennial.github_com.imdea_software.swiftpaxos
