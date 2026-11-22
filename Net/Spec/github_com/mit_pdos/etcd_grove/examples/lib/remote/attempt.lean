/-
`attempt(addr, req, d)`: one try of a call to the node at `addr` (`remoteAddr`): it dials, registers
the connection's slot with the update `slotUpd R i Φ` (`slot_register`), writes the request `req` (the
bytes of `i`, at most `maxLen`), reads the reply and closes. It returns `true` only with the bytes of
a value `v` the far side answered (`rep_read`): an output `ov o`, with `Φ o` taken from the slot
(`slot_take`), or `i`'s unknown output. On a failure the update stays in the slot, which the far
side may claim later, or never. Proved in `Net/Proof/.../lib/remote/attempt.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev attempt.spec : Prop :=
  ∀ (R : RBase GF St I O) (a : GoString) (i : I) (Φ : O → IProp GF) (req : GoSlice) (dq : DFrac)
    (d : w64),
  (R.encIn i).length ≤ maxLen →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ mapCtx (Gg := hG.goose_globalGS) (I := I) ∗ remoteAddr (Gg := hG.goose_globalGS) R a ∗
      req ↦*{dq} R.encIn i ∗ slotUpd (Gg := hG.goose_globalGS) R i Φ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.attempt)) (Val #a)) (Val #req)) (Val #d))
  {{ (rep : GoSlice) (ok : Bool), RET (PairV #rep #ok); req ↦*{dq} R.encIn i ∗
      (⌜ok = false⌝ ∨ ∃ v, ⌜ok = true⌝ ∗ rep ↦* R.encOut v ∗
        ((∃ o, ⌜v = R.ov o⌝ ∗ Φ o) ∨ ⌜v = R.unk i⌝)) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
