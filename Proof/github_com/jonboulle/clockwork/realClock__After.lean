/-
Proof of `Spec/github_com/jonboulle/clockwork/realClock__After.lean` (clockwork v0.5.0): `time.After(d)`,
whose spec (Perennial's model of the runtime clock) gives the stamp and the bounds
(`clockwork.wp_After_stamp`). Lean-first.
-/
module

public import Spec.github_com.jonboulle.clockwork.realClock__After
public import Perennial.Spec.time.After

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.jonboulle.clockwork.Assumptions]

theorem clockwork.realClock.After.wp_proof (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    clockwork.realClock.After.spec (GF := GF) (hG := hG) := by
  intro rc d P n
  wp_start as ⟨#HP, #Hn⟩
  ihave #Ht : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #HA := clockwork.wp_After_stamp wp_After d P n $$ Ht HP Hn
  wp_auto
  wp_apply HA as %ch %γ HT
  wp_end

end proof

end EtcdGrove
end Perennial
