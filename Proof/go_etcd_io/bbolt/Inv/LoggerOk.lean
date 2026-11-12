/-
The option's logger is `logPtrTyped` (batch 38.1 of `notes/bbolt-proof-plan.md`, user-approved
2026-11-04): `OptsM.ok`'s `loggerPtrOk` gives `dbFixed`'s `logPtrTyped` of the logger `Open` stores.
A module of its own so that `Inv/Bolt`'s importers do not rebuild.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt
public import Spec.go_etcd_io.bbolt.Options

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

section
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- A `loggerPtrOk` logger (nil, or a pointer-typed location) is `logPtrTyped`. -/
theorem loggerPtrOk_logPtrTyped (lg : GoInterface) (h : loggerPtrOk lg) : logPtrTyped lg := by
  intro ii hii T _
  subst hii
  obtain ⟨_, l, -, hv⟩ := h
  exact ⟨l, hv⟩

/-- The options' logger, when `OptsM.ok`. -/
theorem OptsM.ok_logPtrTyped (o : OptsM) (h : o.ok) : logPtrTyped o.logger :=
  loggerPtrOk_logPtrTyped _ h.2.2.2.2.2

end

end bbolt
end EtcdGrove
end Perennial
