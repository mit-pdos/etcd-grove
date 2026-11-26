/-
**The `Pos.Countable` instances of mvcc's `Change` and `MvccState`** that the testers' ghost state
(`ghostVar`s at a store state, a log) is built on: `examples/mvccfull` (`History.lean`) and
`examples/k8s/etcd3` (`Inv.lean`). One copy, so that ghost names elaborated in different clients
match (`ghostVar_agree`, `icombine` match syntactically: review round 2's S6,
`notes/review/mvccfull-f1-r2.md`). Until 2026-11-25 `examples/mvccrand`'s `MvccCountable.lean`,
moved here, with mvcc's API, when mvccrand was retired (#49). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris

section model
variable [GooseExts]

/-- A change as a tuple (its tag, key, value, lease). -/
def encChange : Change → Bool × GoString × GoString × w64
  | .put k v l => (false, k, v, l)
  | .del k => (true, k, [], W64 0)

theorem encChange_inj : ∀ a b : Change, encChange a = encChange b → a = b
  | .put _ _ _, .put _ _ _, h => by simp only [encChange, Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl, rfl⟩ := h; rfl
  | .del _, .del _, h => by simp only [encChange, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl
  | .put _ _ _, .del _, h => by simp [encChange] at h
  | .del _, .put _ _ _, h => by simp [encChange] at h

instance change_api_countable : Pos.Countable Change :=
  .ofInjective (fun c => Pos.Countable.encode (encChange c))
    (fun a b h => encChange_inj a b (Pos.encode_inj h))

instance mvccState_countable : Pos.Countable MvccState :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.log, σ.crev, σ.pending))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

end model

end api
end mvcc
end EtcdGrove
end Perennial
