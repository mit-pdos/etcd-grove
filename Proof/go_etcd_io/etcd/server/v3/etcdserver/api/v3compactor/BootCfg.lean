/-
**The compactor's slot** in `NewServer.spec` (the slot convention, `notes/spec-first-plan.md`;
K1 of `notes/k8s-compactor-plan.md`, approved 2026-11-04): `v3compactor.bootCfg mode ret cmp cret`,
the auto-compactor's configuration against the KV's compaction mode. `NewServer.specG` and the
examples' `newServerMode` name the configuration only through it, sealed (`etc/import-all.txt`):
a later mode of the compactor changes its body and laws, not the hub's text. No `bootRes`,
`bootOk` or `srvInv` (the compactor takes no program-start resource; what the running server has
of it is `InvRun.lean`'s `compactorOk`, not yet a slot).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.config

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- **The compactor's boot premise** (sealed): the auto-compactor's configuration (`mode`, `ret`:
`AutoCompactionMode`, `AutoCompactionRetention`) consistent with the KV's compaction mode `cmp` and
the cluster's retention `cret` (the KV names' `cmp`, `cret`: a coupling the compactor owns, read as
parameters as `rafthttp.bootCfg` reads raft's peers; a `Names` argument once the KV's names split).
Either the compactor is off, in either mode (no compaction, or clients compacting: Kubernetes'
deployment, any `cret`, which only burdens the compacting clients), or the KV is in compaction mode
and the compactor is on: in revision mode at a positive retention of at least the cluster's, or in
periodic mode at a period of at least 10ns (`nonissues/etcd-compactor-periodic-tiny-retention.md`)
and a cluster retention of 0. Scope restrictions: Go accepts any nonzero retention; a non-positive
one in revision mode (compactions at a future revision, refused) and one below 10ns in periodic mode
are not covered. The mode is unread when the retention is 0 (`server.go`: `v3compactor.New` only at
`num != 0`). -/
@[no_expose] def v3compactor.bootCfg (mode : GoString) (ret : w64) (cmp : Bool) (cret : Nat) : Prop :=
  ret = W64 0 ∨
    (cmp = true ∧
      ((mode = go!"revision" ∧ 0 < sint.Z ret ∧ (cret : Int) ≤ sint.Z ret) ∨
       (mode = go!"periodic" ∧ 10 ≤ sint.Z ret ∧ cret = 0)))

/-- The compactor off (the retention `0`), in either compaction mode. -/
theorem v3compactor.bootCfg_off (mode : GoString) (ret : w64) (cmp : Bool) (cret : Nat)
    (h : ret = W64 0) : v3compactor.bootCfg mode ret cmp cret :=
  Or.inl h

/-- The compactor on in revision mode, at a positive retention of at least the cluster's. -/
theorem v3compactor.bootCfg_revision (ret : w64) (cret : Nat)
    (hr : 0 < sint.Z ret) (hc : (cret : Int) ≤ sint.Z ret) :
    v3compactor.bootCfg go!"revision" ret true cret :=
  Or.inr ⟨rfl, Or.inl ⟨rfl, hr, hc⟩⟩

/-- The compactor on in periodic mode, at a period of at least 10ns and a cluster retention of 0. -/
theorem v3compactor.bootCfg_periodic (ret : w64) (cret : Nat)
    (hr : 10 ≤ sint.Z ret) (hc : cret = 0) :
    v3compactor.bootCfg go!"periodic" ret true cret :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, hr, hc⟩⟩

/-- **What `NewServer` takes from the slot where it builds a compactor** (`ret ≠ 0`): the KV in
compaction mode, `v3compactor.New`'s premise with its error arm refuted (a known mode), and the
mode's permit against the cluster's retention (`compactableOk_server_mode`'s premise). -/
theorem v3compactor.bootCfg_build {mode : GoString} {ret : w64} {cmp : Bool} {cret : Nat}
    (h : v3compactor.bootCfg mode ret cmp cret) (hr : ret ≠ W64 0) :
    cmp = true ∧ (mode = go!"revision" ∨ mode = go!"periodic") ∧
      (mode = go!"periodic" → 10 ≤ sint.Z ret) ∧
      (if mode = go!"revision" then 0 ≤ sint.Z ret ∧ (cret : Int) ≤ sint.Z ret else cret = 0) := by
  rcases h with h | ⟨hc, ⟨hm, hp, hle⟩ | ⟨hm, hp, hz⟩⟩
  · exact absurd h hr
  · subst hm
    exact ⟨hc, Or.inl rfl, fun h => absurd h (by decide), by
      rw [if_pos rfl]; exact ⟨Int.le_of_lt hp, hle⟩⟩
  · subst hm
    exact ⟨hc, Or.inr rfl, fun _ => hp, by rw [if_neg (by decide)]; exact hz⟩

end slots

end EtcdGrove
end Perennial
