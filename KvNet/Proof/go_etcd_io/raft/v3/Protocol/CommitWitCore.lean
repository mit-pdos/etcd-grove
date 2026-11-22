-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/Protocol/CommitWitCore.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The declarations `hardStateM_countable`, `hsZero`, `phsNext`, `phsNext_empty`, `phsNext_ne`,
`phsNext_zero` of `Proof/go_etcd_io/raft/v3/Protocol/CommitWit.lean`, split from it so that the WAL
(`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until 2026-11-15 an
extract of `etc/gen-part-copies.py` for the part `LinuxFs/`; notes/wal-lean-integration.md). The
source imports this module.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.PbModel

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section extract
variable [GooseExts]

/-- (D22l) Hard states in ghost variables (`node.go`'s `dlv`, `rof`). -/
instance hardStateM_countable : Pos.Countable HardStateM :=
  .ofInjective (fun h => Pos.Countable.encode (h.Term', h.Vote', h.Commit'))
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

/-- (D22l) The zero hard state (`nil`'s, `NewRawNode`'s on an empty storage). -/
abbrev hsZero : HardStateM := HardStateM.mk (W64 0) (W64 0) (W64 0)

/-- (D22l) `prevHardSt`'s update by an accepted `Ready` of hard state `h` (`acceptReady`: `if
!IsEmptyHardState(rd.HardState) { rn.prevHardSt = rd.HardState }`; a `nil` `HardState` reads as the
zero record): `h` unless it is empty. -/
def phsNext (p h : HardStateM) : HardStateM :=
  if h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0 then p else h

theorem phsNext_empty (p h : HardStateM)
    (H : h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) : phsNext p h = p := by
  unfold phsNext; rw [if_pos H]

theorem phsNext_ne (p h : HardStateM)
    (H : ¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)) : phsNext p h = h := by
  unfold phsNext; rw [if_neg H]

theorem phsNext_zero (p : HardStateM) : phsNext p (HardStateM.mk (W64 0) (W64 0) (W64 0)) = p :=
  phsNext_empty p _ ⟨rfl, rfl, rfl⟩

end extract

end EtcdGrove
end Perennial
