/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): a node event's line matches
the specification's server (`stateMatches`, `ValidatePostStates`) when the server is `R`-related to
the state raft logged.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimStr
public import Proof.go_etcd_io.raft.v3.TraceSimLemmas
public import Proof.go_etcd_io.raft.v3.TracedHooksDraft

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

variable [GooseExts]

/-- Raft's role strings are the specification's roles (no pre-candidate: pre-vote off). -/
theorem roleStr_abs (r : PRole) (h : r ≠ .preCandidate) : gsStr (roleStr r) = roleAbs (proleRole r) := by
  cases r <;> first | rfl | exact absurd rfl h

theorem gInt_of_lt (w : w64) (h : uint.Z w < 2 ^ 63) : gInt w = uint.Z w := by
  unfold gInt; word

theorem setIds_mk_perm_eq (xs C : List w64) (h : xs.Perm C) :
    Etcdraft.SetIds.mk (xs.map idAbs) = confAbs C := by
  unfold confAbs; apply setIds_mk_eq; intro x
  exact (h.map idAbs).mem_iff

/-- **A node event's line matches the server `R`-related to the logged state**: raft logs the
term, vote, role, last index, commit index and voters of its state `s`; the specification's server
`a`, `R`-related to `s` (the terms and indices below `2^63`, as Go's `int` reads them), has them. -/
theorem stateMatches_node (C : List w64) (s : NState) (a : Etcdraft.Server) (e : TraceEv) (id : w64)
    (xs : List w64) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate)
    (hterm : e.term = s.term) (hcommit : e.commit = s.logst.committed)
    (hrole : e.role = roleStr s.role) (hlog : e.logSize = plastIndex (toPState s))
    (hxs : xs.Perm C)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (st : Etcdraft.State) (hst : st.s (idAbs id) = a) (hsrv : st.server.contains (idAbs id) = true) :
    ({ ev := evConv e, nid := idAbs id, vote := idAbs s.vote, role := (evConv e).role,
       conf := (Etcdraft.SetIds.mk (xs.map idAbs), Etcdraft.SetIds.mk (([] : List w64).map idAbs)),
       «from» := 0, to := 0 } : Etcdraft.Line).stateMatches st (idAbs id) = true := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, -, -, -⟩ := hR
  unfold Etcdraft.Line.stateMatches
  simp only [hsrv, hst, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have hlen : (a.log.length : Int) = uint.Z (plastIndex (toPState s)) := by
    rw [h6, logAbs_length, plastIndex_length _ _ hs]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [h1]; simp only [evConv, hterm]; rw [gInt_of_lt _ bt]; rfl
  · rw [h2]; simp only [evConv, hrole]; rw [roleStr_abs _ hpre]; rfl
  · exact h3
  · rw [hlen]; simp only [evConv, hlog]; rw [gInt_of_lt _ bl]
  · rw [h7]; simp only [evConv, hcommit]; rw [gInt_of_lt _ bc]; rfl
  · rw [h8]; exact (setIds_mk_perm_eq xs C hxs).symm
  · rw [h8]; rfl

end TraceSim

end EtcdGrove
end Perennial
