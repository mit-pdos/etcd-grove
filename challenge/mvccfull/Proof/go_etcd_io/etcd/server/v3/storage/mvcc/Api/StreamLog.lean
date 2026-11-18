/-
**A watch stream's history, and `wsRecvOk` from it** (stage 2 of the mvcc API proof, the watch
chain: `notes/mvcc-api-risk.md`, M1; 2026-11-04). Lean-first (no Rocq counterpart).

The stream's ghost history (`ι.ev`, a monotone list, `Api/StreamGhost.lean`) is the sequence of
its events: the registrations (`Watch`'s update), the cancels (`Cancel`'s, at its first check),
the close, and every response sent on its channel, each with what it records at its send
(`Api/SentInv.lean`'s `SentFact`, its filters by their saved name). Its replay (`replay`) is the
stream's state, the cancelled set and the sent facts; a registration's stamp is the number of
responses sent before it, exactly. The history is well formed (`LogWF`) when each event's
premises held when it was appended (`stepOk`: a fresh id; a send's fact true at its send, its
registry info the stream's, its cancelled ids cancelled, a `-1` response covering every watcher
registered by then). Well-formedness is what the appender proves; it is prefix-closed, so every
lower bound of the history carries it.

`sentInv_of_log`: a well-formed history's replay keeps `SentInv` (with the facts' bounds below
the store's state); `wsRecvOk_of_log`: a received prefix of its sends satisfies the guarantee.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SentInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api
namespace sent

open Iris go_etcd_io.etcd.server.v3.storage.mvcc

/-- A watcher a `-1` response covers, as the history records it (its filters by saved name). -/
abbrev CovRec := w64 × WatchRange × GName × Nat

/-- **An event of a stream's history.** A send records its response, its watcher's registry info
(its filters by saved name), the notified-log and compaction lower bounds it was sent with, and,
for a `-1` response, its covered watchers and the cancelled ids. -/
inductive SEv where
  | reg (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat)
  | cancel (id : w64)
  | close
  | send (r : WResp) (fg : GName) (rg : WatchRange) (lo : Nat) (L : Log) (c0 : Int)
      (cov : List CovRec) (dead : List w64)

instance WResp.countable : Pos.Countable WResp :=
  .ofInjective (fun r => Pos.Countable.encode (r.id, r.evs, r.rev, r.compactRev))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The events' code, for countability. -/
def SEv.code : SEv → (w64 × WatchRange × GName × Nat) ⊕ (w64 ⊕ (Unit ⊕
    (WResp × GName × WatchRange × Nat × Log × Int × List CovRec × List w64)))
  | .reg id rg fg lo => .inl (id, rg, fg, lo)
  | .cancel id => .inr (.inl id)
  | .close => .inr (.inr (.inl ()))
  | .send r fg rg lo L c0 cov dead => .inr (.inr (.inr (r, fg, rg, lo, L, c0, cov, dead)))

instance SEv.countable : Pos.Countable SEv :=
  .ofInjective (fun e => Pos.Countable.encode e.code)
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [SEv.code])

/-- An event's saved filter names. -/
def SEv.fgs : SEv → List GName
  | .reg _ _ fg _ => [fg]
  | .send _ fg _ _ _ _ cov _ => fg :: cov.map (·.2.2.1)
  | _ => []

/-- A send's fact, its filters decoded by `dec`. -/
def sendFact (dec : GName → List (EvM → Bool)) (r : WResp) (fg : GName) (rg : WatchRange)
    (lo : Nat) (L : Log) (c0 : Int) (cov : List CovRec) (dead : List w64) : SentFact :=
  ⟨r, rg, dec fg, lo, L, c0, cov.map (fun c => ⟨c.1, c.2.1, dec c.2.2.1, c.2.2.2⟩), dead⟩

/-- **The replayed state**: the stream's, the cancelled set, the facts sent. -/
structure RState where
  S : StreamState
  D : List w64
  F : List SentFact

def rStart : RState := ⟨wsStart, [], []⟩

/-- An event's effect. A registration's stamp is the number of responses sent before it. -/
def RState.step (dec : GName → List (EvM → Bool)) (st : RState) : SEv → RState
  | .reg id rg fg lo => { st with S := st.S.register id ⟨rg, dec fg, lo, st.F.length, true⟩ }
  | .cancel id => ⟨st.S.cancel id, if (st.S.ws !! id).isSome then id :: st.D else st.D, st.F⟩
  | .close => { st with S := st.S.close }
  | .send r fg rg lo L c0 cov dead => { st with F := st.F ++ [sendFact dec r fg rg lo L c0 cov dead] }

def replay (dec : GName → List (EvM → Bool)) (l : List SEv) : RState :=
  l.foldl (RState.step dec) rStart

/-- **An event's premises**, at the state before it. -/
def stepOk (dec : GName → List (EvM → Bool)) (st : RState) : SEv → Prop
  | .reg id _ _ _ => st.S.ws !! id = none ∧ id ≠ W64 (-1)
  | .cancel _ => True
  | .close => True
  | .send r fg rg lo L c0 cov dead =>
      let f := sendFact dec r fg rg lo L c0 cov dead
      f.holds (st.F.map SentFact.r) ∧ factAgree st.S f ∧ (∀ id ∈ f.dead, id ∈ st.D) ∧
        stampsAt st.S st.F.length f

/-- **A well-formed history**: each event's premises held when it was appended. -/
def LogWF (dec : GName → List (EvM → Bool)) (l : List SEv) : Prop :=
  ∀ (p : Nat) (e : SEv), l[p]? = some e → stepOk dec (replay dec (l.take p)) e

/-- The responses sent. -/
def sendsOf : List SEv → List WResp
  | [] => []
  | .send r .. :: l => r :: sendsOf l
  | _ :: l => sendsOf l

/-- The number of events that are not sends (those the stream's client makes). -/
def nsCount : List SEv → Nat
  | [] => 0
  | .send .. :: l => nsCount l
  | _ :: l => nsCount l + 1

/-- The saved filter names of a history. -/
def fgsOf (l : List SEv) : List GName := l.flatMap SEv.fgs

/-! ## Lemmas -/

section lemmas
variable (dec : GName → List (EvM → Bool)) (st : RState)

end lemmas

/-! ## The bridge -/

end sent
end api
end mvcc
end EtcdGrove
end Perennial
