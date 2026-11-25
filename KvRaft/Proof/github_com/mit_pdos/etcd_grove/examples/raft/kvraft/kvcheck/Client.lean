/-
kvcheck's clients over kvraft's wire protocol (`notes/kvraft-protocol.md`, "The client's operations"):
a checker whose replicas' addresses carry kvraft's protocols (`kvP F id`, `kvQ F id`,
`kvraft/Proto.lean`) for an abstract record of facts `F`, the replica `i + 1` at the `i`-th address.

* `isCheckerP F c γ ls` (persistent): the checker (`isChecker`), at least one replica, every address
  valid (`addrOk`) with its protocols set (`addrProto`), and the globals a request's connection
  reads (`io.EOF`, `poll.ErrDeadlineExceeded`, `net.errTimeout`).

Where the protocols are set (the addresses' start resources, `addrs_set_proto`) and what `F` is
(raft's and the store's facts) wait for decision B (`notes/kvraft-protocol.md`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Defs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode Net kvraft

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]

/-- The replicas' addresses, each valid, with kvraft's protocols for the replica `i + 1`. -/
def addrsProto (F : KvFacts GF) (ls : List GoString) : IProp GF :=
  iprop([∗list] i ↦ a ∈ ls, ⌜addrOk a = true⌝ ∗ addrProto a (kvP F (W64 (i + 1))) (kvQ F (W64 (i + 1))))

instance addrsProto_persistent (F : KvFacts GF) (ls : List GoString) :
    Persistent (addrsProto F ls) := by
  unfold addrsProto; infer_instance

/-- The globals a request's connection reads. -/
def connGlobals : IProp GF :=
  iprop(∃ eof ed et : GoInterface, globalAddr io.EOF ↦□ eof ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr net.errTimeout ↦□ et)

instance connGlobals_persistent : Persistent (connGlobals (GF := GF)) := by
  unfold connGlobals; infer_instance

/-- The checker at `c` over kvraft's protocols (see the file header). -/
def isCheckerP (F : KvFacts GF) (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) : IProp GF :=
  iprop(isChecker c γ ls ∗ ⌜0 < ls.length ∧ ls.length < 2 ^ 32⌝ ∗ addrsProto F ls ∗ connGlobals)

instance isCheckerP_persistent (F : KvFacts GF) (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) :
    Persistent (isCheckerP F c γ ls) := by
  unfold isCheckerP; infer_instance

/-- The address of the replica `id` and its protocols. -/
theorem addrsProto_at (F : KvFacts GF) (ls : List GoString) (id : w64)
    (h1 : 1 ≤ uint.nat id) (h2 : uint.nat id ≤ ls.length) :
    addrsProto F ls ⊢ ∃ a, ⌜ls[uint.nat id - 1]? = some a ∧ addrOk a = true⌝ ∗
      addrProto a (kvP F id) (kvQ F id) := by
  unfold addrsProto
  have hlt : uint.nat id - 1 < ls.length := by omega
  obtain ⟨a, ha⟩ : ∃ a, ls[uint.nat id - 1]? = some a := ⟨_, List.getElem?_eq_getElem hlt⟩
  iintro #H
  ihave #Ha := BigSepL.bigSepL_lookup (Φ := fun i a =>
      iprop(⌜addrOk a = true⌝ ∗ addrProto a (kvP F (W64 (i + 1))) (kvQ F (W64 (i + 1))))) ha $$ H
  icases Ha with ⟨%Hok, #Hp⟩
  have hid : W64 (((uint.nat id - 1 : Nat) : Int) + 1) = id := by
    rw [show ((uint.nat id - 1 : Nat) : Int) + 1 = (uint.nat id : Int) by omega]; word
  rw [hid]
  iexists a
  iframe Hp
  ipureintro; exact ⟨ha, Hok⟩

end defs

end raft_kvcheck
end EtcdGrove
end Perennial
