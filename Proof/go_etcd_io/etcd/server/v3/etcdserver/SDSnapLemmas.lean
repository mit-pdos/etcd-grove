/-
**The frozen entries, read** (stage P, track S-D, 2026-10-30): the persistence of `srvFrozenAt` and
`srvFrozenBelow`, and `Compact`'s premise at an index from `1` to the applied index from
`srvSnapState`'s frozen parts. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

instance srvFrozenAt_persistent_SD (γs : MemStorNames) (i : Nat) :
    Persistent (srvFrozenAt (GF := GF) γs i) := by
  unfold srvFrozenAt; infer_instance

instance srvFrozenBelow_persistent_SD (γs : MemStorNames) (n : Nat) :
    Persistent (srvFrozenBelow (GF := GF) γs n) := by
  unfold srvFrozenBelow; infer_instance

instance srvSnapStor_persistent_SD (ms : Loc) (γs : MemStorNames) (γr : ReadNames) (nid ai at' : w64) :
    Persistent (srvSnapStor (GF := GF) ms γs γr nid ai at') := by
  unfold srvSnapStor storDL; infer_instance

/-- **`Compact`'s entry premise** at an index `k` from `1` to the applied index `n`: frozen
(`srvFrozenAt` at `n`, `srvFrozenBelow` below it) or compacted. -/
theorem srvFrozen_get (γs : MemStorNames) (n k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    srvFrozenAt (GF := GF) γs n ∗ srvFrozenBelow γs n ⊢
      (∃ e, memLog γs k DFrac.discard [e]) ∨ memCompacted γs k := by
  iintro ⟨Ha, Hb⟩
  by_cases hk : k = n
  · subst hk
    iunfold srvFrozenAt at Ha
    icases Ha with (%h0 | ⟨%e, He⟩)
    · exfalso; omega
    · ileft; iexists e; iexact He
  · have hl : (List.range n)[k]? = some k := by
      rw [List.getElem?_range (by omega)]
    iunfold srvFrozenBelow at Hb
    iapply BigSepL.bigSepL_lookup
      (Φ := fun _ j => iprop((∃ e, memLog (GF := GF) γs j DFrac.discard [e]) ∨ memCompacted γs j)) hl
      $$ Hb

end lemmas

end EtcdGrove
end Perennial
