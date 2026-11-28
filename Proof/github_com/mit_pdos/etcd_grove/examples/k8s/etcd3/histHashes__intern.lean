/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).intern`: the maps made if `canon` is nil; then `canon[k]`'s nodes (taken
out of the map, or none), each compared with `st` (`storeEqual`): an equal one holds the history, by
its `canonNode` facts; otherwise a new node, appended to `canon[k]` and recorded in `is`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__intern
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A literal of one unkeyed element has one element. -/
theorem arrayLiteralSize1 {a} : go.arrayLiteralSize [KeyedElement none a] = 1 := rfl

theorem histHashes.intern.wp_proof (wp_storeHash : storeHash.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG)) :
    histHashes.intern.spec (GF := GF) (hG := hG) := by
  intro hh prev hs st s n
  wp_start as ⟨Hinv, #Hprev, #Hst, %Hn⟩
  iunfold hhInv at Hinv
  icases Hinv with ⟨%mc, %mi, %mg, %C, %I, %G, Hc, Hi, Hg, Hci, Hgs⟩
  (try wp_auto)
  fail "ctx1"

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
