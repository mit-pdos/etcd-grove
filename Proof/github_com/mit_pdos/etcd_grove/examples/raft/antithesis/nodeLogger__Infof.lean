/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/nodeLogger__Infof.lean`: the count
is `atomic.AddUint64` on the node's `autoLeft`, a logically atomic step inside the invariant
`antLogN` that holds the cell.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger__Infof
public import Perennial.Spec.sync.atomic.AddUint64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem nodeLogger.Infof.wp_proof (wp_AddUint64 : sync.atomic.AddUint64.spec (GF := GF) (hG := hG)) :
    nodeLogger.Infof.spec (GF := GF) (hG := hG) := by
  intro l n format args
  wp_start as ⟨#Hn, #Hinv⟩
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · try wp_auto
    wp_apply_core wp_AddUint64 $$ [] [-Hat]
    · iexact Hat
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%x, Hx⟩
    iexists x
    iframe Hx
    iintro Hx
    imod Hmask with -
    imod Hclose $$ [Hx] with -
    · inext; iexists (x + W64 1); iexact Hx
    imodintro
    wp_auto
    iapply HΦ
    itrivial
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
