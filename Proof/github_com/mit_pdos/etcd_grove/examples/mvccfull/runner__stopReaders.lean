/- Lean-first (no Rocq counterpart). The proof of `runner.stopReaders` (`readStop.Store(1)` in its
invariant, then the join's `Wait`, `sync.tokJoin.WaitGroup.wp_Wait`; both Perennial's results):
Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__stopReaders
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.stopReaders.wp_proof :
    runner.stopReaders.spec (GF := GF) (hG := hG) := by
  intro x n P
  unfold rdShared ctrInv
  wp_start as ⟨⟨#Hstop, #Hreads⟩, Had⟩
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Store (rF go!"readStop" x) (W64 1) $$ [] [-]
  · iPkgInit
  iinv Hstop with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "stop") from
    Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hcl with -
  imod Hclose $$ [Hv] with -
  · inext; iexists (W64 1); iexact Hv
  imodintro
  wp_auto
  wp_apply (sync.tokJoin.WaitGroup.wp_Wait rdWgN iprop(False) (rF go!"readWg" x) n P) $$ [Had]
    as ⟨HP, Had⟩
  · iframe Had
  try wp_auto
  iapply HΦ
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
