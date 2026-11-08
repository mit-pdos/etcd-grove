/- Lean-first (no Rocq counterpart). The proof of `writer.cur`: the load of `published` in the
tester's invariant, its value the writer's by the ghost variable's agreement. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__cur

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.cur.wp_proof : writer.cur.spec (GF := GF) (hG := hG) := by
  intro w wv γ p
  wp_start as ⟨Hw, #Hinv, Hp⟩
  iunfold writerRO at Hw
  icases Hw with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Load (hPub wv.h') (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑worldN from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p', %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb, %Hok⟩
  ihave %Hag := ghostVar_agree γ.pv _ _ _ _ $$ Hpv Hp
  obtain ⟨-, rfl⟩ := Hag
  iexists p
  iframe Hpub
  iintro Hpub
  imod Hcl with -
  imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm Hlb] with -
  · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; ipureintro; exact Hok
  imodintro
  wp_auto
  iapply HΦ
  iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
