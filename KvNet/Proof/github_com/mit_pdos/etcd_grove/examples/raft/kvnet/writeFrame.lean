/-
The proof of `writeFrame` (`KvNet/Spec/.../kvnet/writeFrame.lean`): a fresh slice of capacity
`8 + len(body)` (`make`), `putBytes` of `body` into it (`putB xs`), then `writeAll` of it.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.writeFrame
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.writeAll
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putBytes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem writeFrame.wp_proof (wp_putBytes : putBytes.spec (GF := GF) (hG := hG))
    (wp_writeAll : writeAll.spec (GF := GF) (hG := hG)) :
    writeFrame.spec (GF := GF) (hG := hG) := by
  intro c cn s a body xs dq ed P hl
  wp_start as ⟨#Hc, Hb, #Hed, HP, #Hacc⟩
  wp_auto
  ihave %Hbl := ownSlice_len $$ Hb
  have hbz : sint.Z body.len = xs.length := by
    rw [Hbl.1]; exact (Int.toNat_of_nonneg Hbl.2).symm
  have h8 : sint.Z (W64 8 + body.len) = 8 + sint.Z body.len := by word
  have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8 + body.len) := by
    rw [h8, show sint.Z (W64 0) = 0 from rfl]; omega
  wp_apply wp_slice_make3 (V := w8) (W64 0) (W64 8 + body.len) hcap as %buf ⟨Hbuf, Hcap, -⟩
  rw [show List.replicate 0 (zero_val w8) = [] from rfl]
  wp_apply wp_putBytes buf body [] xs dq $$ [Hbuf Hcap Hb] as %fr ⟨Hfr, -, Hb⟩
  · iframe Hbuf Hcap Hb
  rw [List.nil_append]
  wp_apply wp_writeAll c cn s a fr (putB xs) (DFrac.own 1) ed P $$ [Hfr HP]
    as %ok ⟨%w, %res, HP, -, %Hw⟩
  · iframe Hc Hfr Hed HP Hacc
  (try wp_auto)
  iapply HΦ
  iexists w, res
  iframe HP Hb
  ipureintro; exact Hw

end proof

end raft_kvnet
end EtcdGrove
end Perennial
