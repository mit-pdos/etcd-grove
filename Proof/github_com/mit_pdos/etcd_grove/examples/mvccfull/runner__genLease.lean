/- Lean-first (no Rocq counterpart). The proof of `runner.genLease`: proved.

The outline: `choose(2)`, the slice's length, `choose(len)`, the element.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.genLease.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG)) :
    runner.genLease.spec (GF := GF) (hG := hG) := by
  intro x mp sl L
  wp_start as ⟨Hf, Hsl⟩
  ihave %Hsn := ownSlice_len $$ Hsl
  wp_auto
  wp_apply wp_choose (W64 2) as %c %Hc
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; left; rfl
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; left; rfl
  (try wp_auto)
  have hpos : 0 < sint.Z sl.len := by
    have := Hsn.2
    have : sint.Z sl.len ≠ 0 := fun h => Hif (by word)
    omega
  wp_apply wp_choose sl.len as %d %Hd
  have hdl : (sint.Z d).toNat < L.length := by
    have h4 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    have := Hsn.1; have := Hd.2.1 hpos; omega
  have hb : 0 ≤ sint.Z d ∧ sint.Z d < sint.Z sl.len := ⟨Hd.1, Hd.2.1 hpos⟩
  (try wp_auto)
  (try simp only [hb, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index sl (sint.Z d) L (DFrac.own 1) (L[(sint.Z d).toNat]'hdl)
    Hd.1 $$ [Hsl] as Hsl
  · iframe; ipureintro; exact List.getElem?_eq_getElem hdl
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; right; exact List.getElem_mem hdl

end proof

end mvccfull
end EtcdGrove
end Perennial
