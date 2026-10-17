/-
Proof of `Spec/go_etcd_io/etcd/client/v3/authority.lean` (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.authority
public import Spec.strings.SplitN

@[expose] public section

set_option linter.unusedSectionVars false
-- `wp_auto`'s free-variable annotation (`goose.wp.fvAnnot`) makes no progress on this function's
-- body (a Perennial tactic limitation; `notes/STATUS.md`, item 5): off here.
set_option goose.wp.fvAnnot false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem authority.wp_proof (wp_SplitN : strings.SplitN.spec (GF := GF) (hG := hG)) :
    authority.spec (GF := GF) (hG := hG) := by
  intro ep
  wp_start as %Hplain
  obtain ⟨-, Hu, Hus⟩ := Hplain
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_SplitN $$ [$Hstr] as %sl ⟨%xs, Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_if_destruct
  · wp_apply strings.wp_HasPrefix ep go!"unix:" $$ [$Hstr]
    rw [decide_eq_false Hu]
    wp_auto
    wp_apply strings.wp_HasPrefix ep go!"unixs:" $$ [$Hstr]
    rw [decide_eq_false Hus]
    wp_auto
    iapply HΦ
    itrivial
  rw [ite_eq_left (by word)]
  have h1 : (sint.Z (W64 1)).toNat < xs.length := by
    have : sint.Z (W64 1) = 1 := by decide
    rw [this]
    word
  wp_apply wp_load_slice_index sl (sint.Z (W64 1)) xs (DFrac.own 1) (xs[(sint.Z (W64 1)).toNat])
    (by decide) $$ [$Hsl] as Hsl
  · ipureintro; exact List.getElem?_eq_getElem h1
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
