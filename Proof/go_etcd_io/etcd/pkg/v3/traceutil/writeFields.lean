/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/writeFields.lean`, over Perennial's
`strings.Builder` and `Field.format`'s spec: the range loop only reads the fields. Lean-first (no
Rocq counterpart); traceutil-log (2026-11-23).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.writeFields
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Field__format
public import Perennial.Proof.strings.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode _root_.Perennial.go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.writeFields.wp_proof
    (hFmt : traceutil.Field.format.spec (GF := GF) (hG := hG)) :
    traceutil.writeFields.spec (GF := GF) (hG := hG) := by
  intro sl fs dq
  wp_start as ⟨Hs, %Hwf⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe
  · (try wp_auto)
    ihave Hb := _root_.Perennial.strings.ownBuilder_zero buf_ptr $$ buf
    wp_apply _root_.Perennial.strings.Builder.wp_WriteString $$ Hb as Hb
    (try wp_auto)
    ihave %Hfl := ownSlice_len $$ Hs
    ihave IH : iprop(∃ (n : w64) (s : GoString),
        "i" ∷ i_ptr ↦ n ∗ "Hb" ∷ _root_.Perennial.strings.ownBuilder buf_ptr s ∗
        "Hs" ∷ sl ↦*{dq} fs ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hb Hs]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < fs.length := by have h2 := Hfl.1; have h3 := Hn.1; rw [h2]; word
      obtain ⟨x0, Hx0⟩ : ∃ x0, fs[sint.nat n]? = some x0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
      rw [ite_eq_left Hbnd]
      wp_apply wp_load_slice_index sl (sint.Z n) fs dq x0 Hn.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hx0
      (try wp_auto)
      wp_apply hFmt f_ptr x0 $$ [f] as %s1 f
      · iframe #
        iframe
        ipureintro
        exact traceutil.fieldsWf_of_mem Hwf (List.mem_of_getElem? Hx0)
      (try wp_auto)
      wp_apply _root_.Perennial.strings.Builder.wp_WriteString $$ Hb as Hb
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · (try wp_auto)
      wp_apply _root_.Perennial.strings.Builder.wp_WriteString $$ Hb as Hb
      (try wp_auto)
      wp_apply _root_.Perennial.strings.Builder.wp_String $$ Hb as Hb
      (try wp_auto)
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
