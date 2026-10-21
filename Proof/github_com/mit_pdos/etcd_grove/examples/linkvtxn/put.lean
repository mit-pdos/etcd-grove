/-
Lean-first (no Rocq counterpart).

The proof of `put`: `lookup`, then `setKey`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.put
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.setKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem put.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_setKey : setKey.spec (GF := GF) (hG := hG)) : put.spec (GF := GF) (hG := hG) := by
  intro sl es dq r k v
  wp_start as ⟨Hs, %Hb⟩
  wp_auto
  wp_apply wp_lookup sl es dq k $$ [$Hs] as %old %ok ⟨Hs, %Hlk⟩
  have hr : lookupL es k = (old, ok) := Hlk.symm
  cases ok
  · wp_auto
    wp_apply wp_setKey sl es dq k ⟨v, r, W64 1⟩ $$ [$Hs] as %out ⟨Hs, Ho, Hocap⟩
    · ipureintro; exact Hb
    iapply HΦ
    rw [show putL es r k v = setKeyL es k ⟨v, r, W64 1⟩ by simp [putL, hr]]
    iframe
  · wp_auto
    wp_apply wp_setKey sl es dq k ⟨v, r, old.Ver' + W64 1⟩ $$ [$Hs] as %out ⟨Hs, Ho, Hocap⟩
    · ipureintro; exact Hb
    iapply HΦ
    rw [show putL es r k v = setKeyL es k ⟨v, r, old.Ver' + W64 1⟩ by simp [putL, hr]]
    iframe

end proof

end linkvtxn
end EtcdGrove
end Perennial
