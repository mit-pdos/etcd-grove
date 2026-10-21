/-
Proof of `Spec/confchange_chain.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.chain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confchange.chain.wp_proof : confchange.chain.spec (GF := GF) (hG := hG) := by
  intro chg ops fs dq I
  wp_start as ⟨Hops, HI, #Hf⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hops
  ihave IH : iprop(∃ (n : w64) (cfg : tracker.Config) (prs : Loc) (f : GoFunc),
      "i" ∷ i_ptr ↦ n ∗
      "op" ∷ op_ptr ↦ f ∗
      "chg" ∷ chg_ptr ↦ ({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } : confchange.Changer) ∗
      "HI" ∷ I (sint.nat n) cfg prs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i op chg HI]
  · iexists W64 0, chg.Tracker'.Config', chg.Tracker'.Progress', zero_val GoFunc
    simp only [named, show sint.nat (W64 0) = 0 by rfl]
    iframe i op HI
    isplitl [chg]
    · iexact chg
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · cleanup_bool_decide
    have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hf_lk⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ops.len := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index ops (sint.Z n) _ _ f Hn.1 $$ [Hops] with Hops
    · iframe Hops; ipureintro; exact Hf_lk
    -- `op(chg)`: the op's triple, from `I n` to `I (n + 1)`
    ihave #Hop := Hf $$ %(sint.nat n) %f %Hf_lk
    unfold opSpec
    wp_apply Hop $$ %cfg %prs [$HI] as %cfg' %prs' HI
    -- no error: `chg.Tracker.Config`/`.Progress` take the op's result
    wp_for_post
    iframe Hops HΦ
    iexists n + W64 1, cfg', prs', f
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    simp only [named]
    iframe i op HI
    isplitl [chg]
    · iexact chg
    ipureintro; constructor <;> word
  · have Hn' : sint.nat n = fs.length := by word
    rw [Hn']
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
