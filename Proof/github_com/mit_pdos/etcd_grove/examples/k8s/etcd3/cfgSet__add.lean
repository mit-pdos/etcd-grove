/-
Lean-first (no Rocq counterpart).

The proof of `(*cfgSet).add`: the bucket map made if nil; `c`'s history made canonical; the bucket of
`c`'s key taken out of the map (or none), each of its configurations compared with `c` (`storeEqual`,
`pendEqual`): a match is `c`'s configuration, its history the key's (the bucket's facts) and so `c`'s
(`histOwn_agree_len`); otherwise `c` appended to the list and its index to the bucket, every bucket's
indices still into the longer list.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cfgSet__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonical
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pendEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

/-- A bucket's indices into the list `cs` (`cfgSetOwn`'s facts). -/
abbrev bucketIdx (cs : List mcfg) (k : ckey) (is : List w64) : Prop :=
  ∀ i ∈ is, 0 ≤ sint.Z i ∧ ∃ d, cs[sint.nat i]? = some d ∧ d.hist' = k.hist'

theorem bucketIdx_snoc (cs : List mcfg) (x : mcfg) (k : ckey) (is : List w64)
    (h : bucketIdx cs k is) : bucketIdx (cs ++ [x]) k is := by
  intro i hi
  obtain ⟨h0, d, hd, hk⟩ := h i hi
  refine ⟨h0, d, ?_, hk⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hd).1]
  exact hd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- Every bucket's indices into a longer list. -/
theorem buckets_snoc (B : GMap ckey GoSlice) (cs : List mcfg) (x : mcfg) :
    ([∗map] k ↦ sl ∈ B, ∃ is : List w64, sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
      ⌜bucketIdx cs k is⌝) ⊢
    ([∗map] k ↦ sl ∈ B, ∃ is : List w64, sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
      ⌜bucketIdx (cs ++ [x]) k is⌝ : IProp GF) := by
  apply BigSepM.bigSepM_mono
  intro k sl _
  iintro ⟨%is, Hs, Hc, %Hi⟩
  iexists is
  iframe
  ipureintro; exact bucketIdx_snoc cs x k is Hi

theorem cfgSet.add.wp_proof
    (wp_canonical : histHashes.canonical.spec (GF := GF) (hG := hG))
    (wp_storeHash : storeHash.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG))
    (wp_pendEqual : pendEqual.spec (GF := GF) (hG := hG)) :
    cfgSet.add.spec (GF := GF) (hG := hG) := by
  intro s hh gs c g
  wp_start as ⟨#Hhh, Hset, #Hc, %Hgs⟩
  iunfold cfgSetOwn at Hset
  icases Hset with ⟨%lsl, %mb, %cs, %B, Hsh, Hsl, Hsb, Hcs, Hcap, Hcg, %Hcsl, Hb⟩
  ihave %Hlen := BigSepL.bigSepL2_length $$ Hcg
  (try wp_auto)
  wp_join iprop(∃ (mb' : GoMap) (B' : GMap ckey GoSlice),
      s_ptr ↦ s ∗ structFieldRef cfgSet go!"buckets" s ↦ mb' ∗ mb' ↦$ B' ∗
      [∗map] k ↦ sl ∈ B', ∃ is : List w64, sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
        ⌜bucketIdx cs k is⌝) with [s Hsb Hb]
      as ⟨%mb', %B', s, Hsb, HB, HBs⟩
  · (try wp_auto)
    wp_apply (wp_map_make1 (K := ckey) (V := GoSlice) _ _) as %m1 Hm1
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iexists m1, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  · icases Hb with (%Hnil | ⟨HB, HBs⟩)
    · exact absurd Hnil.1 (by assumption)
    · iexists mb, B
      iframe
  unfold cfgOwn
  icases Hc with ⟨#Hcst, #Hch, #Hcp, %Hchl⟩
  (try wp_auto)
  wp_apply wp_canonical hh c.hist' g.st.hist $$ [$Hhh $Hch] as %h' #Hh'
  · ipureintro; exact Hchl
  (try wp_auto)
  done

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
