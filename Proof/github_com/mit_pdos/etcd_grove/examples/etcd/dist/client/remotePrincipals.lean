/-
Proof of `remotePrincipals.spec` (#50 F7 S7; `remoteWriters.wp_proof`'s port). Lean-first (no Rocq counterpart).

Principal `c`'s input is its name `principals[c]` (a Go `string` in an interface: the principals' wire,
`principalWire`, its encoding a few bytes), and the service's precondition `prP` is the principals' environment
(`akDistEnv`, persistent, at the global ghost state: `akDistEnv_eq_G`) and the name's membership. `reportAll` at
the principal service (`principalSvcG`, the share's: one wire for the share and the machine), each principal's
continuation `True`; then the answers are counted, `outs[c].(bool)` asserted only of an answer (`ok`), which the
wire makes a `bool`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remotePrincipals
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalCodec
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Principals
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RemoteWritersDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open etcd_dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [auth_sem : github_com.mit_pdos.etcd_grove.examples.lib.authwork.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- Principal `c`'s input: its name. -/
def prIn (c : Nat) : GoString := (etcd_auth.principals[c]?).getD []

theorem prIn_eq {c : Nat} {w : GoString} (h : etcd_auth.principals[c]? = some w) : prIn c = w := by
  simp [prIn, h]

/-- The principals' names are short. -/
theorem principals_small : ∀ w ∈ etcd_auth.principals, (encStr w).length < 2 ^ 63 := by
  intro w hw
  simp only [etcd_auth.principals, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> decide

/-- Principal `c`'s answer, as `reportAll` returns it at the principal service. -/
def prRes [π : NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (addrs : List GoString) (outs oks : GoSlice)
    (c : Nat) : IProp GF :=
  iprop(∃ (v : GoInterface) (ok : Bool),
    typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) v (DFrac.own 1) ∗
    typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) ok (DFrac.own 1) ∗
    (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗
      ((∃ o : Bool, ⌜v = interface.mkOk go.bool #o⌝ ∗ iprop(True)) ∨ iprop(False)))))

theorem remotePrincipals.wp_proof
    (wp_Principals : etcd_auth.Principals.spec (GF := GF) (hG := hG))
    (wp_reportAll : reportAll.spec (GF := GF) (hG := hG))
    (wp_principalCodec : principalCodec.spec (GF := GF) (hG := hG)) :
    remotePrincipals.spec (GF := GF) (hG := hG) := by
  intro π ρ nodes ns addrs Γ γR Htb
  wp_start as ⟨Htok, #Hns, Hps, #Henv⟩
  iunfold principalsShare at Hps
  icases Hps with ⟨#Hmap, %Hn4, Hl⟩
  ihave %Hnl := ownSlice_len _ _ _ $$ Hns
  have hP4 : etcd_auth.principals.length = 4 := rfl
  ihave #Pauth : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.authwork $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Principals as %psl Hpsl
  imod ownSlice_persist _ _ _ $$ Hpsl with #Hpsl
  ihave %Hpl := ownSlice_len _ _ _ $$ Hpsl
  have hplen : sint.Z psl.len = 4 := by
    have h := Hpl.1; simp only [etcd_auth.principals, List.length] at h; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoInterface) psl.len) as %insl ⟨Hins, -⟩
  · ipureintro; omega
  (try wp_auto)
  -- the inputs: `ins[c] = ps[c]`
  ihave IH : (∃ (k cv : w64) (xsL : List GoInterface),
      "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗ "Hins" ∷ insl ↦* xsL ∗
      "%Hx" ∷ ⌜∀ j : Nat, j < sint.nat k → ∀ w, etcd_auth.principals[j]? = some w →
        xsL[j]? = some (interface.mkOk go.string #w)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 4 ∧ xsL.length = 4⌝ : IProp GF)
    $$ [i c Hins]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨fun j hj => absurd hj (by have : sint.nat (W64 0) = 0 := rfl; omega), by decide, by decide, ?_⟩
    simp only [List.length_replicate]; word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z k < sint.Z psl.len := by simpa using Hif
    have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    have hkN : sint.nat k < etcd_auth.principals.length := by rw [hP4]; omega
    obtain ⟨w, hw⟩ : ∃ w, etcd_auth.principals[sint.nat k]? = some w := ⟨_, List.getElem?_eq_getElem hkN⟩
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, Hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index psl (sint.Z k) etcd_auth.principals DFrac.discard w Hk.1) $$ [] as -
    · iframe #; ipureintro; exact hw
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    wp_apply (wp_load_slice_index psl (sint.Z k) etcd_auth.principals DFrac.discard w Hk.1) $$ [] as -
    · iframe #; ipureintro; exact hw
    (try wp_auto)
    ihave %Hil := ownSlice_len _ _ _ $$ Hins
    have hil : sint.Z insl.len = 4 := by have := Hil.1; rw [Hk.2.2] at this; word
    have hbi : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z insl.len := ⟨Hk.1, by omega⟩
    (try simp only [hbi, _root_.and_self, ↓reduceIte])
    wp_apply (wp_store_slice_index insl (sint.Z k) xsL _) $$ [Hins] as Hins
    · iframe; ipureintro; exact ⟨Hk.1, by omega⟩
    wp_for_post
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    iframe
    iexists (k + W64 1), k, _
    iframe
    ipureintro
    refine ⟨?_, by word, by word, by rw [List.length_set]; exact Hk.2.2⟩
    intro j hj w' hw'
    rw [hk1] at hj
    rw [List.getElem?_set]
    by_cases hjk : j = sint.nat k
    · subst hjk
      rw [hw] at hw'
      cases hw'
      simp only [show (sint.Z k).toNat = sint.nat k from rfl, ↓reduceIte, Hk.2.2]
      simp only [if_pos (show sint.nat k < 4 by omega)]
    · have : ¬ (sint.Z k).toNat = j := by show ¬ sint.nat k = j; omega
      simp only [this, ↓reduceIte]
      exact Hx j (by omega) w' hw'
  -- the inputs done
  have Hk4 : sint.nat k = 4 := by
    have : ¬ sint.Z k < sint.Z psl.len := by simpa using Hif
    have : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    omega
  try iclear i
  try iclear c
  imod ownSlice_persist _ _ _ $$ Hins with #Hins
  (try wp_auto)
  wp_apply (wp_principalCodec (prP (Gg := hG.goose_globalGS) Γ γR addrs) prQ) as %cd #Hcd
  (try wp_auto)
  ihave Hl := bigSepL_range_of ns (fun _ a => iprop(svcAddr (Gg := hG.goose_globalGS)
    (principalSvcG (Gg := hG.goose_globalGS) Γ γR addrs) a ∗ budUnit (Gg := hG.goose_globalGS) a)) $$ Hl
  wp_apply (wp_reportAll (principalSvcG (Gg := hG.goose_globalGS) Γ γR addrs) nodes insl ns xsL prIn
      (fun _ _ => iprop(True)) cd (W64 180000000000) Htb (by rw [Hk.2.2, Hn4]; try rfl))
      $$ [Htok Hl] as %outs %oks ⟨Htok', %Hlo, Hres⟩
  · iframe #
    iframe Htok
    iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ Hl
    iintro !> %j %c %hc ⟨%a, %ha, #Ha, Hbud⟩
    have hcN : c < ns.length := List.mem_range.1 (List.mem_of_getElem? hc)
    have hc4 : c < etcd_auth.principals.length := by rw [hP4]; omega
    obtain ⟨w, hw⟩ : ∃ w, etcd_auth.principals[c]? = some w := ⟨_, List.getElem?_eq_getElem hc4⟩
    iexists a, interface.mkOk go.string #w
    isplitr
    · ipureintro; exact ⟨ha, Hx c (by omega) w hw⟩
    iframe Ha Hbud
    rw [prIn_eq hw]
    simp only [principalWire]
    isplitr
    · ipureintro
      first
        | exact ⟨trivial, principals_small w (List.mem_of_getElem? hw)⟩
        | exact ⟨rfl, principals_small w (List.mem_of_getElem? hw)⟩
        | exact principals_small w (List.mem_of_getElem? hw)
    isplitr
    · iunfold prP
      isplitr
      · rw [← akDistEnv_eq_G]
        iexact Henv
      · ipureintro; exact List.mem_of_getElem? hw
    · iintro %o -
      itrivial
  -- the answers counted: `if oks[c] && outs[c].(bool) { n++ }`
  (try wp_auto)
  have H00 : sint.nat (W64 0) = 0 := rfl
  ihave Hres : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (ns.length - sint.nat (W64 0)),
      prRes Γ γR addrs outs oks c : IProp GF) $$ [Hres]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']
    unfold prRes
    iexact Hres
  ihave IH2 : (∃ (k cv nv : w64),
      "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hres" ∷ ([∗list] c ∈ List.range' (sint.nat k) (ns.length - sint.nat k), prRes Γ γR addrs outs oks c) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝ : IProp GF)
    $$ [i c n Hres]
  · iexists W64 0, _, _
    iframe
    ipureintro
    exact ⟨by decide, by decide⟩
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.Z k < sint.Z psl.len := by simpa [intoVal_eq_iff] using Hif
    have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    have hkN : sint.nat k < etcd_auth.principals.length := by rw [hP4]; omega
    obtain ⟨w, hw⟩ : ∃ w, etcd_auth.principals[sint.nat k]? = some w := ⟨_, List.getElem?_eq_getElem hkN⟩
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, Hlt⟩
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply (wp_load_slice_index psl (sint.Z k) etcd_auth.principals DFrac.discard w Hk.1) $$ [] as -
    · iframe #; ipureintro; exact hw
    (try wp_auto)
    rw [show ns.length - sint.nat k = (ns.length - (sint.nat k + 1)) + 1 by omega, List.range'_succ]
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hres with ⟨Hc, Hres⟩
    iunfold prRes at Hc
    icases Hc with ⟨%v, %ok, Hv, Hok, Hq⟩
    rw [hkk]
    have hbo : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z oks.len := ⟨Hk.1, by rw [Hlo.2]; omega⟩
    have hbu : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z outs.len := ⟨Hk.1, by rw [Hlo.1]; omega⟩
    (try simp only [hbo, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    icases Hq with (%Hf | ⟨%Ht, (⟨%o, %Ho, -⟩ | %Hu)⟩)
    · -- no answer
      subst Hf
      (try wp_auto)
      wp_for_post
      iframe
      iexists (k + W64 1), k, nv
      rw [hk1]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    · -- an answer, a `bool`
      subst Ht
      subst Ho
      (try simp only [hbu, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      (try simp only [hbu, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      (try wp_if_destruct)
      all_goals
        (try wp_auto)
        wp_for_post
        iframe
        iexists (k + W64 1), k, _
        rw [hk1]
        iframe
        ipureintro
        exact ⟨by word, by word⟩
    · exact Hu.elim
  · (try wp_auto)
    iapply HΦ
    iframe Htok'

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
