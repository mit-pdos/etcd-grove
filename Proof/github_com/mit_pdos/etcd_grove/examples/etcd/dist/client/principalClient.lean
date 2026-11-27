/-
Proof of `Spec/.../dist/client/principalClient.lean` (#50 F7 S7). Lean-first (no Rocq counterpart).

`k := len(eps)`, positive; each arm's address `eps[c % k]` (`mod_len_sintD`, `srem_eq_umodD`) is one of `addrs`,
serving a member (`membersAt_of_mem`, `AuthLeaseRunLemmas.lean`); `u`'s and `v`'s clients by `newUserClient` (their principals), `bad`'s and
the default's by `newClient` of the one address, the anonymous client (`anonCli_of_new`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRunLemmas
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem principalClient.wp_proof
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG)) :
    principalClient.spec (GF := GF) (hG := hG) := by
  intro π eps addrs who V Γ Htb Hpe hne hau hauth
  wp_start as ⟨Hlt, #Heps, #Hms⟩
  ihave %Hlen := ownSlice_len $$ Heps
  have hpos : 0 < addrs.length := List.length_pos_iff.2 hne
  have hkl : uint.nat eps.len = addrs.length := by word
  have hk63 : addrs.length < 2 ^ 63 := by word
  have hmodZ := fun c hc => mod_len_sintD eps.len addrs.length c hkl hpos hk63 hc
  have hepsZ : sint.Z eps.len = (addrs.length : Int) := by word
  have hk0' : ¬ (sint.Z eps.len = 0) := by word
  have hpe : ∀ a ∈ addrs, plainEndpoint a := Hpe.2
  have hsr : ∀ c : Nat, c < 2 ^ 32 → BitVec.srem (W64 (c : Int)) eps.len = W64 (c : Int) % eps.len :=
    fun c hc => srem_eq_umodD _ _ (by simp [W64]; omega) (by word)
  have hbd : ∀ c : Nat, c < 2 ^ 32 →
      0 ≤ sint.Z (W64 (c : Int) % eps.len) ∧ sint.Z (W64 (c : Int) % eps.len) < sint.Z eps.len := by
    intro c hc; rw [hmodZ c hc, hepsZ]; have := Nat.mod_lt c hpos; omega
  (try wp_auto)
  wp_if_destruct
  · -- `u`, through `eps[1 % k]`
    (try wp_auto)
    simp only [hk0', ↓reduceIte]
    rw [show BitVec.srem (W64 1) eps.len = W64 1 % eps.len from hsr 1 (by decide)]
    (try wp_auto)
    have Hb : 0 ≤ sint.Z (W64 1 % eps.len) ∧ sint.Z (W64 1 % eps.len) < sint.Z eps.len := hbd 1 (by decide)
    have hm1 : sint.Z (W64 1 % eps.len) = ((1 % addrs.length : Nat) : Int) := hmodZ 1 (by decide)
    obtain ⟨a, hxa⟩ : ∃ x, addrs[1 % addrs.length]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩
    have ham : a ∈ addrs := List.mem_of_getElem? hxa
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index eps (sint.Z (W64 1 % eps.len)) _ _ a Hb.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [hm1, Int.toNat_natCast]; exact hxa
    ihave #Hma := membersAt_of_mem addrs Γ a ham $$ Hms
    (try wp_auto)
    wp_apply (wp_newUserClient a go!"u" go!"u-pw" V Γ Htb (hpe a ham) (by unfold strsSizeOk; decide)
        (by decide) (by decide) hau hauth) $$ [$Hlt] as %cl %err ⟨Hlt, Hr⟩
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    icases Hr with (⟨%Herr, %cfg, #Hu, %hP⟩ | %Hfail)
    · ileft
      isplitr; · ipureintro; exact Herr
      iexists a, cfg
      iframe #
      ipureintro; exact ⟨ham, Or.inr ⟨hP, by simp⟩⟩
    · iright; ipureintro; exact Hfail.1
  wp_if_destruct
  · -- `v`, through `eps[2 % k]`
    (try wp_auto)
    simp only [hk0', ↓reduceIte]
    rw [show BitVec.srem (W64 2) eps.len = W64 2 % eps.len from hsr 2 (by decide)]
    (try wp_auto)
    have Hb : 0 ≤ sint.Z (W64 2 % eps.len) ∧ sint.Z (W64 2 % eps.len) < sint.Z eps.len := hbd 2 (by decide)
    have hm1 : sint.Z (W64 2 % eps.len) = ((2 % addrs.length : Nat) : Int) := hmodZ 2 (by decide)
    obtain ⟨a, hxa⟩ : ∃ x, addrs[2 % addrs.length]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩
    have ham : a ∈ addrs := List.mem_of_getElem? hxa
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index eps (sint.Z (W64 2 % eps.len)) _ _ a Hb.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [hm1, Int.toNat_natCast]; exact hxa
    ihave #Hma := membersAt_of_mem addrs Γ a ham $$ Hms
    (try wp_auto)
    wp_apply (wp_newUserClient a go!"v" go!"v-pw" V Γ Htb (hpe a ham) (by unfold strsSizeOk; decide)
        (by decide) (by decide) hau hauth) $$ [$Hlt] as %cl %err ⟨Hlt, Hr⟩
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    icases Hr with (⟨%Herr, %cfg, #Hu, %hP⟩ | %Hfail)
    · ileft
      isplitr; · ipureintro; exact Herr
      iexists a, cfg
      iframe #
      ipureintro; exact ⟨ham, Or.inr ⟨hP, by simp⟩⟩
    · iright; ipureintro; exact Hfail.1
  wp_if_destruct
  · -- `bad`, anonymously through `eps[1 % k]`
    (try wp_auto)
    simp only [hk0', ↓reduceIte]
    rw [show BitVec.srem (W64 1) eps.len = W64 1 % eps.len from hsr 1 (by decide)]
    (try wp_auto)
    have Hb : 0 ≤ sint.Z (W64 1 % eps.len) ∧ sint.Z (W64 1 % eps.len) < sint.Z eps.len := hbd 1 (by decide)
    have hm1 : sint.Z (W64 1 % eps.len) = ((1 % addrs.length : Nat) : Int) := hmodZ 1 (by decide)
    obtain ⟨a, hxa⟩ : ∃ x, addrs[1 % addrs.length]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩
    have ham : a ∈ addrs := List.mem_of_getElem? hxa
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index eps (sint.Z (W64 1 % eps.len)) _ _ a Hb.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [hm1, Int.toNat_natCast]; exact hxa
    ihave #Hma := membersAt_of_mem addrs Γ a ham $$ Hms
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoString) (l := [a])
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    imod ownSlice_persist _ _ _ $$ Hlit with #Hlit
    (try wp_auto)
    wp_apply (wp_newClient _ [a] V Htb (plainEndpoints_singleton _ (hpe a ham))) $$ [$Hlt]
        as %cl %err ⟨Hlt, Hcl⟩
    · iframe #
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    icases Hcl with (⟨%Herr, #Hnc, #Hnp, #Hcfg⟩ | %Hfail)
    · ihave ⟨%cfg, #Hu, %hP⟩ := anonCli_of_new cl a V $$ [Hnc Hnp Hcfg]
      · iframe #
      ileft
      isplitr; · ipureintro; exact Herr
      iexists a, cfg
      iframe #
      ipureintro; exact ⟨ham, Or.inl hP⟩
    · iright; ipureintro; exact Hfail.1
  -- anyone else, anonymously through `eps[0]`
  (try wp_auto)
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z eps.len := by constructor <;> word
  obtain ⟨a, hxa⟩ : ∃ x, addrs[0]? = some x := ⟨_, List.getElem?_eq_getElem hpos⟩
  have ham : a ∈ addrs := List.mem_of_getElem? hxa
  (try simp only [Hb0, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index eps (sint.Z (W64 0)) _ _ a Hb0.1 $$ [Heps] as -
  · iframe #; ipureintro; exact hxa
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) (l := [a])
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  imod ownSlice_persist _ _ _ $$ Hlit with #Hlit
  (try wp_auto)
  wp_apply (wp_newClient _ [a] V Htb (plainEndpoints_singleton _ (hpe a ham))) $$ [$Hlt]
      as %cl %err ⟨Hlt, Hcl⟩
  · iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hlt
  icases Hcl with (⟨%Herr, #Hnc, #Hnp, #Hcfg⟩ | %Hfail)
  · ihave ⟨%cfg, #Hu, %hP⟩ := anonCli_of_new cl a V $$ [Hnc Hnp Hcfg]
    · iframe #
    ileft
    isplitr; · ipureintro; exact Herr
    iexists a, cfg
    iframe #
    ipureintro; exact ⟨ham, Or.inl hP⟩
  · iright; ipureintro; exact Hfail.1

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
