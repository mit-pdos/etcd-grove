/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/apiserver.lean`. Lean-first.

- `NewCompactor` with the compactors' contracts from the invariant (`casOk_of_cinv`, `keyReadOk_of_cinv`, at
  `Seen := seenOk γ`, `recorded := True`).
- The samples: a loop keeping `last` a lower bound of the compactor's revision (`compactRevLb`), so
  `CompactRevision` never returns less (its spec), and `last ≥ 0` (`recRevOk`).
- `Stop`, a last `CompactRevision`.
- The first `Get`: `r`'s reached bound made a lower bound of the invariant's counter before it
  (`cinv_revLb`), so the read state's revision, the reply's header revision, is at least `r`
  (`readAu_check`); the key's value, if present, is `FormatInt c` (`ParseInt` reads `c` back) for a `c`
  that is `0` or reached.
- The second `Get`: `c`'s reached bound made a lower bound of the counter before it, so its header
  revision is at least `c`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewCompactor
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__CompactRevision
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__Stop
public import Spec.strconv.ParseInt
public import Perennial.Spec.context.Background
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Aus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- A nonzero length that is not negative is positive. -/
theorem len_pos (s : w64) (h : ¬ s = W64 0) (h0 : 0 ≤ sint.Z s) : 0 < sint.Z s := by
  have : sint.Z s ≠ 0 := fun h' => h (by word)
  omega

/-- The same, as a natural number. -/
theorem len_pos_nat (s : w64) (h : ¬ s = W64 0) (h0 : 0 ≤ sint.Z s) : 0 < sint.nat s := by
  have := len_pos s h h0
  word

/-- The read update for a `Get` at a lower bound `n` of the counter, at every member. -/
theorem readAus_check (ms : List (client.SrvAt GF)) (γk : KVNames)
    (hs : ∀ x ∈ ms, kvSame x.γr.kv γk) (γ : CNames) (n : Nat) :
    cinv (GF := GF) γk γ ∗ monoNatLbOwn γ.rv n ⊢
      □ ([∧list] x ∈ ms, ⌜checkQ (GF := GF) γk n = fun _ => iprop(True)⌝ ∨
        kvReadAu x.γr.kv (checkQ γk n)) := by
  iintro #H
  imodintro
  iapply (BigAndL.bigAndL_intro (P := iprop(cinv (GF := GF) γk γ ∗ monoNatLbOwn γ.rv n))
    (fun _ x hx => by
      iintro #H'
      iright
      iapply (readAu_check γk x.γr.kv (hs x (List.mem_of_getElem? hx)) γ n) $$ H'))
  iexact H

/-- A revision that is `0` or reached is a lower bound of the counter (`cinv_revLb`). -/
theorem revOk_lb (γr : ServerRaftNames) (γk : KVNames) (γ : CNames) (r : w64) :
    ⊢ kvInv (GF := GF) γr γk -∗ cinv γk γ -∗ k8s.revOk γk r ={⊤}=∗
      monoNatLbOwn γ.rv (sint.Z r).toNat := by
  iintro #Hkv #Hinv #Hr
  iunfold k8s.revOk at Hr
  icases Hr with (%H0 | ⟨%Hpos, #Hlb⟩)
  · subst H0
    imod (monoNatLbOwn_0 (GF := GF) γ.rv) with #H
    imodintro
    simp
    iexact H
  · iapply (cinv_revLb γr γk γ ⊤ (by
      intro p hp
      rw [Iris.Std.LawfulSet.mem_diff]
      exact ⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩)
      (fun _ _ => CoPset.mem_full) (sint.Z r)) $$ Hkv Hinv Hlb

theorem apiserver.wp_proof
    (wp_NewCompactor : k8s.NewCompactor.spec (GF := GF) (hG := hG))
    (wp_CompactRevision : k8s.compactor.CompactRevision.spec (GF := GF) (hG := hG))
    (wp_Stop : k8s.compactor.Stop.spec (GF := GF) (hG := hG))
    (wp_ParseInt : EtcdGrove.strconv.ParseInt.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    apiserver.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ cl ms V γr γk γ hsame hcmp hcret
  wp_start as ⟨#Hcl, #Hone, #Hregs, #Hst, #Hko, #Hwo, #Hinv, #Hkvi⟩
  rw [show github_com.mit_pdos.etcd_grove.examples.k8s.compactor.compactRevKey = #k8s.compactRevKey
    from rfl]
  ihave #Pe3 : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Hcas := casOk_of_cinv ms γk hsame γ $$ Hinv
  ihave #Hkr := keyReadOk_of_cinv γk γ $$ Hinv
  wp_auto
  wp_apply (wp_NewCompactor cl ms V γk (seenOk γ) (fun _ => iprop(True)) _ _ _ hsame hcmp hcret
      (by decide)) $$ [] as %c %γc ⟨#Hc, #H0⟩
  · iframe #
    -- no `onClose`
    iapply k8s.closeOk_nil
  (try wp_auto)
  ihave IH : (∃ (n l : w64), "i" ∷ i_ptr ↦ n ∗ "last" ∷ last_ptr ↦ l ∗
      "#Hl" ∷ compactRevLb γc l ∗ "%Hl0" ∷ ⌜0 ≤ sint.Z l⌝ : IProp GF) $$ [i last]
  · iexists _, _
    iframe
    simp only [named]
    isplitl
    · iExactEq H0; rfl
    · ipureintro; show (0 : Int) ≤ sint.Z (W64 0); simp
  wp_for IH
  wp_if_destruct
  · wp_apply time.wp_Sleep
    (try iintro -)
    (try wp_auto)
    wp_apply (wp_CompactRevision c cl γk (fun _ => iprop(True)) γc l) $$ [] as %r ⟨#Hrr, #Hlr, %Hle⟩
    · iframe #
    ihave %hr0 : ⌜0 ≤ sint.Z r⌝ $$ [Hrr]
    · iunfold recRevOk at Hrr
      icases Hrr with (%H | ⟨%H, -, -⟩)
      · subst H; ipureintro; simp
      · ipureintro; omega
    have hlt : ¬ (sint.Z r < sint.Z l) := by omega
    simp only [hlt, decide_false]
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, r
    iframe
    iframe #
    ipureintro; exact hr0
  · (try wp_auto)
    wp_apply (wp_Stop c cl γk (fun _ => iprop(True)) γc) $$ []
    · iframe #
    (try iintro -)
    (try wp_auto)
    wp_apply (wp_CompactRevision c cl γk (fun _ => iprop(True)) γc l) $$ [] as %r ⟨#Hrr, #Hlr, %Hle⟩
    · iframe #
    ihave %hr0 : ⌜0 ≤ sint.Z r⌝ $$ [Hrr]
    · iunfold recRevOk at Hrr
      icases Hrr with (%H | ⟨%H, -, -⟩)
      · subst H; ipureintro; simp
      · ipureintro; omega
    have hlt : ¬ (sint.Z r < sint.Z l) := by omega
    simp only [hlt, decide_false]
    (try wp_auto)
    -- `r`'s reached bound, a lower bound of the invariant's counter
    ihave #Hrok : k8s.revOk γk r $$ [Hrr]
    · iunfold recRevOk at Hrr
      iunfold k8s.revOk
      icases Hrr with (%H | ⟨%H, -, #Hlb⟩)
      · ileft; ipureintro; exact H
      · iright; iframe Hlb; ipureintro; exact H
    imod (revOk_lb γr γk γ r) $$ Hkvi Hinv Hrok with #Hrlb
    ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
    · iunfold optsAt
      iexists ([] : List GoFunc)
      isplitl
      · iapply ownSlice_nil
      isplitl
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      simp at Hf
    wp_apply wp_Background
    (try iintro -)
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny EtcdGrove.rpctypesEtcdError_asTarget _) $$ []
      as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
    (try wp_auto)
    ihave #Haus := readAus_check ms γk hsame γ (sint.Z r).toNat $$ [Hinv Hrlb]
    · iframe #
    wp_apply (client.client_Get_st cl ms V ctx cd k8s.compactRevKey slice.nil
        (checkQ γk (sint.Z r).toNat)
        (opSizeOk_opGetModel (K := 15) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide)
          (by decide))) $$ [] as %resp %err Hout
    · iframe #
    (try wp_auto)
    wp_apply Hcancel
    (try iintro -)
    icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hσ⟩ | ⟨%Herr, -⟩)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => ?_
      (try wp_auto)
      iapply HΦ; itrivial
    subst Herr
    obtain ⟨hkvs, hrev, hb⟩ := Hσ
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    iunfold checkQ at HQ
    icases HQ with ⟨%Hrσ, HK⟩
    have hhdr : sint.Z m.hdr.revision = (σ.rev : Int) := by
      have := hb.lt
      rw [hrev]; word
    have hgt : ¬ (sint.Z m.hdr.revision < sint.Z r) := by omega
    (try wp_auto)
    simp only [hgt, decide_false]
    (try wp_auto)
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; itrivial
    · obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
        have : 0 < ps.length := by
          rw [Hsll.1]; exact len_pos_nat sl.len Hif Hsll.2
        exact ⟨ps[0], List.getElem?_eq_getElem this⟩
      obtain ⟨kv0, Hkv0⟩ : ∃ kv0, m.kvs[0]? = some kv0 := by
        have : 0 < m.kvs.length := by
          rw [← Hlen]; exact List.length_pos_of_mem (List.mem_of_getElem? Hp0)
        exact ⟨m.kvs[0], List.getElem?_eq_getElem this⟩
      ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
      iunfold txn.kvIs at Hkv
      icases Hkv with ⟨%kSl, %vSl, -, -, -, #HmF, #HvF, #HvalF, #HvS, -⟩
      have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
        have h3 := len_pos sl.len Hif Hsll.2
        have h4 : sint.Z (W64 0) = 0 := by decide
        omega
      simp only [Hbnd0, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact Hp0
      (try wp_auto)
      wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
      · iexact HvS
      -- the key's value: `FormatInt c` for a `c` that is `0` or reached
      have hkv : keyValue σ k8s.compactRevKey = some kv0.value := by
        unfold keyValue; rw [← hkvs]
        cases hm : m.kvs with
        | nil => simp [hm] at Hkv0
        | cons a l => simp only [hm, List.getElem?_cons_zero, Option.some.injEq] at Hkv0; subst Hkv0; rfl
      icases HK with (%Hn | ⟨%c, %Hc, #Hrc⟩)
      · rw [hkv] at Hn; cases Hn
      rw [hkv] at Hc
      have hval : kv0.value = fmtInt c (W64 10) := Option.some.inj Hc
      rw [hval]
      (try wp_auto)
      wp_apply (wp_ParseInt (fmtInt c (W64 10)) (W64 10) (W64 64)) as %v %err2 %Hp
      obtain ⟨rfl, rfl⟩ := Hp c rfl rfl rfl
      (try wp_auto)
      -- the second `Get`: `c`'s reached bound, a lower bound of the counter, before it
      imod (revOk_lb γr γk γ v) $$ Hkvi Hinv Hrc with #Hclb
      wp_apply wp_Background
      (try iintro -)
      (try wp_auto)
      wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny EtcdGrove.rpctypesEtcdError_asTarget _) $$ []
        as %ctx2 %cd2 %cancel2 ⟨#Hcancel2, #Hctx2, #Hce2, -⟩
      (try wp_auto)
      ihave #Haus2 := readAus_check ms γk hsame γ (sint.Z v).toNat $$ [Hinv Hclb]
      · iframe #
      wp_apply (client.client_Get_st cl ms V ctx2 cd2 k8s.compactRevKey slice.nil
          (checkQ γk (sint.Z v).toNat)
          (opSizeOk_opGetModel (K := 15) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide)
            (by decide))) $$ [] as %resp2 %err3 Hout2
      · iframe #
      (try wp_auto)
      wp_apply Hcancel2
      (try iintro -)
      icases Hout2 with (⟨%Herr3, %m2, %σ2, #Hm2, #HQ2, %Hσ2⟩ | ⟨%Herr3, -⟩)
      rotate_left
      · cases err3 with
        | nil => exact absurd rfl Herr3
        | ok ei => ?_
        (try wp_auto)
        iapply HΦ; itrivial
      subst Herr3
      obtain ⟨-, hrev2, hb2⟩ := Hσ2
      iunfold rangeRespMsg at Hm2
      icases Hm2 with ⟨%Hnn2, %h2, %sl2, %ps2, #Hh2, #Hhf2, -, -, -, -, -⟩
      iunfold hdrFull at Hhf2
      icases Hhf2 with ⟨%Hhn2, -, -, #Hrevf2, -, -⟩
      iunfold checkQ at HQ2
      icases HQ2 with ⟨%Hvσ, -⟩
      have hhdr2 : sint.Z m2.hdr.revision = (σ2.rev : Int) := by
        have := hb2.lt
        rw [hrev2]; word
      ihave %hv0 : ⌜0 ≤ sint.Z v⌝ $$ [Hrc]
      · iunfold k8s.revOk at Hrc
        icases Hrc with (%H | ⟨%H, -⟩)
        · subst H; ipureintro; simp
        · ipureintro; omega
      have hgt2 : ¬ (sint.Z m2.hdr.revision < sint.Z v) := by omega
      (try wp_auto)
      simp only [hgt2, decide_false]
      (try wp_auto)
      iapply HΦ; itrivial

end proof

end k8s_compactor
end EtcdGrove
end Perennial
