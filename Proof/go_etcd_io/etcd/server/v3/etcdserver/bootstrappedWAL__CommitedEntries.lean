/-
Proof of `(*bootstrappedWAL).CommitedEntries()`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__CommitedEntries.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__CommitedEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedWAL.CommitedEntries.wp_proof
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF))
    (wp_Uint64 : zap.Uint64.spec (GF := GF))
    (wp_Int' : zap.Int'.spec (GF := GF))
    (wp_Info : zap.Logger.Info.spec (GF := GF)) :
    bootstrappedWAL.CommitedEntries.spec (GF := GF) := by
  intro w dq dqs bw sv hs es Hlg Hwf Hc_ge
  wp_start as Hpre
  iNamed Hpre
  icases typedPointsto_not_null_dup _ _ _ $$ Hwal with ⟨Hwal, %Hwnn⟩
  iStructNamedSuffix Hwal "W"
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, Hs, #Hb⟩
  ihave %Heq := entsBig_length _ _ $$ Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hsl_wf := ownSlice_wf _ _ _ $$ Hs
  ihave #Hpkgr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hpkgz : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  rename_i ig
  irename : (ig ↦ (W64 0) : IProp GF) => gi
  ihave IH : iprop(∃ (n i0 : w64) (e0 : Loc),
      "wal" ∷ wal_ptr ↦ w ∗
      "lgW" ∷ w.[bootstrappedWAL, go!"lg"] ↦{dq} bw.lg' ∗
      "stW" ∷ w.[bootstrappedWAL, go!"st"] ↦{dq} bw.st' ∗
      "entsW" ∷ w.[bootstrappedWAL, go!"ents"] ↦{dq} bw.ents' ∗
      "Hst" ∷ hsPts bw.st' dqs hs ∗
      "Hs" ∷ bw.ents' ↦* ls ∗
      "Hcap" ∷ ownSliceCap Loc bw.ents' (DFrac.own 1) ∗
      "j" ∷ i_ptr ↦ n ∗
      "gi" ∷ ig ↦ i0 ∗
      "ent" ∷ ent_ptr ↦ e0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int) ∧
        sint.nat n ≤ (uint.Z hs.Commit' - uint.Z sv.Metadata'.Index').toNat⌝)
    $$ [wal lgW stW entsW Hst Hs Hcap i gi ent]
  · iexists W64 0, _, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, Nat.zero_le _⟩
  wp_for IH
  wp_if_destruct
  · -- Inside loop: `sint.Z n < sint.Z bw.ents'.len`
    have Hlt : sint.nat n < ls.length := by word
    obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨e, He⟩ : ∃ e, es[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Heq]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z bw.ents'.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    have Hl' : ls[(sint.Z n).toNat]? = some l := Hl
    icases ownSlice_elem_acc (sint.Z n) l bw.ents' (DFrac.own 1) ls Hn.1 Hl' $$ Hs
      with ⟨Hle, Hs_close⟩
    ihave #Hent : entRO l e $$ []
    · iapply (BigSepL2.bigSepL2_lookup Hl He) $$ Hb
    (try wp_auto)
    ihave Hs := Hs_close $$ Hle
    rw [list_insert_id Hl']
    ihave #HentPts : entPts l DFrac.discard e $$ []
    · iexact Hent
    wp_apply wp_Entry_GetIndex.1 l DFrac.discard e $$ [$Hpkgr $HentPts] as _
    (try wp_auto)
    wp_apply wp_hsPts_GetCommit bw.st' dqs hs $$ [$Hpkgr $Hst] as Hst
    (try wp_auto)
    have He_idx := Hwf (sint.nat n) e He
    simp only [snapId] at He_idx
    wp_if_destruct
    · -- `e.Index' > hs.Commit'`: log and return `wal.ents[:n]`
      have Hgt_z : uint.Z hs.Commit' < uint.Z e.Index' := by word
      have Hn_eq : sint.nat n = (uint.Z hs.Commit' - uint.Z sv.Metadata'.Index').toNat := by
        have := Hn.2.2
        omega
      (try wp_auto)
      wp_apply wp_Entry_GetIndex.1 l DFrac.discard e $$ [$Hpkgr $HentPts] as _
      (try wp_auto)
      wp_apply wp_Uint64 $$ [$Hpkgz] as %f0 _
      (try wp_auto)
      wp_apply wp_hsPts_GetCommit bw.st' dqs hs $$ [$Hpkgr $Hst] as Hst
      (try wp_auto)
      wp_apply wp_Uint64 $$ [$Hpkgz] as %f1 _
      (try wp_auto)
      wp_apply wp_Int' $$ [$Hpkgz] as %f2 _
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr; · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply (wp_Info bw.lg') $$ [$Hpkgz]
      · ipureintro; exact Hlg
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      icases ownSlice_slice_with_cap (W64 0) n bw.ents' ls ⟨by word, by word, by word⟩
        $$ [$Hs $Hcap] with ⟨-, Hs_sub, Hcap_sub⟩
      have hsub : subslice (sint.nat (W64 0)) (sint.nat n) ls = ls.take (sint.nat n) := rfl
      rw [hsub]
      ihave #Hb_sub := entsBig_take (sint.nat n) ls es $$ Hb
      ihave Hwal : w ↦{dq} bw $$ [lgW haveWALW wW stW entsW snapshotW meta'W]
      · iapply typedPointsto_combine _ _ _ Hwnn
        simp only [TypedPointsto.typedPointstoDef, named]
        iframe
      iapply HΦ
      rw [← Hn_eq]
      iframe Hwal Hst Hcap_sub
      iunfold entsPts
      iexists (ls.take (sint.nat n))
      iframe Hs_sub Hb_sub
    · -- `e.Index' ≤ hs.Commit'`: advance `n`
      have Hle_z : uint.Z e.Index' ≤ uint.Z hs.Commit' := by word
      (try wp_auto)
      wp_for_post
      iframe
      iexists (n + W64 1), n, l
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      omega
  · -- Loop finished normally: `sint.Z bw.ents'.len ≤ sint.Z n`
    (try wp_auto)
    have Hn_len : sint.nat n = es.length := by
      have := Hlen.1
      have := Hn.2.1
      word
    have Htake_all : es.take (uint.Z hs.Commit' - uint.Z sv.Metadata'.Index').toNat = es := by
      apply List.take_of_length_le
      rw [← Hn_len]
      exact Hn.2.2
    ihave Hwal : w ↦{dq} bw $$ [lgW haveWALW wW stW entsW snapshotW meta'W]
    · iapply typedPointsto_combine _ _ _ Hwnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iapply HΦ
    rw [Htake_all]
    iframe Hwal Hst Hcap
    iunfold entsPts
    iexists ls
    iframe Hs Hb

end proof

end EtcdGrove
end Perennial
