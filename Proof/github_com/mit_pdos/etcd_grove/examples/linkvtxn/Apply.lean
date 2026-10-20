/-
Lean-first (no Rocq counterpart).

The proof of `Apply(cli, input)` (linkv-txn stage F, as `linkv/Apply.lean`'s): `NewProph()` gives a
prophecy of the `ResolveBool` at the end (`!out.Err`, the call's outcome), and the commit
(`Inv.lean`'s steps) is chosen by the operation's kind and the prophecy's head before the client
is called:

- a write, prophecy `ok`: the call's update is `write_ok_au` (fired at most once on the
  one-attempt client); it commits `lintest`'s update at the server's apply with `call`'s output at
  the state it fired at, and the call returns that output (`call.spec`, the state good: `wQ`). An
  error return contradicts the prophecy; so does a state whose answer's revision does not fit a
  word (the reply's state is below `2^63`).
- a write, prophecy error: commit now, the write pending (`write_err_commit`); the call's update is
  `write_pend_au`, whose firing (during the call, after it, or never) is the late effect.
- a read, prophecy error: commit now (`read_err_commit`); the call without an update.
- a read (get, list, read-only transaction), prophecies `ok` and revision `R` (the second
  prophecy, resolved with the reply's header revision): a call invariant (`callInv`) holds
  `lintest`'s update; the call's read update is `read_ok_au`, persistent, committing at its first
  firing at a state of revision `R`. After the reply (`readQ` of the state read, good, whose
  revision is the reply's), `ResolveU64` gives `R` the reply's revision, so the commit bit holds
  that state, and `Apply` takes the continuation (`callInv_take`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.call
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.isWrite
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem Apply.wp_proof (wp_call : call.spec (GF := GF) (hG := hG))
    (wp_isWrite : isWrite.spec (GF := GF) (hG := hG)) :
    Apply.spec (GF := GF) (hG := hG) := by
  intro _ γ cl ep V E γr cid mid hAs
  iintro #Hpkg #Pcli #Hcl #Hone #Hput #Hrange #Hdel #Htxn #Hinv
  iintro %i
  imodintro
  iintro %Φ %Hin HAU
  obtain ⟨x, rfl, Hgen⟩ := Hin
  obtain ⟨ix, hx, hkeys⟩ := Hgen.1
  have hi := inKeys_keysIn ix hkeys
  have hwL := isWriteL_dec x ix hx
  wp_func_call
  wp_call
  wp_auto_lc 2
  wp_apply (linkv.wp_NewProph_typed (τ := Bool) github_com.goose_lang.primitive.wp_NewProph)
    as %p %xs Hp
  wp_apply (linkv.wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph)
    as %rp %rs Hrp
  cases hw : ix.isWrite
  · by_cases Hok : xs.head? = some true
    · -- the prophecies say `ok` at revision `R`: the read update commits at its first firing at
      -- a state of revision `R` (`read_ok_au`), and `Apply` takes the continuation after the reply
      imod dghostVar_alloc (GF := GF) (none : Option KVState) with ⟨%γc, Hγc⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod inv_alloc callN ⊤ (iprop(
          (linU γ (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
          (∃ σ : KVState, dghostVar γc DFrac.discard (some σ) ∗
            ghostMapElem γ.r (uint.nat (rs.headD (W64 0))) DFrac.discard σ ∗
            (contAt x (outAt ix σ) Φ ∨ dghostVar γt (DFrac.own 1) ())))) $$ [HAU Hlc1 Hγc]
        with #Hci
      · inext
        ileft
        iframe Hlc1 Hγc
        iunfold linU
        iexact HAU
      ihave #Hc : callInv γ γc γt x ix (rs.headD (W64 0)) Φ $$ []
      · iunfold callInv; iexact Hci
      ihave #Hau := read_ok_au γ γr.kv γc γt x ix hx hw (rs.headD (W64 0)) Φ $$ []
      · iframe #
      (try wp_auto)
      wp_apply (wp_call cl ep V E γr cid mid hAs x ix (readQ γc (rs.headD (W64 0))) hx Hgen) $$ []
        as %y Hy
      · iframe #
        unfold callUpd
        rw [hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iright
        iexact Hau
      unfold callRes
      rw [hw]
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hy with (%Hy | ⟨%σ, #HQ, %Hy⟩)
      · subst Hy
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
      · obtain ⟨herr, hb, hy⟩ := Hy
        unfold readQ
        icases HQ with ⟨%hg, #Hbit⟩
        have hy' := hy hg
        simp only [herr, Bool.not_false]
        wp_pures
        (try wp_auto)
        wp_apply wp_isWrite x
        rw [hwL, hw]
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        by_cases HR : rs.headD (W64 0) = y.Rev'
        rotate_left
        · wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
            rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
          · iframe
          exact absurd (by rw [Hrs]; rfl) HR
        have Hσr : σ.rev = uint.nat (rs.headD (W64 0)) := by
          rw [HR, hy', outAt, outOf_rev, outRev_read ix σ hw]
          unfold uint.nat; word
        ihave #Hv := Hbit $$ %Hσr
        iapply fupd_wp
        imod (callInv_take γ γc γt x ix (rs.headD (W64 0)) Φ σ) $$ [Htok Hlc2] with HΦ
        · iframe Hc Hv Htok Hlc2
        imodintro
        wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
          rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
        · iframe
        rw [hy']
        iapply HΦ
        simp only [linkvtxnS]
        ipureintro; exact ⟨x, _, rfl, rfl, Hgen.1⟩
    · -- the prophecy says error: commit now
      iapply fupd_wp
      imod (read_err_commit γ γr.kv x ix hx hw Φ) $$ [HAU] with HΦ
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      (try wp_auto)
      wp_apply (wp_call cl ep V E γr cid mid hAs x ix (fun _ => iprop(True)) hx Hgen) $$ []
        as %y Hy
      · iframe #
        unfold callUpd
        rw [hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        ileft; ipureintro; first | rfl | trivial
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
          rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
        · iframe
        iapply HΦ
        simp only [linkvtxnS]
        ipureintro; exact ⟨x, _, rfl, rfl, Hgen.1⟩
      · obtain ⟨herr, -, -⟩ := Hy
        simp only [herr, Bool.not_false]
        wp_pures
        (try wp_auto)
        wp_apply wp_isWrite x
        rw [hwL, hw]
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs, herr] at Hok
  · by_cases Hok : xs.head? = some true
    · -- the prophecy says `ok`: the update the server fires commits
      ihave Hau := write_ok_au γ γr.kv x ix hx hi hw Φ $$ [HAU]
      · iframe Hinv; iunfold linU; iexact HAU
      (try wp_auto)
      wp_apply (wp_call cl ep V E γr cid mid hAs x ix (wQ x ix Φ) hx Hgen) $$ [Hau] as %y Hy
      · iframe #
        unfold callUpd
        rw [hw]
        simp only [↓reduceIte]
        iexact Hau
      unfold callRes
      rw [hw]
      simp only [↓reduceIte]
      icases Hy with (%Hy | ⟨%σ, HQ, %Hy⟩)
      · -- an error: contradicts the prophecy
        subst Hy
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
      · obtain ⟨herr, hb, hy⟩ := Hy
        unfold wQ
        icases HQ with (⟨%Hg, HΦ⟩ | %Hbad)
        · obtain ⟨hg, -⟩ := Hg
          have hy' := hy hg
          simp only [herr, Bool.not_false]
          wp_pures
          (try wp_auto)
          wp_apply wp_isWrite x
          rw [hwL, hw]
          wp_auto
          wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
            rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
          · iframe
          rw [hy']
          iapply HΦ
          simp only [linkvtxnS]
          ipureintro; exact ⟨x, _, rfl, rfl, Hgen.1⟩
        · exfalso
          have := outRev_le ix σ
          omega
    · -- the prophecy says error: commit now, the write pending
      iapply fupd_wp
      imod (write_err_commit γ γr.kv x ix hx hi hw Φ) $$ [HAU] with ⟨%n, HΦ, Htok⟩
      · iframe Hinv; iunfold linU; iexact HAU
      ihave Hau := write_pend_au γ γr.kv n ix $$ [Htok]
      · iframe Hinv; iexact Htok
      imodintro
      (try wp_auto)
      wp_apply (wp_call cl ep V E γr cid mid hAs x ix (fun _ => iprop(True)) hx Hgen) $$ [Hau]
        as %y Hy
      · iframe #
        unfold callUpd
        rw [hw]
        simp only [↓reduceIte]
        iexact Hau
      icases Hy with (%Hy | ⟨%σ, -, %Hy⟩)
      · subst Hy
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
          rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
        · iframe
        iapply HΦ
        simp only [linkvtxnS]
        ipureintro; exact ⟨x, _, rfl, rfl, Hgen.1⟩
      · obtain ⟨herr, -, -⟩ := Hy
        simp only [herr, Bool.not_false]
        wp_pures
        (try wp_auto)
        wp_apply wp_isWrite x
        rw [hwL, hw]
        wp_auto
        wp_apply (linkv.wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs, herr] at Hok

end proof

end linkvtxn
end EtcdGrove
end Perennial
