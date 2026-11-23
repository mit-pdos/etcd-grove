/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/InternalPrepareOK.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onInternalPrepareOK`: the pending entry of the op takes the client's address and request, then `onPrepareOK`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.Logs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.PrepareOK

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- An internal PrepareOK (valid), with its client's address. -/
theorem replica.wp_onInternalPrepareOK (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (d : replica.InternalPrepareOKData) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ network.addrOk tcp d.clientaddr' ∗
        VsrGhost.fact γ (.msg (.prepareOK (uint.nat d.pok'.ViewNum') (uint.nat d.pok'.OpNum')
          (uint.nat d.pok'.ReplicaID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onInternalPrepareOK")) (Val #src)) (Val #d))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Ha, #Hpf⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (ipv4port.IPv4Port.String_ptr.wp from_ptr (DFrac.own 1) src) $$ [«from»] as «from»
  · iexact «from»
  wp_log
  wp_apply wp_map_lookup2 $$ Hpk as Hpk
  wp_join iprop(∃ pk' : GMap w64 replica.PendingPrepareOK,
      v.internal'.pendingPOKs' ↦$ pk' ∗ ([∗map] k ↦ e ∈ pk', replica.pokOk γ n tcp v r k e) ∗
      rp ↦ v ∗ r_ptr ↦ rp ∗ pok_ptr ↦ d)
    with [Hpk Hpks Hr r pok] as ⟨%pk', Hpk, Hpks, Hr, r, pok⟩
  · -- the existing entry takes the client's address and request
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp Hif
    wp_apply wp_map_lookup1 $$ Hpk as Hpk
    simp only [he, Option.getD_some]
    wp_apply wp_mapInsert $$ Hpk as Hpk
    wp_join_done
    iexists _
    iframe Hpk Hr r pok
    ihave ⟨He, Hpks⟩ := (BI.BigSepM.bigSepM_delete he).1 $$ Hpks
    iapply (BI.BigSepM.bigSepM_insert_delete (PROP := IProp GF)).2
    iframe Hpks
    unfold replica.pokOk
    icases He with ⟨%rs, Hrs, -, Hf⟩
    iexists rs
    iframe Hrs Hf
    ileft; iexact Ha
  · -- a new entry
    have hnone : pk !! d.pok'.OpNum' = none := by simpa using Hif
    wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %m Hm
    wp_apply wp_mapInsert $$ Hpk as Hpk
    wp_join_done
    iexists _
    iframe Hpk Hr r pok
    iapply (BI.BigSepM.bigSepM_insert hnone).2
    iframe Hpks
    unfold replica.pokOk
    iexists ∅
    iframe Hm
    isplitl []
    · ileft; iexact Ha
    split
    · iapply (BI.BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
    · itrivial
  wp_apply (replica.wp_onPrepareOK H rp γ r tcp src d.pok') $$ [-HΦ] as Hown
  · iframe Hpf
    unfold replica.ownR
    iexists v
    iframe Hr
    unfold replica.repInv
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk', sv, dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  unfold replica.ownR replica.repInv
  iapply HΦ $$ Hown

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
