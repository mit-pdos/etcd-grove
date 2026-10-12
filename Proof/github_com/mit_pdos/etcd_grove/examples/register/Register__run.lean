/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__run.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.fits
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.RegStorageInstance

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.run.wp_proof
    (wp_fits : register.fits.spec (GF := GF) (hG := hG))
    (wp_apply : register.Register.apply.spec (GF := GF) (hG := hG))
    (wp_node_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_node_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_MemoryStorage_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG)) :
    Register.run.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st send
  wp_start as ⟨#Hrep, Hdrv, Hrun, #Hsend⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_node_Ready γp.node id n $$ [$HisNode] as %ch #Hch
  ihave IH : iprop(∃ (ds : List raftpb.Entry) (rdv : Ready),
      "Hrd" ∷ rd_ptr ↦ rdv ∗ "Hdrv" ∷ nodeDriver γp.node id n ds ∗ "Hrun" ∷ runOwn γr r ds)
    $$ [rd Hdrv Hrun]
  · iexists [], _
    iframe
  wp_for IH
  wp_apply node_ready_receive γp.node id n ch ds $$ [$Hch $Hdrv] as %rdv' ⟨%ce, %es, %msgs, Hdata, Hbusy⟩
  unfold readyData
  icases Hdata with ⟨#Hce, #Hcomm, #Hes, Happ, Hms, Hmsok, %Hsnap⟩
  wp_apply wp_fits rdv'.Entries' es DFrac.discard $$ [$Hes] as %b ⟨-, %Hfit⟩
  cases b
  · -- a log past `maxIndex`: the replica stops
    wp_auto
    ihave Hspin : iprop(True) $$ []
    · itrivial
    wp_for Hspin
    wp_for_post
    iframe
  -- `r.storage.Append(rd.Entries)`, the promoted `MemoryStorage.Append`
  icases Hsrec with ⟨%ms, %γs, #Hrec⟩
  ihave #Hrec' := Hrec
  iunfold regStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  ihave Htok : iprop(∃ σ, ⌜es = []⌝ ∨ memAppendTok ms γs σ es) $$ [Happ]
  · unfold appendRight
    rw [Hstor]
    icases Happ with (%Hnil | ⟨%σ, Htok⟩)
    · iexists memStorEmpty; ileft; ipureintro; exact Hnil
    ihave Htok : regAppendTok (regStorIface st) σ es $$ Htok
    unfold regAppendTok
    icases Htok with ⟨%s', %ms', %γs', %Hst, #Hrec2, Htok⟩
    have := regStorIface_inj (GF := GF) _ _ Hst
    subst this
    icases regStorRec_agree st ms ms' γs γs' $$ Hrec Hrec2 with ⟨%H1, %H2⟩
    subst H1 H2
    iexists σ; iright; iexact Htok
  icases Htok with ⟨%σ, Htok⟩
  wp_auto
  wp_apply wp_MemoryStorage_Append ms γs σ es rdv'.Entries' DFrac.discard (Hfit rfl)
    $$ [$Hraftinit $Htok $Hes] as ⟨Hdone, -⟩
  ihave Hrcpt : appendReceipt γp.node.stor es $$ [Hdone]
  · unfold appendReceipt
    rw [Hstor]
    icases Hdone with (%Hnil | Hd)
    · ileft; ipureintro; exact Hnil
    iright; iexists σ
    ihave H : regAppendedTok (regStorIface st) σ es $$ [Hd]
    · unfold regAppendedTok
      iexists st, ms, γs
      iframe Hrec Hd
      ipureintro; rfl
    iexact H
  wp_bind (App (Val #send) _)
  iunfold sendSpec at Hsend
  iapply Hsend $$ [Hms Hmsok]
  · iframe
  iintro !> -
  wp_auto
  -- applying the committed entries, in order
  ihave %Hcelen := ownSlice_len $$ Hce
  ihave IHa : iprop(∃ (k : w64) (ev : raftpb.Entry),
      "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "Hrun" ∷ runOwn γr r (ds ++ ce.take (sint.nat k)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int)⌝) $$ [i e Hrun]
  · iexists W64 0, _
    iframe i e
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
    iframe Hrun
    ipureintro; constructor <;> word
  wp_for IHa
  wp_if_destruct
  · have Hlt : sint.nat k < ce.length := by word
    obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat k]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv'.CommittedEntries'.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index rdv'.CommittedEntries' (sint.Z k) _ DFrac.discard en Hk.1 $$ [Hce] as -
    · iframe Hce; ipureintro; exact Hen
    have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
      rw [List.take_add_one, Hen]; rfl
    ihave #Hc1 := isCommitted_mono γp.node.raft (ds ++ ce.take (sint.nat k) ++ [en]) (ds ++ ce)
      (by rw [List.append_assoc, ← Htk]; exact List.prefix_append_right_inj _ |>.mpr (List.take_prefix _ _))
      $$ Hcomm
    rw [Hraft]
    wp_apply wp_apply γr γp r id n st (ds ++ ce.take (sint.nat k)) en $$ [$Hpkg $Hrep $Hrun $Hc1] as Hrun
    wp_for_post
    iframe
    iexists k + W64 1, en
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, Htk, List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Hfull : sint.nat k = ce.length := by word
    rw [Hfull, List.take_of_length_le (by omega)]
    wp_apply wp_node_Advance γp.node id n (ds ++ ce) es $$ [$Hraftinit $Hbusy $Hrcpt] as Hdrv
    wp_for_post
    iframe
    iexists ds ++ ce, rdv'
    iframe

end proof

end register
end EtcdGrove
end Perennial
