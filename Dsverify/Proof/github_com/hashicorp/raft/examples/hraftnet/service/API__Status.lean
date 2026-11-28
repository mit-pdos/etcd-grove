/-
The proof of `service.API.Status` (kit change 5: `LeaderWithID` on a goroutine of its own, which has
the thread token its read lock borrows).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Status
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.waitFuture
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__State
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeaderWithID
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__GetConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.configurationsFuture__Configuration
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QTok
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.service.API.Status.wp_proof
    (wp_State : github_com.hashicorp.raft.Raft.State.spec (GF := GF) (hG := hG))
    (wp_LeaderWithID : github_com.hashicorp.raft.Raft.LeaderWithID.spec (GF := GF) (hG := hG))
    (wp_GetConfiguration : github_com.hashicorp.raft.Raft.GetConfiguration.spec (GF := GF) (hG := hG))
    (wp_waitFuture : github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.spec (GF := GF) (hG := hG))
    (wp_dErr : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (wp_Configuration : github_com.hashicorp.raft.configurationsFuture.Configuration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.API.Status.spec (GF := GF) (hG := hG) := by
  intro a args reply γ rc i fc alb rep0
  wp_start as ⟨#Hapi, Hrep⟩
  ihave #Hraft : (isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft) $$ []
  · iPkgInit
  iunfold isAPI at Hapi
  icases Hapi with ⟨%r, %fsm, %enq, %wt, #Hr, #Hfsm, #Henq, #Hwt, #Hisr, %Hresp, #Hst, #Hmu⟩
  wp_auto
  wp_apply (wp_State r γ rc i) $$ [$Hraft $Hisr] as %st -
  try wp_auto
  wp_apply (chan.wp_make2 (V := ServerID) (W64 1)) as %ich %γi ⟨#Hich, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) _ ich γi (by simp) $$ Hich Hown with #Hbag
  try wp_auto
  ipersist a
  ipersist idCh
  wp_bind (Fork _)
  iapply (wp_fork_rtok _ _) $$ []
  · inext
    iintro %tid Htok
    try wp_auto
    wp_apply (wp_LeaderWithID r γ rc i tid) $$ [$Hraft $Hisr $Htok] as %ad %id Htok
    try wp_auto
    wp_apply (wp_bag_send γi ich id (fun _ => iprop(True))) $$ [$Hbag]
    try wp_auto
    iframe Htok
  inext
  try wp_auto
  wp_apply (wp_bag_receive γi ich (fun _ => iprop(True))) $$ [$Hbag] as %lid -
  try wp_auto
  wp_apply (wp_GetConfiguration r γ rc i) $$ [$Hraft $Hisr] as %fi ⟨%f, %cf, %hfi, Hcf, #Hcfg, Hw⟩
  subst hfi
  try wp_auto
  wp_apply (wp_waitFuture ⟨_, #f⟩ _ (fun _ => iprop(True)) wt
    (snapFut.wp_cf_Error wp_dErr f (fun _ => iprop(True)))) $$ [$Hpkg $Hw] as %err %ok Hok
  icases Hok with (%Hok | ⟨%Hok, -⟩)
  · subst Hok
    wp_auto
    iapply HΦ
    iexists _
    iframe
  subst Hok
  rcases err with ei | _
  · wp_auto
    iapply HΦ
    iexists _
    iframe
  wp_auto
  wp_apply (wp_Configuration f cf (DFrac.own 1)) $$ [$Hraft $Hcf] as Hcf
  iunfold cfgOpt at Hcfg
  icases Hcfg with ⟨%ss, #Hss, -⟩
  try wp_auto
  ihave %Hsllen := ownSlice_len $$ Hss
  ihave HI : (∃ k : Nat, "Hctr" ∷ i_ptr ↦ W64 k ∗
      "Hrep" ∷ (∃ rep : StatusReply, reply ↦ rep) ∗
      "srv" ∷ (∃ v : Server, srv_ptr ↦ v) ∗
      "%Hk" ∷ ⌜k ≤ ss.length⌝ : IProp GF) $$ [i Hrep srv]
  · iexists 0; iframe
    isplitl [Hrep]
    · iexists _; iexact Hrep
    isplitl [srv]
    · iexists _; iexact srv
    ipureintro; omega
  wp_for HI
  split
  · rename_i Hc
    icases srv with ⟨%sv0, srv⟩
    icases Hrep with ⟨%rp, Hrep⟩
    have hk : k < ss.length := by simp only [decide_eq_true_eq] at Hc; word
    list_elem ss k as sv
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index cf.latest'.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] with -
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsv_lookup
    have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (k + 1)
      rw [hctr]
      iframe
      isplitl [Hrep]
      · iexists _; iexact Hrep
      isplitl [srv]
      · iexists _; iframe
      ipureintro; omega
    · wp_for_post
      iframe
      iexists (k + 1)
      rw [hctr]
      iframe
      isplitl [Hrep]
      · iexists _; iexact Hrep
      isplitl [srv]
      · iexists _; iframe
      ipureintro; omega
  wp_auto
  iapply HΦ
  iexact Hrep

end proof

end Perennial
