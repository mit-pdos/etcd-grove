/-
The proof of `KvRaft/Spec/.../kvraft/Transport__dial.lean`: `net.DialTimeout` (its update from the
address's protocols, `dial_au`), `closeAfter`, `writeAll` of the hello byte (its accessor
`write_acc` of `kvP`, which admits `[helloPeerB]`: no frame yet).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__dial
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.writeAll
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.closeAfter
public import KvRaft.Spec.net.DialTimeout
public import KvRaft.Spec.net.Conn__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions]

/-- The peer hello is a prefix of a peer stream (no frame yet). -/
theorem kvP_hello (F : KvFacts GF) (pid : w64) (cn : Nat) : ⊢ kvP F pid cn [helloPeerB] := by
  unfold kvP kvFull framesOk
  iexists [helloPeerB]
  isplitr
  · ipureintro; exact List.prefix_refl _
  ileft
  iexists []
  isplitr
  · ipureintro; rfl
  iexists []
  isplitr
  · ipureintro; simp [framesBytes]
  iapply BigSepL.bigSepL_nil.2
  iempintro

theorem Transport.dial.wp_proof (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_DialTimeout : net.DialTimeout.spec (GF := GF) (hG := hG))
    (wp_closeAfter : closeAfter.spec (GF := GF) (hG := hG))
    (wp_writeAll : writeAll.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    Transport.dial.spec (GF := GF) (hG := hG) := by
  intro F t γ N id n p pid a et ed
  wp_start as ⟨#Ht, #Hp, #Het, #Hed⟩
  iunfold isTransportCore at Ht
  icases Ht with ⟨%sp, %sc, %γsc, #Hid, #Hnode, #Hstats, #Hs, #Hn, -, -⟩
  iunfold isPeerAddr at Hp
  icases Hp with ⟨#Hpid, #Hpa, #Hap, %Hok⟩
  try wp_auto
  wp_apply wp_add sp (W64 20) (by decide) (by decide) $$ [$Hpkg $Hs]
  try wp_auto
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply wp_DialTimeout go!"tcp" net.tcpNet_tcp a _ et ed iprop(True)
      (fun cn => iprop(connEnd cn false (kvP F pid) (kvQ F pid) [] [] ∗ connFresh cn false)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hce, -⟩⟩ | ⟨-, %x, %e, -, #Herr, -⟩)
  · (try iframe HnetPk)
    iframe %Hok
    iframe Het Hed
    isplit
    · itrivial
    iapply dial_au a (kvP F pid) (kvQ F pid) $$ Hap
  rotate_left
  · -- the dial failed
    icases net.opErr_netErr _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne
    try wp_auto
    wp_apply wp_add sp (W64 21) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  subst Herr
  unfold connEnd
  icases Hce with ⟨HW, HR⟩
  ihave #Hci := sendTok_connIs _ _ _ _ $$ HW
  ihave #Hca := cAcc_of_connIs cn false $$ Hci
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%tc, %la, %ra, %Hct, #Hcat⟩
  subst Hct
  try wp_auto
  wp_apply wp_closeAfter _ cn false a _ iprop(True) $$ [] as %disarm #Hdis
  · iframe Hc
    isplitl []
    · itrivial
    imodintro
    iintro -
    iunfold cAcc at Hca
    iexact Hca
  try wp_auto
  wp_apply wp_slice_literal (V := w8) [W8 80]
  isplitr
  · ipureintro; rfl
  iintro %hp ⟨Hh, -⟩
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #(W8 80))] = 1 from rfl]
  try wp_auto
  ihave HW := writeP_init cn false (kvP F pid) [] $$ HW
  ihave #Hpr : □ kvP F pid cn ([] ++ [helloPeerB]) $$ []
  · rw [List.nil_append]; imodintro; iapply kvP_hello
  ihave #Hacc := write_acc cn false (kvP F pid) [] [helloPeerB] $$ Hpr
  wp_apply wp_writeAll _ cn false a _ [W8 80] (DFrac.own 1) ed
      (fun w res => writeP cn false (kvP F pid) [] w res) $$ [Hh HW]
    as %ok1 ⟨%w1, %res1, HW, -, %Hw1⟩
  · iframe Hc Hh Hed HW
    iunfold helloPeerB at Hacc
    iexact Hacc
  try wp_auto
  wp_bind (App (Val #disarm) (Val #()))
  iapply Hdis
  iintro %inTime -
  cases inTime <;> cases ok1
  all_goals try wp_auto
  -- (the three failures: the connection closed, `nil`)
  any_goals
    wp_apply wp_add sp (W64 21) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    wp_apply wp_Close tc cn false a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hcat
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  -- written in time
  obtain ⟨-, Hw⟩ := Hw1
  have Hw := Hw rfl
  subst Hw
  iapply HΦ
  iright
  iexists cn
  iframe Hc HR Hci
  unfold writeP
  simp only [List.nil_append]
  unfold helloPeerB
  iexact HW

end proof

end kvraft
end EtcdGrove
end Perennial
