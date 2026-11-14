/-
**The restart-only rows in a one-member cluster** (restart S7.3, 2026-11-14; `notes/restart-s7-p2a.md`,
P2-a, approved by etcd-grove-81): `srvRestartRows_single`, `NewServer.specR`'s premise `srvRestartRows`
discharged for a cluster whose voters are the member alone. Raft's API says of every `MsgSnap` a
`Ready` hands out or a node sends (`readyRest_snapTo`, `sentMsg_snapTo`) that it is not to its
sender and is to an id of a committed membership (`snapTo_confAt`); the server's membership is the
boot one at every committed index (`srv_confAt_eq_simple`), here `{id}`. So no `MsgSnap` is ever sent:
row 4 (`rnSnapTermAbove`) and row 1 (`srvWinPend`) hold vacuously. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStart
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section single
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **No `MsgSnap` in a one-member cluster**: a message with raft's `snapTo` from the member `id` of
a server cluster whose voters are `[id]` is no `MsgSnap`. -/
theorem srv_single_noSnap (γ : SrvRaft) (id : w64) (hvs : γ.vs = [id]) (st : MsgSt) :
    letI := srvStor (GF := GF) γ;
    ⊢ srvRaftLogInv (GF := GF) ⟨γ, [], W64 0⟩ -∗ snapTo γ.cl id st ={⊤}=∗
      ⌜st.msg.Type' ≠ MsgSnap⌝ := by
  letI := srvStor (GF := GF) γ
  iintro #Hsrl #Hs
  by_cases Hty : st.msg.Type' = MsgSnap
  rotate_left
  · imodintro; ipureintro; exact Hty
  ihave #Hsrl' := Hsrl
  iunfold srvRaftLogInv at Hsrl'
  icases Hsrl' with ⟨-, #Hco, -⟩
  iunfold srvClusterOk at Hco
  icases Hco with ⟨#Hcl, -, #Hc0, -⟩
  imod (snapTo_confAt γ.cl srvClusterN ⊤ (fun _ _ => CoPset.mem_full) id st 0
    (Membership.simple γ.cfg) Hty) $$ Hcl Hc0 Hs with ⟨%Hne, %k, %m, %l, #Hm, #Hl, %Hkl⟩
  imod (srv_confAt_eq_simple ⟨γ, [], W64 0⟩ l k m Hkl.1 ⊤ (fun _ _ => CoPset.mem_full)
    (fun _ _ => CoPset.mem_full)) $$ [$Hsrl $Hl $Hm] with %Heq
  exfalso
  have Hin := Hkl.2
  rw [Heq] at Hin
  simp only [Membership.ids, Membership.simple, SrvRaft.cfg, hvs] at Hin
  have Hin' : st.msg.To' ∈ GMap.listToSet [id] := by
    simpa [GMap.elem_of_union, GMap.not_elem_of_empty] using Hin
  rw [GMap.elem_of_list_to_set] at Hin'
  simp at Hin'
  exact Hne Hin'

/-- **No `MsgSnap` among a list of messages** with raft's `snapTo` (`srv_single_noSnap`, each). -/
theorem srv_single_noSnaps (γ : SrvRaft) (id : w64) (hvs : γ.vs = [id]) (ms : List QMsg) :
    letI := srvStor (GF := GF) γ;
    ⊢ srvRaftLogInv (GF := GF) ⟨γ, [], W64 0⟩ -∗ ([∗list] q ∈ ms, snapTo γ.cl id q.st) ={⊤}=∗
      ⌜∀ q ∈ ms, q.st.msg.Type' ≠ MsgSnap⌝ := by
  letI := srvStor (GF := GF) γ
  induction ms with
  | nil => iintro - -; imodintro; ipureintro; intro q hq; cases hq
  | cons q ms ih =>
    iintro #Hsrl #Hst
    icases BigSepL.bigSepL_cons.1 $$ Hst with ⟨#Hq, #Hst⟩
    imod (srv_single_noSnap γ id hvs q.st) $$ Hsrl Hq with %Hq1
    imod ih $$ Hsrl Hst with %Hrest
    imodintro; ipureintro
    intro q' hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact Hq1
    · exact Hrest q' hq'

/-- **The restart-only rows in a one-member cluster** (see the file header). -/
theorem srvRestartRows_single (γ : SrvRaft) (id : w64) (A : List EntryModel) (σ : StorContents)
    (hvs : γ.vs = [id]) :
    srvRaftLogInv (GF := GF) ⟨γ, [], W64 0⟩ ⊢ srvRestartRows γ id A σ := by
  iintro #Hsrl
  unfold srvRestartRows
  iintro %s %γr %γn %Hn #Hmid0
  obtain ⟨hnode, hid, -, -, -, hγr⟩ := Hn
  imod token_alloc with ⟨%γwp, Hwp⟩
  imodintro
  isplitr
  · -- row 4: a `Ready`'s messages are no `MsgSnap`s
    unfold rnSnapTermAbove
    iintro !> %rd %L %p %S %r %ce %es %h %Lo %ms %ss H
    rw [hnode, hid] at *
    letI := srvStor (GF := GF) γ
    ihave ⟨H, #Hst⟩ := readyRest_snapTo γ.cl srvClusterN id rd (rnDrvSt γn L p S r) ce es h Lo ms ss
      $$ H
    imod (srv_single_noSnaps γ id hvs ms) $$ Hsrl Hst with %Hno
    imodintro
    iframe H
    ipureintro
    intro q hq hs
    exact absurd hs (Hno q hq)
  · -- row 1: a sent message is no `MsgSnap`
    unfold srvWinPend
    iexists γwp
    iframe Hwp
    iintro !> %rt %n Htok %Hc Hrt %id' %m %st #Hmid Hmo #Hsent
    icombine Hmid Hmid0 gives %Heq
    subst Heq
    rw [hγr] at *
    letI := srvStor (GF := GF) γ
    ihave #Hsnap := sentMsg_snapTo γ.cl srvClusterN id' st $$ Hsent
    imod (srv_single_noSnap γ id' hvs st) $$ Hsrl Hsnap with %Hns
    imodintro
    iframe Hmo Htok
    ipureintro
    intro h; exact absurd h Hns

end single

end EtcdGrove
end Perennial
