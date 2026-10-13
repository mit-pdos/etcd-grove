/-
Lean-first (no Rocq counterpart).

# The cluster driver's predicates (2026-10-11)

`examples/register/cluster.go`: `Main` builds a cluster of three replicas over raft's
`Node`, connected in process by `deliver`, each node driven by a `tick` goroutine, and runs
two clients on it.

* **The logger** (`qLogger`): the `quietLogger{}` the nodes' `Config`s carry. Its formatting
  methods return (`quietLogger.{Debugf,Errorf,Infof,Warningf}`), which is raft's
  `isLogger` (`qLogger_isLogger`).
* **The transport** (`deliverable`, `deliver`): `Ready` says of each of its messages only
  that it was legitimately sent (`isRaftMsg`) and of a term within the budget (`termLB`);
  `Node.Step` takes more (`stepP`: the type, the target, a nonzero term and sender, no
  context, its entries owned). The transport checks in Go what it can (`Deliverable`: the
  type, a sender other than the target, a term, a nil context), routes by `To` (so the
  target is the receiver) and copies the entries; raft sends nothing it drops. It does not
  deliver the read-index messages (`regNetTypes`; the register reads through the log), so
  the read credits `Ready` hands out with them (2026-10-13) are dropped with them, and a
  delivered message carries none.
* **The peers** (`peerOk`): the node a peer table maps an id to is that id's, of the
  cluster's raft ghost state and term budget (persistent).
* **The clients** (`clientInv`): the client's half of the register's value, and half of a
  ghost flag (`γf`, "A's `Put` is done") whose other half client A holds; once the flag is
  set the value is `"hello"`. A's `Put` sets both at its linearization point, and gives the
  flag's half (now `true`) to B through the channel; B's `Get` reads the value with it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs
public import Spec.go_etcd_io.raft.v3.RawNode__Step

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The register's `quietLogger` type. -/
abbrev qLoggerTy [FfiSyntax] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.register.quietLogger.ty

/-- `quietLogger{}`. -/
abbrev qLoggerV [FfiSyntax] : github_com.mit_pdos.etcd_grove.examples.register.quietLogger :=
  github_com.mit_pdos.etcd_grove.examples.register.quietLogger.mk

/-- `quietLogger{}` as a `raft.Logger`. -/
def qLogger [FfiSyntax] [GoGlobalContext] : GoInterfaceOk := interface.mk qLoggerTy #qLoggerV

/-- The message types `deliverable` delivers besides proposals: replication and leader
election (`RawNode.Step`'s `netStepTypes` but the read-index ones, since 2026-10-13). -/
def regNetTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp]

/-- What `deliverable` checks of a message (see the file header). -/
def Deliverable [FfiSyntax] (m : raftpb.Message) : Prop :=
  (m.Type' = MsgProp ∨ (m.Type' ∈ regNetTypes ∧ m.Term' ≠ W64 0)) ∧
  m.From' ≠ W64 0 ∧ m.From' ≠ m.To' ∧ m.Context' = slice.nil

/-- A node's ticks (`ticks`). -/
def ticksN : Nat := 2 ^ 20

/-- `"hello"`. -/
abbrev helloB : List w8 := go!"hello"

def clientN : Namespace := nroot.@"register_cluster"

theorem clientN_regMask : (↑clientN : CoPset) ⊆ regMask := by
  unfold regMask
  intro p hp
  have h1 := mask_ndot_ne' nroot "register_cluster" "raft_commit" (by decide) p hp
  have h2 := mask_ndot_ne' nroot "register_cluster" "register" (by decide) p hp
  rw [Std.LawfulSet.mem_diff] at h1 h2 ⊢
  rw [Std.LawfulSet.mem_diff]
  exact ⟨h1, h2.2⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

/-- The node `nd` is node `id` of the cluster's raft ghost state `γ` and term budget `bud`
(persistent). -/
def peerOk (γ : RaftNames) (bud : BudgetNames) (id : w64) (nd : GoInterface) : IProp GF :=
  iprop(∃ (γn : NodeNames) (n : Loc),
    ⌜γn.raft = γ ∧ γn.bud = bud ∧ nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    isNode γn id n)

instance peerOk_persistent (γ : RaftNames) (bud : BudgetNames) (id : w64) (nd : GoInterface) :
    Persistent (peerOk (GF := GF) γ bud id nd) := by
  unfold peerOk; infer_instance

/-- A deliverable message is of a type the protocol describes, not a snapshot. -/
theorem deliverable_mtype (m : raftpb.Message) (Hd : Deliverable m) :
    ∃ ty, mtypeOf m.Type' = some ty ∧ ty ≠ .snap := by
  obtain ⟨Hty, -⟩ := Hd
  unfold regNetTypes at Hty
  rcases Hty with h | ⟨h, -⟩
  · exact ⟨_, by rw [h]; exact mtypeOf_MsgProp, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> rw [h]
    · exact ⟨_, mtypeOf_MsgApp, by decide⟩
    · exact ⟨_, mtypeOf_MsgAppResp, by decide⟩
    · exact ⟨_, mtypeOf_MsgVote, by decide⟩
    · exact ⟨_, mtypeOf_MsgVoteResp, by decide⟩
    · exact ⟨_, mtypeOf_MsgHeartbeat, by decide⟩
    · exact ⟨_, mtypeOf_MsgHeartbeatResp, by decide⟩

/-- What `Ready` says of a deliverable message: its entries, read-only, and its abstraction
sent. -/
theorem raftMsg_deliverable (γ : RaftNames) (m : raftpb.Message) (Hd : Deliverable m) :
    isRaftMsg (GF := GF) γ m ⊢ ∃ (ty : MsgType) (ents : List raftpb.Entry),
      ⌜mtypeOf m.Type' = some ty⌝ ∗ m.Entries' ↦*□ ents ∗ isMessage γ (absMsg ty m ents) := by
  obtain ⟨ty0, Hty0, Hns⟩ := deliverable_mtype m Hd
  iintro Hm
  unfold isRaftMsg msgAbs
  icases Hm with ⟨%a, (⟨%Hn, -⟩ | ⟨%ty, %ents, %ctx, %H, #He, #Hc⟩ | ⟨%sv, %voters, %H, -⟩), #Hl⟩
  · rw [Hty0] at Hn; cases Hn
  · obtain ⟨H1, -, rfl⟩ := H
    -- a deliverable message's `Context` is nil, so the abstraction's is empty
    obtain ⟨-, -, -, Hcnil⟩ := Hd
    ihave %Hlc := ownSlice_len _ _ _ $$ Hc
    have Hc0 : ctx = [] := by
      rw [Hcnil] at Hlc
      exact List.eq_nil_of_length_eq_zero Hlc.1
    subst Hc0
    iexists ty, ents
    iframe He
    isplitr
    · ipureintro; exact H1
    simp only [Option.toList_some]
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).1 $$ Hl
  · rw [Hty0] at H; cases H.1; exact absurd rfl Hns

/-- ... and with its entries copied (`s'`), what `Node.Step` takes, at the node `id` it
is addressed to. -/
theorem stepP_deliverable (γn : NodeNames) (id : w64) (m : raftpb.Message) (ty : MsgType)
    (ents : List raftpb.Entry) (s' : GoSlice) (Hd : Deliverable m) (Hto : m.To' = id)
    (Hty : mtypeOf m.Type' = some ty) :
    ⊢ isMessage (GF := GF) γn.raft (absMsg ty m ents) -∗ termLB γn.bud m.Term' -∗
      s' ↦* ents -∗ ownSliceCap raftpb.Entry s' (DFrac.own 1) ==∗
      stepP γn id { m with Entries' := s' } := by
  iintro #Hmsg #Hlb Hs Hcap
  obtain ⟨Hty', HF, HFT, Hctx⟩ := Hd
  have Habs : ∀ ty', absMsg ty' { m with Entries' := s' } ents = absMsg ty' m ents :=
    fun _ => rfl
  ihave #Hctx' : (m.Context' ↦*□ ([] : List w8)) $$ []
  · rw [Hctx]; iapply ownSlice_nil
  have Hct : ([] : List w8) ≠ campaignTransfer := by simp [campaignTransfer]
  unfold stepP
  rcases Hty' with Hp | ⟨Hn, Ht⟩
  · imodintro
    iright
    unfold fwdP
    isplitr
    · ipureintro; exact Hp
    iexists ents, []
    iframe Hs Hcap Hctx'
    isplitr
    · ipureintro; exact Hct
    rw [Habs]
    rw [Hp] at Hty
    cases Hty
    iexact Hmsg
  · imod ownSlice_persist s' _ _ $$ Hs with #Hs
    -- not a read-index request: no read credit to pass on
    imod rdCred_zero_upd (GF := GF) γn.raft with Hcr
    have Hnri : m.Type' ≠ MsgReadIndex := by
      intro h
      rw [h] at Hn
      simp [regNetTypes, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
        MsgHeartbeatResp, MsgReadIndex] at Hn
    have Hnri' : ({ m with Entries' := s' } : raftpb.Message).Type' ≠ MsgReadIndex := Hnri
    have Hnet : m.Type' ∈ netStepTypes := by
      simp only [regNetTypes, List.mem_cons, List.not_mem_nil, or_false] at Hn
      simp only [netStepTypes, List.mem_cons, List.not_mem_nil, or_false]
      rcases Hn with h | h | h | h | h | h <;> simp [h]
    imodintro
    ileft
    unfold netP
    isplitr
    · ipureintro
      exact ⟨Hnet, fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hnri, fun _ => Hto ▸ HFT,
        fun _ _ => Hto ▸ HFT⟩
    iexists ents, []
    iframe Hs Hcap Hctx' Hlb
    isplitr
    · ipureintro; exact ⟨Hct, fun h => absurd h Hnri'⟩
    isplitr
    · imodintro
      iintro %ty' %Hty2
      rw [Habs]
      simp only at Hty2
      rw [Hty] at Hty2
      cases Hty2
      iexact Hmsg
    rw [if_neg Hnri']
    iexact Hcr

end defs

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
def clientInvBody (γr : RegNames) (γf : GName) : IProp GF :=
  iprop(∃ (x : List w8) (b : Bool), regVal γr x ∗ ghostVar γf (1 : Qp).half b ∗
    ⌜b = true → x = helloB⌝)

def clientInv (γr : RegNames) (γf : GName) : IProp GF := inv clientN (clientInvBody γr γf)

instance clientInv_persistent (γr : RegNames) (γf : GName) :
    Persistent (clientInv (GF := GF) γr γf) := by
  unfold clientInv; infer_instance

instance clientInvBody_timeless (γr : RegNames) (γf : GName) :
    Timeless (clientInvBody (GF := GF) γr γf) := by
  unfold clientInvBody regVal; infer_instance

/-- Client A's `Put("hello")` update: it sets the value and the flag. -/
theorem client_put_au (γr : RegNames) (γf : GName) :
    ⊢ clientInv (GF := GF) γr γf -∗ ghostVar γf (1 : Qp).half false -∗
      AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅
        <{ regVal γr helloB, COMM ghostVar γf (1 : Qp).half true }> := by
  iintro #Hinv Hf
  iauintro
  unfold atomic_acc clientInv
  have Hcm := clientN_regMask
  iinv Hinv with >Hi Hclose
  unfold clientInvBody
  icases Hi with ⟨%x, %b, Hx, Hfi, %Hb⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ regMask \ ↑clientN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hx
  isplit
  · iintro Hx
    imod Hclose2 with -
    imod Hclose $$ [Hx Hfi] with -
    · inext
      iexists x, b
      iframe Hx Hfi
      ipureintro; exact Hb
    imodintro
    iexact Hf
  · iintro Hx
    imod Hclose2 with -
    imod ghostVar_update_halves true γf b false $$ Hfi Hf with ⟨Hfi, Hf⟩
    imod Hclose $$ [Hx Hfi] with -
    · inext
      iexists helloB, true
      iframe Hx Hfi
      ipureintro; intro _; rfl
    imodintro
    iexact Hf

/-- Client B's `Get()` update, after A's `Put`: it returns `"hello"`. -/
theorem client_get_au (γr : RegNames) (γf : GName) :
    ⊢ clientInv (GF := GF) γr γf -∗ ghostVar γf (1 : Qp).half true -∗
      AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅
        <{ regVal γr x, COMM ⌜x = helloB⌝ }> := by
  iintro #Hinv Hf
  iauintro
  unfold atomic_acc clientInv
  have Hcm := clientN_regMask
  iinv Hinv with >Hi Hclose
  unfold clientInvBody
  icases Hi with ⟨%x, %b, Hx, Hfi, %Hb⟩
  ihave %Hbt := ghostVar_agree γf b (1 : Qp).half true (1 : Qp).half $$ Hfi Hf
  subst Hbt
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ regMask \ ↑clientN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hx
  isplit
  · iintro Hx
    imod Hclose2 with -
    imod Hclose $$ [Hx Hfi] with -
    · inext
      iexists x, true
      iframe Hx Hfi
      ipureintro; exact Hb
    imodintro
    iexact Hf
  · iintro Hx
    imod Hclose2 with -
    imod Hclose $$ [Hx Hfi] with -
    · inext
      iexists x, true
      iframe Hx Hfi
      ipureintro; exact Hb
    imodintro
    ipureintro; exact Hb rfl

end client

end EtcdGrove
end Perennial
