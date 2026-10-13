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
  `Node.Step` takes more (`stepP`: the type, the target, a nonzero term and sender but for a
  forwarded read-index request (unstamped), a context that is not the leader-transfer
  marker, its entries owned, and a `MsgReadIndex`'s read credit). The transport checks in
  Go what it can (`Deliverable`: the type, a sender other than the target, a term (none on
  a forwarded read-index request), a nil context but on a heartbeat or its response),
  routes by `To` (so the target is the receiver), copies the entries and passes each
  message's read credit on (2026-10-13); raft sends nothing it drops. A heartbeat's (or
  its response's) context is a read-index position, eight bytes (`isMessage`), so not the
  marker (`hb_ctx_ok`).
* **The peers** (`peerOk`): the node a peer table maps an id to is that id's, of the
  cluster's raft ghost state and term budget (persistent).
* **The clients** (`clientInv`): the client's half of the register's value, and half of a
  ghost flag (`γf`, "A's `Put` is done") whose other half client A holds; once the flag is
  set the value is `"hello"`. A's `Put` sets both at its linearization point, and gives the
  flag's half (now `true`) to B through the channel; B's `Get` reads the value with it.
  B's `Read` after it (2026-10-13) needs only a read credit and the empty history's lower
  bound; its value is not checked (its spec bounds the history, not the value).
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

/-- The message types `deliverable` delivers, of a term, besides the forwarded proposals and
read-index requests: replication, leader election and the read-index responses
(`RawNode.Step`'s `netStepTypes` but `MsgReadIndex`). -/
def regNetTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp]

/-- What `deliverable` checks of a message (see the file header). -/
def Deliverable [FfiSyntax] (m : raftpb.Message) : Prop :=
  (m.Type' = MsgProp ∨ (m.Type' = MsgReadIndex ∧ m.Term' = W64 0) ∨
    (m.Type' ∈ regNetTypes ∧ m.Term' ≠ W64 0)) ∧
  m.From' ≠ W64 0 ∧ m.From' ≠ m.To' ∧
  (m.Context' = slice.nil ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgHeartbeatResp)

/-- A read-index position is not the leader-transfer marker. -/
theorem u64Le_ne_campaignTransfer [FfiSyntax] (q : w64) : u64Le q ≠ campaignTransfer := by
  intro h
  have := congrArg List.length h
  rw [u64Le_length] at this
  simp [campaignTransfer] at this

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
  rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨_, by rw [h]; exact mtypeOf_MsgProp, by decide⟩
  · exact ⟨_, by rw [h]; exact mtypeOf_MsgReadIndex, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> rw [h]
    · exact ⟨_, mtypeOf_MsgApp, by decide⟩
    · exact ⟨_, mtypeOf_MsgAppResp, by decide⟩
    · exact ⟨_, mtypeOf_MsgVote, by decide⟩
    · exact ⟨_, mtypeOf_MsgVoteResp, by decide⟩
    · exact ⟨_, mtypeOf_MsgHeartbeat, by decide⟩
    · exact ⟨_, mtypeOf_MsgHeartbeatResp, by decide⟩
    · exact ⟨.readIndexResp, rfl, by decide⟩

/-- A heartbeat's (or its response's) context is none or a read-index position: not the
leader-transfer marker. -/
theorem hb_ctx_ok (γ : RaftNames) (m : raftpb.Message) (ents : List raftpb.Entry)
    (ctx : List w8) (ty : MsgType) (Hty : ty = .heartbeat ∨ ty = .heartbeatResp) :
    isMessage (GF := GF) γ (absMsg ty m ents ctx) ⊢ ⌜ctx ≠ campaignTransfer⌝ := by
  have Hnil : ([] : List w8) ≠ campaignTransfer := by simp [campaignTransfer]
  rcases Hty with rfl | rfl
  · unfold isMessage
    simp only [absMsg, absMsgFrom]
    iintro ⟨-, -, -, -, (%Hc | ⟨%q, %recs, %Hq, -, -⟩)⟩
    · ipureintro; rw [Hc]; exact Hnil
    · ipureintro; rw [Hq.1]; exact u64Le_ne_campaignTransfer q
  · unfold isMessage
    simp only [absMsg, absMsgFrom]
    iintro (%Hc | ⟨%q, %recs, %Hq, -⟩)
    · ipureintro; rw [Hc]; exact Hnil
    · ipureintro; rw [Hq.1]; exact u64Le_ne_campaignTransfer q

/-- What `Ready` says of a deliverable message: its entries and context, read-only, the
context not the leader-transfer marker (and empty if the slice is nil), and its
abstraction sent. -/
theorem raftMsg_deliverable (γ : RaftNames) (m : raftpb.Message) (Hd : Deliverable m) :
    isRaftMsg (GF := GF) γ m ⊢ ∃ (ty : MsgType) (ents : List raftpb.Entry) (ctx : List w8),
      ⌜mtypeOf m.Type' = some ty ∧ ctx ≠ campaignTransfer ∧ (m.Context' = slice.nil → ctx = [])⌝ ∗
      m.Entries' ↦*□ ents ∗ m.Context' ↦*□ ctx ∗ isMessage γ (absMsg ty m ents ctx) := by
  obtain ⟨ty0, Hty0, Hns⟩ := deliverable_mtype m Hd
  iintro Hm
  unfold isRaftMsg msgAbs
  icases Hm with ⟨%a, (⟨%Hn, -⟩ | ⟨%ty, %ents, %ctx, %H, #He, #Hc⟩ | ⟨%sv, %voters, %H, -⟩), #Hl⟩
  · rw [Hty0] at Hn; cases Hn
  · obtain ⟨H1, -, rfl⟩ := H
    ihave #Hmsg : isMessage (GF := GF) γ (absMsg ty m ents ctx) $$ [Hl]
    · simp only [Option.toList_some]
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).1 $$ Hl
    ihave %Hlc := ownSlice_len _ _ _ $$ Hc
    have Hnil : m.Context' = slice.nil → ctx = [] := by
      intro h
      rw [h] at Hlc
      exact List.eq_nil_of_length_eq_zero Hlc.1
    obtain ⟨-, -, -, Hctx⟩ := Hd
    ihave %Hct : ⌜ctx ≠ campaignTransfer⌝ $$ [Hmsg]
    · rcases Hctx with Hcn | Hhb | Hhb
      · ipureintro; rw [Hnil Hcn]; simp [campaignTransfer]
      · rw [Hhb, mtypeOf_MsgHeartbeat] at H1
        cases H1
        iapply hb_ctx_ok γ m ents ctx .heartbeat (.inl rfl) $$ Hmsg
      · rw [Hhb, mtypeOf_MsgHeartbeatResp] at H1
        cases H1
        iapply hb_ctx_ok γ m ents ctx .heartbeatResp (.inr rfl) $$ Hmsg
    iexists ty, ents, ctx
    iframe He Hc Hmsg
    ipureintro; exact ⟨H1, Hct, Hnil⟩
  · rw [Hty0] at H; cases H.1; exact absurd rfl Hns

/-- ... and with its entries copied (`s'`) and its read credit, what `Node.Step` takes, at
the node `id` it is addressed to (a read-index request only with more than one voter). -/
theorem stepP_deliverable (γn : NodeNames) (id : w64) (m : raftpb.Message) (ty : MsgType)
    (ents : List raftpb.Entry) (ctx : List w8) (s' : GoSlice) (Hd : Deliverable m)
    (Hto : m.To' = id) (Hty : mtypeOf m.Type' = some ty) (Hct : ctx ≠ campaignTransfer)
    (Hnil : m.Context' = slice.nil → ctx = []) (Hcfg : 1 < GMap.size γn.raft.reCfg) :
    ⊢ isMessage (GF := GF) γn.raft (absMsg ty m ents ctx) -∗ m.Context' ↦*□ ctx -∗
      termLB γn.bud m.Term' -∗ s' ↦* ents -∗ ownSliceCap raftpb.Entry s' (DFrac.own 1) -∗
      rdCred γn.raft (if m.Type' = MsgReadIndex then 1 else 0) ==∗
      stepP γn id { m with Entries' := s' } := by
  iintro #Hmsg #Hctx' #Hlb Hs Hcap Hcr
  obtain ⟨Hty', HF, HFT, Hctxc⟩ := Hd
  have Habs : ∀ ty' c', absMsg ty' { m with Entries' := s' } ents c' = absMsg ty' m ents c' :=
    fun _ _ => rfl
  unfold stepP
  rcases Hty' with Hp | ⟨Hri, Ht0⟩ | ⟨Hn, Ht⟩
  · -- a forwarded proposal: no context
    have Hcn : m.Context' = slice.nil := by
      rcases Hctxc with h | h | h
      · exact h
      · rw [Hp] at h; simp [MsgProp, MsgHeartbeat] at h
      · rw [Hp] at h; simp [MsgProp, MsgHeartbeatResp] at h
    have Hc0 := Hnil Hcn
    subst Hc0
    imodintro
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
  · -- a forwarded read-index request, with its credit
    imod ownSlice_persist s' _ _ $$ Hs with #Hs
    imodintro
    ileft
    unfold netP
    isplitr
    · ipureintro
      refine ⟨?_, fun h => absurd Hri h, fun _ => Ht0, fun _ => Hto ▸ HFT, fun _ _ => Hto ▸ HFT⟩
      show m.Type' ∈ netStepTypes
      rw [Hri]; simp [netStepTypes]
    iexists ents, ctx
    iframe Hs Hcap Hctx' Hlb
    isplitr
    · ipureintro; exact ⟨Hct, fun _ => Hcfg⟩
    isplitr
    · imodintro
      iintro %ty' %Hty2
      rw [Habs]
      simp only at Hty2
      rw [Hty] at Hty2
      cases Hty2
      iexact Hmsg
    iexact Hcr
  · imod ownSlice_persist s' _ _ $$ Hs with #Hs
    have Hnri : m.Type' ≠ MsgReadIndex := by
      intro h
      rw [h] at Hn
      simp [regNetTypes, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
        MsgHeartbeatResp, MsgReadIndexResp, MsgReadIndex] at Hn
    have Hnri' : ({ m with Entries' := s' } : raftpb.Message).Type' ≠ MsgReadIndex := Hnri
    have Hnet : m.Type' ∈ netStepTypes := by
      simp only [regNetTypes, List.mem_cons, List.not_mem_nil, or_false] at Hn
      simp only [netStepTypes, List.mem_cons, List.not_mem_nil, or_false]
      rcases Hn with h | h | h | h | h | h | h <;> simp [h]
    imodintro
    ileft
    unfold netP
    isplitr
    · ipureintro
      exact ⟨Hnet, fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hnri, fun _ => Hto ▸ HFT,
        fun _ _ => Hto ▸ HFT⟩
    iexists ents, ctx
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
