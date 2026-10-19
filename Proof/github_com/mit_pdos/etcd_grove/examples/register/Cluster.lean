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
  forwarded read-index request (unstamped), its entries owned, a `MsgReadIndex`'s read
  credit and (2026-10-13) a `MsgTimeoutNow`'s tick credit). The transport checks in Go what
  it can (`Deliverable`: the type, a sender other than the target, a term (none on a
  forwarded read-index request), a nil context but on a heartbeat, its response or a vote
  request, and (2026-10-13) no entries on a `MsgTimeoutNow`), routes by `To` (so the target
  is the receiver), copies the entries and passes each message's read credit on
  (2026-10-13); raft sends nothing it drops but a follower's forwarded transfer request
  (stamped, which `Node.Step` does not take). Since 2026-10-13 a vote request's context
  may be the leader-transfer marker (a transfer's campaign; `Node.Step` takes it).
  Raft v3.7 (2026-10-16, stage R6b): the messages are `*pb.Message`s a `Ready` hands out owned
  (D8, `readyDq`: whole, but a response at half), and `Node.Step` takes the pointer for good
  (Q3, `msgIn`): `Deliverable` is over the message's state `st : MsgSt`, `stepP_deliverable`
  takes the message at `1` with its entries slice fresh (`deliver`'s copy). A response
  (`MsgAppResp`, `MsgVoteResp`) comes at half, so the in-process transport cannot write its
  `Entries` nor hand it to `Step`: a gap between D8 and the register's transport, left as a
  `sorry` in `deliver.wp_proof` (see there).
* **The transfer budget** (`isTransfers`, 2026-10-13): a `MsgTimeoutNow` makes its target
  campaign at once, one term past its own or the message's, so `Node.Step` takes it with a
  tick credit of the term budget (`netP`). The transport holds `timeouts` of them in a
  mutex-protected counter (`transfers`, `transfersInv`: one credit per count) and passes a
  `MsgTimeoutNow` on only while one is left (`transfers.take`), as `tick` bounds a node's
  ticks; `Main` allocates them with the budget.
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

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

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
read-index requests and (2026-10-13) `MsgTimeoutNow`: replication, leader election and the
read-index responses (`RawNode.Step`'s `netStepTypes` but `MsgReadIndex` and the leader
transfer and local types). -/
def regNetTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp]

/-- What `deliverable` checks of a message holding `st` (see the file header; raft v3.7, stage
R6b: over the message's state, `m.Entries != nil` and `m.Context == nil` read as its entries and
context bytes being empty, `msgPtsC_fields_acc`). -/
def Deliverable [FfiSyntax] (st : MsgSt) : Prop :=
  (st.msg.Type' = MsgProp ∨ (st.msg.Type' = MsgReadIndex ∧ st.msg.Term' = W64 0) ∨
    (st.msg.Type' ∈ regNetTypes ∧ st.msg.Term' ≠ W64 0) ∨
    (st.msg.Type' = MsgTimeoutNow ∧ st.msg.Term' ≠ W64 0 ∧ st.ents = [])) ∧
  st.msg.From' ≠ W64 0 ∧ st.msg.From' ≠ st.msg.To' ∧
  (st.ctx = [] ∨ st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp ∨
    st.msg.Type' = MsgVote)

/-- A node's ticks (`ticks`). -/
def ticksN : Nat := 2 ^ 20

/-- The `MsgTimeoutNow` the transport passes on (`timeouts`, 2026-10-13). -/
def timeoutsN : Nat := 2 ^ 20

/-- The register's `transfers` struct. -/
abbrev RTransfers [FfiSyntax] := github_com.mit_pdos.etcd_grove.examples.register.transfers

abbrev rTransfersTy [FfiSyntax] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.register.transfers.ty

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

/-- The transfer budget's lock invariant (see the file header): the number of `MsgTimeoutNow`s
the transport may still pass on (D19b, 2026-10-18: until then with one tick credit each; `take`
takes the credit, a time receipt, from a Go step of its own). -/
def transfersInv (_bud : BudgetNames) (tr : Loc) : IProp GF :=
  iprop(∃ n : w64, tr.[RTransfers, go!"left"] ↦ n)

/-- The transport's transfer budget `tr` (persistent). -/
def isTransfers (bud : BudgetNames) (tr : Loc) : IProp GF :=
  sync.isMutex (tr.[RTransfers, go!"mu"]) (transfersInv bud tr)

instance isTransfers_persistent (bud : BudgetNames) (tr : Loc) :
    Persistent (isTransfers (GF := GF) bud tr) := by
  unfold isTransfers; infer_instance

/-- A deliverable message is a `MsgTimeoutNow` or of a type the protocol describes, not a
snapshot. -/
theorem deliverable_mtype (st : MsgSt) (Hd : Deliverable st) :
    st.msg.Type' = MsgTimeoutNow ∨ ∃ ty, mtypeOf st.msg.Type' = some ty ∧ ty ≠ .snap := by
  obtain ⟨Hty, -⟩ := Hd
  unfold regNetTypes at Hty
  rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact .inr ⟨_, by rw [h]; exact mtypeOf_MsgProp, by decide⟩
  · exact .inr ⟨_, by rw [h]; exact mtypeOf_MsgReadIndex, by decide⟩
  · right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> rw [h]
    · exact ⟨_, mtypeOf_MsgApp, by decide⟩
    · exact ⟨_, mtypeOf_MsgAppResp, by decide⟩
    · exact ⟨_, mtypeOf_MsgVote, by decide⟩
    · exact ⟨_, mtypeOf_MsgVoteResp, by decide⟩
    · exact ⟨_, mtypeOf_MsgHeartbeat, by decide⟩
    · exact ⟨_, mtypeOf_MsgHeartbeatResp, by decide⟩
    · exact ⟨.readIndexResp, rfl, by decide⟩
  · exact .inl h

/-- What `Ready` says of a deliverable message holding `st`: its abstraction sent (none for a
`MsgTimeoutNow`, which carries nothing). -/
theorem raftMsg_deliverable (γ : RaftNames) (st : MsgSt) (Hd : Deliverable st) :
    isRaftMsg (GF := GF) γ st ⊢
      □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ isMessage γ (absMsg ty st.msg st.ents st.ctx)) := by
  rcases deliverable_mtype st Hd with Htn | ⟨ty0, Hty0, Hns⟩
  · -- a `MsgTimeoutNow`: no protocol message
    iintro -
    imodintro
    iintro %ty %Hty'
    rw [Htn] at Hty'
    cases Hty'
  iintro Hm
  unfold isRaftMsg
  icases Hm with ⟨-, -, %a, %Habs, #Hl⟩
  unfold msgAbs at Habs
  rcases Habs with ⟨Hn, -⟩ | ⟨ty, Hty, -, rfl⟩ | ⟨sv, Hsn, -, -⟩
  · rw [Hty0] at Hn; cases Hn
  · ihave #Hmsg : isMessage (GF := GF) γ (absMsg ty st.msg st.ents st.ctx) $$ [Hl]
    · simp only [Option.toList_some]
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).1 $$ Hl
    imodintro
    iintro %ty' %Hty'
    rw [Hty] at Hty'
    cases Hty'
    iexact Hmsg
  · rw [Hty0] at Hsn; cases Hsn; exact absurd rfl Hns

/-- (2026-10-17) No pre-vote request is delivered (`regNetTypes`). -/
theorem deliverable_not_prevote (st : MsgSt) (Hd : Deliverable st) : st.msg.Type' ≠ MsgPreVote := by
  obtain ⟨Hty, -⟩ := Hd
  rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; simp [MsgProp, MsgPreVote]
  · rw [h]; simp [MsgReadIndex, MsgPreVote]
  · simp only [regNetTypes, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> rw [h] <;>
      simp [MsgPreVote, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
        MsgHeartbeatResp, MsgReadIndexResp]
  · rw [h]; simp [MsgTimeoutNow, MsgPreVote]

/-- A deliverable message other than a proposal, addressed to `id`, is what `RawNode.Step`
takes from the network (`NetMsgOk`). -/
theorem deliverable_netMsgOk (id : w64) (st : MsgSt) (Hd : Deliverable st)
    (Hnp : st.msg.Type' ≠ MsgProp) (Hto : st.msg.To' = id) :
    NetMsgOk id st := by
  obtain ⟨Hty, HF, HFT, -⟩ := Hd
  have HF' : st.msg.From' ≠ id := Hto ▸ HFT
  have Hntl : st.msg.Type' ≠ MsgTransferLeader := by
    rcases Hty with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h Hnp
    · rw [h]; simp [MsgReadIndex, MsgTransferLeader]
    · simp only [regNetTypes, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h <;> rw [h] <;>
        simp [MsgTransferLeader, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
          MsgHeartbeatResp, MsgReadIndexResp]
    · rw [h]; simp [MsgTimeoutNow, MsgTransferLeader]
  show st.msg.Type' ∈ netStepTypes ∧
    (¬ UnstampedType st.msg.Type' → st.msg.To' = id ∧ st.msg.Term' ≠ W64 0 ∧ st.msg.From' ≠ W64 0) ∧
    (UnstampedType st.msg.Type' → st.msg.Term' = W64 0) ∧
    (st.msg.Type' = MsgApp ∨ st.msg.Type' = MsgHeartbeat ∨ st.msg.Type' = MsgHeartbeatResp ∨
       st.msg.Type' = MsgReadIndexResp → st.msg.From' ≠ id) ∧
    (st.msg.Type' = MsgAppResp → st.msg.Reject' = true → st.msg.From' ≠ id) ∧
    (st.msg.Type' = MsgTransferLeader → st.ents = [] ∧ st.ctx = []) ∧
    (st.msg.Type' = MsgPreVote → st.msg.From' ≠ id)
  rcases Hty with h | ⟨Hri, Ht0⟩ | ⟨Hn, Ht⟩ | ⟨Htn, Ht, -⟩
  · exact absurd h Hnp
  · refine ⟨by rw [Hri]; simp [netStepTypes], fun h => absurd (.inl Hri) h, fun _ => Ht0,
      fun _ => HF', fun _ _ => HF', fun h => absurd h Hntl, fun _ => HF'⟩
  · have Hun : ¬ UnstampedType st.msg.Type' := by
      simp only [regNetTypes, List.mem_cons, List.not_mem_nil, or_false] at Hn
      rcases Hn with h | h | h | h | h | h | h <;> rw [h] <;>
        simp [UnstampedType, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat,
          MsgHeartbeatResp, MsgReadIndexResp, MsgReadIndex, MsgTransferLeader, MsgForgetLeader,
          MsgUnreachable, MsgSnapStatus]
    have Hnet : st.msg.Type' ∈ netStepTypes := by
      simp only [regNetTypes, List.mem_cons, List.not_mem_nil, or_false] at Hn
      simp only [netStepTypes, List.mem_cons, List.not_mem_nil, or_false]
      rcases Hn with h | h | h | h | h | h | h <;> simp [h]
    exact ⟨Hnet, fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hun, fun _ => HF', fun _ _ => HF',
      fun h => absurd h Hntl, fun _ => HF'⟩
  · have Hun : ¬ UnstampedType st.msg.Type' := by
      rw [Htn]
      simp [UnstampedType, MsgTimeoutNow, MsgReadIndex, MsgTransferLeader, MsgForgetLeader,
        MsgUnreachable, MsgSnapStatus]
    exact ⟨by rw [Htn]; simp [netStepTypes], fun _ => ⟨Hto, Ht, HF⟩, fun h => absurd h Hun,
      fun _ => HF', fun _ _ => HF', fun h => absurd h Hntl, fun _ => HF'⟩

/-- A deliverable message holding `st` at `l`, owned with its entries slice fresh (the elements
at `1`, the capacity: `deliver`'s copy, `msgPtsC_store_Entries`), with its read credit and its
tick credit (one for a `MsgTimeoutNow`, 2026-10-13), is what `Node.Step` takes (`stepP`), at the
node `id` it is addressed to: a forwarded proposal (`fwdP`, the entries' slots owned) or a
network message (`netP`, the entries frozen). -/
theorem stepP_deliverable (γn : NodeNames) (id : w64) (l : Loc) (st : MsgSt)
    (Hd : Deliverable st) (Hto : st.msg.To' = id) :
    ⊢ □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗
          isMessage (GF := GF) γn.raft (absMsg ty st.msg st.ents st.ctx)) -∗
      termLB γn.bud st.msg.Term' -∗ msgPtsC l (DFrac.own 1) (DFrac.own 1) true st -∗
      rdCred γn.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) -∗
      tickCred γn.bud (if st.msg.Type' = MsgTimeoutNow then 1 else 0) ==∗
      stepP γn id l := by
  iintro #Hmsg #Hlb Hm Hcr Htc
  unfold stepP
  by_cases Hp : st.msg.Type' = MsgProp
  · -- a forwarded proposal: no context
    have Hcn : st.ctx = [] := by
      rcases Hd.2.2.2 with h | h | h | h
      · exact h
      all_goals (rw [Hp] at h; simp [MsgProp, MsgHeartbeat, MsgHeartbeatResp, MsgVote] at h)
    imodintro
    iright
    unfold fwdP
    iexists st
    isplitl [Hm]
    · iapply msgPtsC_cap_any $$ Hm
    isplitr
    · ipureintro; exact Hp
    ihave #H := Hmsg $$ %MsgType.propose %(by rw [Hp]; exact mtypeOf_MsgProp)
    iExactEq H
    rw [Hcn]
  · imod msgPtsC_persist_els $$ Hm with Hm
    imodintro
    ileft
    unfold netP
    iexists st
    isplitl [Hm]
    · iapply msgPtsC_cap_any $$ Hm
    isplitr
    · ipureintro; exact deliverable_netMsgOk id st Hd Hp Hto
    isplitr
    · ipureintro
      refine ⟨fun h => (deliverable_not_prevote st Hd h).elim, fun h => ?_⟩
      exfalso
      rcases deliverable_mtype st Hd with h' | ⟨ty, h', -⟩
      · rw [h] at h'; simp [MsgTransferLeader, MsgTimeoutNow] at h'
      · rw [h] at h'; cases h'
    iframe Hmsg Hlb Hcr Htc

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
