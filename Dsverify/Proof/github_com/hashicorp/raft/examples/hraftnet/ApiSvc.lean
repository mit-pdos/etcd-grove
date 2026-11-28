/-
**The service spec of a server's API** (`apiSvc`, notes/dsv-hraft.md, S5): the net/rpc world's spec
of service "API" at a server's address, per method the deposit of a request's encoding with its facts,
whose success answers are the encodings of the API's replies with theirs (`answers`: the error answers
carry nothing). The requests' facts are what the API's method specs ask (`service/API__*.lean`):
* `Apply`: the command's operation token (`opTok γ d n`, gprot's E1), which travels in the deposit;
  the reply is `applyOut` (no effect: the token back; done: the command committed, the frontier past
  it, the FSM's answer);
* `AddVoter`, `AddNonvoter`, `DemoteVoter`, `RemoveServer`: the ID of a protocol server (`γ.srvs`),
  at its address (its ID) for an addition; `LeadershipTransfer`: an empty ID, or a protocol server at
  its address; `Snapshot`, `Status`: nothing. Their replies carry nothing.
* `Read` (S6): no request facts and no reply facts yet; S6 states the reads' (a read's `□ lin`, and
  the answer at the frontier).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiWire
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Facts
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.ApiDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport service github_com.hashicorp.raft github_com.hashicorp.raft.proto
  github_com.hashicorp.raft.gprot

section svc
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An `ApplyReply` as its record. -/
abbrev applyRepOf (r : ApplyReplyV) : ApplyReply := ApplyReply.mk r.status r.found r.v

/-- A request naming a protocol server to add, at its address (`AddVoter`, `AddNonvoter`). -/
def addReqW (γ : GNames) (v : AdminArgsV) : Prop :=
  v.id ∈ γ.srvs ∧ v.addr = v.id ∧ (v.id ≠ [] ∧ v.id.length < 2 ^ 63 ∧ γ.srvs.length < 2 ^ 32)

/-- A request naming a protocol server (`DemoteVoter`, `RemoveServer`). -/
def srvReqW (γ : GNames) (v : AdminArgsV) : Prop :=
  v.id ∈ γ.srvs ∧ (v.id ≠ [] ∧ v.id.length < 2 ^ 63 ∧ γ.srvs.length < 2 ^ 32)

/-- A leadership transfer's request: to the server raft picks (an empty ID), or to a protocol
server at its address. -/
def transferReqW (γ : GNames) (v : AdminArgsV) : IProp GF :=
  iprop(⌜v.id = []⌝ ∨ isSrv γ v.id ∗ ⌜v.addr = v.id⌝)

instance transferReqW_persistent γ v : Persistent (transferReqW (GF := GF) γ v) := by
  unfold transferReqW; infer_instance

/-- An admin request's deposit: an `AdminArgs`'s encoding with the facts `W`, whose success answers
are an `AdminReply`'s. -/
def adminDep (W : AdminArgsV → IProp GF) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    IProp GF :=
  iprop(∃ v : AdminArgsV, ⌜bs = encAdminArgs v⌝ ∗ W v ∗
    answers (fun rep => iprop(∃ r : AdminReplyV, ⌜rep = encAdminReply r⌝)) Φ)

/-- **The service spec of the API of a server** of the protocol `γ` whose FSMs' context is `fc`. -/
def apiSvc (γ : GNames) (fc : FCtx GF) : net.rpc.MethodSpec GF :=
  fun m bs Φ =>
    if m = go!"Apply" then
      iprop(∃ (v : ApplyArgsV) (n : Nat), ⌜bs = encApplyArgs v⌝ ∗ opTok γ v.data n ∗
        answers (fun rep => iprop(∃ r : ApplyReplyV, ⌜rep = encApplyReply r⌝ ∗
          applyOut γ fc v.data n (applyRepOf r))) Φ)
    else if m = go!"Read" then
      iprop(∃ v : ReadArgsV, ⌜bs = encReadArgs v⌝ ∗
        answers (fun rep => iprop(∃ r : ReadReplyV, ⌜rep = encReadReply r⌝)) Φ)
    else if m = go!"AddVoter" then adminDep (fun v => iprop(⌜addReqW γ v⌝)) bs Φ
    else if m = go!"AddNonvoter" then adminDep (fun v => iprop(⌜addReqW γ v⌝)) bs Φ
    else if m = go!"DemoteVoter" then adminDep (fun v => iprop(⌜srvReqW γ v⌝)) bs Φ
    else if m = go!"RemoveServer" then adminDep (fun v => iprop(⌜srvReqW γ v⌝)) bs Φ
    else if m = go!"LeadershipTransfer" then adminDep (transferReqW γ) bs Φ
    else if m = go!"Snapshot" then adminDep (fun _ => iprop(True)) bs Φ
    else if m = go!"Status" then
      iprop(∃ v : AdminArgsV, ⌜bs = encAdminArgs v⌝ ∗
        answers (fun rep => iprop(∃ r : StatusReplyV, ⌜rep = encStatusReply r⌝)) Φ)
    else iprop(False)

/-! ## Its deposits are encodings -/

theorem adminDep_enc (W : AdminArgsV → IProp GF) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    adminDep W bs Φ ⊢ ⌜∃ v, bs = encAdminArgs v⌝ := by
  unfold adminDep
  iintro ⟨%v, %h, -⟩
  ipureintro; exact ⟨v, h⟩

theorem apiSvc_Apply_enc γ fc bs Φ :
    apiSvc (GF := GF) γ fc go!"Apply" bs Φ ⊢ ⌜∃ v, bs = encApplyArgs v⌝ := by
  unfold apiSvc; rw [if_pos rfl]
  iintro ⟨%v, %n, %h, -⟩
  ipureintro; exact ⟨v, h⟩

theorem apiSvc_Read_enc γ fc bs Φ :
    apiSvc (GF := GF) γ fc go!"Read" bs Φ ⊢ ⌜∃ v, bs = encReadArgs v⌝ := by
  unfold apiSvc; rw [if_neg (by decide), if_pos rfl]
  iintro ⟨%v, %h, -⟩
  ipureintro; exact ⟨v, h⟩

theorem apiSvc_Status_enc γ fc bs Φ :
    apiSvc (GF := GF) γ fc go!"Status" bs Φ ⊢ ⌜∃ v, bs = encAdminArgs v⌝ := by
  unfold apiSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  iintro ⟨%v, %h, -⟩
  ipureintro; exact ⟨v, h⟩

/-- An admin method's deposit (`AddVoter` ... `Snapshot`) is an `AdminArgs`'s encoding. -/
theorem apiSvc_admin_enc γ fc (m : GoString)
    (hm : m = go!"AddVoter" ∨ m = go!"AddNonvoter" ∨ m = go!"DemoteVoter" ∨ m = go!"RemoveServer" ∨
      m = go!"LeadershipTransfer" ∨ m = go!"Snapshot") bs Φ :
    apiSvc (GF := GF) γ fc m bs Φ ⊢ ⌜∃ v, bs = encAdminArgs v⌝ := by
  unfold apiSvc
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [↓reduceIte] <;>
    first
    | exact adminDep_enc _ bs Φ
    | (rw [if_neg (by decide)]; exact adminDep_enc _ bs Φ)

end svc

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
