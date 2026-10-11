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
  type, a sender other than the target, a term, an empty context), routes by `To` (so the
  target is the receiver) and copies the entries; raft sends nothing it drops.
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

/-- What `deliverable` checks of a message (see the file header). -/
def Deliverable [FfiSyntax] (m : raftpb.Message) : Prop :=
  (m.Type' = MsgProp ∨ (m.Type' ∈ netStepTypes ∧ m.Term' ≠ W64 0)) ∧
  m.From' ≠ W64 0 ∧ m.From' ≠ m.To' ∧ m.Context'.len = W64 0

/-- A node's ticks (`ticks`). -/
def ticksN : Nat := 2 ^ 20

/-- `"hello"`. -/
def helloB : List w8 := go!"hello"

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
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

end defs

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
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
