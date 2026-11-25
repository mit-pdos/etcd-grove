/- Lean-first (no Rocq counterpart).

# What the clientv3 KV contracts across machines take of the client (`notes/etcd-dist-plan.md` §18.4)

`kvClientAt cl api eps V Γ`: `New`'s client `cl` of the endpoints `eps` (no proxy dial path), its `KV`
field the `*kv` `api`, every endpoint serving a member of the cluster view `Γ` (`membersAt`). The
precondition every interim KV contract (`KV_Put_dist`, `KV_Get_dist`, `KV_Delete_dist`, `KV_Compact_dist`,
`Txn_Commit_dist`) shares; `kvClient_of_new` builds it from `New`'s result.

`putGetInvK γk γf key val`: putget's client invariant (`client.putGetInv`) at KV names, not read names
(`client.putGetInv γ = putGetInvK γ.kv`, `putGetInv_eq_K`): what a deployment's start allocates at the cluster's
view's KV names (`putGetInvK_alloc`), with its put and read updates (`putAu_of_putGetInvK`,
`getAu_of_putGetInvK`, `client.putAu_of_putGetInv`'s and `client.getAu_of_putGetInv`'s proofs at KV names):
the start of a deployment whose configuration the programs refuse has no read names to give.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.PutThenGet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client

section kv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What every KV contract across machines takes of the client** (persistent; see the file header). -/
def kvClientAt [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) :
    IProp GF :=
  iprop(isNewClient cl eps V ∗ clientNoProxy cl ∗
    clientF cl go!"KV" ↦□ interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api ∗
    membersAt (Gg := hG.goose_globalGS) eps Γ)

instance kvClientAt_persistent [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) : Persistent (kvClientAt cl api eps V Γ) := by
  unfold kvClientAt; infer_instance

/-- **`New`'s client of endpoints serving the view, with no proxy dial path, is a KV client of it**:
`isNewClient` names its `KV` field's `*kv`. -/
theorem kvClient_of_new [π : NetProtoGS] (cl : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) :
    isNewClient cl eps V ∗ clientNoProxy cl ∗ membersAt (Gg := hG.goose_globalGS) eps Γ ⊢
      ∃ api : Loc, kvClientAt cl api eps V Γ := by
  iintro ⟨#Hcl, #Hnp, #Hms⟩
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, -, ⟨%api, #Hkvf, -⟩, -⟩
  iexists api
  iunfold kvClientAt
  iframe #

end kv

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **putget's client invariant at KV names** (see the file header). -/
def putGetInvK (γk : KVNames) (γf : GName) (key val : GoString) : IProp GF :=
  inv client.kvClientN iprop(∃ (σ : KVState) (n : Nat), etcdKV γk σ ∗ monoNatAuthOwn γf 1 n ∗
    ⌜client.putGetOk key val σ n⌝)

instance putGetInvK_persistent (γk : KVNames) (γf : GName) (key val : GoString) :
    Persistent (putGetInvK (GF := GF) γk γf key val) := by
  unfold putGetInvK; infer_instance

/-- `client.putGetInv` reads its read names only through their KV names. -/
theorem putGetInv_eq_K (γ : ReadNames) (γf : GName) (key val : GoString) :
    client.putGetInv (GF := GF) γ γf key val = putGetInvK γ.kv γf key val := rfl

/-- **The put's update** (persistent): each firing writes `key ↦ val` and sets the flag; its
result is the flag's lower bound `1`. -/
theorem putAu_of_putGetInvK (γk : KVNames) (γf : GName) (key val : GoString) :
    putGetInvK γk γf key val ⊢
      kvOpAu (GF := GF) γk (.put (putKeyOp key val)) (fun _ => monoNatLbOwn γf 1) := by
  have Hm := client.kvClientN_mask
  iintro #Hinv
  iunfold kvOpAu
  iunfold putGetInvK at Hinv
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, Hσ, Hmn, %Hok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ, n; iframe Hσ Hmn; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro ⟨Hσ, -⟩
    imod Hmask with -
    imod (mono_nat_own_update (GF := GF) (γ := γf) (max n 1) (Nat.le_max_left n 1))
      $$ Hmn with ⟨Hmn, #Hlb⟩
    have Hstep := client.kvOpStep_putKey key val σ Hok.1
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists (kvOpStep (.put (putKeyOp key val)) σ), (max n 1); iframe Hσ Hmn
      ipureintro; exact ⟨Hstep.1, fun _ => Hstep.2⟩
    imodintro
    iintro !>
    iapply monoNatLbOwn_le 1 (Nat.le_max_right n 1) $$ Hlb

/-- **A get's update after the put fired** (persistent): a read update whose result is that the
state's value of `key` is `val`. -/
theorem getAu_of_putGetInvK (γk : KVNames) (γf : GName) (key val : GoString) :
    putGetInvK γk γf key val ∗ monoNatLbOwn γf 1 ⊢
      kvReadAu (GF := GF) γk
        (fun σ => iprop(⌜(mvcc.findKey key σ.kvs).map EtcdKv.value = some val⌝)) := by
  have Hm := client.kvClientN_mask
  iintro ⟨#Hinv, #Hlb⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold putGetInvK at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %n, Hσ, Hmn, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γf 1 n 1 $$ Hmn Hlb
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ, n; iframe Hσ Hmn; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro ⟨Hσ, -⟩
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ, n; iframe Hσ Hmn; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro; exact Hok.2 Hv.2

end inv

end etcd_dist
end EtcdGrove
end Perennial

end
