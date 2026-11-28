/- Lean-first (no Rocq counterpart).

# What the clientv3 KV contracts across machines take of the client (`notes/etcd-dist-plan.md` §18.4)

`kvClientAt cl api eps V Γ`: `New`'s client `cl` of the endpoints `eps` (no proxy dial path), its `KV`
field the `*kv` `api`, every endpoint serving a member of the cluster view `Γ` (`membersAt`);
`kvClient_of_new` builds it from `New`'s result. With auth off it is a client of the cluster's KV that
sends a write at most once (`isKv_of_kvClientAt`, stage B′): each endpoint's table (`etcdSvc`) registers
etcd's KV methods at the view specs, flagged as never refusing, so the client's specs (`kv.Put.spec`, ...)
apply across machines.

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
public import Proof.go_etcd_io.etcd.client.v3.KVServiceV

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

/-- **Each endpoint's flagged entries are the endpoints'**: a no-refusal registration at each endpoint
of `addrs` is one at `addrs` (`isGrpcRpcsNR`). -/
theorem isGrpcRpcsNR_of_each (name : GoString) (P : GoString → IProp GF)
    (h : ∀ a, P a ⊢ isGrpcRpcNR a name) :
    ∀ addrs : List GoString, ([∗list] a ∈ addrs, P a) ⊢ isGrpcRpcsNR addrs name
  | [] => by iintro -; unfold isGrpcRpcsNR; itrivial
  | [a] => by
    iintro H
    iapply (h a)
    iapply (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ a => P a)).1 $$ H
  | a :: b :: rest => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, Hr⟩
    unfold isGrpcRpcsNR
    isplitl [Ha]
    · iapply (h a) $$ Ha
    · iapply (isGrpcRpcsNR_of_each name P h (b :: rest)) $$ Hr

/-- **What an auth-off member's address gives a client** (persistent): an address serving etcd's table
for a member of an auth-off view registers etcd's KV methods at the view specs (`kvRegsV`), and its
`Put`, `DeleteRange` and `Txn` entries are flagged as never refusing (`etcdKvSvc`). -/
def kvViewAt (a : GoString) (γk : KVNames) : IProp GF :=
  iprop(client.kvRegsV a γk ∗ isGrpcRpcNR a go!"/etcdserverpb.KV/Put" ∗
    isGrpcRpcNR a go!"/etcdserverpb.KV/DeleteRange" ∗ isGrpcRpcNR a go!"/etcdserverpb.KV/Txn")

instance kvViewAt_persistent (a : GoString) (γk : KVNames) : Persistent (kvViewAt (GF := GF) a γk) := by
  unfold kvViewAt; infer_instance

theorem kvViewAt_regs (a : GoString) (γk : KVNames) : kvViewAt (GF := GF) a γk ⊢ client.kvRegsV a γk := by
  unfold kvViewAt; iintro ⟨H, -⟩; iexact H

theorem kvViewAt_put (a : GoString) (γk : KVNames) :
    kvViewAt (GF := GF) a γk ⊢ isGrpcRpcNR a go!"/etcdserverpb.KV/Put" := by
  unfold kvViewAt; iintro ⟨-, H, -⟩; iexact H

theorem kvViewAt_del (a : GoString) (γk : KVNames) :
    kvViewAt (GF := GF) a γk ⊢ isGrpcRpcNR a go!"/etcdserverpb.KV/DeleteRange" := by
  unfold kvViewAt; iintro ⟨-, -, H, -⟩; iexact H

theorem kvViewAt_txn (a : GoString) (γk : KVNames) :
    kvViewAt (GF := GF) a γk ⊢ isGrpcRpcNR a go!"/etcdserverpb.KV/Txn" := by
  unfold kvViewAt; iintro ⟨-, -, -, H⟩; iexact H

theorem kvRegsV_of_addr [π : NetProtoGS] (a : GoString) (Γ : DistView) (mid : w64)
    (hauth : Γ.auth = false) :
    etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid ⊢ client.kvRegsV a Γ.kv := by
  iintro #Ha
  iunfold etcdAddrAt at Ha
  icases Ha with ⟨%σ, #Ha⟩
  unfold client.kvRegsV
  isplitl []
  · iapply (isGrpcRpcMd_of_addr (Req := pbPutRequest) (Rep := pbPutResponse) (σ := σ) a
      go!"/etcdserverpb.KV/Put" (etcdSvc (GF := GF) Γ mid) (client.etcdPutSpecV Γ.kv) true
      (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_put Γ.kv))) $$ Ha
  isplitl []
  · iapply (isGrpcRpcMd_of_addr (Req := pbRangeRequest) (Rep := pbRangeResponse) (σ := σ) a
      go!"/etcdserverpb.KV/Range" (etcdSvc (GF := GF) Γ mid) (client.etcdRangeSpecV Γ.kv) true
      (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_range Γ.kv))) $$ Ha
  isplitl []
  · iapply (isGrpcRpcMd_of_addr (Req := pbDeleteRangeRequest) (Rep := pbDeleteRangeResponse)
      (σ := σ) a go!"/etcdserverpb.KV/DeleteRange" (etcdSvc (GF := GF) Γ mid) (client.etcdDeleteSpecV Γ.kv)
      true (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_delete Γ.kv))) $$ Ha
  isplitl []
  · iapply (isGrpcRpcMd_of_addr (Req := pbTxnRequest) (Rep := pbTxnResponse) (σ := σ) a
      go!"/etcdserverpb.KV/Txn" (etcdSvc (GF := GF) Γ mid) (client.etcdTxnSpecV Γ.kv) true
      (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_txn Γ.kv))) $$ Ha
  · imodintro
    iintro -
    iapply (isGrpcRpcMd_of_addr (Req := pbCompactionRequest) (Rep := pbCompactionResponse)
      (σ := σ) a go!"/etcdserverpb.KV/Compact" (etcdSvc (GF := GF) Γ mid) (client.etcdCompactSpecV Γ.kv)
      true (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_compact Γ.kv))) $$ Ha

theorem kvViewAt_of_addr [π : NetProtoGS] (a : GoString) (Γ : DistView) (mid : w64)
    (hauth : Γ.auth = false) :
    etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid ⊢ kvViewAt a Γ.kv := by
  iintro #Ha
  ihave #Hr := kvRegsV_of_addr a Γ mid hauth $$ Ha
  iunfold etcdAddrAt at Ha
  icases Ha with ⟨%σ, #Ha⟩
  unfold kvViewAt
  isplitl []
  · iexact Hr
  isplitl []
  · iapply (isGrpcRpcNR_of_addr (σ := σ) a go!"/etcdserverpb.KV/Put" (etcdSvc (GF := GF) Γ mid) _
      (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_put Γ.kv)) rfl) $$ Ha
  isplitl []
  · iapply (isGrpcRpcNR_of_addr (σ := σ) a go!"/etcdserverpb.KV/DeleteRange" (etcdSvc (GF := GF) Γ mid) _
      (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_delete Γ.kv)) rfl) $$ Ha
  · iapply (isGrpcRpcNR_of_addr (σ := σ) a go!"/etcdserverpb.KV/Txn" (etcdSvc (GF := GF) Γ mid) _
      (etcdSvc_kv Γ mid _ _ hauth (etcdKvSvc_txn Γ.kv)) rfl) $$ Ha

theorem kvViewAt_of_members [π : NetProtoGS] (Γ : DistView) (hauth : Γ.auth = false) :
    ∀ eps : List GoString, membersAt (Gg := hG.goose_globalGS) eps Γ ⊢ [∗list] a ∈ eps, kvViewAt a Γ.kv
  | [] => by iintro -; iapply BigSepL.bigSepL_nil.2; itrivial
  | a :: eps => by
    iintro H
    iunfold membersAt at H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%mid, Ha⟩, Hr⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iapply (kvViewAt_of_addr a Γ mid hauth) $$ Ha
    · iapply (kvViewAt_of_members Γ hauth eps)
      iunfold membersAt
      iexact Hr

/-- **A KV client of an auth-off view's members is a client of the cluster's KV that sends a write at
most once** (stage B′, 2026-11-28): `kvClientAt`'s `*kv` over the endpoints, each endpoint registering
etcd's KV methods at the view specs, every write method flagged as never refusing at every endpoint. -/
theorem isKv_of_kvClientAt [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF)
    (Γ : DistView) (hauth : Γ.auth = false) :
    kvClientAt cl api eps V Γ ⊢ client.isKv api Γ.kv false := by
  iintro #H
  iunfold kvClientAt at H
  icases H with ⟨#Hcl, -, #Hkf, #Hms⟩
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api', #Hkf', #Hobj⟩, -⟩
  ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hkf Hkf'
  have hapi : api' = api := by
    have h := ((interface_mkOk_inj _ _ _ _).1 Hag).2
    exact (go.intoVal_inj h).symm
  subst hapi
  ihave #Hv := kvViewAt_of_members Γ hauth eps $$ Hms
  unfold client.isKv
  iexists eps
  iframe Hobj
  isplitl []
  · iapply (BigSepL.bigSepL_mono (PROP := IProp GF) (Φ := fun _ a => kvViewAt a Γ.kv)
      (Ψ := fun _ a => client.kvRegsV a Γ.kv) (l := eps) (fun _ => kvViewAt_regs _ _)) $$ Hv
  unfold client.kvDupNR kvWriteNR
  iright
  iright
  isplitl []
  · iapply (isGrpcRpcsNR_of_each _ (fun a => kvViewAt (GF := GF) a Γ.kv)
      (fun a => kvViewAt_put a Γ.kv) eps) $$ Hv
  isplitl []
  · iapply (isGrpcRpcsNR_of_each _ (fun a => kvViewAt (GF := GF) a Γ.kv)
      (fun a => kvViewAt_del a Γ.kv) eps) $$ Hv
  · iapply (isGrpcRpcsNR_of_each _ (fun a => kvViewAt (GF := GF) a Γ.kv)
      (fun a => kvViewAt_txn a Γ.kv) eps) $$ Hv

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
