/-
**The writers' puts through the cluster's clients** (W4d of `notes/watch-cut-plan.md`,
2026-10-22; over etcd's KV state since 2026-10-26, D45/D48). Lean-first (no Rocq counterpart).

* `memberPut γk x`: a member as a writer's put sees it: etcd's KV registered at its bridge
  (`kvRegsAt`), its store's empty log certified (`idxCert_nil`), its KV state variable the
  cluster's (`γk`'s: the updates read only that, `kvOpAu1_names`).
* `client_Put_km`: `cli.Put` through a client of the members `ms` (failover, its writes sent at
  most once, D29) with the writer's update at `γk` (`client_Put_rep`): `nil`, the update's result
  `Q σ` at the state `σ` it met (a log's state: no compaction, revision `1` or more) and the
  reply's revision `σ`'s next; or an error.
* `wsInvH`: the writers' log's lock invariant (watchkv's `wsInv`), its records' `okFactK`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchKV
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A member as a writer's put sees it** (persistent; see the file header). -/
def memberPut (γk : KVNames) (x : client.SrvAt GF) : IProp GF :=
  iprop(client.kvRegsAt x ∗ mvcc.idxCert x.E.γ.idx [] ∗ ⌜x.γr.kv.st = γk.st⌝)

instance memberPut_persistent (γk : KVNames) (x : client.SrvAt GF) :
    Persistent (memberPut (GF := GF) γk x) := by
  unfold memberPut; infer_instance

/-- **The writers' log's lock invariant** (watchkv's `wsInv`, its records' `okFactK`). -/
def wsInvH (w : Loc) (γ : client.KMNames) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Ok" w ↦ sl ∗
    sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗ □ [∗list] p ∈ oks, okFactK γ p)

end defs

section put
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`cli.Put(ctx, key, val)` through a client of the members `ms`** (see the file header). -/
theorem client_Put_km [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF)
    (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map client.SrvAt.addr) V ∗
        client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
        ([∗list] x ∈ ms, memberPut γk x) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu1 γk (.put (client.putKeyOp key val)) Q }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
          ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ σ.compacted = 0 ∧ 1 ≤ σ.rev ∧
            σ.rev + 4 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hms, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  ihave #Hregs : ([∗list] x ∈ ms, client.kvRegsAt x) $$ [Hms]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => memberPut (GF := GF) γk x) fun _ => by
      iintro #H; iunfold memberPut at H; icases H with ⟨#H1, -⟩; iexact H1) $$ Hms
  ihave #HF : ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) $$ [Hms]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => memberPut (GF := GF) γk x) fun _ => by
      iintro #H; iunfold memberPut at H; icases H with ⟨-, #H1, -⟩; iexact H1) $$ Hms
  have hau := client.bigAndL_of_sep ms (kvOpAu1 (GF := GF) γk (.put (client.putKeyOp key val)) Q)
    (fun y : client.SrvAt GF => memberPut γk y)
    (fun y : client.SrvAt GF => kvOpAu1 y.γr.kv (.put (client.putKeyOp key val)) Q)
    (fun y _ => by
      iintro ⟨Hk, #Hm⟩
      iunfold memberPut at Hm
      icases Hm with ⟨-, -, %h⟩
      rw [client.kvOpAu1_names y.γr.kv γk h]
      iexact Hk)
  ihave Hau := hau $$ [Hau Hms]
  · iframe Hau; iframe #
  wp_apply (client.client_Put_rep cl ms V ci cd key val sl Q) $$ [Hau] as %resp %err Hout
  · iframe #; iexact Hau
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iunfold client.putReplied at Hr
    icases Hr with ⟨%hm, %y, %y', %l, %skip, %Hp, -, -, -, -, HQ⟩
    obtain ⟨-, hrev, -, -, -, -, hlen, hb⟩ := Hp
    iexists m, kvStateOf y.log
    iframe Hm HQ
    ipureintro
    refine ⟨?_, kvStateOf_compacted _, ?_, ?_⟩
    · rw [hrev, client.kvStateOf_rev_succ _ hlen]
    · rw [kvStateOf_rev]; omega
    · rw [kvStateOf_rev]; omega
  · iright
    ipureintro; exact Herr

end put

end linkv3p
end EtcdGrove
end Perennial
