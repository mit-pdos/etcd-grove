/-
Lean-first (no Rocq counterpart).

The proof of `Apply(cli, input)` (D20 (c)): `NewProph()` gives a prophecy of the `ResolveBool` at
the end (`!out.Err`, the call's outcome), and the commit (`Inv.lean`'s steps) is chosen by its
head before the client is called:

- a put, prophecy `ok`: the client's update is `put_ok_au` (ordinary, fired at most once on the
  one-attempt client, `putAuOk`'s second case); it commits `lintest`'s update at the server's
  apply with output `ok`, and `Put`'s success returns its continuation. An error return
  contradicts the prophecy.
- a put, prophecy error: commit now, the put pending (`put_err_commit`); the client's update is
  `put_pend_au`, whose firing (during the call, after it, or never) is the pending put's late
  effect. One model step covers both a failed put the server applied and one it did not: the
  output step adds the pending put, the late effect is in the closed set. A success return
  contradicts the prophecy.
- a get, prophecy error: commit now with `Err` (`get_err_commit`); `Get` without an update. A
  success return (stepped through the reply) contradicts the prophecy.
- **a get, prophecy `ok`: `sorry`** (the only one). The client's `Get` spec takes a *persistent*
  read update (`kvReadAu`), which the server fires at every committed log from the read index's
  deposit on, and returns `□ Q` of the one log the reply was read at. `lintest`'s update is
  one-shot and must commit at the state whose value the call returns; at a firing, a one-bit
  prophecy cannot tell whether that firing's state is the reply's (writes may commit between
  the deposit and the read). What would close it: a prophecy identifying the reply (e.g. a second
  `ResolveU64` of the reply's header revision, which is the state's `rev`: a Go change to
  `Apply`), or a `Get` spec firing an ordinary update once at the state the reply is read from.
  See `notes/STATUS.md` (D20).

The client's calls go through `New`'s `KV` field (`client_Put_once`, `client_Get_plain`, as
`ClientPutGet.lean` does), the `kvOnce` of `clientKVOnce` matched with `isNewClient`'s `*kv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Apply
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]


/-- `cli.Put(ctx, key, val)` by `New`'s client configured for one attempt, with an update fired at
most once (`client_put_end_to_end` through the `KV` field): `nil` and the update's result at the
state it fired at; or an error. -/
theorem zero_val_Output :
    (zero_val github_com.mit_pdos.etcd_grove.examples.linkv.Output) = okOut := rfl

theorem client_Put_once [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl ep V ∗
        clientKVOnce cl ep ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu1 γr.kv (.put (putOp key val)) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ σ, Q σ) ∨ ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hrpc, #Hctx, #Hce, #Hopts, Hau, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  iunfold clientKVOnce at Hone
  icases Hone with ⟨%api', #Hkvf', #Honce⟩
  icombine Hkvf Hkvf' gives %Heq
  have Heq' : api = api' := by
    unfold interface.mkOk at Heq
    simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    exact go.intoVal_inj Heq
  subst Heq'
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_put_end_to_end api ep E γr cid mid ci cd key val sl Q F) $$ [Hau]
    as %resp %err Hout
  · iframe #
    iunfold client.putAuOk
    iright
    iframe Hau
    iexact Honce
  iapply HΦ
  icases Hout with (⟨%Herr, %m, -, Hm⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iunfold client.putReplied at Hm
    icases Hm with ⟨%hm, %x, %x', %l, %skip, -, -, -, -, -, HQ⟩
    iexists _
    iexact HQ
  · iright
    ipureintro; exact Herr

/-- `cli.Get(ctx, key)` by `New`'s client, with no update: `nil` and the reply; or an error. -/
theorem client_Get_plain [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl ep V ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Range" (client.etcdRangeSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr (W64 0) ∗
        mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc, #Hctx, #Hce, #Hopts, #Hc, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_get_end_to_end api ep E γr (W64 0) cid mid ci cd key sl
      (fun _ => iprop(True)) F) $$ [] as %resp %err Hout
  · iframe #
    ileft; ipureintro; rfl
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, -⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iexact Hm
  · iright
    ipureintro; exact Herr

theorem Apply.wp_proof : Apply.spec (GF := GF) (hG := hG) := by
  intro _ γ cl ep V E γr cid mid hAs
  iintro #Hpkg #Pcli #Hcl #Hone #Hput #Hrange #Hinv
  iintro %i
  imodintro
  iintro %Φ %Hin HAU
  obtain ⟨x, rfl, Hgen⟩ := Hin
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_NewProph_typed (τ := Bool) github_com.goose_lang.primitive.wp_NewProph) as %p %xs Hp
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  imod monoNatLbOwn_0 (GF := GF) γr.committed with #Hc0
  ihave #Hc0' : committedAtLeast (GF := GF) γr (W64 0) $$ []
  · iunfold committedAtLeast
    iExactEq Hc0; rfl
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  cases hP : x.Put'
  · wp_pures
    by_cases Hok : xs.head? = some true
    · -- the prophecy says `ok`: no linearization point from the client's `Get` spec (see the
      -- file header and `notes/STATUS.md`, D20)
      sorry
    · -- the prophecy says error: commit now
      iapply fupd_wp
      imod (get_err_commit γ γr.kv x hP Φ) $$ [HAU] with HΦ
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      wp_auto
      wp_apply (client_Get_plain cl ep V E γr cid mid context.backgroundCtxVal cd x.Key' slice.nil
          []) $$ [] as %resp %err Hout
      · iframe #
      icases Hout with (⟨%Herr, %m, #Hm⟩ | %Herr)
      · subst Herr
        iunfold rangeRespMsg at Hm
        icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
        wp_auto
        iunfold txn.kvsIs at Hkvs
        icases Hkvs with ⟨%Hlen, #Hall⟩
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        wp_if_destruct
        · obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
            have : 0 < ps.length := by have := Hsll.1; word
            exact ⟨ps[0], List.getElem?_eq_getElem this⟩
          obtain ⟨kv0, Hkv0⟩ : ∃ kv0, m.kvs[0]? = some kv0 := by
            have : 0 < m.kvs.length := by
              rw [← Hlen]; exact List.length_pos_of_mem (List.mem_of_getElem? Hp0)
            exact ⟨m.kvs[0], List.getElem?_eq_getElem this⟩
          ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
          iunfold txn.kvIs at Hkv
          icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
          have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
            have := Hsll.1
            constructor <;> word
          simp only [Hbnd, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
          · iframe Hsl; ipureintro; exact Hp0
          wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
          · iframe #
          wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          simp [Hxs] at Hok
        · wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          simp [Hxs] at Hok
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, p, Hp⟩
        · iframe
        iapply HΦ
        simp only [linkvS]
        ipureintro; exact ⟨x, errOut, rfl, rfl⟩
  · wp_pures
    by_cases Hok : xs.head? = some true
    · -- the prophecy says `ok`: the update the server fires commits
      ihave Hau := put_ok_au γ γr.kv x hP Φ $$ [HAU]
      · iframe Hinv; iunfold linU; iexact HAU
      wp_auto
      wp_apply (client_Put_once cl ep V E γr cid mid context.backgroundCtxVal cd x.Key' x.Val'
          slice.nil _ []) $$ [Hau] as %resp %err Hout
      · iframe #
        iexact Hau
      icases Hout with (⟨%Herr, %σ, HΦ⟩ | %Herr)
      · subst Herr
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, p, Hp⟩
        · iframe
        rw [zero_val_Output]
        iapply HΦ
        simp only [linkvS]
        ipureintro; exact ⟨x, okOut, rfl, rfl⟩
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
    · -- the prophecy says error: commit now, the put pending
      iapply fupd_wp
      imod (put_err_commit γ γr.kv x hP Φ) $$ [HAU] with ⟨%n, HΦ, Htok⟩
      · iframe Hinv; iunfold linU; iexact HAU
      ihave Hau := put_pend_au γ γr.kv n x.Key' x.Val' $$ [Htok]
      · iframe Hinv; iexact Htok
      imodintro
      wp_auto
      wp_apply (client_Put_once cl ep V E γr cid mid context.backgroundCtxVal cd x.Key' x.Val'
          slice.nil _ []) $$ [Hau] as %resp %err Hout
      · iframe #
        iexact Hau
      icases Hout with (⟨%Herr, -⟩ | %Herr)
      · subst Herr
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, p, Hp⟩
        · iframe
        iapply HΦ
        simp only [linkvS]
        ipureintro; exact ⟨x, errOut, rfl, rfl⟩

end proof

end linkv
end EtcdGrove
end Perennial
