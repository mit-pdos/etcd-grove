/-
What the txn package's loggers (`util.go`: `WarnOfExpensiveReadOnlyRangeRequest`,
`WarnOfExpensiveReadOnlyTxnRequest`, `warnOfExpensiveGenericRequest`, `isNil`) need of their
arguments (unit P4, 2026-10-14). Lean-first (no Rocq counterpart).

When the request took longer than the warning's duration, a logger calls the request's
`String()` (`stringerOk`: any `fmt.Stringer` whose method returns), and, unless the response is
nil (`isNil`: the interface nil, or `reflect.ValueOf(..).IsNil()` of the pointer it holds),
`proto.Size` of it (`sizeOk m P`: the triple of `proto.Size` at `m`, lending `P`, the resources
the boundary's case for `m`'s type needs: `Spec/google_golang_org/protobuf/proto/Size.lean`); the
read-only transaction's also walks the responses (`respOpShow`: a range's `Kvs`).

**A read-only transaction's response** (`roTxnRespRd`), complete or partly filled: what
`Txn` returns on success (`txnResponseIs` of a read-only transaction, `roTxnRespRd_of`), and on
the context's error during a range (`executeTxn` stops at the range: the ranges before it filled
in, the others with their `ResponseRange` still `nil`; `roOps_of_opsSkel`), read-only. Each
operation's response is a range's (`roOpRd`): a read-only transaction has only gets
(`txnReadonly`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 google_golang_org.protobuf

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `fmt.Stringer` `s`**: not nil, its `String()` returns some string (persistent). -/
def stringerOk (s : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜s = GoInterface.ok si⌝ ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"String" si.v)) (Val #()))
      {{ (str : GoString), RET #str; True }}))

instance stringerOk_persistent (s : GoInterface) : Persistent (stringerOk (GF := GF) s) := by
  unfold stringerOk; infer_instance

/-- **`proto.Size(m)` returns**, lent `P` (the resources the boundary's case for `m` needs) and
giving it back (persistent). -/
def sizeOk (m : GoInterface) (P : IProp GF) : IProp GF :=
  iprop(□ ({{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ P }}
    (App (Val (@! proto.Size)) (Val #m)) {{ (n : w64), RET #n; P }}))

instance sizeOk_persistent (m : GoInterface) (P : IProp GF) : Persistent (sizeOk (GF := GF) m P) := by
  unfold sizeOk; infer_instance

/-- What `WarnOfExpensiveReadOnlyTxnRequest` reads of a `*pb.ResponseOp` `p`: not nil, its
`Response`; a range's wrapper `w` (then `w`'s `ResponseRange` and, if not nil, its `Kvs`,
read-only), or a value of another type (the type switch's `default`). -/
def respOpShow (p : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ u : GoInterface,
    structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□ u ∗
    ((∃ (w rr : Loc),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
        (⌜rr = null⌝ ∨ ∃ sl : GoSlice, structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦□ sl)) ∨
      ⌜∀ ii : GoInterfaceOk, u = GoInterface.ok ii →
        ii.ty ≠ go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty⌝))

instance respOpShow_persistent (p : Loc) : Persistent (respOpShow (GF := GF) p) := by
  unfold respOpShow; infer_instance

/-- What `WarnOfExpensiveReadOnlyTxnRequest` reads of a `*pb.TxnResponse` `resp` (not nil): its
`Responses` and theirs (`respOpShow`). -/
def txnRespShow (resp : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    [∗list] p ∈ ps, respOpShow p)

instance txnRespShow_persistent (resp : Loc) : Persistent (txnRespShow (GF := GF) resp) := by
  unfold txnRespShow; infer_instance

/-- **A read-only transaction's `*pb.ResponseOp` `p`** (read-only), filled in or not: a range's
wrapper `w`, whose `ResponseRange` is `nil` or a range's response. -/
def roOpRd (p : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (w rr : Loc),
    structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
      (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w :
        GoInterface) ∗
    structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
    (⌜rr = null⌝ ∨ ∃ (rev : w64) (kvs : List EtcdKv) (more : Bool) (count : w64),
      rangeResponseIs rr rev kvs more count))

instance roOpRd_persistent (p : Loc) : Persistent (roOpRd (GF := GF) p) := by
  unfold roOpRd; infer_instance

/-- **A read-only transaction's responses** (the `Responses` of the `*pb.TxnResponse` `resp`,
read-only), filled in or not (`roOpRd`). -/
def roRespsRd (resp : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    [∗list] p ∈ ps, roOpRd p)

instance roRespsRd_persistent (resp : Loc) : Persistent (roRespsRd (GF := GF) resp) := by
  unfold roRespsRd; infer_instance

/-- **A read-only transaction's `*pb.TxnResponse` `resp`** (not nil, read-only), complete or
partly filled: its header and the header's revision, `Succeeded`, and its responses
(`roRespsRd`). The header's id fields are apart (`respHdrOwn`, owned by the request's
goroutine). -/
def roTxnRespRd (resp : Loc) : IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ (h : Loc) (rev : w64) (ok : Bool),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ ok ∗ roRespsRd resp)

instance roTxnRespRd_persistent (resp : Loc) : Persistent (roTxnRespRd (GF := GF) resp) := by
  unfold roTxnRespRd; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem respOpShow_of_roOpRd (p : Loc) : roOpRd (GF := GF) p ⊢ respOpShow p := by
  unfold roOpRd
  iintro #⟨%Hp, %w, %rr, #Hu, #Hw, #Hrr⟩
  iunfold respOpShow
  isplitl []; · ipureintro; exact Hp
  iexists _
  iframe Hu
  ileft
  iexists w, rr
  isplitl []; · ipureintro; rfl
  iframe Hw
  icases Hrr with (%Hn | ⟨%rev, %kvs, %more, %count, #Hr⟩)
  · ileft; ipureintro; exact Hn
  · iright
    iunfold rangeResponseIs at Hr
    icases Hr with ⟨-, %h, %sl, %ps, -, -, -, #Hk, -⟩
    iexists sl; iexact Hk

theorem txnRespShow_of_roOps (resp : Loc) (sl : GoSlice) (ps : List Loc) :
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ⊢ sl ↦*□ ps -∗
      ([∗list] p ∈ ps, roOpRd (GF := GF) p) -∗ txnRespShow resp := by
  iintro #Hr #Hs #Hps
  iunfold txnRespShow
  iexists sl, ps
  iframe Hr Hs
  iapply (BigSepL.bigSepL_mono (Φ := fun _ p => roOpRd (GF := GF) p)
    (fun _ => respOpShow_of_roOpRd _)) $$ Hps

theorem txnRespShow_of_rd (resp : Loc) : roTxnRespRd (GF := GF) resp ⊢ txnRespShow resp := by
  unfold roTxnRespRd roRespsRd
  iintro #⟨-, %h, %rev, %ok, -, -, -, -, %sl, %ps, #Hr, #Hs, #Hps⟩
  iapply txnRespShow_of_roOps resp sl ps $$ Hr Hs Hps

/-- A range's response of a transaction, read-only. -/
theorem roOpRd_of_responseOpIs (skip : Bool) (p : Loc) (o : OpFull) (res : TxnOpResult) :
    responseOpIs (GF := GF) skip p (.get o) res ⊢ roOpRd p := by
  cases res with
  | range sel n =>
    unfold responseOpIs
    iintro #⟨%Hp, %u, %w, %r, #Hu, %Hueq, #Hw, %rev, Hr⟩
    subst Hueq
    iunfold roOpRd
    isplitl []; · ipureintro; exact Hp
    iexists w, r
    iframe Hu Hw
    iright
    cases skip
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%kvs, %more, #Hr, -⟩
      iexists rev, kvs, more, _
      iexact Hr
    · simp only [↓reduceIte]
      iexists rev, [], false, _
      iexact Hr
  | put => unfold responseOpIs; iintro #⟨-, %u, %w, %r, -, H⟩; iexfalso; iexact H
  | delete n => unfold responseOpIs; iintro #⟨-, %u, %w, %r, -, H⟩; iexfalso; iexact H
  | txn ok rs => unfold responseOpIs; iintro #⟨-, %u, %w, %r, -, H⟩; iexfalso; iexact H

/-- The responses of gets, read-only. -/
theorem roOps_of_responseOpsIs (skip : Bool) :
    ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult), ops.all opIsGet = true →
      responseOpsIs (GF := GF) skip ps ops rs ⊢ [∗list] p ∈ ps, roOpRd p
  | [], [], [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; itrivial
  | p :: ps, op :: ops, r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    unfold responseOpsIs
    iintro ⟨Hp, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hp]
    · cases op with
      | get o => iapply roOpRd_of_responseOpIs skip p o r $$ Hp
      | _ => simp [opIsGet] at h
    · iapply roOps_of_responseOpsIs skip ps ops rs h.2 $$ H
  | [], [], _ :: _, _ => by unfold responseOpsIs; iintro H; iexfalso; iexact H
  | [], _ :: _, _, _ => by unfold responseOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [], _, _ => by unfold responseOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, _ :: _, [], _ => by unfold responseOpsIs; iintro H; iexfalso; iexact H

/-- The skeletons of gets, made read-only (their `ResponseRange` still `nil`). -/
theorem roOps_of_opsSkel (s0 : List EtcdKv) :
    ∀ (ps : List Loc) (ops : List TxnOp), ops.all opIsGet = true →
      opsSkel (GF := GF) s0 ps ops ⊢ |==> [∗list] p ∈ ps, roOpRd p
  | [], [], _ => by iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
  | p :: ps, op :: ops, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    unfold opsSkel
    iintro ⟨Hp, H⟩
    imod roOps_of_opsSkel s0 ps ops h.2 $$ H with H
    cases op with
    | get o =>
      iunfold opSkel at Hp
      icases Hp with ⟨%Hpn, %w, #Hu, Hw⟩
      ipersist Hw
      imodintro
      iapply BigSepL.bigSepL_cons.2
      iframe H
      iunfold roOpRd
      isplitl []; · ipureintro; exact Hpn
      iexists w, null
      iframe Hu Hw
      ileft; ipureintro; rfl
    | _ => simp [opIsGet] at h
  | [], _ :: _, _ => by unfold opsSkel; iintro H; iexfalso; iexact H
  | _ :: _, [], _ => by unfold opsSkel; iintro H; iexfalso; iexact H

/-- **A read-only transaction's response**, read-only. -/
theorem roTxnRespRd_of (skip : Bool) (resp : Loc) (rev : w64) (t : TxnModel) (ok : Bool)
    (rs : List TxnOpResult) (hro : txnReadonly t = true) :
    txnResponseIs (GF := GF) skip resp rev t ok rs ⊢ roTxnRespRd resp := by
  unfold txnResponseIs txnRespFieldsIs respsIs
  iintro #⟨%Hn, %h, #Hh, %Hhn, #Hrev, #Hok, %sl, %ps, #Hr, #Hs, #Hops⟩
  iunfold roTxnRespRd
  isplitl []; · ipureintro; exact Hn
  iexists h, rev, ok
  iframe Hh Hrev Hok
  isplitl []; · ipureintro; exact Hhn
  iunfold roRespsRd
  iexists sl, ps
  iframe Hr Hs
  have hb : (t.branch ok).all opIsGet = true := by
    simp only [txnReadonly, List.all_append, Bool.and_eq_true] at hro
    cases ok <;> simp [TxnModel.branch, hro.1, hro.2]
  iapply roOps_of_responseOpsIs skip ps _ rs hb $$ Hops

/-- A partly filled read-only transaction's responses: the ranges before the `n`-th answered
(`responseOpsIs`), the others' skeletons (`opsSkel`), made read-only. -/
theorem roOps_split (skip : Bool) (s0 : List EtcdKv) (ps : List Loc) (ops : List TxnOp)
    (rs : List TxnOpResult) (n : Nat) (hg : ops.all opIsGet = true) :
    responseOpsIs (GF := GF) skip (ps.take n) (ops.take n) rs ⊢
      opsSkel s0 (ps.drop n) (ops.drop n) -∗ |==> [∗list] p ∈ ps, roOpRd p := by
  iintro #Hd Hs
  have hg1 : (ops.take n).all opIsGet = true := by
    rw [List.all_eq_true] at hg ⊢; intro x hx; exact hg x (List.mem_of_mem_take hx)
  have hg2 : (ops.drop n).all opIsGet = true := by
    rw [List.all_eq_true] at hg ⊢; intro x hx; exact hg x (List.mem_of_mem_drop hx)
  ihave H1 := roOps_of_responseOpsIs skip _ _ rs hg1 $$ Hd
  imod roOps_of_opsSkel s0 _ _ hg2 $$ Hs with H2
  have hsplit : (([∗list] p ∈ ps.take n, roOpRd (GF := GF) p) ∗
      ([∗list] p ∈ ps.drop n, roOpRd (GF := GF) p)) ⊢ [∗list] p ∈ ps, roOpRd p := by
    conv => rhs; rw [← List.take_append_drop n ps]
    exact BigSepL.bigSepL_append.2
  imodintro
  iapply hsplit
  iframe H1 H2

end lemmas

end txn
end EtcdGrove
end Perennial
