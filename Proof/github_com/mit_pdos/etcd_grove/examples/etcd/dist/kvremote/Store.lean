/-
# kvremote's far-side store (`notes/etcd-dist-plan.md` §11.3, step 1)

The cluster's one KV state as `remote`'s store (`RBase`, `Net/Proof/.../lib/remote/Defs.lean`), for
the kv workload's model, txnlin's `linkvtxnS`:

- **The wire input** `VIn`: a Go `Input` that `Gen` may return (`GenIn`); its model input `kvMi x`
  is its decoding (`decIn`, total on `GenIn`). Two wire inputs may decode to one model input
  (`Gen` fills fields the decoder ignores), which is why the store's `J` is not its `I`.
- **The output** `VOut`: a Go `Output` that is not the unknown one (`Err` false) and whose encoding
  fits a slice (`outputBytes` shorter than `2 ^ 63`). Only such outputs can be told apart by their
  bytes (`kvR_hinj`: no injection of all outputs into lists of bounded length exists, and every
  store's encodings are shorter than `2 ^ 63`, `RBase.encOut_len`).
- **The base store** `TSo`: txnlin's `TS`, its answers as `call` builds them (`outOf`), when they
  fit (`kvOut`; else the zero output, at no state the far side holds: `kvGood`).
- **The state** `kvSys γk st`: the client half of the cluster's KV ghost variable at a state `σ`
  that is good (`GoodKV`: sorted, keys the workload's) and abstracts to `st` (`linkv.absSt`), and
  `st` is `kvGood`: its revision below `2 ^ 63` (the model's answers' revisions fit a word) and its
  values at most `inMax` bytes (so do its answers' strings, `outOf_short`).
- **The mask** `kvEop`: the server's invariants an update of the KV may have open
  (`kvOpAu1`/`kvReadAu`'s `(⊤ \ srvRaftN) \ kvN`).
- The bytes: an input's `inputBytes`, an output's `outputBytes` (each cut to nothing past `2 ^ 63`,
  which no value the codec encodes reaches: a slice holds it).

`kvPendDec`: porcupine's model `linkvtxnS` agrees with `pSeq TSo` at every good configuration
(`remote.PendDec`), from `decOut_outOf` and `linkv`'s `pSeq_ok`/`pSeq_errW_pending`/`pSeq_errR`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Enc
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.GenLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin
open EtcdGrove EtcdGrove.etcd_txnlin
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## Strings' bounds through the model's steps -/

section bounds
variable [GooseExts]

/-- A store's values at most `N` bytes. -/
def StoreLe (N : Nat) (m : linkv.MStore GoString GoString) : Prop :=
  ∀ k r, m k = some r → r.val.length ≤ N

/-- A transaction result's value at most `N` bytes. -/
def ResLe (N : Nat) : linkv.MRes GoString → Prop
  | .get (some r) => r.val.length ≤ N
  | _ => True

/-- An answer's strings at most `N` bytes. -/
def OutLe (N : Nat) : MO → Prop
  | .get _ r => ∀ x, r = some x → x.val.length ≤ N
  | .list _ rs => ∀ p ∈ rs, p.1.length ≤ N ∧ p.2.val.length ≤ N
  | .txn _ _ rs => ∀ x ∈ rs, ResLe N x
  | _ => True

theorem storeLe_put {N : Nat} {m : linkv.MStore GoString GoString} (hm : StoreLe N m) (r : Nat)
    (k v : GoString) (hv : v.length ≤ N) : StoreLe N (m.put r k v) := by
  intro k' x h
  unfold linkv.MStore.put at h
  split at h
  · cases h; exact hv
  · exact hm k' x h

theorem storeLe_del {N : Nat} {m : linkv.MStore GoString GoString} (hm : StoreLe N m)
    (k : GoString) : StoreLe N (m.del k) := by
  intro k' x h
  unfold linkv.MStore.del at h
  split at h
  · cases h
  · exact hm k' x h

theorem runOps_le (N r : Nat) : ∀ (m : linkv.MStore GoString GoString)
    (ops : List (linkv.MOp GoString GoString)), StoreLe N m → (∀ o ∈ ops, mopBytesLe N o) →
    StoreLe N (linkv.runOps r m ops).1 ∧ ∀ x ∈ (linkv.runOps r m ops).2.1, ResLe N x
  | m, [], hm, _ => ⟨hm, fun _ h => by cases h⟩
  | m, op :: ops, hm, hops => by
    have hop := hops op List.mem_cons_self
    have hrest : ∀ o ∈ ops, mopBytesLe N o := fun o h => hops o (List.mem_cons_of_mem _ h)
    have h1 : StoreLe N (op.run r m).1 ∧ ResLe N (op.run r m).2.1 := by
      cases op with
      | get k =>
        refine ⟨hm, ?_⟩
        simp only [linkv.MOp.run]
        cases hk : m k with
        | none => trivial
        | some x => exact hm k x hk
      | put k v => exact ⟨storeLe_put hm r k v hop.2, trivial⟩
      | del k =>
        simp only [linkv.MOp.run]
        cases m k with
        | none => exact ⟨hm, trivial⟩
        | some _ => exact ⟨storeLe_del hm k, trivial⟩
    obtain ⟨ih1, ih2⟩ := runOps_le N r (op.run r m).1 ops h1.1 hrest
    refine ⟨ih1, fun x hx => ?_⟩
    simp only [linkv.runOps, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h1.2
    · exact ih2 x hx

/-- **A step keeps the values' bound, and its answer's strings are bounded**, for an input whose
strings are, and listed keys that are. -/
theorem mStep_le {N : Nat} (ks : List GoString) (hks : ∀ k ∈ ks, k.length ≤ N) (i : MI) (s : MS)
    (hs : StoreLe N s.kv) (hi : minBytesLe N i) :
    StoreLe N (linkv.mStep ks i s).1.kv ∧ OutLe N (linkv.mStep ks i s).2 := by
  cases i with
  | get k => exact ⟨hs, fun x hx => hs k x hx⟩
  | list =>
    refine ⟨hs, ?_⟩
    simp only [linkv.mStep, OutLe]
    intro p hp
    obtain ⟨k, hk, hp⟩ := List.mem_filterMap.1 hp
    cases hv : s.kv k with
    | none => rw [hv] at hp; cases hp
    | some x =>
      rw [hv] at hp; cases hp
      exact ⟨hks k hk, hs k x hv⟩
  | put k v => exact ⟨storeLe_put hs _ k v hi.2, trivial⟩
  | del k =>
    simp only [linkv.mStep]
    cases s.kv k with
    | none => exact ⟨hs, trivial⟩
    | some _ => exact ⟨storeLe_del hs k, trivial⟩
  | txn cs t e =>
    simp only [linkv.mStep, OutLe]
    have hb : ∀ o ∈ (if cs.all (linkv.MCmp.holds s.kv) = true then t else e), mopBytesLe N o := by
      intro o ho
      split at ho
      · exact hi.2 o (List.mem_append_left _ ho)
      · exact hi.2 o (List.mem_append_right _ ho)
    exact runOps_le N (s.rev + 1) s.kv _ hs hb

/-- An `Output`'s strings at most `N` bytes. -/
def OutStrLe (N : Nat) (y : Output) : Prop :=
  y.R'.Val'.length ≤ N ∧ y.Res0'.R'.Val'.length ≤ N ∧ y.Res1'.R'.Val'.length ≤ N ∧
    y.Res2'.R'.Val'.length ≤ N ∧ y.KV0'.Key'.length ≤ N ∧ y.KV0'.R'.Val'.length ≤ N ∧
    y.KV1'.Key'.length ≤ N ∧ y.KV1'.R'.Val'.length ≤ N ∧ y.KV2'.Key'.length ≤ N ∧
    y.KV2'.R'.Val'.length ≤ N

/-- An output's bytes: a constant and its strings. -/
theorem outputBytes_le {N : Nat} (y : Output) (h : OutStrLe N y) :
    (outputBytes y).length ≤ 300 + 10 * N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [outputBytes, tResBytes, kvBytes, vrBytes, encStr, encBool, List.length_append,
    encU64_length, List.length_singleton]
  omega

theorem getD_forall {α : Type} (P : α → Prop) (l : List α) (d : α) (i : Nat)
    (hl : ∀ x ∈ l, P x) (hd : P d) : P (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hd
  | some x => exact hl x (List.mem_of_getElem? h)

theorem encRes_le {N : Nat} (r : linkv.MRes GoString) (h : ResLe N r) :
    (encRes r).R'.Val'.length ≤ N := by
  cases r with
  | get v =>
    cases v with
    | none => simp [encRes, getRes, zVR]
    | some x => exact h
  | put => simp [encRes, putRes, zVR]
  | del n => simp [encRes, delRes, zVR]

/-- **`call`'s output of an answer has its strings' bound.** -/
theorem outOf_le {N : Nat} (o : MO) (h : OutLe N o) : OutStrLe N (outOf o) := by
  cases o with
  | get rev v =>
    cases v with
    | none => simp [OutStrLe, outOf, zOut, zVR, zOut.putRes0, zOut.kv0]
    | some x =>
      have := h x rfl
      simp [OutStrLe, outOf, zOut, zOut.putRes0, zOut.kv0, etcd_txnlin.encVR, this, zVR]
  | list rev rs =>
    simp only [outOf, OutStrLe, withKVsL]
    have hk : ∀ x ∈ rs.map (fun p => (⟨p.1, etcd_txnlin.encVR p.2⟩ : KV)),
        x.Key'.length ≤ N ∧ x.R'.Val'.length ≤ N := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact h p hp
    have hz : zOut.KV0'.Key'.length ≤ N ∧ zOut.KV0'.R'.Val'.length ≤ N := by
      simp [zOut, zOut.kv0, zVR]
    have g0 := getD_forall _ _ _ 0 hk hz
    have g1 := getD_forall _ _ _ 1 hk hz
    have g2 := getD_forall _ _ _ 2 hk hz
    refine ⟨?_, ?_, ?_, ?_, g0.1, g0.2, g1.1, g1.2, g2.1, g2.2⟩ <;>
      simp [zOut, zVR, zOut.putRes0]
  | put rev => simp [OutStrLe, outOf, zOut, zVR, zOut.putRes0, zOut.kv0]
  | del rev n => simp [OutStrLe, outOf, zOut, zVR, zOut.putRes0, zOut.kv0]
  | txn rev ok rs =>
    simp only [outOf, OutStrLe, withResL]
    have hr : ∀ x ∈ rs.map encRes, x.R'.Val'.length ≤ N := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact encRes_le r (h r hr)
    have hz : zOut.Res0'.R'.Val'.length ≤ N := by simp [zOut, zOut.putRes0, zVR]
    have g0 := getD_forall _ _ _ 0 hr hz
    have g1 := getD_forall _ _ _ 1 hr hz
    have g2 := getD_forall _ _ _ 2 hr hz
    refine ⟨?_, g0, g1, g2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [zOut, zVR, zOut.kv0]

/-- `call`'s outputs of answers are not the unknown one. -/
theorem outOf_err (o : MO) : (outOf o).Err' = false := by
  cases o with
  | get rev v => cases v <;> rfl
  | _ => rfl

/-- An output whose strings are at most `inMax` bytes fits a slice. -/
theorem outputBytes_short (y : Output) (h : OutStrLe inMax y) : (outputBytes y).length < 2 ^ 63 :=
  Nat.lt_of_le_of_lt (outputBytes_le y h) (by decide)

/-- The unknown output's strings are empty. -/
theorem errOut_short : (outputBytes errOut).length < 2 ^ 63 :=
  outputBytes_short _ (by simp [OutStrLe, errOut, zOut, zVR, zOut.putRes0, zOut.kv0])

end bounds

/-! ## The store -/

section store
variable [GooseExts]

/-- **A wire input** (see the file header): an `Input` `Gen` may return. -/
abbrev VIn := {x : Input // GenIn x}

/-- **An output** (see the file header): not the unknown one, its bytes fitting a slice. -/
abbrev VOut := {y : Output // y.Err' = false ∧ (outputBytes y).length < 2 ^ 63}

theorem VIn.dec (x : VIn) : (decIn x.1).isSome := by
  obtain ⟨i, h, _⟩ := x.2.1
  simp [h]

/-- **A wire input's model input**: its decoding. -/
def kvMi (x : VIn) : MI := (decIn x.1).get x.dec

theorem kvMi_dec (x : VIn) : decIn x.1 = some (kvMi x) := by
  simp [kvMi]

/-- The zero output, as a `VOut`. -/
def zVOut : VOut := ⟨zOut, rfl,
  outputBytes_short _ (by simp [OutStrLe, zOut, zVR, zOut.putRes0, zOut.kv0])⟩

/-- `call`'s output of an answer, when it is a `VOut` (always, at a good state: `kvOut_good`). -/
def kvOut (o : MO) : VOut :=
  if h : (outOf o).Err' = false ∧ (outputBytes (outOf o)).length < 2 ^ 63 then ⟨outOf o, h⟩
  else zVOut

/-- **The base store** (see the file header). -/
def TSo : linkv.PendSpec MS MI VOut where
  init := TS.init
  step j s := ((TS.step j s).1, kvOut (TS.step j s).2)
  isWrite := TS.isWrite

/-- **A good state** (see the file header). -/
def kvGood (st : MS) : Prop := st.rev < 2 ^ 63 ∧ StoreLe inMax st.kv

/-- At a good state, a wire input's step answers `call`'s output, and the next state's values
keep their bound (its revision's comes from the server's room at the commit, `kvRoom`). -/
theorem kvOut_good (x : VIn) (st : MS) (hg : kvGood st) :
    (kvOut (TS.step (kvMi x) st).2).1 = outOf (TS.step (kvMi x) st).2 ∧
      StoreLe inMax (TS.step (kvMi x) st).1.kv := by
  have hb : minBytesLe inMax (kvMi x) := x.2.2.2 _ (kvMi_dec x)
  obtain ⟨h1, h2⟩ := mStep_le wks wks_short (kvMi x) st hg.2 hb
  refine ⟨?_, h1⟩
  unfold kvOut
  rw [dif_pos ⟨outOf_err _, outputBytes_short _ (outOf_le _ h2)⟩]

/-- An input's bytes, cut to nothing past a slice's length (never: `EncInput` returns them in a
slice). -/
def inEnc (x : Input) : List w8 :=
  if (inputBytes x).length < 2 ^ 63 then inputBytes x else []

/-- An output's bytes, likewise. -/
def outEnc (y : Output) : List w8 :=
  if (outputBytes y).length < 2 ^ 63 then outputBytes y else []

theorem inEnc_len (x : Input) : (inEnc x).length < 2 ^ 63 := by
  unfold inEnc; split
  · assumption
  · simp

theorem outEnc_len (y : Output) : (outEnc y).length < 2 ^ 63 := by
  unfold outEnc; split
  · assumption
  · simp

theorem inEnc_eq (x : Input) (h : (inputBytes x).length < 2 ^ 63) : inEnc x = inputBytes x := by
  simp [inEnc, h]

theorem outEnc_eq (y : Output) (h : (outputBytes y).length < 2 ^ 63) : outEnc y = outputBytes y := by
  simp [outEnc, h]

/-- Bytes a decoder accepted as `b`'s encoding were `a`'s: `a` is `b`. -/
theorem inEnc_dec {a b : Input} (h : inEnc a = inputBytes b) : a = b := by
  unfold inEnc at h
  split at h
  · exact inputBytes_inj h (by omega)
  · have := congrArg List.length h
    simp only [inputBytes, List.length_append, encU64_length, List.length_nil] at this
    omega

theorem outEnc_dec {a b : Output} (h : outEnc a = outputBytes b) : a = b := by
  unfold outEnc at h
  split at h
  · exact outputBytes_inj h (by omega)
  · have := congrArg List.length h
    simp only [outputBytes, List.length_append, encBool, List.length_singleton,
      List.length_nil] at this
    omega

variable [go_gctx : GoGlobalContext] in
open Classical in
/-- A value's bytes: a boxed `Output`'s, or nothing for any other value (never encoded). -/
def kvEncOut (v : GoInterface) : List w8 :=
  if h : ∃ y : Output, v = boxOut y then outEnc (choose h) else []

theorem kvEncOut_len [GoGlobalContext] (v : GoInterface) : (kvEncOut v).length < 2 ^ 63 := by
  unfold kvEncOut; split
  · exact outEnc_len _
  · simp

/-- **The update's mask** (see the file header): the server's invariants. -/
def kvEop : CoPset := ↑srvRaftN ∪ ↑kvN

theorem kvEop_mask : (⊤ \ kvEop : CoPset) = (⊤ \ ↑srvRaftN) \ ↑kvN := by
  apply CoPset.ext
  intro p
  simp only [kvEop, CoPset.in_diff, CoPset.in_union, not_or, and_assoc]

/-! ### The ghost maps' keys -/

/-- A transaction operation's fields. -/
def tOpT (o : TOp) : w64 × GoString × GoString := (o.Kind', o.Key', o.Val')

/-- An input's fields. -/
def inT (x : Input) :=
  (x.Kind', x.Key', x.Val', x.NCmps', (x.Cmp0'.Kind', x.Cmp0'.Key', x.Cmp0'.Val', x.Cmp0'.Num'),
    x.NThen', tOpT x.Then0', tOpT x.Then1', tOpT x.Then2', x.NElse', tOpT x.Else0')

/-- A value's fields. -/
def vrT (r : VR) : GoString × w64 × w64 := (r.Val', r.Mod', r.Ver')

/-- A result's fields. -/
def tResT (r : TRes) := (r.Kind', r.Found', vrT r.R', r.N')

/-- A key-value's fields. -/
def kvT (kv : KV) := (kv.Key', vrT kv.R')

/-- An output's fields. -/
def outT (y : Output) :=
  (y.Err', y.Rev', y.Found', vrT y.R', y.N', y.Ok', y.NRes', tResT y.Res0', tResT y.Res1',
    tResT y.Res2', y.NKVs', kvT y.KV0', kvT y.KV1', kvT y.KV2')

theorem inT_inj : Function.Injective inT := by
  rintro ⟨a1, a2, a3, a4, ⟨c1, c2, c3, c4⟩, a6, ⟨t1, t2, t3⟩, ⟨u1, u2, u3⟩, ⟨v1, v2, v3⟩, a10,
    ⟨w1, w2, w3⟩⟩ ⟨b1, b2, b3, b4, ⟨d1, d2, d3, d4⟩, b6, ⟨t1', t2', t3'⟩, ⟨u1', u2', u3'⟩,
    ⟨v1', v2', v3'⟩, b10, ⟨w1', w2', w3'⟩⟩ h
  simp only [inT, tOpT, Prod.mk.injEq] at h
  simp only [h]

theorem outT_inj : Function.Injective outT := by
  rintro ⟨a1, a2, a3, ⟨r1, r2, r3⟩, a5, a6, a7, ⟨p1, p2, ⟨p3, p4, p5⟩, p6⟩,
    ⟨q1, q2, ⟨q3, q4, q5⟩, q6⟩, ⟨s1, s2, ⟨s3, s4, s5⟩, s6⟩, a11, ⟨k1, ⟨k2, k3, k4⟩⟩,
    ⟨l1, ⟨l2, l3, l4⟩⟩, ⟨m1, ⟨m2, m3, m4⟩⟩⟩
    ⟨b1, b2, b3, ⟨r1', r2', r3'⟩, b5, b6, b7, ⟨p1', p2', ⟨p3', p4', p5'⟩, p6'⟩,
    ⟨q1', q2', ⟨q3', q4', q5'⟩, q6'⟩, ⟨s1', s2', ⟨s3', s4', s5'⟩, s6'⟩, b11, ⟨k1', ⟨k2', k3', k4'⟩⟩,
    ⟨l1', ⟨l2', l3', l4'⟩⟩, ⟨m1', ⟨m2', m3', m4'⟩⟩⟩ h
  simp only [outT, vrT, tResT, kvT, Prod.mk.injEq] at h
  simp only [h]

instance VIn.countable : Pos.Countable VIn :=
  .ofInjective (fun x => Pos.Countable.encode (inT x.1))
    (fun _ _ h => Subtype.ext (inT_inj (Pos.encode_inj h)))

instance VOut.countable : Pos.Countable VOut :=
  .ofInjective (fun y => Pos.Countable.encode (outT y.1))
    (fun _ _ h => Subtype.ext (outT_inj (Pos.encode_inj h)))

end store

section sys
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The far side's state** (see the file header). -/
def kvSys (γk : KVNames) (st : MS) : IProp GF :=
  iprop(∃ σ : KVState, etcdKV γk σ ∗ ⌜GoodKV σ ∧ linkv.absSt σ = st ∧ kvGood st⌝)

instance kvSys_timeless (γk : KVNames) (st : MS) : Timeless (kvSys (GF := GF) γk st) := by
  unfold kvSys etcdKV; infer_instance

/-- **The cluster's KV as `remote`'s store** (see the file header). -/
def kvR (γk : KVNames) : RBase GF MS MI VIn VOut where
  B := TSo
  mi := kvMi
  sysState := kvSys γk
  good := kvGood
  sysState_good st := by
    unfold kvSys
    iintro ⟨%σ, -, %h⟩
    ipureintro
    exact h.2.2
  Eop := kvEop
  iv x := boxIn x.1
  ov y := boxOut y.1
  unk _ := boxOut errOut
  encIn x := inEnc x.1
  encOut := kvEncOut
  reads_stay j st h := linkv.mStep_read wks j st h
  encIn_len x := inEnc_len x.1
  encOut_len := kvEncOut_len

instance kvR_timeless (γk : KVNames) (st : MS) : Timeless ((kvR (GF := GF) γk).sysState st) :=
  kvSys_timeless γk st

end sys

/-! ## The store's laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

include sem package_sem in
theorem boxOut_inj {y y' : Output} (h : boxOut y = boxOut y') : y = y' := by
  simp only [boxOut, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact Output_intoVal_inj (sem := sem) (package_sem := package_sem) h

include sem package_sem in
theorem boxIn_inj {x x' : Input} (h : boxIn x = boxIn x') : x = x' := by
  simp only [boxIn, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact Input_intoVal_inj (sem := sem) (package_sem := package_sem) h

include sem package_sem in
/-- A boxed output's bytes. -/
theorem kvEncOut_boxOut (y : Output) : kvEncOut (boxOut y) = outEnc y := by
  have h : ∃ y' : Output, boxOut y = boxOut y' := ⟨y, rfl⟩
  unfold kvEncOut
  rw [dif_pos h]
  exact congrArg outEnc (boxOut_inj (sem := sem) (package_sem := package_sem)
    (Classical.choose_spec h)).symm

include sem package_sem in
/-- **`remote.Run.spec`'s `hinj`**: an output is told by its bytes. -/
theorem kvR_hinj (γk : KVNames) (o o' : VOut)
    (h : (kvR (GF := GF) γk).encOut ((kvR (GF := GF) γk).ov o) =
      (kvR (GF := GF) γk).encOut ((kvR (GF := GF) γk).ov o')) : o = o' := by
  simp only [kvR] at h
  rw [kvEncOut_boxOut (sem := sem) (package_sem := package_sem),
    kvEncOut_boxOut (sem := sem) (package_sem := package_sem), outEnc_eq _ o.2.2,
    outEnc_eq _ o'.2.2] at h
  exact Subtype.ext (outputBytes_inj h (Nat.lt_trans o.2.2 (by decide)))

/-- A silent step of `TSo` is one of `TS` (they step the state alike). -/
theorem reach_TSo {c c' : linkv.PCfg MS MI} (h : linkv.PReach TSo c c') : linkv.PReach TS c c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    refine .step ?_ ih
    cases hs with
    | apply i hm => exact .apply _ i hm
    | perm p hp => exact .perm _ p hp

theorem closed_TSo {S : linkv.PSet MS MI} (h : linkv.PSet.Closed TS S) : linkv.PSet.Closed TSo S :=
  fun c c' hc hr => h c c' hc (reach_TSo hr)

include sem package_sem in
/-- **porcupine's model is the store's, at good configurations** (`remote.PendDec`). -/
theorem kvPendDec (γk : KVNames) : PendDec (kvR (GF := GF) γk) (linkvtxnS (GF := GF)) where
  init := rfl
  ok s c x hc hg := by
    obtain ⟨ho, -⟩ := kvOut_good x c.st hg
    simp only [kvR, TSo] at ho ⊢
    rw [ho]
    have hd : (linkvtxnS (GF := GF)).M.step s (boxIn x.1, boxOut (outOf (TS.step (kvMi x) c.st).2)) =
        (linkv.pSeq TS).step s (kvMi x, .ok (TS.step (kvMi x) c.st).2) := by
      show (linkv.pM TS decOp).step s _ = _
      apply linkv.pM_step
      rw [decOp_box (sem := sem) (package_sem := package_sem), decIO, kvMi_dec x]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
      apply decOut_outOf x.1 (kvMi x) (kvMi_dec x) c.st
      have h1 := linkv.mStep_rev wks (kvMi x) c.st
      have h2 := linkv.mStep_rev_le wks (kvMi x) c.st
      have h3 := hg.1
      omega
    rw [hd]
    obtain ⟨S', h1, h2⟩ := linkv.pSeq_ok (P := TS) hc (kvMi x)
    exact ⟨S', h1, h2, closed_TSo (linkv.pSeq_step_closed h1)⟩
  errW s c x hc _ hw := by
    have hd : (linkvtxnS (GF := GF)).M.step s (boxIn x.1, boxOut errOut) =
        (linkv.pSeq TS).step s (kvMi x, .err) := by
      show (linkv.pM TS decOp).step s _ = _
      apply linkv.pM_step
      rw [decOp_box (sem := sem) (package_sem := package_sem), decIO, kvMi_dec x]
      rfl
    simp only [kvR]
    rw [hd]
    obtain ⟨S', h1, h2⟩ := linkv.pSeq_errW_pending (P := TS) hc (kvMi x) hw
    exact ⟨S', h1, h2, closed_TSo (linkv.pSeq_step_closed h1)⟩
  errR s c x hc _ hw := by
    have hd : (linkvtxnS (GF := GF)).M.step s (boxIn x.1, boxOut errOut) =
        (linkv.pSeq TS).step s (kvMi x, .err) := by
      show (linkv.pM TS decOp).step s _ = _
      apply linkv.pM_step
      rw [decOp_box (sem := sem) (package_sem := package_sem), decIO, kvMi_dec x]
      rfl
    simp only [kvR]
    rw [hd]
    obtain ⟨S', h1, h2⟩ := linkv.pSeq_errR (P := TS) hc (kvMi x) hw
    exact ⟨S', h1, h2, closed_TSo (linkv.pSeq_step_closed h1)⟩
  ioOk_ok x o := by
    simp only [linkvtxnS, kvR]
    exact BI.pure_intro ⟨x.1, o.1, rfl, rfl, x.2.1⟩
  ioOk_err x := by
    simp only [linkvtxnS, kvR]
    exact BI.pure_intro ⟨x.1, errOut, rfl, rfl, x.2.1⟩
  noObs _ := rfl

end laws

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
