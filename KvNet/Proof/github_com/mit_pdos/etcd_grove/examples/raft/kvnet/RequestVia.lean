/-
The proof of `KvNet/Spec/.../kvnet/RequestVia.lean`: the dial (the caller's dialer); on a
connection, the two defers (`c.Close()` with the caller's close accessor, `closeAfter(c, total)`
with `R := True`), the request (`putUint64` of the timeout after the kind, the payload appended),
`writeAll` of `helloClient` and `writeFrame` of the request with the caller's write accessor (the
writer predicates `W` after what this call wrote before), `readFrame` with the read accessor, and
the answer's first byte; on the way out, the disarm (its result unused) and the close.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RequestVia
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.writeAll
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.writeFrame
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFrame
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.closeAfter
public import KvNet.Spec.net.Conn__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions]

private theorem wp_min_dur (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [_root_.Perennial.time.Duration.ty,
        _root_.Perennial.time.Duration.ty])) (Val #x)) (Val #y))
    {{ RET #(if sint.Z x < sint.Z y then x else y); True }} := by
  wp_start
  by_cases h : sint.Z x < sint.Z y
  · rw [decide_eq_true h, ite_eq_left_of_eq_true _ _ (eq_true h)]; wp_auto; iapply HΦ; itrivial
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]; wp_auto; iapply HΦ; itrivial

theorem RequestVia.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_writeAll : writeAll.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_closeAfter : closeAfter.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    RequestVia.spec (GF := GF) (hG := hG) := by
  intro dial addr kind tmo total payload pl dqp W Rd Fl eof ed Hpl
  wp_start as ⟨Hp, #Heof, #Hed, Hdial⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply wp_min_dur
  generalize (if sint.Z (W64 50000000) < sint.Z total then W64 50000000 else total) = dd
  try wp_auto
  wp_bind (App (App (Val #dial) (Val #addr)) (Val #dd))
  iapply Hdial
  iintro %c %err Hres
  icases Hres with (⟨%Herr, %cn, %s, %a, #Hc, Hcr⟩ | ⟨%Herr, HFl⟩)
  rotate_left
  · -- the dial failed
    cases err with
    | nil => exact absurd rfl Herr
    | ok i => ?_
    try wp_auto
    iapply HΦ
    iframe Hp
    iright
    isplitr
    · ipureintro; rfl
    ileft
    iexact HFl
  subst Herr
  iunfold connRes at Hcr
  icases Hcr with ⟨HW0, HR0, #Hwa, #Hra, #Hca⟩
  ihave #Hc' := Hc
  iunfold net.isConn at Hc'
  icases Hc' with ⟨%t, %la, %ra, %Hct, #Hca'⟩
  subst Hct
  try wp_auto
  wp_apply wp_closeAfter _ cn s a total iprop(True) $$ [] as %disarm #Hdis
  · iframe Hc
    isplitl []
    · itrivial
    imodintro
    iintro -
    iunfold cAcc at Hca
    iexact Hca
  try wp_auto
  wp_apply wp_slice_literal (V := w8) [kind]
  isplitr
  · ipureintro; rfl
  iintro %kp ⟨Hk, Hkc⟩
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #kind)] = 1 from rfl]
  try wp_auto
  wp_apply wp_putUint64 _ [kind] _ $$ [$Hk $Hkc] as %r1 ⟨Hr1, Hr1c⟩
  try wp_auto
  wp_apply wp_slice_append r1 _ _ pl dqp $$ [$Hr1 $Hr1c $Hp] as %rq ⟨Hrq, Hrqc, Hp⟩
  try wp_auto
  wp_apply wp_slice_literal (V := w8) [W8 67]
  isplitr
  · ipureintro; rfl
  iintro %hp ⟨Hh, -⟩
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #(W8 67))] = 1 from rfl]
  try wp_auto
  wp_apply wp_writeAll _ cn s a _ [W8 67] (DFrac.own 1) ed (fun w _ => W cn s w) $$ [HW0 Hh]
    as %ok1 ⟨%w1, %res1, HW1, Hh, %Hw1⟩
  · iframe Hc Hh Hed HW0
    imodintro
    iintro %w %rs %Hwrs HP
    iunfold wAcc at Hwa
    iapply Hwa $$ %w %rs %(by rw [Hwrs]; exact ⟨_, rfl⟩) HP
  cases ok1
  · -- the hello's write failed
    try wp_auto
    wp_bind (App (Val #disarm) (Val #()))
    iapply Hdis
    iintro %inTime -
    try wp_auto
    wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hca'
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    iframe Hp
    iright
    isplitr
    · ipureintro; rfl
    iright
    iexists cn, s, w1, []
    iframe HW1 HR0
  -- the hello written: the request frame
  have hw1 := Hw1.2 rfl
  subst hw1
  try wp_auto
  have Hreq : [kind] ++ u64Le (BitVec.sdiv tmo (W64 1000000)) ++ pl = reqBytes kind tmo pl := by
    simp [reqBytes]
  rw [Hreq]
  wp_apply wp_writeFrame _ cn s a rq (reqBytes kind tmo pl) (DFrac.own 1) ed
      (fun w _ => W cn s (W8 67 :: w)) $$ [HW1 Hrq]
    as %ok2 ⟨%w2, %res2, HW2, Hrq, %Hw2⟩
  · iframe Hc Hrq Hed HW1
    imodintro
    iintro %w %rs %Hwrs HP
    iunfold wAcc at Hwa
    simp only [← List.cons_append]
    iapply Hwa $$ %(W8 67 :: w) %rs %(by rw [List.cons_append, Hwrs]; exact List.prefix_refl _) HP
  cases ok2
  · -- the request's write failed
    try wp_auto
    wp_bind (App (Val #disarm) (Val #()))
    iapply Hdis
    iintro %inTime -
    try wp_auto
    wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hca'
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    iframe Hp
    iright
    isplitr
    · ipureintro; rfl
    iright
    iexists cn, s, W8 67 :: w2, []
    iframe HW2 HR0
  -- the request written: the answer
  have hw2 := Hw2.2.1 rfl
  subst hw2
  try wp_auto
  wp_apply wp_readFrame _ cn s a (Rd cn s) eof ed $$ [HR0] as %b %ok3 ⟨%got, HR3, Hans⟩
  · iframe Hc Heof Hed HR0
    iunfold rAcc at Hra
    iexact Hra
  icases Hans with (%Hf | ⟨%l, %Hl, Hb⟩)
  · -- no frame
    subst Hf
    try wp_auto
    wp_bind (App (Val #disarm) (Val #()))
    iapply Hdis
    iintro %inTime -
    try wp_auto
    wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hca'
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    iframe Hp
    iright
    isplitr
    · ipureintro; rfl
    iright
    iexists cn, s, W8 67 :: putB (reqBytes kind tmo pl), got
    iframe HW2 HR3
  obtain ⟨rfl, rfl, Hl26⟩ := Hl
  ihave %Hbl := ownSlice_len $$ Hb
  try wp_auto
  cases l with
  | nil =>
    -- an empty answer
    rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hbl; word)]
    try wp_auto
    wp_bind (App (Val #disarm) (Val #()))
    iapply Hdis
    iintro %inTime -
    try wp_auto
    wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %err' -
    · iframe Hca'
      iunfold cAcc at Hca
      iexact Hca
    try wp_auto
    iapply HΦ
    iframe Hp
    iright
    isplitr
    · ipureintro; rfl
    iright
    iexists cn, s, W8 67 :: putB (reqBytes kind tmo pl), _
    iframe HW2 HR3
  | cons x l' =>
    simp only [List.length_cons] at Hbl
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by word)]
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by word)]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ _ x (by decide) $$ [$Hb] as Hb
    · ipureintro; rfl
    try wp_auto
    by_cases hx : x = W8 1
    · -- the answer
      subst hx
      rw [decide_eq_true rfl]
      try wp_auto
      ihave %Hw := ownSlice_wf $$ Hb
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
        sint.Z b.len ≤ sint.Z b.cap by refine ⟨by decide, by word, Hw.2⟩)]
      icases (ownSlice_split_all (W64 1) b (DFrac.own 1) _ ⟨by decide, by word⟩).1 $$ Hb with ⟨-, Hb⟩
      simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
      try wp_auto
      wp_bind (App (Val #disarm) (Val #()))
      iapply Hdis
      iintro %inTime -
      try wp_auto
      wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %err' -
      · iframe Hca'
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      iapply HΦ
      iframe Hp
      ileft
      isplitr
      · ipureintro; rfl
      iexists l', cn, s
      simp only [helloClientB]
      iframe Hb HW2 HR3
    · -- not an answer
      rw [decide_eq_false hx]
      try wp_auto
      wp_bind (App (Val #disarm) (Val #()))
      iapply Hdis
      iintro %inTime -
      try wp_auto
      wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [] as %err' -
      · iframe Hca'
        iunfold cAcc at Hca
        iexact Hca
      try wp_auto
      iapply HΦ
      iframe Hp
      iright
      isplitr
      · ipureintro; rfl
      iright
      iexists cn, s, W8 67 :: putB (reqBytes kind tmo pl), _
      iframe HW2 HR3

end proof

end raft_kvnet
end EtcdGrove
end Perennial
