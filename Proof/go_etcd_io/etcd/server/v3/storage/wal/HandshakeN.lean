/- Lean-first (no Rocq counterpart).

# An indexed handshake on an unbuffered channel

Perennial's `Handshake` idiom (`Perennial/Golang/Theory/Chan/Idioms/Handshake.lean`) with the
exchanges counted: the `n`-th exchange hands the receiver `P n v` (the value `v` sent) and the
sender `Q n` (what the receiver offered). Each side keeps its count (`hsnSnd γ n`, `hsnRcv γ n`,
halves of two ghost variables whose other halves the invariant holds); the side that completes an
exchange finds the other's resource indexed by its own count.

The WAL's file pipeline (`filePipeline`, S/file_pipeline.go) needs it: its `n`-th file is
`N.tmp` with `N = n % 2`, and the receiver of file `n` hands back the claim on the name of file
`n + 1` (the name it renamed away in its previous cut). The plain handshake's `Q` is one
proposition for every exchange, so the sender cannot know which name it gets back.

A general idiom: to be proposed to Perennial (`notes/perennial-changes.md`); local until then.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- The ghost names of an indexed handshake: the channel's, and the two sides' counts. -/
structure HsnNames where
  ch : ChanNames
  γs : GName
  γr : GName

section hsn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The sender's count: `n` exchanges done. -/
def hsnSnd (γ : HsnNames) (n : Nat) : IProp GF := ghostVar γ.γs (1 : Qp).half n

/-- The receiver's count: `n` exchanges done. -/
def hsnRcv (γ : HsnNames) (n : Nat) : IProp GF := ghostVar γ.γr (1 : Qp).half n

/-- The indexed handshake's invariant: the channel's state, the counts (`ns` sent, `nr`
received; a side's first step of an exchange advances its own count), and the resource in flight
(`P k v` from the sender of exchange `k`, `Q k` from its receiver). -/
def hsnInv (γ : HsnNames) (P : Nat → V → IProp GF) (Q : Nat → IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState V) (ns nr : Nat), ownChan γ.ch V s ∗
    ghostVar γ.γs (1 : Qp).half ns ∗ ghostVar γ.γr (1 : Qp).half nr ∗
    (match s with
     | .Idle => iprop(⌜ns = nr⌝)
     | .SndPending v => iprop(⌜ns = nr + 1⌝ ∗ P nr v)
     | .SndCommit v => iprop(∃ k, ⌜ns = k + 1 ∧ nr = k + 1⌝ ∗ P k v)
     | .RcvPending => iprop(⌜nr = ns + 1⌝ ∗ Q ns)
     | .RcvCommit => iprop(∃ k, ⌜ns = k + 1 ∧ nr = k + 1⌝ ∗ Q k)
     | _ => iprop(False)))

/-- **An indexed handshake on the unbuffered channel `ch`** (persistent; never closed). -/
def isHsn (γ : HsnNames) (ch : Loc) (P : Nat → V → IProp GF) (Q : Nat → IProp GF) : IProp GF :=
  iprop(isChan ch γ.ch V ∗ inv nroot (hsnInv γ P Q))

instance isHsn_persistent (γ : HsnNames) (ch : Loc) (P : Nat → V → IProp GF) (Q : Nat → IProp GF) :
    Persistent (isHsn γ ch P Q) := by
  unfold isHsn; infer_instance

theorem isHsn_is_chan (γ : HsnNames) (ch : Loc) (P : Nat → V → IProp GF) (Q : Nat → IProp GF) :
    isHsn γ ch P Q ⊢ isChan ch γ.ch V := by
  unfold isHsn; iintro ⟨$, -⟩

omit [IntoValTyped (GF := GF) V t] in
theorem start_hsn (ch : Loc) (P : Nat → V → IProp GF) (Q : Nat → IProp GF) (γc : ChanNames) :
    ⊢ isChan ch γc V -∗ ownChan γc V .Idle ={⊤}=∗
      ∃ γ : HsnNames, ⌜γ.ch = γc⌝ ∗ isHsn γ ch P Q ∗ hsnSnd γ 0 ∗ hsnRcv γ 0 := by
  iintro #Hch Hoc
  imod ghostVar_alloc (0 : Nat) with ⟨%γs, Hs⟩
  icases ghostVar_split_half γs 1 (0 : Nat) $$ Hs with ⟨HsA, HsB⟩
  imod ghostVar_alloc (0 : Nat) with ⟨%γr, Hr⟩
  icases ghostVar_split_half γr 1 (0 : Nat) $$ Hr with ⟨HrA, HrB⟩
  imod inv_alloc nroot ⊤ (hsnInv ⟨γc, γs, γr⟩ P Q) $$ [Hoc HsA HrA] with #Hinv
  · inext
    unfold hsnInv
    iexists .Idle, 0, 0
    dsimp only
    iframe
    ipureintro; rfl
  imodintro
  iexists ⟨γc, γs, γr⟩
  unfold isHsn hsnSnd hsnRcv
  iframe
  iframe #
  ipureintro; rfl

theorem hsn_receive_au (γ : HsnNames) (ch : Loc) (P : Nat → V → IProp GF) (Q : Nat → IProp GF)
    (n : Nat) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isHsn γ ch P Q -∗ hsnRcv γ n -∗ Q n -∗
      ▷ (∀ v, hsnRcv γ (n + 1) -∗ P n v -∗ Φ v true) -∗ recvAu γ.ch V Φ := by
  unfold isHsn recvAu hsnRcv
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hchan, #Hinv⟩ Hrcv HQ Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold hsnInv
  icases Hi with ⟨%s, %ns, %nr, Hch, Hs, Hr, Hi⟩
  ihave %Hnr := ghostVar_agree _ _ _ _ _ $$ Hr Hrcv
  subst nr
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨_, _⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    icases Hi with %Hn
    subst ns
    iintro H
    imod Hmask with -
    imod ghostVar_update_halves (n + 1) γ.γr n n $$ Hr Hrcv with ⟨Hr, Hrcv⟩
    imod Hclose $$ [H HQ Hs Hr] with -
    · inext
      iexists .RcvPending, n, n + 1
      dsimp only
      iframe
      ipureintro; omega
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, %ns, %nr, Hch, Hs, Hr, Hi⟩
    ihave %Hnr := ghostVar_agree _ _ _ _ _ $$ Hr Hrcv
    subst nr
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      icases Hi with ⟨%k, %Hk, HP⟩
      obtain ⟨rfl, hk⟩ := Hk
      have hkn : k = n := by omega
      subst hkn
      iintro Hid
      imod Hmask with -
      imod Hclose $$ [Hid Hs Hr] with -
      · inext
        iexists .Idle, k + 1, k + 1
        dsimp only
        iframe
        ipureintro; rfl
      imodintro
      iapply Hau $$ Hrcv HP
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case SndPending =>
    icases Hi with ⟨%Hn, HP⟩
    iintro H
    imod Hmask with -
    imod ghostVar_update_halves (n + 1) γ.γr n n $$ Hr Hrcv with ⟨Hr, Hrcv⟩
    imod Hclose $$ [H HQ Hs Hr] with -
    · inext
      iexists .RcvCommit, ns, n + 1
      dsimp only
      iframe
      ipureintro; omega
    imodintro
    iapply Hau $$ Hrcv HP
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_hsn_receive (γ : HsnNames) (ch : Loc) (P : Nat → V → IProp GF) (Q : Nat → IProp GF)
    (n : Nat) :
    {{ isHsn γ ch P Q ∗ hsnRcv γ n ∗ Q n }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V), RET (PairV #v #true); hsnRcv γ (n + 1) ∗ P n v }} := by
  iintro %Φ ⟨#His, Hrcv, HQ⟩ HΦ
  ihave #Hchan := isHsn_is_chan γ ch P Q $$ His
  iapply chan.wp_receive ch γ.ch $$ Hchan
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply hsn_receive_au γ ch P Q n (fun v ok => Φ (PairV #v #ok)) $$ [$Hlc1 $Hlc2] His Hrcv HQ
  inext
  iintro %v Hrcv HP
  iapply HΦ
  iframe

theorem hsn_send_au (γ : HsnNames) (ch : Loc) (v : V) (P : Nat → V → IProp GF)
    (Q : Nat → IProp GF) (n : Nat) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isHsn γ ch P Q -∗ hsnSnd γ n -∗ P n v -∗
      ▷ (hsnSnd γ (n + 1) -∗ Q n -∗ Φ) -∗ sendAu γ.ch v Φ := by
  unfold isHsn sendAu hsnSnd
  iintro ⟨Hlc1, Hlc2, Hlc3⟩ ⟨#Hchan, #Hinv⟩ Hsnd HP Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold hsnInv
  icases Hi with ⟨%s, %ns, %nr, Hch, Hs, Hr, Hi⟩
  ihave %Hns := ghostVar_agree _ _ _ _ _ $$ Hs Hsnd
  subst ns
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with b | _ | _ | _ | _ | _ | d
  all_goals dsimp only
  case Idle =>
    icases Hi with %Hn
    subst nr
    iintro H
    imod Hmask with -
    imod ghostVar_update_halves (n + 1) γ.γs n n $$ Hs Hsnd with ⟨Hs, Hsnd⟩
    imod Hclose $$ [H HP Hs Hr] with -
    · inext
      iexists .SndPending v, n + 1, n
      dsimp only
      iframe
      ipureintro; rfl
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, %ns, %nr, Hch, Hs, Hr, Hi⟩
    ihave %Hns := ghostVar_agree _ _ _ _ _ $$ Hs Hsnd
    subst ns
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    case RcvCommit =>
      icases Hi with ⟨%k, %Hk, HQ⟩
      obtain ⟨hk, rfl⟩ := Hk
      have hkn : k = n := by omega
      subst hkn
      iintro Hid
      imod Hmask with -
      imod Hclose $$ [Hid Hs Hr] with -
      · inext
        iexists .Idle, k + 1, k + 1
        dsimp only
        iframe
        ipureintro; rfl
      imodintro
      iapply Hau $$ Hsnd HQ
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    icases Hi with ⟨%Hn, HQ⟩
    iintro H
    imod Hmask with -
    imod ghostVar_update_halves (n + 1) γ.γs n n $$ Hs Hsnd with ⟨Hs, Hsnd⟩
    imod Hclose $$ [H HP Hs Hr] with -
    · inext
      iexists .SndCommit v, n + 1, nr
      dsimp only
      iframe
      ipureintro; omega
    imodintro
    iapply Hau $$ Hsnd HQ
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_hsn_send (γ : HsnNames) (ch : Loc) (v : V) (P : Nat → V → IProp GF)
    (Q : Nat → IProp GF) (n : Nat) :
    {{ isHsn γ ch P Q ∗ hsnSnd γ n ∗ P n v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); hsnSnd γ (n + 1) ∗ Q n }} := by
  iintro %Φ ⟨#His, Hsnd, HP⟩ HΦ
  ihave #Hchan := isHsn_is_chan γ ch P Q $$ His
  iapply chan.wp_send ch v γ.ch $$ Hchan
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply hsn_send_au γ ch v P Q n (Φ #()) $$ [$Hlc1 $Hlc2 $Hlc3] His Hsnd HP
  inext
  iintro Hsnd HQ
  iapply HΦ
  iframe

end hsn

end WalFs
end EtcdGrove
end Perennial
