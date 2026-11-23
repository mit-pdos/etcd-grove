/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ServersDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The server nodes' proof (`ServersOk`): the test package's internal specs (kit.go's `decode`,
`host`, `port`, `at`, `nodeConfig`, `awaitConf`, `register`, `serve`) and their vocabulary.
Internal to the swiftnet group (not frozen): see notes/prove-servers.md.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Perennial.Golang.Theory.Chan.Idioms.Future

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## The configuration as the Go struct -/

/-- `Conf` as kit.go's struct. -/
def goConf (c : Conf) : examples.swiftnet.Conf :=
  ⟨W64 c.n, W64 c.fastRead, W64 c.pool, W64 c.desc⟩

/-- A leader change as `decode` returns it (`Client` 0). -/
def goChange (ch : Change) : examples.swiftnet.change :=
  ⟨W64 0, W64 ch.node, W64 ch.after⟩

instance goConf_countable [GooseExts] : Pos.Countable examples.swiftnet.Conf :=
  .ofInjective (fun c => Pos.Countable.encode (c.N', c.FastRead', c.Pool', c.Desc'))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- Every configuration message is `confLen` (nine) bytes. -/
theorem Conf.encodeC_length (c : Conf) (cs : List Change) : (c.encodeC cs).length = confLen := by
  unfold Conf.encodeC confLen maxChanges
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [show List.range 2 = [0, 1] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.append_nil]
  split <;> split <;> simp

instance goMsg_countable [GooseExts] : Pos.Countable examples.swiftnet.msg :=
  .ofInjective (fun m => Pos.Countable.encode (m.conf', m.cs'))
    (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; have h := Pos.encode_inj h; simp_all)

section conf
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

/-- `conf.dialP` is prefix-closed (what a reader of a configuration port uses). -/
theorem conf.dialP_closed (γ : SwiftNames netDistGF) : ProtoPrefixClosed (conf.dialP γ) where
  nil cid := by
    unfold conf.dialP
    iintro !>
    ileft; ipureintro; rfl
  pre cid a b h := by
    unfold conf.dialP
    iintro #(%Hb | ⟨%c, #Hc, %Hb⟩)
    · iintro !>; ileft; ipureintro; subst Hb; exact List.prefix_nil.mp h
    · iintro !>; iright; iexists c; iframe Hc; ipureintro; exact h.trans Hb

/-- `conf.dialPC` is prefix-closed. -/
theorem conf.dialPC_closed (γ : SwiftNames netDistGF) : ProtoPrefixClosed (conf.dialPC γ) where
  nil cid := by
    unfold conf.dialPC
    iintro !>
    ileft; ipureintro; rfl
  pre cid a b h := by
    unfold conf.dialPC
    iintro #(%Hb | ⟨%c, %cs, #Hc, %Hb⟩)
    · iintro !>; ileft; ipureintro; subst Hb; exact List.prefix_nil.mp h
    · iintro !>; iright; iexists c, cs; iframe Hc; ipureintro; exact ⟨Hb.1, h.trans Hb.2⟩

/-- What a server node's configuration port's reader has read, `confLen` bytes of it: a
configuration's encoding with no change. -/
theorem conf.dialP_full (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.dialP γ cid bs ⊢ ∃ c cs, conf.is γ c ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ cs = []⌝ := by
  unfold conf.dialP
  iintro (%Hb | ⟨%c, #Hc, %Hb⟩)
  · subst Hb; simp [confLen, maxChanges] at hl
  · ihave %Hv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
    iexists c, []
    iframe Hc
    ipureintro
    refine ⟨?_, Hv, ⟨by simp [maxChanges], by simp⟩, rfl⟩
    exact Hb.eq_of_length (by rw [hl]; exact (Conf.encodeC_length c []).symm)

/-- What a client node's configuration port's reader has read, `confLen` bytes of it: a
configuration's encoding with changes `decode` accepts. -/
theorem conf.dialPC_full (γ : SwiftNames netDistGF) (cid : Nat) (bs : List w8)
    (hl : bs.length = confLen) :
    conf.dialPC γ cid bs ⊢ ∃ c cs, conf.is γ c ∗
      ⌜bs = c.encodeC cs ∧ c.valid ∧ c.changesOk cs ∧ True⌝ := by
  unfold conf.dialPC
  iintro (%Hb | ⟨%c, %cs, #Hc, %Hb⟩)
  · subst Hb; simp [confLen, maxChanges] at hl
  · ihave %Hv := ((conf.is_confIs γ c).1.trans (confIs_valid γ.conf c)) $$ Hc
    iexists c, cs
    iframe Hc
    ipureintro
    refine ⟨?_, Hv, Hb.1, trivial⟩
    exact Hb.2.eq_of_length (by rw [hl]; exact (Conf.encodeC_length c cs).symm)

end conf

section msg
variable [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- What `awaitConf` hands to its caller over the channel (the future's contract): the
decoded message `m` is a configuration `c` (with its fact) and its changes `cs` (`decode`'s
slice, owned), which the port's dialer protocol allows (`Ok`), and `R`, what the node got when it
registered before its first acknowledgment (`awaitConf`'s `Pre ={⊤}=∗ A ∗ R`). -/
def confMsg (γ : SwiftNames netDistGF) (Ok : Conf → List Change → Prop) (R : IProp netDistGF)
    (m : examples.swiftnet.msg) : IProp netDistGF :=
  iprop(∃ (c : Conf) (cs : List Change), conf.is γ c ∗
    ⌜c.valid ∧ c.changesOk cs ∧ Ok c cs ∧ m.conf' = goConf c⌝ ∗
    m.cs' ↦* cs.map goChange ∗ R)

end msg

theorem Conf.valid_lt {c : Conf} (h : c.valid) :
    c.n < 256 ∧ c.fastRead < 256 ∧ c.pool < 256 ∧ c.desc < 256 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; omega

end Perennial.github_com.imdea_software.swiftpaxos
